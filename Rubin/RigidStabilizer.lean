import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Basic

import Rubin.Support
import Rubin.MulActionExt

namespace Rubin

-- comment by Cedric: would be nicer to define just a subset, and then show it is a subgroup
def rigidStabilizer' (G : Type _) [Group G] [MulAction G α] (U : Set α) : Set G :=
  {g : G | ∀ x : α, g • x = x ∨ x ∈ U}
#align rigid_stabilizer' Rubin.rigidStabilizer'

/--
A "rigid stabilizer" is a subgroup of `G` associated with a set `U` for which `Support α g ⊆ U` is true for all of its elements.

In other words, a rigid stabilizer for a set `U` contains all elements of `G` that don't move points outside of `U`.

The notation for this subgroup is `G•[U]`.
You might sometimes find an expression written as `↑G•[U]` when `G•[U]` is used as a set.
--/
def RigidStabilizer (G : Type _) [Group G] [MulAction G α] (U : Set α) : Subgroup G
    where
  carrier := {g : G | ∀ (x) (_ : x ∉ U), g • x = x}
  mul_mem' ha hb x x_notin_U := by rw [mul_smul, hb x x_notin_U, ha x x_notin_U]
  inv_mem' hg x x_notin_U := smul_eq_iff_inv_smul_eq.mp (hg x x_notin_U)
  one_mem' x _ := one_smul G x
#align rigid_stabilizer Rubin.RigidStabilizer

notation:max G "•[" U "]" => RigidStabilizer G U

variable {G α: Type _}
variable [Group G]
variable [MulAction G α]

theorem rigidStabilizer_support {g : G} {U : Set α} :
  g ∈ RigidStabilizer G U ↔ Support α g ⊆ U :=
⟨
  fun h x x_in_support =>
    by_contradiction (x_in_support ∘ h x),
  by
    intro support_sub
    rw [<-Subgroup.mem_carrier]
    unfold RigidStabilizer; simp
    intro x x_notin_U
    by_contra h
    exact x_notin_U (support_sub h)
⟩
#align rist_supported_in_set Rubin.rigidStabilizer_support

theorem rigidStabilizer_mono {U V : Set α} (V_ss_U : V ⊆ U) :
  (RigidStabilizer G V : Set G) ⊆ (RigidStabilizer G U : Set G) :=
by
  intro g g_in_ristV x x_notin_U
  have x_notin_V : x ∉ V := by intro x_in_V; exact x_notin_U (V_ss_U x_in_V)
  exact g_in_ristV x x_notin_V
#align rist_ss_rist Rubin.rigidStabilizer_mono

theorem monotone_rigidStabilizer : Monotone (RigidStabilizer (α := α) G) := fun _ _ => rigidStabilizer_mono

theorem rigidStabilizer_compl [FaithfulSMul G α] {U : Set α} {f : G} (f_ne_one : f ≠ 1) :
  f ∈ G•[Uᶜ] → f ∉ G•[U] :=
by
  intro f_in_rist_compl
  intro f_in_rist
  rw [rigidStabilizer_support] at f_in_rist_compl
  rw [rigidStabilizer_support] at f_in_rist
  rw [Set.subset_compl_iff_disjoint_left] at f_in_rist_compl
  have supp_empty : Support α f = ∅ := empty_of_subset_disjoint f_in_rist_compl.symm f_in_rist
  exact f_ne_one ((support_empty_iff f).mp supp_empty)

theorem commute_if_rigidStabilizer_and_disjoint {g h : G} {U : Set α} [FaithfulSMul G α] :
  g ∈ RigidStabilizer G U → Disjoint U (Support α h) → Commute g h :=
by
  intro g_in_rist U_disj
  unfold Commute
  unfold SemiconjBy
  apply eq_of_smul_eq_smul (α := α)
  intro x

  by_cases x_in_U?: x ∈ U
  {
    rw [rigidStabilizer_support] at g_in_rist
    have x_notin_support : x ∉ Support α h := disjoint_not_mem U_disj x_in_U?

    rw [mul_smul]
    rw [not_mem_support.mp x_notin_support]
    rw [mul_smul]

    by_cases gx_in_U?: g • x ∈ U
    {
      symm
      apply not_mem_support.mp
      apply disjoint_not_mem U_disj
      exact gx_in_U?
    }
    {
      have gx_notin_support : g • x ∉ Support α g := by
        intro h
        exact gx_in_U? (g_in_rist h)
      rw [<-support_inv] at gx_notin_support
      rw [not_mem_support] at gx_notin_support
      simp at gx_notin_support
      symm at gx_notin_support
      rw [fixes_inv] at gx_notin_support
      rw [<-gx_notin_support]
      group_action
      rw [not_mem_support.mp x_notin_support]
    }
  }
  {
    have x_fixed : g • x = x := g_in_rist _ x_in_U?
    repeat rw [mul_smul]
    rw [x_fixed]

    by_cases hx_in_U?: h • x ∈ U
    {
      have hx_notin_support := disjoint_not_mem U_disj hx_in_U?
      rw [<-support_inv] at hx_notin_support
      rw [not_mem_support] at hx_notin_support
      group_action at hx_notin_support
      rw [<-hx_notin_support]
      exact x_fixed
    }
    {
      rw [g_in_rist _ hx_in_U?]
    }
  }

theorem rigidStabilizer_inter (U V : Set α) :
  G•[U ∩ V] = G•[U] ⊓ G•[V] :=
by
  ext x
  simp
  repeat rw [rigidStabilizer_support]
  rw [Set.subset_inter_iff]

theorem rigidStabilizer_empty (G α: Type _) [Group G] [MulAction G α] [FaithfulSMul G α]:
  G•[(∅ : Set α)] = ⊥ :=
by
  rw [Subgroup.eq_bot_iff_forall]
  intro f f_in_rist
  rw [<-Subgroup.mem_carrier] at f_in_rist
  apply eq_of_smul_eq_smul (α := α)

  intro x
  rw [f_in_rist x (Set.not_mem_empty x)]
  simp

theorem rigidStabilizer_sInter (S : Set (Set α)) :
  G•[⋂₀ S] = ⨅ T ∈ S, G•[T] :=
by
  ext x
  rw [rigidStabilizer_support]
  constructor
  · intro supp_ss_sInter
    rw [Subgroup.mem_iInf]
    intro T
    rw [Subgroup.mem_iInf]
    intro T_in_S
    rw [rigidStabilizer_support]
    rw [Set.subset_sInter_iff] at supp_ss_sInter
    exact supp_ss_sInter T T_in_S
  · intro x_in_rist
    rw [Set.subset_sInter_iff]
    intro T T_in_S
    rw [<-rigidStabilizer_support]
    rw [Subgroup.mem_iInf] at x_in_rist
    specialize x_in_rist T
    rw [Subgroup.mem_iInf] at x_in_rist
    exact x_in_rist T_in_S

theorem rigidStabilizer_smulImage (f g : G) (S : Set α) :
  g ∈ G•[f •'' S] ↔ f⁻¹ * g * f ∈ G•[S] :=
by
  repeat rw [rigidStabilizer_support]
  nth_rw 3 [<-inv_inv f]
  rw [support_conjugate]
  rw [smulImage_subset_inv]
  simp

theorem orbit_rigidStabilizer_subset {p : α} {U : Set α} (p_in_U : p ∈ U):
  MulAction.orbit G•[U] p ⊆ U :=
by
  intro q q_in_orbit
  have ⟨⟨h, h_in_rist⟩, hp_eq_q⟩ := MulAction.mem_orbit_iff.mp q_in_orbit
  simp at hp_eq_q
  rw [<-hp_eq_q]
  rw [rigidStabilizer_support] at h_in_rist
  rw [<-elem_moved_in_support' p h_in_rist]
  assumption

end Rubin
