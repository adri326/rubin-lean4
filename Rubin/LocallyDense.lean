import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.ConstMulAction

import Rubin.RigidStabilizer
import Rubin.InteriorClosure

namespace Rubin

open Topology

/--
A group action is said to be "locally dense" if for any open set `U` and `p ∈ U`,
the closure of the orbit of `p` under the `RigidStabilizer G U` contains a neighborhood of `p`.

The definition provided here is an equivalent one, that does not require using filters.
See [`LocallyDense.from_rigidStabilizer_in_nhds`] and [`LocallyDense.rigidStabilizer_in_nhds`]
to translate from/to the original definition.

A weaker relationship, [`LocallyMoving`], is used whenever possible.
The main difference between the two is that `LocallyMoving` does not allow us to find a group member
`g ∈ G` such that `g • p ≠ p` — it only allows us to know that `∃ g ∈ RigidStabilizer G U, g ≠ 1`.
--/
class LocallyDense (G α : Type _) [Group G] [TopologicalSpace α] [MulAction G α] :=
  isLocallyDense:
    ∀ U : Set α,
    IsOpen U →
    ∀ p ∈ U,
    p ∈ interior (closure (MulAction.orbit (RigidStabilizer G U) p))
#align is_locally_dense Rubin.LocallyDense

theorem LocallyDense.from_rigidStabilizer_in_nhds (G α : Type _) [Group G] [TopologicalSpace α] [MulAction G α] :
  (∀ U : Set α, IsOpen U → ∀ p ∈ U, closure (MulAction.orbit G•[U] p) ∈ 𝓝 p) →
  LocallyDense G α :=
by
  intro hyp
  constructor
  intro U U_open p p_in_U

  have closure_in_nhds := hyp U U_open p p_in_U
  rw [mem_nhds_iff] at closure_in_nhds

  rw [mem_interior]
  exact closure_in_nhds

theorem LocallyDense.rigidStabilizer_in_nhds (G α : Type _) [Group G] [TopologicalSpace α]
  [MulAction G α] [LocallyDense G α]
  {U : Set α} (U_open : IsOpen U) {p : α} (p_in_U : p ∈ U)
:
  closure (MulAction.orbit G•[U] p) ∈ 𝓝 p :=
by
  rw [mem_nhds_iff]
  rw [<-mem_interior]
  apply LocallyDense.isLocallyDense <;> assumption

lemma LocallyDense.elem_from_nonEmpty {G α : Type _} [Group G] [TopologicalSpace α] [MulAction G α] [LocallyDense G α]:
  ∀ {U : Set α},
  IsOpen U →
  Set.Nonempty U →
  ∃ p ∈ U, p ∈ interior (closure (MulAction.orbit G•[U] p)) :=
by
  intros U U_open H_ne
  exact ⟨H_ne.some, H_ne.some_mem, LocallyDense.isLocallyDense U U_open H_ne.some H_ne.some_mem⟩

/--
This is a stronger statement than `LocallyMoving.get_nontrivial_rist_elem`,
as here we are able to prove that the nontrivial element does move `p`.

The condition that `Filer.NeBot (𝓝[≠] p)` is automatically satisfied by the `HasNoIsolatedPoints` class.
--/
theorem get_moving_elem_in_rigidStabilizer (G : Type _) {α : Type _}
  [Group G] [TopologicalSpace α] [MulAction G α] [LocallyDense G α]
  [T1Space α] {p : α} [Filter.NeBot (𝓝[≠] p)]
  {U : Set α} (U_open : IsOpen U) (p_in_U : p ∈ U) :
  ∃ g : G, g ∈ G•[U] ∧ g • p ≠ p :=
by
  by_contra g_not_exist
  rw [<-Classical.not_forall_not] at g_not_exist
  simp at g_not_exist

  have orbit_singleton : MulAction.orbit (RigidStabilizer G U) p = {p} := by
    ext x
    rw [MulAction.mem_orbit_iff]
    rw [Set.mem_singleton_iff]
    simp
    constructor
    · intro ⟨g, g_in_rist, g_eq_p⟩
      rw [g_not_exist g g_in_rist] at g_eq_p
      exact g_eq_p.symm
    · intro x_eq_p
      use 1
      rw [x_eq_p, one_smul]
      exact ⟨Subgroup.one_mem _, rfl⟩

  have regular_orbit_empty : interior (closure (MulAction.orbit (RigidStabilizer G U) p)) = ∅ := by
    rw [orbit_singleton]
    rw [closure_singleton]
    rw [interior_singleton]

  have p_in_regular_orbit := LocallyDense.isLocallyDense (G := G) U U_open p p_in_U
  rw [regular_orbit_empty] at p_in_regular_orbit
  exact p_in_regular_orbit

class LocallyMoving (G α : Type _) [Group G] [TopologicalSpace α] [MulAction G α] :=
  locally_moving: ∀ U : Set α, IsOpen U → Set.Nonempty U → RigidStabilizer G U ≠ ⊥
#align is_locally_moving Rubin.LocallyMoving

theorem LocallyMoving.get_nontrivial_rist_elem {G α : Type _}
  [Group G]
  [TopologicalSpace α]
  [MulAction G α]
  [h_lm : LocallyMoving G α]
  {U: Set α}
  (U_open : IsOpen U)
  (U_nonempty : U.Nonempty) :
  ∃ x : G, x ∈ G•[U] ∧ x ≠ 1 :=
by
  have rist_ne_bot := h_lm.locally_moving U U_open U_nonempty
  exact (or_iff_right rist_ne_bot).mp (Subgroup.bot_or_exists_ne_one _)

theorem LocallyMoving.nontrivial_elem (G α : Type _) [Group G] [TopologicalSpace α]
  [MulAction G α] [LocallyMoving G α] [Nonempty α] :
  ∃ g: G, g ≠ 1 :=
by
  let ⟨g, _, g_ne_one⟩ := (get_nontrivial_rist_elem (G := G) (α := α) isOpen_univ Set.univ_nonempty)
  use g

theorem LocallyMoving.nontrivial {G α : Type _} [Group G] [TopologicalSpace α]
  [MulAction G α] [LocallyMoving G α] [Nonempty α] : Nontrivial G where
  exists_pair_ne := by
    use 1
    simp only [ne_comm]
    exact nontrivial_elem G α

variable {G α : Type _}
variable [Group G]
variable [TopologicalSpace α]
variable [MulAction G α]
variable [ContinuousConstSMul G α]
variable [FaithfulSMul G α]

instance dense_locally_moving [T2Space α]
  [H_nip : HasNoIsolatedPoints α]
  [H_ld : LocallyDense G α] :
  LocallyMoving G α
where
  locally_moving := by
    intros U U_open H_nonempty
    by_contra h_rs
    have ⟨elem, ⟨_, some_in_orbit⟩⟩ := H_ld.elem_from_nonEmpty U_open H_nonempty
    rw [h_rs] at some_in_orbit
    simp at some_in_orbit

lemma disjoint_nbhd [T2Space α] {g : G} {x : α} (x_moved: g • x ≠ x) :
  ∃ U: Set α, IsOpen U ∧ x ∈ U ∧ Disjoint U (g •'' U) :=
by
  have ⟨V, W, V_open, W_open, gx_in_V, x_in_W, disjoint_V_W⟩ := T2Space.t2 (g • x) x x_moved
  let U := (g⁻¹ •'' V) ∩ W
  use U
  constructor
  exact IsOpen.inter (smulImage_isOpen g⁻¹ V_open) W_open

  constructor
  {
    simp
    rw [mem_inv_smulImage]
    trivial
  }
  {
    apply Set.disjoint_of_subset
    · apply Set.inter_subset_right
    · intro y hy; show y ∈ V

      rw [<-smul_inv_smul g y]
      rw [<-mem_inv_smulImage]

      rw [mem_smulImage] at hy
      simp at hy
      simp

      exact hy.left
    · exact disjoint_V_W.symm
  }

lemma disjoint_nbhd_in [T2Space α] {g : G} {x : α} {V : Set α}
  (V_open : IsOpen V) (x_in_V : x ∈ V) (x_moved : g • x ≠ x) :
  ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ Disjoint U (g •'' U) :=
by
  have ⟨W, W_open, x_in_W, disjoint_W_img⟩ := disjoint_nbhd x_moved
  use W ∩ V
  simp
  constructor
  {
    apply IsOpen.inter <;> assumption
  }
  constructor
  {
    constructor <;> assumption
  }
  show Disjoint (W ∩ V) (g •'' W ∩ V)
  apply Set.disjoint_of_subset
  · exact Set.inter_subset_left W V
  · show g •'' W ∩ V ⊆ g •'' W
    rewrite [smulImage_inter]
    exact Set.inter_subset_left _ _
  · exact disjoint_W_img

/--
## Proposition 3.1:

If a group action is faithful, continuous and "locally moving",
then `U ⊆ V` if and only if `G•[U] ≤ G•[V]` when `U` and `V` are regular.
--/
theorem rigidStabilizer_subset_iff (G : Type _) {α : Type _} [Group G] [TopologicalSpace α]
  [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α]
  [h_lm : LocallyMoving G α]
  {U V : Set α} (U_reg : Regular U) (V_reg : Regular V):
  U ⊆ V ↔ G•[U] ≤ G•[V] :=
by
  constructor
  exact rigidStabilizer_mono
  intro rist_ss

  by_contra U_not_ss_V

  let W := U \ closure V
  have W_nonempty : Set.Nonempty W := by
    by_contra W_empty
    apply U_not_ss_V
    apply subset_from_diff_closure_eq_empty
    · assumption
    · exact U_reg.isOpen
    · rw [Set.not_nonempty_iff_eq_empty] at W_empty
      exact W_empty
  have W_ss_U : W ⊆ U := by
    simp
    exact Set.diff_subset _ _
  have W_open : IsOpen W := by
    unfold_let
    rw [Set.diff_eq_compl_inter]
    apply IsOpen.inter
    simp
    exact U_reg.isOpen

  have ⟨f, f_in_ristW, f_ne_one⟩ := h_lm.get_nontrivial_rist_elem W_open W_nonempty

  have f_in_ristU : f ∈ RigidStabilizer G U := by
    exact rigidStabilizer_mono W_ss_U f_in_ristW

  have f_notin_ristV : f ∉ RigidStabilizer G V := by
    apply rigidStabilizer_compl f_ne_one
    apply rigidStabilizer_mono _ f_in_ristW
    calc
      W = U ∩ (closure V)ᶜ := by unfold_let; rw [Set.diff_eq_compl_inter, Set.inter_comm]
      _ ⊆ (closure V)ᶜ := Set.inter_subset_right _ _
      _ ⊆ Vᶜ := by
        rw [Set.compl_subset_compl]
        exact subset_closure

  exact f_notin_ristV (rist_ss f_in_ristU)

/--
A corollary of the previous theorem is that the rigid stabilizers of two regular sets `U` and `V`
are equal if and only if `U = V`.
--/
theorem rigidStabilizer_eq_iff (G : Type _) [Group G] {α : Type _} [TopologicalSpace α]
  [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α] [LocallyMoving G α]
  {U V : Set α} (U_reg : Regular U) (V_reg : Regular V):
  G•[U] = G•[V] ↔ U = V :=
by
  constructor
  · intro rist_eq
    apply le_antisymm <;> simp only [Set.le_eq_subset]
    all_goals {
      rw [rigidStabilizer_subset_iff G] <;> try assumption
      rewrite [rist_eq]
      rfl
    }
  · intro H_eq
    rw [H_eq]

theorem rigidStabilizer_empty_iff (G : Type _) [Group G] {α : Type _} [TopologicalSpace α]
  [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α] [LocallyMoving G α]
  {U : Set α} (U_reg : Regular U) :
  G•[U] = ⊥ ↔ U = ∅ :=
by
  rw [<-rigidStabilizer_empty (α := α) (G := G)]
  exact rigidStabilizer_eq_iff G U_reg (regular_empty α)

end Rubin
