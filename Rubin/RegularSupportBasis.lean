/-
This files defines `RegularSupportBasis`, which is a basis of the topological space α,
made up of finite intersections of `RegularSupport α g` for `g : G`.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Algebra.ConstMulAction

import Rubin.LocallyDense
import Rubin.Topology
import Rubin.Support
import Rubin.RegularSupport

namespace Rubin

/--
Maps a "seed" of homeorphisms in α to the intersection of their regular support in α.

Note that the condition that the resulting set is non-empty is introduced later in `RegularSupportBasis₀`
--/
def RegularSupport.FiniteInter {G : Type _} [Group G] (α : Type _) [TopologicalSpace α] [MulAction G α] (S : Finset G): Set α :=
  ⋂ (g ∈ S), RegularSupport α g

def RegularSupportBasis (G α : Type _) [Group G] [TopologicalSpace α] [MulAction G α] : Set (Set α) :=
  { S : Set α | S.Nonempty ∧ ∃ (seed : Finset G), S = RegularSupport.FiniteInter α seed }

variable {G : Type _}
variable {α : Type _}
variable [Group G]
variable [TopologicalSpace α]
variable [MulAction G α]

theorem RegularSupport.FiniteInter_sInter (S : Finset G) :
  RegularSupport.FiniteInter α S = ⋂₀ ((fun (g : G) => RegularSupport α g) '' S) :=
by
  rw [Set.sInter_image]
  rfl

theorem RegularSupportBasis.mem_iff (S : Set α) :
  S ∈ RegularSupportBasis G α ↔ S.Nonempty ∧ ∃ (seed : Finset G), S = RegularSupport.FiniteInter α seed :=
by
  simp only [RegularSupportBasis, Set.mem_setOf_eq]

@[simp]

theorem RegularSupport.FiniteInter_regular (F : Finset G) :
  Regular (RegularSupport.FiniteInter α F) :=
by
  rw [RegularSupport.FiniteInter_sInter]
  apply regular_sInter
  · have set_decidable : DecidableEq (Set α) := Classical.typeDecidableEq (Set α)
    let fin : Finset (Set α) := F.image ((fun g => RegularSupport α g))

    apply Set.Finite.ofFinset fin
    simp
  · intro S S_in_set
    simp at S_in_set
    let ⟨g, ⟨_, Heq⟩⟩ := S_in_set
    rw [←Heq]
    exact regularSupport_regular α g

@[simp]
theorem RegularSupportBasis.regular {S : Set α} (S_mem_basis : S ∈ RegularSupportBasis G α) : Regular S := by
  let ⟨_, ⟨seed, S_eq_inter⟩⟩ := (RegularSupportBasis.mem_iff S).mp S_mem_basis
  rw [S_eq_inter]
  apply RegularSupport.FiniteInter_regular

variable [ContinuousConstSMul G α] [DecidableEq G]

lemma RegularSupport.FiniteInter_conj (seed : Finset G) (f : G):
  RegularSupport.FiniteInter α (Finset.image (fun g => f * g * f⁻¹) seed) = f •'' RegularSupport.FiniteInter α seed :=
by
  unfold RegularSupport.FiniteInter
  simp
  conv => {
    rhs
    ext; lhs; ext x; ext; lhs
    ext
    rw [regularSupport_smulImage]
  }

/--
A group element `f` acts on sets of `RegularSupportBasis G α`,
by mapping each element `g` of `S.seed` to `f * g * f⁻¹`
--/
noncomputable instance RegularSupportBasis.instSmul : SMul G (RegularSupportBasis G α) where
  smul := fun f S =>
    let new_seed := (Finset.image (fun g => f * g * f⁻¹) S.prop.right.choose)
    ⟨
      RegularSupport.FiniteInter α new_seed,
      by
        rw [RegularSupportBasis.mem_iff]
        nth_rw 1 [RegularSupport.FiniteInter_conj, smulImage_nonempty]
        rw [←S.prop.right.choose_spec]

        constructor
        · exact S.prop.left
        · use new_seed
    ⟩

theorem RegularSupportBasis.smul_eq' (f : G) (S : RegularSupportBasis G α) :
  (f • S).val
    = RegularSupport.FiniteInter α (Finset.image (fun g => f * g * f⁻¹) S.prop.right.choose) := rfl

theorem RegularSupportBasis.smul_eq (f : G) (S : RegularSupportBasis G α) :
  (f • S).val = f •'' S.val :=
by
  rw [RegularSupportBasis.smul_eq']
  rw [RegularSupport.FiniteInter_conj]
  rw [←S.prop.right.choose_spec]

theorem RegularSupportBasis.smulImage_in_basis {U : Set α} (U_in_basis : U ∈ RegularSupportBasis G α)
  (f : G) : f •'' U ∈ RegularSupportBasis G α :=
by
  have eq := smul_eq f ⟨U, U_in_basis⟩
  simp only at eq
  rw [←eq]
  exact Subtype.coe_prop _

def RegularSupportBasis.fromSingleton [T2Space α] [FaithfulSMul G α] (g : G) (g_ne_one : g ≠ 1) : { S : Set α // S ∈ RegularSupportBasis G α } :=
  let seed : Finset G := {g}
  ⟨
    RegularSupport.FiniteInter α seed,
    by
      rw [RegularSupportBasis.mem_iff]
      constructor
      swap
      use seed

      rw [Set.nonempty_iff_ne_empty]
      intro rsupp_empty
      apply g_ne_one
      apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
      intro x
      simp
      rw [←not_mem_support]
      apply Set.not_mem_subset
      · apply support_subset_regularSupport
      · simp [RegularSupport.FiniteInter] at rsupp_empty
        rw [rsupp_empty]
        exact Set.not_mem_empty x
  ⟩

theorem RegularSupportBasis.fromSingleton_val [T2Space α] [FaithfulSMul G α] (g : G) (g_ne_one : g ≠ 1) :
  (fromSingleton g g_ne_one).val = RegularSupport α g := by simp [fromSingleton, RegularSupport.FiniteInter]

-- Note: we could potentially implement MulActionHom
noncomputable instance RegularSupportBasis.instMulAction : MulAction G (RegularSupportBasis G α) where
  one_smul := by
    intro S
    apply Subtype.eq
    rw [RegularSupportBasis.smul_eq]
    rw [one_smulImage]
  mul_smul := by
    intro S f g
    apply Subtype.eq
    repeat rw [RegularSupportBasis.smul_eq]
    rw [smulImage_mul]

theorem RegularSupportBasis.smul_mono {S T : RegularSupportBasis G α} (f : G) (S_le_T : S.val ⊆ T.val) :
  (f • S).val ⊆ (f • T).val :=
by
  repeat rw [RegularSupportBasis.smul_eq]
  apply smulImage_mono
  assumption

section Basis
open Topology

variable (G α : Type _)
variable [Group G]
variable [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] [HasNoIsolatedPoints α]
variable [MulAction G α] [LocallyDense G α] [ContinuousConstSMul G α]

-- TODO: clean this lemma to not mention W anymore?
lemma proposition_3_2_subset
  {U : Set α} (U_open : IsOpen U) {p : α} (p_in_U : p ∈ U) :
  ∃ (W : Set α), W ∈ 𝓝 p ∧ closure W ⊆ U ∧
  ∃ (g : G), g ∈ RigidStabilizer G W ∧ p ∈ RegularSupport α g ∧ RegularSupport α g ⊆ closure W :=
by
  have U_in_nhds : U ∈ 𝓝 p := by
    rw [mem_nhds_iff]
    use U

  let ⟨W', W'_in_nhds, W'_ss_U, W'_compact⟩ := local_compact_nhds U_in_nhds

  -- This feels like black magic, but okay
  let ⟨W, _W_compact, W_closed, W'_ss_int_W, W_ss_U⟩ := exists_compact_closed_between W'_compact U_open W'_ss_U
  have W_cl_eq_W : closure W = W := IsClosed.closure_eq W_closed

  have W_in_nhds : W ∈ 𝓝 p := by
    rw [mem_nhds_iff]
    use interior W
    repeat' apply And.intro
    · exact interior_subset
    · simp
    · exact W'_ss_int_W (mem_of_mem_nhds W'_in_nhds)

  use W

  repeat' apply And.intro
  exact W_in_nhds
  {
    rw [W_cl_eq_W]
    exact W_ss_U
  }

  have p_in_int_W : p ∈ interior W := W'_ss_int_W (mem_of_mem_nhds W'_in_nhds)

  let ⟨g, g_in_rist, g_moves_p⟩ := get_moving_elem_in_rigidStabilizer G isOpen_interior p_in_int_W

  use g
  repeat' apply And.intro
  · apply rigidStabilizer_mono interior_subset
    simp
    exact g_in_rist
  · rw [←mem_support] at g_moves_p
    apply support_subset_regularSupport
    exact g_moves_p
  · rw [rigidStabilizer_support] at g_in_rist
    apply subset_trans
    exact regularSupport_subset_closure_support
    apply closure_mono
    apply subset_trans
    exact g_in_rist
    exact interior_subset

/--
## Proposition 3.2 : RegularSupportBasis is a topological basis of `α`
-/
theorem RegularSupportBasis.isBasis :
  TopologicalSpace.IsTopologicalBasis (RegularSupportBasis G α) :=
by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  {
    intro U U_in_poset
    exact (RegularSupportBasis.regular U_in_poset).isOpen
  }
  intro p U p_in_U U_open

  let ⟨W, _, clW_ss_U, ⟨g, _, p_in_rsupp, rsupp_ss_clW⟩⟩ := proposition_3_2_subset G α U_open p_in_U
  use RegularSupport α g
  repeat' apply And.intro
  · exact ⟨p, p_in_rsupp⟩
  · use {g}
    simp [RegularSupport.FiniteInter]
  · assumption
  · apply subset_trans
    exact rsupp_ss_clW
    exact clW_ss_U

theorem RegularSupportBasis.closed_inter (b1 b2 : Set α)
  (b1_in_basis : b1 ∈ RegularSupportBasis G α)
  (b2_in_basis : b2 ∈ RegularSupportBasis G α)
  (inter_nonempty : Set.Nonempty (b1 ∩ b2)) :
  (b1 ∩ b2) ∈ RegularSupportBasis G α :=
by
  unfold RegularSupportBasis
  simp
  constructor
  assumption

  let ⟨_, ⟨s1, b1_eq⟩⟩ := b1_in_basis
  let ⟨_, ⟨s2, b2_eq⟩⟩ := b2_in_basis

  have dec_eq : DecidableEq G := Classical.typeDecidableEq G
  use s1 ∪ s2
  rw [RegularSupport.FiniteInter_sInter]
  rw [Finset.coe_union, Set.image_union, Set.sInter_union]
  repeat rw [←RegularSupport.FiniteInter_sInter]
  rw [b2_eq, b1_eq]

theorem RegularSupportBasis.empty_not_mem :
  ∅ ∉ RegularSupportBasis G α :=
by
  intro empty_mem
  rw [RegularSupportBasis.mem_iff] at empty_mem
  exact Set.not_nonempty_empty empty_mem.left

theorem RegularSupportBasis.univ_mem [Nonempty α]:
  Set.univ ∈ RegularSupportBasis G α :=
by
  rw [RegularSupportBasis.mem_iff]
  constructor
  exact Set.univ_nonempty
  use ∅
  simp [RegularSupport.FiniteInter]

end Basis
end Rubin
