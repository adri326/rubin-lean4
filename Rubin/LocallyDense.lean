import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Basic

import Rubin.RigidStabilizer

namespace Rubin

open Topology

class LocallyDense (G α : Type _) [Group G] [TopologicalSpace α] [MulAction G α] :=
  isLocallyDense:
    ∀ U : Set α,
    ∀ p ∈ U,
    p ∈ interior (closure (MulAction.orbit (RigidStabilizer G U) p))
#align is_locally_dense Rubin.LocallyDense

lemma LocallyDense.nonEmpty {G α : Type _} [Group G] [TopologicalSpace α] [MulAction G α] [LocallyDense G α]:
  ∀ {U : Set α},
  Set.Nonempty U →
  ∃ p ∈ U, p ∈ interior (closure (MulAction.orbit (RigidStabilizer G U) p)) :=
by
  intros U H_ne
  exact ⟨H_ne.some, H_ne.some_mem, LocallyDense.isLocallyDense U H_ne.some H_ne.some_mem⟩

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
  ∃ x : G, x ∈ RigidStabilizer G U ∧ x ≠ 1 :=
by
  have rist_ne_bot := h_lm.locally_moving U U_open U_nonempty
  exact (or_iff_right rist_ne_bot).mp (Subgroup.bot_or_exists_ne_one _)

variable {G α : Type _}
variable [Group G]
variable [TopologicalSpace α]
variable [MulAction G α]
variable [ContinuousMulAction G α]
variable [FaithfulSMul G α]

instance dense_locally_moving [T2Space α]
  [H_nip : HasNoIsolatedPoints α]
  [H_ld : LocallyDense G α] :
  LocallyMoving G α
where
  locally_moving := by
    intros U _ H_nonempty
    by_contra h_rs
    have ⟨elem, ⟨_, some_in_orbit⟩⟩ := H_ld.nonEmpty H_nonempty
    rw [h_rs] at some_in_orbit
    simp at some_in_orbit

lemma disjoint_nbhd [T2Space α] {g : G} {x : α} (x_moved: g • x ≠ x) :
  ∃ U: Set α, IsOpen U ∧ x ∈ U ∧ Disjoint U (g •'' U) :=
by
  have ⟨V, W, V_open, W_open, gx_in_V, x_in_W, disjoint_V_W⟩ := T2Space.t2 (g • x) x x_moved
  let U := (g⁻¹ •'' V) ∩ W
  use U
  constructor
  {
    -- NOTE: if this is common, then we should make a tactic for solving IsOpen goals
    exact IsOpen.inter (img_open_open g⁻¹ V V_open) W_open
  }
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


end Rubin
