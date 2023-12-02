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

theorem LocallyDense.from_rigidStabilizer_in_nhds (G α : Type _) [Group G] [TopologicalSpace α] [MulAction G α] :
  (∀ U : Set α, IsOpen U → ∀ p ∈ U, closure (MulAction.orbit (RigidStabilizer G U) p) ∈ 𝓝 p) →
  LocallyDense G α :=
by
  intro hyp
  constructor
  intro U p p_in_U

  -- TODO: potentially add that requirement to LocallyDense?
  have U_open : IsOpen U := sorry

  have closure_in_nhds := hyp U U_open p p_in_U
  rw [mem_nhds_iff] at closure_in_nhds

  rw [mem_interior]
  exact closure_in_nhds

-- TODO: rename
lemma LocallyDense.nonEmpty {G α : Type _} [Group G] [TopologicalSpace α] [MulAction G α] [LocallyDense G α]:
  ∀ {U : Set α},
  Set.Nonempty U →
  ∃ p ∈ U, p ∈ interior (closure (MulAction.orbit (RigidStabilizer G U) p)) :=
by
  intros U H_ne
  exact ⟨H_ne.some, H_ne.some_mem, LocallyDense.isLocallyDense U H_ne.some H_ne.some_mem⟩

/--
This is a stronger statement than `LocallyMoving.get_nontrivial_rist_elem`,
as here we are able to prove that the nontrivial element does move `p`.

The condition that `Filer.NeBot (𝓝[≠] p)` is automatically satisfied by the `HasNoIsolatedPoints` class.
--/
theorem get_moving_elem_in_rigidStabilizer (G : Type _) {α : Type _}
  [Group G] [TopologicalSpace α] [MulAction G α] [LocallyDense G α]
  [T1Space α] {p : α} [Filter.NeBot (𝓝[≠] p)]
  {U : Set α} (p_in_U : p ∈ U) :
  ∃ g : G, g ∈ RigidStabilizer G U ∧ g • p ≠ p :=
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

  have p_in_regular_orbit := LocallyDense.isLocallyDense (G := G) U p p_in_U
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
