import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Basic

import Rubin.Support

namespace Rubin

-- comment by Cedric: would be nicer to define just a subset, and then show it is a subgroup
def rigidStabilizer' (G : Type _) [Group G] [MulAction G α] (U : Set α) : Set G :=
  {g : G | ∀ x : α, g • x = x ∨ x ∈ U}
#align rigid_stabilizer' Rubin.rigidStabilizer'

-- A subgroup of G for which `Support α g ⊆ U`, or in other words, all elements of `G` that don't move points outside of `U`.
def RigidStabilizer (G : Type _) [Group G] [MulAction G α] (U : Set α) : Subgroup G
    where
  carrier := {g : G | ∀ (x) (_ : x ∉ U), g • x = x}
  mul_mem' ha hb x x_notin_U := by rw [mul_smul, hb x x_notin_U, ha x x_notin_U]
  inv_mem' hg x x_notin_U := smul_eq_iff_inv_smul_eq.mp (hg x x_notin_U)
  one_mem' x _ := one_smul G x
#align rigid_stabilizer Rubin.RigidStabilizer

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

theorem rigidStabilizer_to_subgroup_closure {g : G} {U : Set α} :
  g ∈ RigidStabilizer G U → g ∈ Subgroup.closure { g : G | Support α g ⊆ U } :=
by
  rw [rigidStabilizer_support]
  intro h
  rw [Subgroup.mem_closure]
  intro V orbit_subset_V
  apply orbit_subset_V
  simp
  exact h

end Rubin
