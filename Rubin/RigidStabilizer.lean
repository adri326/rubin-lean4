import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Basic

import Rubin.Support

namespace Rubin

-- comment by Cedric: would be nicer to define just a subset, and then show it is a subgroup
def rigidStabilizer' (G : Type _) [Group G] [MulAction G α] (U : Set α) : Set G :=
  {g : G | ∀ x : α, g • x = x ∨ x ∈ U}
#align rigid_stabilizer' Rubin.rigidStabilizer'

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

theorem rist_supported_in_set {g : G} {U : Set α} :
    g ∈ RigidStabilizer G U → Support α g ⊆ U := fun h x x_in_support =>
  by_contradiction (x_in_support ∘ h x)
#align rist_supported_in_set Rubin.rist_supported_in_set

theorem rist_ss_rist {U V : Set α} (V_ss_U : V ⊆ U) :
    (RigidStabilizer G V : Set G) ⊆ (RigidStabilizer G U : Set G) :=
  by
  intro g g_in_ristV x x_notin_U
  have x_notin_V : x ∉ V := by intro x_in_V; exact x_notin_U (V_ss_U x_in_V)
  exact g_in_ristV x x_notin_V
#align rist_ss_rist Rubin.rist_ss_rist

end Rubin
