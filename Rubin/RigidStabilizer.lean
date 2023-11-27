import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Basic

import Rubin.Support
import Rubin.MulActionExt

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

end Rubin
