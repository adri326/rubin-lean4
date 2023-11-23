import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.GroupAction.Basic

import Rubin.Tactic
import Rubin.Support
import Rubin.RigidStabilizer

namespace Rubin

variable {G α: Type _}
variable [Group G]
variable [MulAction G α] [FaithfulSMul G α]

theorem faithful_moves_point {g : G} (h2 : ∀ x : α, g • x = x) : g = 1 := by
  have h3 : ∀ x : α, g • x = (1 : G) • x := by group_action; apply h2
  exact eq_of_smul_eq_smul h3
#align faithful_moves_point Rubin.faithful_moves_point

theorem faithful_moves_point' {g : G} (α : Type _) [MulAction G α] [FaithfulSMul G α] :
    g ≠ 1 → ∃ x : α, g • x ≠ x := by
  intro k
  apply Classical.byContradiction; intro h
  rewrite [Classical.not_exists_not] at h
  exact k (faithful_moves_point h)
#align faithful_moves_point' Rubin.faithful_moves_point'

theorem faithful_rigid_stabilizer_moves_point {g : G} {U : Set α} :
    g ∈ rigidStabilizer G U → g ≠ 1 → ∃ x ∈ U, g • x ≠ x :=
  by
  intro g_rigid g_ne_one
  let ⟨x, xmoved⟩ := Rubin.faithful_moves_point' α g_ne_one
  exact ⟨x, rist_supported_in_set g_rigid xmoved, xmoved⟩
#align faithful_rist_moves_point Rubin.faithful_rigid_stabilizer_moves_point

theorem ne_one_support_nonempty {g : G} : g ≠ 1 → (Support α g).Nonempty :=
  by
  intro h1
  let ⟨x, h⟩ := Rubin.faithful_moves_point' α h1
  use x
  exact h
#align ne_one_support_nempty Rubin.ne_one_support_nonempty

theorem disjoint_commute {f g : G} :
    Disjoint (Support α f) (Support α g) → Commute f g :=
  by
  intro hdisjoint
  rw [← commutatorElement_eq_one_iff_commute]
  apply Rubin.faithful_moves_point (α := α)
  intro x
  rw [commutatorElement_def, mul_smul, mul_smul, mul_smul]

  by_cases hffixed: (x ∈ Support α f)
  {
    rename _ => hfmoved
    rw [
      smul_eq_iff_inv_smul_eq.mp (not_mem_support.mp (Set.disjoint_left.mp hdisjoint hfmoved)),
      not_mem_support.mp
        (Set.disjoint_left.mp hdisjoint (inv_smul_mem_support hfmoved)),
      smul_inv_smul
    ]
  }

  by_cases hgfixed: (x ∈ Support α g)
  · rename _ => hgmoved
    rw [smul_eq_iff_inv_smul_eq.mp
        (not_mem_support.mp <|
          Set.disjoint_right.mp hdisjoint (inv_smul_mem_support hgmoved)),
      smul_inv_smul, not_mem_support.mp hffixed]
  · rw [
      smul_eq_iff_inv_smul_eq.mp (not_mem_support.mp hgfixed),
      smul_eq_iff_inv_smul_eq.mp (not_mem_support.mp hffixed),
      not_mem_support.mp hgfixed,
      not_mem_support.mp hffixed
    ]
#align disjoint_commute Rubin.disjoint_commute

end Rubin
