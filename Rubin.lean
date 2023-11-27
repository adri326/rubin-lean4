/-
Copyright (c) 2023 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Laurent Bartholdi
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation
import Mathlib.Topology.Homeomorph

import Rubin.Tactic
import Rubin.MulActionExt
import Rubin.SmulImage
import Rubin.Support
import Rubin.Topological
import Rubin.RigidStabilizer
import Rubin.Period
import Rubin.AlgebraicDisjointness
import Rubin.RegularSupport

#align_import rubin

namespace Rubin
open Rubin.Tactic

-- TODO: find a home
theorem equiv_congr_ne {ι ι' : Type _} (e : ι ≃ ι') {x y : ι} : x ≠ y → e x ≠ e y :=
  by
  intro x_ne_y
  by_contra h
  apply x_ne_y
  convert congr_arg e.symm h <;> simp only [Equiv.symm_apply_apply]
#align equiv.congr_ne Rubin.equiv_congr_ne

----------------------------------------------------------------
section Rubin

variable {G α β : Type _} [Group G]

----------------------------------------------------------------
section RubinActions

variable [TopologicalSpace α] [TopologicalSpace β]

structure RubinAction (G α : Type _) extends
  Group G,
  TopologicalSpace α,
  MulAction G α,
  FaithfulSMul G α
where
  locally_compact : LocallyCompactSpace α
  hausdorff : T2Space α
  no_isolated_points : Rubin.has_no_isolated_points α
  locallyDense : LocallyDense G α
#align rubin_action Rubin.RubinAction

end RubinActions

lemma lemma_2_2 (G: Type _) {α : Type _} [Group G] [TopologicalSpace α] [ContinuousMulAction G α] [FaithfulSMul G α]
  [T2Space α] [h_lm : LocallyMoving G α]
  {U : Set α} (U_open : IsOpen U) (U_nonempty : Set.Nonempty U) :
  Monoid.exponent (RigidStabilizer G U) = 0 :=
by
  by_contra exp_ne_zero

  let ⟨p, ⟨g, g_in_ristU⟩, n, p_in_U, n_pos, hpgn, n_eq_Sup⟩ := Period.period_from_exponent U U_nonempty exp_ne_zero
  simp at hpgn
  let ⟨V', V'_open, p_in_V', disj'⟩ := disjoint_nbhd_fin (smul_injective_within_period hpgn)

  let V := U ∩ V'
  have V_open : IsOpen V := U_open.inter V'_open
  have p_in_V : p ∈ V := ⟨p_in_U, p_in_V'⟩
  have disj : ∀ (i j : Fin n), i ≠ j → Disjoint (g ^ (i : ℕ) •'' V) (g ^ (j : ℕ) •'' V) := by
    intro i j i_ne_j
    apply Set.disjoint_of_subset
    · apply smulImage_subset
      apply Set.inter_subset_right
    · apply smulImage_subset
      apply Set.inter_subset_right
    exact disj' i j i_ne_j

  let ⟨h, h_in_ristV, h_ne_one⟩ := h_lm.get_nontrivial_rist_elem V_open (Set.nonempty_of_mem p_in_V)
  have hg_in_ristU : h * g ∈ RigidStabilizer G U := by
    simp [RigidStabilizer]
    intro x x_notin_U
    rw [mul_smul]
    rw [g_in_ristU _ x_notin_U]
    have x_notin_V : x ∉ V := fun x_in_V => x_notin_U x_in_V.left
    rw [h_in_ristV _ x_notin_V]
  let ⟨q, q_in_V, hq_ne_q ⟩ := faithful_rigid_stabilizer_moves_point h_in_ristV h_ne_one
  have gpowi_q_notin_V : ∀ (i : Fin n), (i : ℕ) > 0 → g ^ (i : ℕ) • q ∉ V := by
    apply smulImage_distinct_of_disjoint_exp n_pos disj
    exact q_in_V

  -- We have (hg)^i q = g^i q for all 0 < i < n
  have hgpow_eq_gpow : ∀ (i : Fin n), (h * g) ^ (i : ℕ) • q = g ^ (i : ℕ) • q := by
    intro ⟨i, i_lt_n⟩
    simp
    induction i with
    | zero => simp
    | succ i' IH =>
      have i'_lt_n: i' < n := Nat.lt_of_succ_lt i_lt_n
      have IH := IH i'_lt_n
      rw [smul_succ]
      rw [IH]
      rw [smul_succ]
      rw [mul_smul]
      rw [<-smul_succ]

      -- We can show that `g^(Nat.succ i') • q ∉ V`,
      -- which means that with `h` in `RigidStabilizer G V`, `h` fixes that point
      apply h_in_ristV (g^(Nat.succ i') • q)

      let i'₂ : Fin n := ⟨Nat.succ i', i_lt_n⟩
      have h_eq: Nat.succ i' = (i'₂ : ℕ) := by simp
      rw [h_eq]
      apply smulImage_distinct_of_disjoint_exp
      · exact n_pos
      · exact disj
      · exact q_in_V
      · simp

  -- Combined with `g^i • q ≠ q`, this yields `(hg)^i • q ≠ q` for all `0 < i < n`
  have hgpow_moves : ∀ (i : Fin n), 0 < (i : ℕ) → (h*g)^(i : ℕ) • q ≠ q := by
    intro ⟨i, i_lt_n⟩ i_pos
    simp at i_pos
    rw [hgpow_eq_gpow]
    simp
    by_contra h'
    apply gpowi_q_notin_V ⟨i, i_lt_n⟩
    exact i_pos
    simp (config := {zeta := false}) only []
    rw [h']
    exact q_in_V

  -- This even holds for `i = n`
  have hgpown_moves : (h * g) ^ n • q ≠ q := by
    -- Rewrite (hg)^n • q = h * g^n • q
    rw [<-Nat.succ_pred n_pos.ne.symm]
    rw [pow_succ]
    have h_eq := hgpow_eq_gpow ⟨Nat.pred n, Nat.pred_lt_self n_pos⟩
    simp at h_eq
    rw [mul_smul, h_eq, <-mul_smul, mul_assoc, <-pow_succ]
    rw [<-Nat.succ_eq_add_one, Nat.succ_pred n_pos.ne.symm]

    -- We first eliminate `g^n • q` by proving that `n = Period g q`
    have period_gq_eq_n : Period.period q g = n := by
      apply ge_antisymm
      {
        apply Period.notfix_le_period'
        · exact n_pos
        · apply Period.period_pos'
          · exact Set.nonempty_of_mem p_in_U
          · exact exp_ne_zero
          · exact q_in_V.left
          · exact g_in_ristU
        · intro i i_pos
          rw [<-hgpow_eq_gpow]
          apply hgpow_moves i i_pos
      }
      {
        rw [n_eq_Sup]
        apply Period.period_le_Sup_periods'
        · exact Set.nonempty_of_mem p_in_U
        · exact exp_ne_zero
        · exact q_in_V.left
        · exact g_in_ristU
      }

    rw [mul_smul, <-period_gq_eq_n]
    rw [Period.pow_period_fix]
    -- Finally, we have `h • q ≠ q`
    exact hq_ne_q

  -- Finally, we derive a contradiction
  have ⟨period_hg_pos, period_hg_le_n⟩ := Period.zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero ⟨q, q_in_V.left⟩ ⟨h * g, hg_in_ristU⟩
  simp at period_hg_pos
  simp at period_hg_le_n
  rw [<-n_eq_Sup] at period_hg_le_n
  cases (lt_or_eq_of_le period_hg_le_n) with
  | inl period_hg_lt_n =>
      apply hgpow_moves ⟨Period.period q (h * g), period_hg_lt_n⟩
      exact period_hg_pos
      simp
      apply Period.pow_period_fix
  | inr period_hg_eq_n =>
      apply hgpown_moves
      rw [<-period_hg_eq_n]
      apply Period.pow_period_fix

section proposition_2_1

-- TODO: put in a different file and introduce some QoL theorems
def AlgebraicSubgroup {G : Type _} [Group G] (f : G) : Set G :=
  (fun g : G => g^12) '' { g : G | IsAlgebraicallyDisjoint f g }

def AlgebraicCentralizer {G: Type _} (α : Type _) [Group G] [MulAction G α] (f : G) : Set G :=
  Set.centralizer (AlgebraicSubgroup f)

-- Given the statement `¬Support α h ⊆ RegularSupport α f`,
-- we construct an open subset within `Support α h \ RegularSupport α f`,
-- and we show that it is non-empty, open and (by construction) disjoint from `Support α f`.
lemma open_set_from_supp_not_subset_rsupp {G α : Type _}
  [Group G] [TopologicalSpace α] [ContinuousMulAction G α] [T2Space α]
  {f h : G} (not_support_subset_rsupp : ¬Support α h ⊆ RegularSupport α f):
  ∃ V : Set α, V ⊆ Support α h ∧ Set.Nonempty V ∧ IsOpen V ∧ Disjoint V (Support α f) :=
by
  let U := Support α h \ closure (RegularSupport α f)
  have U_open : IsOpen U := by
    unfold_let
    rw [Set.diff_eq_compl_inter]
    apply IsOpen.inter
    · simp
    · exact support_open _
  have U_subset_supp_h : U ⊆ Support α h := by simp; apply Set.diff_subset
  have U_disj_supp_f : Disjoint U (Support α f) := by
    apply Set.disjoint_of_subset_right
    · exact subset_closure
    · simp
      rw [Set.diff_eq_compl_inter]
      apply Disjoint.inter_left
      apply Disjoint.closure_right; swap; simp

      rw [Set.disjoint_compl_left_iff_subset]
      apply subset_trans
      exact subset_closure
      apply closure_mono
      apply support_subset_regularSupport

  have U_nonempty : Set.Nonempty U; swap
  exact ⟨U, U_subset_supp_h, U_nonempty, U_open, U_disj_supp_f⟩

  -- We prove that U isn't empty by contradiction:
  -- if it is empty, then `Support α h \ closure (RegularSupport α f) = ∅`,
  -- so we can show that `Support α h ⊆ RegularSupport α f`,
  -- contradicting with our initial hypothesis.
  by_contra U_empty
  apply not_support_subset_rsupp
  show Support α h ⊆ RegularSupport α f

  apply subset_of_diff_closure_regular_empty
  · apply regularSupport_regular
  · exact support_open _
  · rw [Set.not_nonempty_iff_eq_empty] at U_empty
    exact U_empty

lemma nontrivial_pow_from_exponent_eq_zero {G : Type _} [Group G]
  (exp_eq_zero : Monoid.exponent G = 0) :
  ∀ (n : ℕ), n > 0 → ∃ g : G, g^n ≠ 1 :=
by
  intro n n_pos
  rw [Monoid.exponent_eq_zero_iff] at exp_eq_zero
  unfold Monoid.ExponentExists at exp_eq_zero
  rw [<-Classical.not_forall_not, Classical.not_not] at exp_eq_zero
  simp at exp_eq_zero
  exact exp_eq_zero n n_pos

lemma Commute.inv {G : Type _} [Group G] {f g : G} : Commute f g → Commute f g⁻¹ := by
  unfold Commute SemiconjBy
  intro h
  have h₁ : f = g * f * g⁻¹ := by
    nth_rw 1 [<-mul_one f]
    rw [<-mul_right_inv g, <-mul_assoc]
    rw [h]
  nth_rw 2 [h₁]
  group

lemma Commute.inv_iff {G : Type _} [Group G] {f g : G} : Commute f g ↔ Commute f g⁻¹ := ⟨
  Commute.inv,
  by
    nth_rw 2 [<-inv_inv g]
    apply Commute.inv
⟩

lemma Commute.inv_iff₂ {G : Type _} [Group G] {f g : G} : Commute f g ↔ Commute f⁻¹ g := ⟨
  Commute.symm ∘ Commute.inv_iff.mp ∘ Commute.symm,
  Commute.symm ∘ Commute.inv_iff.mpr ∘ Commute.symm
⟩

lemma Commute.into {G : Type _} [Group G] {f g : G} : Commute f g → f * g = g * f := by
  unfold Commute SemiconjBy
  tauto

lemma proposition_2_1 {G α : Type _}
  [Group G] [TopologicalSpace α] [ContinuousMulAction G α] [T2Space α]
  [LocallyMoving G α] [h_faithful : FaithfulSMul G α]
  (f : G) :
  AlgebraicCentralizer α f = RigidStabilizer G (RegularSupport α f) :=
by
  apply Set.eq_of_subset_of_subset
  swap
  {
    intro h h_in_rist
    simp at h_in_rist
    unfold AlgebraicCentralizer
    rw [Set.mem_centralizer_iff]
    intro g g_in_S
    simp [AlgebraicSubgroup] at g_in_S
    let ⟨g', ⟨g'_alg_disj, g_eq_g'⟩⟩ := g_in_S
    have supp_disj := proposition_1_1_2 f g' g'_alg_disj (α := α)

    apply Commute.eq
    symm
    apply commute_if_rigidStabilizer_and_disjoint (α := α)
    · exact h_in_rist
    · show Disjoint (RegularSupport α f) (Support α g)
      have cl_supp_disj : Disjoint (closure (Support α f)) (Support α g)
      swap

      apply Set.disjoint_of_subset _ _ cl_supp_disj
      · rw [RegularSupport.def]
        exact interior_subset
      · rfl
      · rw [<-g_eq_g']
        exact Disjoint.closure_left supp_disj (support_open _)
  }

  intro h h_in_centralizer
  by_contra h_notin_rist
  simp at h_notin_rist
  rw [rigidStabilizer_support] at h_notin_rist
  let ⟨V, V_in_supp_h, V_nonempty, V_open, V_disj_supp_f⟩ := open_set_from_supp_not_subset_rsupp h_notin_rist
  let ⟨v, v_in_V⟩ := V_nonempty
  have v_moved := V_in_supp_h v_in_V
  rw [mem_support] at v_moved

  have ⟨W, W_open, v_in_W, W_subset_support, disj_W_img⟩ := disjoint_nbhd_in V_open v_in_V v_moved

  have mono_exp := lemma_2_2 G W_open (Set.nonempty_of_mem v_in_W)
  let ⟨⟨g, g_in_rist⟩, g12_ne_one⟩ := nontrivial_pow_from_exponent_eq_zero mono_exp 12 (by norm_num)
  simp at g12_ne_one

  have disj_supports : Disjoint (Support α f) (Support α g) := by
    apply Set.disjoint_of_subset_right
    · apply rigidStabilizer_support.mp
      exact g_in_rist
    · apply Set.disjoint_of_subset_right
      · exact W_subset_support
      · exact V_disj_supp_f.symm
  have alg_disj_f_g := proposition_1_1_1 _ _ disj_supports
  have g12_in_algebraic_subgroup : g^12 ∈ AlgebraicSubgroup f := by
    simp [AlgebraicSubgroup]
    use g
    constructor
    exact ↑alg_disj_f_g
    rfl

  have h_nc_g12 : ¬Commute (g^12) h := by
    have supp_g12_sub_W : Support α (g^12) ⊆ W := by
      rw [rigidStabilizer_support] at g_in_rist
      calc
        Support α (g^12) ⊆ Support α g := by apply support_pow
        _ ⊆ W := g_in_rist
    have supp_g12_disj_hW : Disjoint (Support α (g^12)) (h •'' W) := by
      apply Set.disjoint_of_subset_left
      swap
      · exact disj_W_img
      · exact supp_g12_sub_W

    exact not_commute_of_disj_support_smulImage
      g12_ne_one
      supp_g12_sub_W
      supp_g12_disj_hW

  apply h_nc_g12
  exact h_in_centralizer _ g12_in_algebraic_subgroup


end proposition_2_1
-- variables [topological_space α] [topological_space β] [continuous_mul_action G α] [continuous_mul_action G β]
-- noncomputable theorem rubin (hα : rubin_action G α) (hβ : rubin_action G β) : equivariant_homeomorph G α β := sorry
end Rubin

end Rubin
