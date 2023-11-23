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

----------------------------------------------------------------
section Rubin.RegularSupport.RegularSupport

variable [TopologicalSpace α] [Rubin.ContinuousMulAction G α]

def RegularSupport.InteriorClosure (U : Set α) :=
  interior (closure U)
#align interior_closure Rubin.RegularSupport.InteriorClosure

theorem RegularSupport.is_open_interiorClosure (U : Set α) :
    IsOpen (Rubin.RegularSupport.InteriorClosure U) :=
  isOpen_interior
#align is_open_interior_closure Rubin.RegularSupport.is_open_interiorClosure

theorem RegularSupport.interiorClosure_mono {U V : Set α} :
    U ⊆ V → Rubin.RegularSupport.InteriorClosure U ⊆ Rubin.RegularSupport.InteriorClosure V :=
  interior_mono ∘ closure_mono
#align interior_closure_mono Rubin.RegularSupport.interiorClosure_mono

def is_regular_open (U : Set α) :=
  Rubin.RegularSupport.InteriorClosure U = U
#align set.is_regular_open Rubin.is_regular_open

theorem is_regular_def (U : Set α) :
    is_regular_open U ↔ Rubin.RegularSupport.InteriorClosure U = U := by rfl
#align set.is_regular_def Rubin.is_regular_def

theorem RegularSupport.IsOpen.in_closure {U : Set α} : IsOpen U → U ⊆ interior (closure U) :=
  by
  intro U_open x x_in_U
  apply interior_mono subset_closure
  rw [U_open.interior_eq]
  exact x_in_U
#align is_open.in_closure Rubin.RegularSupport.IsOpen.in_closure

theorem RegularSupport.IsOpen.interiorClosure_subset {U : Set α} :
    IsOpen U → U ⊆ Rubin.RegularSupport.InteriorClosure U := fun h =>
  (subset_interior_iff_isOpen.mpr h).trans (interior_mono subset_closure)
#align is_open.interior_closure_subset Rubin.RegularSupport.IsOpen.interiorClosure_subset

theorem RegularSupport.regular_interior_closure (U : Set α) :
    is_regular_open (Rubin.RegularSupport.InteriorClosure U) :=
  by
  rw [is_regular_def]
  apply Set.Subset.antisymm
  exact interior_mono ((closure_mono interior_subset).trans (subset_of_eq closure_closure))
  exact (subset_of_eq interior_interior.symm).trans (interior_mono subset_closure)
#align regular_interior_closure Rubin.RegularSupport.regular_interior_closure

def RegularSupport.RegularSupport (α : Type _) [TopologicalSpace α] [MulAction G α] (g : G) :=
  Rubin.RegularSupport.InteriorClosure (Support α g)
#align regular_support Rubin.RegularSupport.RegularSupport

theorem RegularSupport.regularSupport_regular {g : G} :
    is_regular_open (Rubin.RegularSupport.RegularSupport α g) :=
  Rubin.RegularSupport.regular_interior_closure _
#align regular_regular_support Rubin.RegularSupport.regularSupport_regular

theorem RegularSupport.support_subset_regularSupport [T2Space α] (g : G) :
    Support α g ⊆ Rubin.RegularSupport.RegularSupport α g :=
  Rubin.RegularSupport.IsOpen.interiorClosure_subset (Rubin.support_open g)
#align support_in_regular_support Rubin.RegularSupport.support_subset_regularSupport

theorem RegularSupport.mem_regularSupport (g : G) (U : Set α) :
    is_regular_open U → g ∈ RigidStabilizer G U → Rubin.RegularSupport.RegularSupport α g ⊆ U :=
  fun U_ro g_moves =>
  (is_regular_def _).mp U_ro ▸
    Rubin.RegularSupport.interiorClosure_mono (rist_supported_in_set g_moves)
#align mem_regular_support Rubin.RegularSupport.mem_regularSupport

-- FIXME: Weird naming?
def RegularSupport.AlgebraicCentralizer (f : G) : Set G :=
  {h | ∃ g, h = g ^ 12 ∧ AlgebraicallyDisjoint f g}
#align algebraic_centralizer Rubin.RegularSupport.AlgebraicCentralizer

end Rubin.RegularSupport.RegularSupport

-- ----------------------------------------------------------------
-- section finite_exponent
-- lemma coe_nat_fin {n i : ℕ} (h : i < n) : ∃ (i' : fin n), i = i' := ⟨ ⟨ i, h ⟩, rfl ⟩
-- variables [topological_space α] [continuous_mul_action G α] [has_faithful_smul G α]
-- lemma distinct_images_from_disjoint {g : G} {V : set α} {n : ℕ}
--   (n_pos : 0 < n)
--   (h_disj : ∀ (i j : fin n) (i_ne_j : i ≠ j), disjoint (g ^ (i : ℕ) •'' V) (g ^ (j : ℕ) •'' V)) :
--   ∀ (q : α) (hq : q ∈ V) (i : fin n), (i : ℕ) > 0 → g ^ (i : ℕ) • (q : α) ∉ V :=
-- begin
--   intros q hq i i_pos hcontra,
--   have i_ne_zero : i ≠ (⟨ 0, n_pos ⟩ : fin n), { intro, done },
--   have hcontra' : g ^ (i : ℕ) • (q : α) ∈ g ^ (i : ℕ) •'' V, exact ⟨ q, hq, rfl ⟩,
--   have giq_notin_V := Set.disjoint_left.mp (h_disj i (⟨ 0, n_pos ⟩ : fin n) i_ne_zero) hcontra',
--   exact ((by done : g ^ 0 •'' V = V) ▸ giq_notin_V) hcontra
-- end
-- lemma moves_inj_period {g : G} {p : α} {n : ℕ} (period_eq_n : period p g = n) : function.injective (λ (i : fin n), g ^ (i : ℕ) • p) := begin
--   have period_ge_n : ∀ (k : ℕ), 1 ≤ k → k < n → g ^ k • p ≠ p,
--   { intros k one_le_k k_lt_n gkp_eq_p,
--     have := period_le_fix (nat.succ_le_iff.mp one_le_k) gkp_eq_p,
--     rw period_eq_n at this,
--     linarith },
--   exact moves_inj_N period_ge_n
-- end
-- lemma lemma_2_2 {α : Type u_2} [topological_space α] [continuous_mul_action G α] [has_faithful_smul G α] [t2_space α]
--   (U : set α) (U_open : is_open U) (locally_moving : is_locally_moving G α) :
--   U.nonempty → monoid.exponent (rigid_stabilizer G U) = 0 :=
-- begin
--   intro U_nonempty,
--   by_contra exp_ne_zero,
--   rcases (period_from_exponent U U_nonempty exp_ne_zero) with ⟨ p, g, n, n_pos, hpgn, n_eq_Sup ⟩,
--   rcases disjoint_nbhd_fin (moves_inj_period hpgn) with ⟨ V', V'_open, p_in_V', disj' ⟩,
--   dsimp at disj',
--   let V := U ∩ V',
--   have V_ss_U : V ⊆ U := Set.inter_subset_left U V',
--   have V'_ss_V : V ⊆ V' := Set.inter_subset_right U V',
--   have V_open : is_open V := is_open.inter U_open V'_open,
--   have p_in_V : (p : α) ∈ V := ⟨ subtype.mem p, p_in_V' ⟩,
--   have disj : ∀ (i j : fin n), ¬ i = j → disjoint (↑g ^ ↑i •'' V) (↑g ^ ↑j •'' V),
--   { intros i j i_ne_j W W_ss_giV W_ss_gjV,
--     exact disj' i j i_ne_j
--     (Set.subset.trans W_ss_giV (smul''_subset (↑g ^ ↑i) V'_ss_V))
--     (Set.subset.trans W_ss_gjV (smul''_subset (↑g ^ ↑j) V'_ss_V)) },
--   have ristV_ne_bot := locally_moving V V_open (Set.nonempty_of_mem p_in_V),
--   rcases (or_iff_right ristV_ne_bot).mp (Subgroup.bot_or_exists_ne_one _) with ⟨h,h_in_ristV,h_ne_one⟩,
--   rcases faithful_rist_moves_point h_in_ristV h_ne_one with ⟨ q, q_in_V, hq_ne_q ⟩,
--   have hg_in_ristU : (h : G) * (g : G) ∈ rigid_stabilizer G U := (rigid_stabilizer G U).mul_mem' (rist_ss_rist V_ss_U h_in_ristV) (subtype.mem g),
--   have giq_notin_V : ∀ (i : fin n), (i : ℕ) > 0 → g ^ (i : ℕ) • (q : α) ∉ V := distinct_images_from_disjoint n_pos disj q q_in_V,
--   have giq_ne_q : ∀ (i : fin n), (i : ℕ) > 0 → g ^ (i : ℕ) • (q : α) ≠ (q : α),
--   { intros i i_pos giq_eq_q, exact (giq_eq_q ▸ (giq_notin_V i i_pos)) q_in_V, },
--   have q_in_U : q ∈ U, { have : q ∈ U ∩ V' := q_in_V, exact this.1 },
--   -- We have (hg)^i q = g^i q for all 0 < i < n
--   have pow_hgq_eq_pow_gq : ∀ (i : fin n), (i : ℕ) < n → (h * g) ^ (i : ℕ) • q = (g : G) ^ (i : ℕ) • q,
--   { intros i, induction (i : ℕ) with i',
--     { intro, repeat {rw pow_zero} },
--     { intro succ_i'_lt_n,
--       rw [smul_succ, ih (nat.lt_of_succ_lt succ_i'_lt_n), smul_smul, mul_assoc, ← smul_smul, ← smul_smul, ← smul_succ],
--       have image_q_notin_V : g ^ i'.succ • q ∉ V,
--       { have i'succ_ne_zero := ne_zero.pos i'.succ,
--         exact giq_notin_V (⟨ i'.succ, succ_i'_lt_n ⟩ : fin n) i'succ_ne_zero },
--       exact by_contradiction (λ c, c (by_contradiction (λ c', image_q_notin_V ((rist_supported_in_set h_in_ristV) c')))) } },
--   -- Combined with g^i q ≠ q, this yields (hg)^i q ≠ q for all 0 < i < n
--   have hgiq_ne_q : ∀ (i : fin n), (i : ℕ) > 0 → (h * g) ^ (i : ℕ) • q ≠ q,
--   { intros i i_pos, rw pow_hgq_eq_pow_gq i (fin.is_lt i), by_contra c, exact (giq_notin_V i i_pos) (c.symm ▸ q_in_V) },
--   -- This even holds for i = n
--   have hgnq_ne_q : (h * g) ^ n • q ≠ q,
--   { -- Rewrite (hg)^n q = hg^n q
--     have npred_lt_n : n.pred < n, exact (nat.succ_pred_eq_of_pos n_pos) ▸ (lt_add_one n.pred),
--     rcases coe_nat_fin npred_lt_n with ⟨ i', i'_eq_pred_n ⟩,
--     have hgi'q_eq_gi'q := pow_hgq_eq_pow_gq i' (i'_eq_pred_n ▸ npred_lt_n),
--     have : n = (i' : ℕ).succ := i'_eq_pred_n ▸ (nat.succ_pred_eq_of_pos n_pos).symm,
--     rw [this, smul_succ, hgi'q_eq_gi'q, ← smul_smul, ← smul_succ, ← this],
--     -- Now it follows from g^n q = q and h q ≠ q
--     have n_le_period_qg := notfix_le_period' n_pos ((zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero (⟨ q, q_in_U ⟩ : U) g)).1 giq_ne_q,
--     have period_qg_le_n := (zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero (⟨ q, q_in_U ⟩ : U) g).2, rw ← n_eq_Sup at period_qg_le_n,
--     exact (ge_antisymm period_qg_le_n n_le_period_qg).symm ▸ ((pow_period_fix q (g : G)).symm ▸ hq_ne_q) },
--   -- Finally, we derive a contradiction
--   have period_pos_le_n := zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero (⟨ q, q_in_U ⟩ : U) (⟨ h * g, hg_in_ristU ⟩ : rigid_stabilizer G U),
--   rw ← n_eq_Sup at period_pos_le_n,
--   cases (lt_or_eq_of_le period_pos_le_n.2),
--   { exact (hgiq_ne_q (⟨ (period (q : α) ((h : G) * (g : G))), h_1 ⟩ : fin n) period_pos_le_n.1) (pow_period_fix (q : α) ((h : G) * (g : G))) },
--   { exact hgnq_ne_q (h_1 ▸ (pow_period_fix (q : α) ((h : G) * (g : G)))) }
-- end
-- lemma proposition_2_1 [t2_space α] (f : G) : is_locally_moving G α → (algebraic_centralizer f).centralizer = rigid_stabilizer G (regular_support α f) := sorry
-- end finite_exponent
-- variables [topological_space α] [topological_space β] [continuous_mul_action G α] [continuous_mul_action G β]
-- noncomputable theorem rubin (hα : rubin_action G α) (hβ : rubin_action G β) : equivariant_homeomorph G α β := sorry
end Rubin

end Rubin
