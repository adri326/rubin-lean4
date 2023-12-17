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
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation
import Mathlib.Topology.Homeomorph

import Rubin.Tactic
import Rubin.MulActionExt
import Rubin.SmulImage
import Rubin.Support
import Rubin.Topology
import Rubin.RigidStabilizer
import Rubin.RigidStabilizerBasis
import Rubin.Period
import Rubin.AlgebraicDisjointness
import Rubin.RegularSupport
import Rubin.RegularSupportBasis
import Rubin.HomeoGroup

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

----------------------------------------------------------------
section RubinActions

structure RubinAction (G α : Type _) extends
  Group G,
  TopologicalSpace α,
  MulAction G α,
  FaithfulSMul G α
where
  locally_compact : LocallyCompactSpace α
  hausdorff : T2Space α
  no_isolated_points : HasNoIsolatedPoints α
  locallyDense : LocallyDense G α
#align rubin_action Rubin.RubinAction

end RubinActions

section AlgebraicDisjointness

variable {G α : Type _}
variable [TopologicalSpace α]
variable [Group G]
variable [MulAction G α]
variable [ContinuousMulAction G α]
variable [FaithfulSMul G α]

-- TODO: modify the proof to be less "let everything"-y, especially the first half
lemma proposition_1_1_1 [h_lm : LocallyMoving G α] [T2Space α] (f g : G) (supp_disjoint : Disjoint (Support α f) (Support α g)) : AlgebraicallyDisjoint f g := by
  apply AlgebraicallyDisjoint_mk
  intros h h_not_commute
  -- h is not the identity on `Support α f`
  have f_h_not_disjoint := (mt (disjoint_commute (G := G) (α := α)) h_not_commute)
  have ⟨x, ⟨x_in_supp_f, x_in_supp_h⟩⟩ := Set.not_disjoint_iff.mp f_h_not_disjoint
  have hx_ne_x := mem_support.mp x_in_supp_h

  -- Since α is Hausdoff, there is a nonempty V ⊆ Support α f, with h •'' V disjoint from V
  have ⟨V, V_open, x_in_V, V_in_support, disjoint_img_V⟩ := disjoint_nbhd_in (support_open f) x_in_supp_f hx_ne_x

  -- let f₂ be a nontrivial element of the RigidStabilizer G V
  let ⟨f₂, f₂_in_rist_V, f₂_ne_one⟩ := h_lm.get_nontrivial_rist_elem V_open (Set.nonempty_of_mem x_in_V)

  -- Re-use the Hausdoff property of α again, this time yielding W ⊆ V
  let ⟨y, y_moved⟩ := faithful_moves_point' α f₂_ne_one
  have y_in_V := (rigidStabilizer_support.mp f₂_in_rist_V) (mem_support.mpr y_moved)
  let ⟨W, W_open, y_in_W, W_in_V, disjoint_img_W⟩ := disjoint_nbhd_in V_open y_in_V y_moved

  -- Let f₁ be a nontrivial element of RigidStabilizer G W
  let ⟨f₁, f₁_in_rist_W, f₁_ne_one⟩ := h_lm.get_nontrivial_rist_elem W_open (Set.nonempty_of_mem y_in_W)

  use f₁
  use f₂
  constructor <;> try constructor
  · apply disjoint_commute (α := α)
    apply Set.disjoint_of_subset_left _ supp_disjoint
    calc
      Support α f₁ ⊆ W := rigidStabilizer_support.mp f₁_in_rist_W
      W ⊆ V := W_in_V
      V ⊆ Support α f := V_in_support
  · apply disjoint_commute (α := α)
    apply Set.disjoint_of_subset_left _ supp_disjoint
    calc
      Support α f₂ ⊆ V := rigidStabilizer_support.mp f₂_in_rist_V
      V ⊆ Support α f := V_in_support

  -- We claim that [f₁, [f₂, h]] is a nontrivial elelement of Centralizer G g
  let k := ⁅f₂, h⁆
  have h₂ : ∀ z ∈ W, f₂ • z = k • z := by
    intro z z_in_W
    simp
    symm
    apply disjoint_support_comm f₂ h _ disjoint_img_V
    · exact W_in_V z_in_W
    · exact rigidStabilizer_support.mp f₂_in_rist_V

  constructor
  · -- then `k*f₁⁻¹*k⁻¹` is supported on k W = f₂ W,
    -- so [f₁,k] is supported on W ∪ f₂ W ⊆ V ⊆ support f, so commutes with g.
    apply disjoint_commute (α := α)
    apply Set.disjoint_of_subset_left _ supp_disjoint
    have supp_f₁_subset_W := (rigidStabilizer_support.mp f₁_in_rist_W)

    show Support α ⁅f₁, ⁅f₂, h⁆⁆ ⊆ Support α f
    calc
      Support α ⁅f₁, k⁆ = Support α ⁅k, f₁⁆ := by rw [<-commutatorElement_inv, support_inv]
      _ ⊆ Support α f₁ ∪ (k •'' Support α f₁) := support_comm α k f₁
      _ ⊆ W ∪ (k •'' Support α f₁) := Set.union_subset_union_left _ supp_f₁_subset_W
      _ ⊆ W ∪ (k •'' W) := by
        apply Set.union_subset_union_right
        exact (smulImage_mono k supp_f₁_subset_W)
      _ = W ∪ (f₂ •'' W) := by rw [<-smulImage_eq_of_smul_eq h₂]
      _ ⊆ V ∪ (f₂ •'' W) := Set.union_subset_union_left _ W_in_V
      _ ⊆ V ∪ V := by
        apply Set.union_subset_union_right
        apply smulImage_subset_in_support f₂ W V W_in_V
        exact rigidStabilizer_support.mp f₂_in_rist_V
      _ ⊆ V := by rw [Set.union_self]
      _ ⊆ Support α f := V_in_support

  · -- finally, [f₁,k] agrees with f₁ on W, so is not the identity.
    have h₄: ∀ z ∈ W, ⁅f₁, k⁆ • z = f₁ • z := by
      apply disjoint_support_comm f₁ k
      exact rigidStabilizer_support.mp f₁_in_rist_W
      rw [<-smulImage_eq_of_smul_eq h₂]
      exact disjoint_img_W
    let ⟨z, z_in_W, z_moved⟩ := faithful_rigid_stabilizer_moves_point f₁_in_rist_W f₁_ne_one

    by_contra h₅
    rw [<-h₄ z z_in_W] at z_moved
    have h₆ : ⁅f₁, ⁅f₂, h⁆⁆ • z = z := by rw [h₅, one_smul]
    exact z_moved h₆
#align proposition_1_1_1 Rubin.proposition_1_1_1


-- TODO: move to Rubin.lean
lemma moves_1234_of_moves_12 {g : G} {x : α} (g12_moves : g^12 • x ≠ x) :
  Function.Injective (fun i : Fin 5 => g^(i : ℤ) • x) :=
by
  apply moves_inj
  intros k k_ge_1 k_lt_5
  simp at k_lt_5

  by_contra x_fixed
  have k_div_12 : k ∣ 12 := by
    -- Note: norm_num does not support ℤ.dvd yet, nor ℤ.mod, nor Int.natAbs, nor Int.div, etc.
    have h: (12 : ℤ) = (12 : ℕ) := by norm_num
    rw [h, Int.ofNat_dvd_right]
    apply Nat.dvd_of_mod_eq_zero

    interval_cases k
    all_goals unfold Int.natAbs
    all_goals norm_num

  have g12_fixed : g^12 • x = x := by
    rw [<-zpow_ofNat]
    simp
    rw [<-Int.mul_ediv_cancel' k_div_12]
    have res := smul_zpow_eq_of_smul_eq (12/k) x_fixed
    group_action at res
    exact res

  exact g12_moves g12_fixed

lemma proposition_1_1_2 [T2Space α] [h_lm : LocallyMoving G α]
  (f g : G) (h_disj : AlgebraicallyDisjoint f g) : Disjoint (Support α f) (Support α (g^12)) :=
by
  by_contra not_disjoint
  let U := Support α f ∩ Support α (g^12)
  have U_nonempty : U.Nonempty := by
    apply Set.not_disjoint_iff_nonempty_inter.mp
    exact not_disjoint

  -- Since G is Hausdorff, we can find a nonempty set V ⊆ such that f(V) is disjoint from V and the sets {g^i(V): i=0..4} are pairwise disjoint
  let x := U_nonempty.some
  have x_in_U : x ∈ U := Set.Nonempty.some_mem U_nonempty
  have fx_moves : f • x ≠ x := Set.inter_subset_left _ _ x_in_U

  have five_points : Function.Injective (fun i : Fin 5 => g^(i : ℤ) • x) := by
    apply moves_1234_of_moves_12
    exact (Set.inter_subset_right _ _ x_in_U)
  have U_open: IsOpen U := (IsOpen.inter (support_open f) (support_open (g^12)))

  let ⟨V₀, V₀_open, x_in_V₀, V₀_in_support, disjoint_img_V₀⟩ := disjoint_nbhd_in U_open x_in_U fx_moves
  let ⟨V₁, V₁_open, x_in_V₁, disjoint_img_V₁⟩ := disjoint_nbhd_fin five_points

  let V := V₀ ∩ V₁
  -- Let h be a nontrivial element of the RigidStabilizer G V
  let ⟨h, ⟨h_in_ristV, h_ne_one⟩⟩ := h_lm.get_nontrivial_rist_elem (IsOpen.inter V₀_open V₁_open) (Set.nonempty_of_mem ⟨x_in_V₀, x_in_V₁⟩)

  have V_disjoint_smulImage: Disjoint V (f •'' V) := by
    apply Set.disjoint_of_subset
    · exact Set.inter_subset_left _ _
    · apply smulImage_mono
      exact Set.inter_subset_left _ _
    · exact disjoint_img_V₀

  have comm_non_trivial : ¬Commute f h := by
    by_contra comm_trivial
    let ⟨z, z_in_V, z_moved⟩ := faithful_rigid_stabilizer_moves_point h_in_ristV h_ne_one
    apply z_moved

    nth_rewrite 2 [<-one_smul G z]
    rw [<-commutatorElement_eq_one_iff_commute.mpr comm_trivial.symm]
    symm

    apply disjoint_support_comm h f
    · exact rigidStabilizer_support.mp h_in_ristV
    · exact V_disjoint_smulImage
    · exact z_in_V

  -- Since g is algebraically disjoint from f, there exist f₁,f₂ ∈ C_G(g) so that the commutator h' = [f1,[f2,h]] is a nontrivial element of C_G(g)
  let alg_disj_elem := h_disj h comm_non_trivial
  let f₁ := alg_disj_elem.fst
  let f₂ := alg_disj_elem.snd
  let h' := alg_disj_elem.comm_elem
  have f₁_commutes : Commute f₁ g := alg_disj_elem.fst_commute
  have f₂_commutes : Commute f₂ g := alg_disj_elem.snd_commute
  have h'_commutes : Commute h' g := alg_disj_elem.comm_elem_commute
  have h'_nontrivial : h' ≠ 1 := alg_disj_elem.comm_elem_nontrivial

  have support_f₂_h : Support α ⁅f₂,h⁆ ⊆ V ∪ (f₂ •'' V) := by
    calc
      Support α ⁅f₂, h⁆ ⊆ Support α h ∪ (f₂ •'' Support α h) := support_comm α f₂ h
      _ ⊆ V ∪ (f₂ •'' Support α h) := by
        apply Set.union_subset_union_left
        exact rigidStabilizer_support.mp h_in_ristV
      _ ⊆ V ∪ (f₂ •'' V) := by
        apply Set.union_subset_union_right
        apply smulImage_mono
        exact rigidStabilizer_support.mp h_in_ristV
  have support_h' : Support α h' ⊆ ⋃(i : Fin 2 × Fin 2), (f₁^(i.1.val) * f₂^(i.2.val)) •'' V := by
    rw [rewrite_Union]
    simp (config := {zeta := false})
    rw [<-smulImage_mul, <-smulImage_union]
    calc
      Support α h' ⊆ Support α ⁅f₂,h⁆ ∪ (f₁ •'' Support α ⁅f₂, h⁆) := support_comm α f₁ ⁅f₂,h⁆
      _ ⊆ V ∪ (f₂ •'' V) ∪ (f₁ •'' Support α ⁅f₂, h⁆) := by
        apply Set.union_subset_union_left
        exact support_f₂_h
      _ ⊆ V ∪ (f₂ •'' V) ∪ (f₁ •'' V ∪ (f₂ •'' V)) := by
        apply Set.union_subset_union_right
        apply smulImage_mono f₁
        exact support_f₂_h

  -- Since h' is nontrivial, it has at least one point p in its support
  let ⟨p, p_moves⟩ := faithful_moves_point' α h'_nontrivial
  -- Since g commutes with h', all five of the points {gi(p):i=0..4} lie in supp(h')
  have gi_in_support : ∀ (i: Fin 5), g^(i.val) • p ∈ Support α h' := by
    intro i
    rw [mem_support]
    by_contra p_fixed
    rw [<-mul_smul, h'_commutes.pow_right, mul_smul] at p_fixed
    group_action at p_fixed
    exact p_moves p_fixed

  -- The next section gets tricky, so let us clear away some stuff first :3
  clear h'_commutes h'_nontrivial
  clear V₀_open x_in_V₀ V₀_in_support disjoint_img_V₀
  clear V₁_open x_in_V₁
  clear five_points h_in_ristV h_ne_one V_disjoint_smulImage
  clear support_f₂_h

  -- by the pigeonhole principle, one of the four sets V, f₁(V), f₂(V), f₁f₂(V) must contain two of these points,
  -- say g^i(p),g^j(p) ∈ k(V) for some 0 ≤ i < j ≤ 4 and k ∈ {1,f₁,f₂,f₁f₂}
  let pigeonhole : Fintype.card (Fin 5) > Fintype.card (Fin 2 × Fin 2) := by trivial
  let choice_pred := fun (i : Fin 5) => (Set.mem_iUnion.mp (support_h' (gi_in_support i)))
  let choice := fun (i : Fin 5) => (choice_pred i).choose
  let ⟨i, _, j, _, i_ne_j, same_choice⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    pigeonhole
    (fun (i : Fin 5) _ => Finset.mem_univ (choice i))

  let k := f₁^(choice i).1.val * f₂^(choice i).2.val
  have same_k : f₁^(choice j).1.val * f₂^(choice j).2.val = k := by rw [<-same_choice]
  have gi : g^i.val • p ∈ k •'' V := (choice_pred i).choose_spec
  have gk : g^j.val • p ∈ k •'' V := by
    have gk' := (choice_pred j).choose_spec
    rw [same_k] at gk'
    exact gk'

  -- Since g^(j-i)(V) is disjoint from V and k commutes with g,
  -- we know that g^(j−i)k(V) is disjoint from k(V),
  -- which leads to a contradiction since g^i(p) and g^j(p) both lie in k(V).

  have g_disjoint : Disjoint ((g^i.val)⁻¹ •'' V) ((g^j.val)⁻¹ •'' V) := by
    apply smulImage_disjoint_subset (Set.inter_subset_right V₀ V₁)
    group
    rw [smulImage_disjoint_inv_pow]
    group
    apply disjoint_img_V₁
    symm; exact i_ne_j

  have k_commutes: Commute k g := by
    apply Commute.mul_left
    · exact f₁_commutes.pow_left _
    · exact f₂_commutes.pow_left _
  clear f₁_commutes f₂_commutes

  have g_k_disjoint : Disjoint ((g^i.val)⁻¹ •'' (k •'' V)) ((g^j.val)⁻¹ •'' (k •'' V)) := by
    repeat rw [smulImage_mul]
    repeat rw [<-inv_pow]
    repeat rw [k_commutes.symm.inv_left.pow_left]
    repeat rw [<-smulImage_mul k]
    repeat rw [inv_pow]
    exact smulImage_disjoint k g_disjoint

  apply Set.disjoint_left.mp g_k_disjoint
  · rw [mem_inv_smulImage]
    exact gi
  · rw [mem_inv_smulImage]
    exact gk

lemma remark_1_2 (f g : G) (h_disj : AlgebraicallyDisjoint f g): Commute f g := by
  by_contra non_commute
  let disj_elem := h_disj g non_commute
  let nontrivial := disj_elem.comm_elem_nontrivial

  rw [commutatorElement_eq_one_iff_commute.mpr disj_elem.snd_commute] at nontrivial
  rw [commutatorElement_one_right] at nontrivial

  tauto

end AlgebraicDisjointness

section RegularSupport

lemma lemma_2_2 (G: Type _) {α : Type _} [Group G] [TopologicalSpace α] [MulAction G α]
  [ContinuousMulAction G α] [FaithfulSMul G α]
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
    · apply smulImage_mono
      apply Set.inter_subset_right
    · apply smulImage_mono
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
    apply smulImage_distinct_of_disjoint_pow n_pos disj
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
      apply smulImage_distinct_of_disjoint_pow
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


-- Given the statement `¬Support α h ⊆ RegularSupport α f`,
-- we construct an open subset within `Support α h \ RegularSupport α f`,
-- and we show that it is non-empty, open and (by construction) disjoint from `Support α f`.
lemma open_set_from_supp_not_subset_rsupp {G α : Type _}
  [Group G] [TopologicalSpace α] [MulAction G α] [ContinuousMulAction G α] [T2Space α]
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

  apply subset_from_diff_closure_eq_empty
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


lemma proposition_2_1 {G α : Type _}
  [Group G] [TopologicalSpace α] [MulAction G α] [ContinuousMulAction G α] [T2Space α]
  [LocallyMoving G α] [h_faithful : FaithfulSMul G α]
  (f : G) :
  AlgebraicCentralizer f = RigidStabilizer G (RegularSupport α f) :=
by
  ext h

  constructor
  swap
  {
    intro h_in_rist
    simp at h_in_rist
    unfold AlgebraicCentralizer
    rw [Subgroup.mem_centralizer_iff]
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

  intro h_in_centralizer
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

-- Small lemma for remark 2.3
theorem rigidStabilizer_inter_bot_iff_regularSupport_disj {G α : Type _}
  [Group G] [TopologicalSpace α] [MulAction G α] [ContinuousMulAction G α] [LocallyMoving G α] [FaithfulSMul G α]
  {f g : G} :
  RigidStabilizer G (RegularSupport α f) ⊓ RigidStabilizer G (RegularSupport α g) = ⊥
  ↔ Disjoint (RegularSupport α f) (RegularSupport α g) :=
by
  rw [<-rigidStabilizer_inter]
  constructor
  {
    intro rist_disj

    by_contra rsupp_not_disj
    rw [Set.not_disjoint_iff] at rsupp_not_disj
    let ⟨x, x_in_rsupp_f, x_in_rsupp_g⟩ := rsupp_not_disj

    have rsupp_open: IsOpen (RegularSupport α f ∩ RegularSupport α g) := by
      apply IsOpen.inter <;> exact regularSupport_open _ _

    -- The contradiction occurs by applying the definition of LocallyMoving:
    apply LocallyMoving.locally_moving (G := G) _ rsupp_open _ rist_disj

    exact ⟨x, x_in_rsupp_f, x_in_rsupp_g⟩
  }
  {
    intro rsupp_disj
    rw [Set.disjoint_iff_inter_eq_empty] at rsupp_disj
    rw [rsupp_disj]

    by_contra rist_ne_bot
    rw [<-ne_eq, Subgroup.ne_bot_iff_exists_ne_one] at rist_ne_bot
    let ⟨⟨h, h_in_rist⟩, h_ne_one⟩ := rist_ne_bot
    simp at h_ne_one
    apply h_ne_one
    rw [rigidStabilizer_empty] at h_in_rist
    rw [Subgroup.mem_bot] at h_in_rist
    exact h_in_rist
  }

variable {G α : Type _}
variable [Group G]
variable [TopologicalSpace α] [T2Space α]
variable [MulAction G α] [ContinuousMulAction G α] [FaithfulSMul G α] [LocallyMoving G α]

/--
This demonstrates that the disjointness of the supports of two elements `f` and `g`
can be proven without knowing anything about how `f` and `g` act on `α`
(bar the more global properties of the group action).

We could prove that the intersection of the algebraic centralizers of `f` and `g` is trivial
purely within group theory, and then apply this theorem to know that their support
in `α` will be disjoint.
--/
lemma remark_2_3 {f g : G} :
  (AlgebraicCentralizer f) ⊓ (AlgebraicCentralizer g) = ⊥ → Disjoint (Support α f) (Support α g) :=
by
  intro alg_disj
  rw [disjoint_interiorClosure_iff (support_open _) (support_open _)]
  simp
  repeat rw [<-RegularSupport.def]
  rw [<-rigidStabilizer_inter_bot_iff_regularSupport_disj]

  repeat rw [<-proposition_2_1]
  exact alg_disj

#check proposition_2_1
lemma rigidStabilizerInter_eq_algebraicCentralizerInter {S : Finset G} :
  RigidStabilizerInter₀ α S = AlgebraicCentralizerInter₀ S :=
by
  unfold RigidStabilizerInter₀
  unfold AlgebraicCentralizerInter₀
  simp only [<-proposition_2_1]
  -- conv => {
  --   rhs
  --   congr; intro; congr; intro
  --   rw [proposition_2_1 (α := α)]
  -- }

theorem rigidStabilizerBasis_eq_algebraicCentralizerBasis :
  AlgebraicCentralizerBasis G = RigidStabilizerBasis G α :=
by
  apply le_antisymm <;> intro B B_mem
  any_goals rw [RigidStabilizerBasis.mem_iff]
  any_goals rw [AlgebraicCentralizerBasis.mem_iff]
  any_goals rw [RigidStabilizerBasis.mem_iff] at B_mem
  any_goals rw [AlgebraicCentralizerBasis.mem_iff] at B_mem

  all_goals let ⟨⟨seed, B_ne_bot⟩, B_eq⟩ := B_mem

  any_goals rw [RigidStabilizerBasis₀.val_def] at B_eq
  any_goals rw [AlgebraicCentralizerBasis₀.val_def] at B_eq
  all_goals simp at B_eq
  all_goals rw [<-B_eq]

  rw [<-rigidStabilizerInter_eq_algebraicCentralizerInter (α := α)] at B_ne_bot
  swap
  rw [rigidStabilizerInter_eq_algebraicCentralizerInter (α := α)] at B_ne_bot

  all_goals use ⟨seed, B_ne_bot⟩

  symm
  all_goals apply rigidStabilizerInter_eq_algebraicCentralizerInter

end RegularSupport

section HomeoGroup

open Topology

variable {G α : Type _} [Group G] [TopologicalSpace α] [T2Space α]
variable [MulAction G α] [ContinuousMulAction G α] [FaithfulSMul G α] [LocallyMoving G α]

example : TopologicalSpace G := TopologicalSpace.generateFrom (RigidStabilizerBasis.asSets G α)

-- TODO: remove
-- proposition_3_4_1
example {α : Type _} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] (F : Ultrafilter α) (p : α):
  F ≤ 𝓝 p ↔ p ∈ ⋂ (S ∈ F), closure S :=
by
  rw [<-Ultrafilter.clusterPt_iff]
  simp
  exact clusterPt_iff_forall_mem_closure

theorem proposition_3_4_2 {α : Type _} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] (F : Ultrafilter α):
  (∃ p : α, ClusterPt p F) ↔ ∃ S ∈ F, IsCompact (closure S) :=
by
  constructor
  · intro ⟨p, p_clusterPt⟩
    rw [Ultrafilter.clusterPt_iff] at p_clusterPt
    have ⟨S, S_in_nhds, S_compact⟩ := (compact_basis_nhds p).ex_mem
    use S
    constructor
    exact p_clusterPt S_in_nhds
    rw [IsClosed.closure_eq S_compact.isClosed]
    exact S_compact
  · intro ⟨S, S_in_F, clS_compact⟩
    have F_le_principal_S : F ≤ Filter.principal (closure S) := by
      rw [Filter.le_principal_iff]
      simp
      apply Filter.sets_of_superset
      exact S_in_F
      exact subset_closure
    let ⟨x, _, F_clusterPt⟩ := clS_compact F_le_principal_S
    use x

def RSuppSubsets {α : Type _} [TopologicalSpace α] (V : Set α) : Set (Set α) :=
  {W ∈ RegularSupportBasis.asSet α | W ⊆ V}

def RSuppOrbit {G α : Type _} [Group G] [TopologicalSpace α] [MulAction G α] (F : Filter α) (H : Subgroup G) : Set (Set α) :=
  { g •'' W | (g ∈ H) (W ∈ F) }

lemma moving_elem_of_open_subset_closure_orbit {U V : Set α} (U_open : IsOpen U) {p : α}
  (U_ss_clOrbit : U ⊆ closure (MulAction.orbit (RigidStabilizer G V) p)) :
  ∃ h : G, h ∈ RigidStabilizer G V ∧ h • p ∈ U :=
by
  -- Idea: can `Support α g ⊆ MulAction.orbit (RigidStabilizer G (RegularSupport α g)) p` be proven?
  sorry

lemma compact_subset_of_rsupp_basis [LocallyCompactSpace α]
  (U : RegularSupportBasis α):
  ∃ V : RegularSupportBasis α, (closure V.val) ⊆ U.val ∧ IsCompact (closure V.val) :=
by
  -- Idea: use (RegularSupportBasis.isBasis G α).nhds_hasBasis and compact_basis_nhds together?
  -- Note: exists_compact_subset is *very* close to this theorem
  sorry

theorem proposition_3_5 [LocallyDense G α] [LocallyCompactSpace α] [HasNoIsolatedPoints α]
  (U : RegularSupportBasis α) (F: Ultrafilter α):
  (∃ p ∈ U.val, ClusterPt p F)
  ↔ ∃ V : RegularSupportBasis α, V ≤ U ∧ RSuppSubsets V.val ⊆ RSuppOrbit F (RigidStabilizer G U.val) :=
by
  constructor
  {
    simp
    intro p p_in_U p_clusterPt
    have U_open : IsOpen U.val := U.regular.isOpen

    -- First, get a neighborhood of p that is a subset of the closure of the orbit of G_U
    have clOrbit_in_nhds := LocallyDense.rigidStabilizer_in_nhds G α U_open p_in_U
    rw [mem_nhds_iff] at clOrbit_in_nhds
    let ⟨V, V_ss_clOrbit, V_open, p_in_V⟩ := clOrbit_in_nhds
    clear clOrbit_in_nhds

    -- Then, get a nontrivial element from that set
    let ⟨g, g_in_rist, g_ne_one⟩ := LocallyMoving.get_nontrivial_rist_elem (G := G) V_open ⟨p, p_in_V⟩

    -- Somehow, the regular support of g is within U
    have rsupp_ss_U : RegularSupport α g ⊆ U.val := by
      rw [RegularSupport, InteriorClosure]

      apply interiorClosure_subset_of_regular _ U.regular
      rw [<-rigidStabilizer_support]
      apply rigidStabilizer_mono _ g_in_rist

      show V ⊆ U.val
      -- Would probably require showing that the orbit of the rigidstabilizer is a subset of U
      sorry

    -- Use as the chosen set RegularSupport g
    let g' : HomeoGroup α := HomeoGroup.fromContinuous α g
    have g'_ne_one : g' ≠ 1 := by
      simp
      rw [<-HomeoGroup.fromContinuous_one (G := G)]
      rw [HomeoGroup.fromContinuous_eq_iff]
      exact g_ne_one
    use RegularSupportBasis.fromSingleton g' g'_ne_one

    constructor
    · -- This statement is equivalent to rsupp(g) ⊆ U
      rw [RegularSupportBasis.le_def]
      rw [RegularSupportBasis.fromSingleton_val]
      unfold RegularSupportInter₀
      simp
      exact rsupp_ss_U
    · intro W W_in_subsets
      rw [RegularSupportBasis.fromSingleton_val] at W_in_subsets
      unfold RSuppSubsets RegularSupportInter₀ at W_in_subsets
      simp at W_in_subsets
      let ⟨W_in_basis, W_subset_rsupp⟩ := W_in_subsets
      clear W_in_subsets g' g'_ne_one

      -- We have that W is a subset of the closure of the orbit of G_U
      have W_ss_clOrbit : W ⊆ closure (MulAction.orbit (↥(RigidStabilizer G U.val)) p) := by
        rw [rigidStabilizer_support] at g_in_rist
        calc
          W ⊆ RegularSupport α g := by assumption
          _ ⊆ closure (Support α g) := regularSupport_subset_closure_support
          _ ⊆ closure V := by
            apply closure_mono
            assumption
          _ ⊆ _ := by
            rw [<-closure_closure (s := MulAction.orbit _ _)]
            apply closure_mono
            assumption
      unfold RSuppOrbit
      simp

      have W_open : IsOpen W := by
        let ⟨W', W'_eq⟩ := (RegularSupportBasis.mem_asSet _).mp W_in_basis
        rw [<-W'_eq]
        exact W'.regular.isOpen
      have W_nonempty : Set.Nonempty W := by
        let ⟨W', W'_eq⟩ := (RegularSupportBasis.mem_asSet _).mp W_in_basis
        rw [<-W'_eq]
        exact W'.nonempty

      -- We get an element `h` such that `h • p ∈ W` and `h ∈ G_U`
      let ⟨h, h_in_rist, hp_in_W⟩ := moving_elem_of_open_subset_closure_orbit W_open W_ss_clOrbit

      use h
      constructor
      exact h_in_rist

      use h⁻¹ •'' W
      constructor
      swap
      {
        rw [smulImage_mul]
        simp
      }

      -- We just need to show that h⁻¹ •'' W ∈ F, that is, h⁻¹ •'' W ∈ 𝓝 p
      rw [Ultrafilter.clusterPt_iff] at p_clusterPt
      apply p_clusterPt

      have basis := (RegularSupportBasis.isBasis G α).nhds_hasBasis (a := p)
      rw [basis.mem_iff]
      use h⁻¹ •'' W
      repeat' apply And.intro
      · rw [RegularSupportBasis.mem_asSet]
        rw [RegularSupportBasis.mem_asSet] at W_in_basis
        let ⟨W', W'_eq⟩ := W_in_basis
        have dec_eq : DecidableEq (HomeoGroup α) := Classical.decEq _
        use (HomeoGroup.fromContinuous α h⁻¹) • W'
        rw [RegularSupportBasis.smul_val, W'_eq]
        simp
      · rw [mem_smulImage, inv_inv]
        exact hp_in_W
      · exact Eq.subset rfl
  }
  {
    intro ⟨V, ⟨V_ss_U, subsets_ss_orbit⟩⟩
    rw [RegularSupportBasis.le_def] at V_ss_U

    -- Obtain a compact subset of V' in the basis
    let ⟨V', clV'_ss_V, clV'_compact⟩ := compact_subset_of_rsupp_basis V

    have V'_in_subsets : V'.val ∈ RSuppSubsets V.val := by
      unfold RSuppSubsets
      simp
      constructor
      unfold RegularSupportBasis.asSet
      simp
      exact subset_trans subset_closure clV'_ss_V

    -- V' is in the orbit, so there exists a value `g ∈ G_U` such that `gV ∈ F`
    -- Note that with the way we set up the equations, we obtain `g⁻¹`
    have V'_in_orbit := subsets_ss_orbit V'_in_subsets
    simp [RSuppOrbit] at V'_in_orbit
    let ⟨g, g_in_rist, ⟨W, W_in_F, gW_eq_V⟩⟩ := V'_in_orbit

    have gV'_in_F : g⁻¹ •'' V' ∈ F := by
      rw [smulImage_inv] at gW_eq_V
      rw [<-gW_eq_V]
      assumption
    have gV'_compact : IsCompact (closure (g⁻¹ •'' V'.val)) := by
      rw [smulImage_closure _ _ (continuousMulAction_elem_continuous α g⁻¹)]
      -- TODO: smulImage_compact
      sorry

    have ⟨p, p_lim⟩ := (proposition_3_4_2 F).mpr ⟨g⁻¹ •'' V'.val, ⟨gV'_in_F, gV'_compact⟩⟩
    use p
    constructor
    swap
    assumption

    rw [clusterPt_iff_forall_mem_closure] at p_lim
    specialize p_lim (g⁻¹ •'' V') gV'_in_F
    rw [smulImage_closure _ _ (continuousMulAction_elem_continuous α g⁻¹)] at p_lim
    rw [mem_smulImage, inv_inv] at p_lim

    rw [rigidStabilizer_support] at g_in_rist
    rw [<-support_inv] at g_in_rist
    have q := fixed_smulImage_in_support g⁻¹ g_in_rist
    rw [<-fixed_smulImage_in_support g⁻¹ g_in_rist]

    rw [mem_smulImage, inv_inv]
    apply V_ss_U
    apply clV'_ss_V
    exact p_lim
  }

end HomeoGroup

variable {G α β : Type _}
variable [Group G]

variable [TopologicalSpace α] [MulAction G α] [ContinuousMulAction G α]
         [TopologicalSpace β] [MulAction G β] [ContinuousMulAction G β]

theorem rubin (hα : RubinAction G α) (hβ : RubinAction G β) : EquivariantHomeomorph G α β := by
  sorry

end Rubin

end Rubin
