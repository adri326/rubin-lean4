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
import Mathlib.Topology.Algebra.ConstMulAction

import Rubin.Tactic
import Rubin.MulActionExt
import Rubin.SmulImage
import Rubin.Support
import Rubin.Topology
import Rubin.RigidStabilizer
-- import Rubin.RigidStabilizerBasis
import Rubin.Period
import Rubin.AlgebraicDisjointness
import Rubin.RegularSupport
import Rubin.RegularSupportBasis
import Rubin.HomeoGroup
import Rubin.Filter

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
variable [ContinuousConstSMul G α]
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
  have ⟨V, V_open, x_in_V, V_in_support, disjoint_img_V⟩ := disjoint_nbhd_in (support_isOpen f) x_in_supp_f hx_ne_x

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
  have U_open: IsOpen U := (IsOpen.inter (support_isOpen f) (support_isOpen (g^12)))

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
  [ContinuousConstSMul G α] [FaithfulSMul G α]
  [T2Space α] [h_lm : LocallyMoving G α]
  {U : Set α} (U_open : IsOpen U) (U_nonempty : Set.Nonempty U) :
  Monoid.exponent G•[U] = 0 :=
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
  [Group G] [TopologicalSpace α] [MulAction G α] [ContinuousConstSMul G α] [T2Space α]
  {f h : G} (not_support_subset_rsupp : ¬Support α h ⊆ RegularSupport α f):
  ∃ V : Set α, V ⊆ Support α h ∧ Set.Nonempty V ∧ IsOpen V ∧ Disjoint V (Support α f) :=
by
  let U := Support α h \ closure (RegularSupport α f)
  have U_open : IsOpen U := by
    unfold_let
    rw [Set.diff_eq_compl_inter]
    apply IsOpen.inter
    · simp
    · exact support_isOpen _
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
  · exact support_isOpen _
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
  [Group G] [TopologicalSpace α] [MulAction G α] [ContinuousConstSMul G α] [T2Space α]
  [LocallyMoving G α] [h_faithful : FaithfulSMul G α]
  (f : G) :
  AlgebraicCentralizer f = G•[RegularSupport α f] :=
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
        exact Disjoint.closure_left supp_disj (support_isOpen _)
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
  [Group G] [TopologicalSpace α] [MulAction G α] [ContinuousConstSMul G α] [LocallyMoving G α] [FaithfulSMul G α]
  {f g : G} :
  G•[RegularSupport α f] ⊓ G•[RegularSupport α g] = ⊥
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
variable [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α] [LocallyMoving G α]

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
  rw [disjoint_interiorClosure_iff (support_isOpen _) (support_isOpen _)]
  simp
  repeat rw [<-RegularSupport.def]
  rw [<-rigidStabilizer_inter_bot_iff_regularSupport_disj]

  repeat rw [<-proposition_2_1]
  exact alg_disj

-- lemma remark_2_3' {f g : G} :
--   (AlgebraicCentralizer f) ⊓ (AlgebraicCentralizer g) ≠ ⊥ →
--   Set.Nonempty ((RegularSupport α f) ∩ (RegularSupport α g)) :=
-- by
--   intro alg_inter_neBot
--   repeat rw [proposition_2_1 (α := α)] at alg_inter_neBot
--   rw [ne_eq] at alg_inter_neBot

--   rw [rigidStabilizer_inter_bot_iff_regularSupport_disj] at alg_inter_neBot
--   rw [Set.not_disjoint_iff_nonempty_inter] at alg_inter_neBot
--   exact alg_inter_neBot

lemma rigidStabilizer_inter_eq_algebraicCentralizerInter {S : Finset G} :
  G•[RegularSupport.FiniteInter α S] = AlgebraicCentralizerInter S :=
by
  unfold RegularSupport.FiniteInter
  unfold AlgebraicCentralizerInter
  rw [rigidStabilizer_iInter_regularSupport']
  simp only [<-proposition_2_1]

lemma regularSupportInter_nonEmpty_iff_neBot {S : Finset G} [Nonempty α]:
  AlgebraicCentralizerInter S ≠ ⊥ ↔
  Set.Nonempty (RegularSupport.FiniteInter α S) :=
by
  constructor
  · rw [<-rigidStabilizer_inter_eq_algebraicCentralizerInter (α := α), ne_eq]
    intro rist_neBot
    by_contra eq_empty
    rw [Set.not_nonempty_iff_eq_empty] at eq_empty
    rw [eq_empty, rigidStabilizer_empty] at rist_neBot
    exact rist_neBot rfl
  · intro nonempty
    intro eq_bot
    rw [<-rigidStabilizer_inter_eq_algebraicCentralizerInter (α := α)] at eq_bot
    rw [<-rigidStabilizer_empty (G := G) (α := α), rigidStabilizer_eq_iff] at eq_bot
    · rw [eq_bot, Set.nonempty_iff_ne_empty] at nonempty
      exact nonempty rfl
    · apply RegularSupport.FiniteInter_regular
    · simp

theorem AlgebraicCentralizerBasis.exists_rigidStabilizer_inv (H : Set G) [Nonempty α]:
  ∃ S,
    (H ∈ AlgebraicCentralizerBasis G → S ∈ RegularSupportBasis G α ∧ H = G•[S])
    ∧ (H ∉ AlgebraicCentralizerBasis G → S = ∅) :=
by
  by_cases H_in_basis?: H ∈ AlgebraicCentralizerBasis G
  swap
  {
    use ∅
    constructor
    tauto
    intro _
    rfl
  }

  have ⟨H_ne_one, ⟨seed, H_eq⟩⟩ := (AlgebraicCentralizerBasis.mem_iff H).mp H_in_basis?

  rw [H_eq, <-Subgroup.coe_bot, ne_eq, SetLike.coe_set_eq, <-ne_eq] at H_ne_one

  use RegularSupport.FiniteInter α seed
  constructor
  · intro _
    rw [RegularSupportBasis.mem_iff]
    repeat' apply And.intro
    · rw [<-regularSupportInter_nonEmpty_iff_neBot]
      exact H_ne_one
    · use seed
    · rw [rigidStabilizer_inter_eq_algebraicCentralizerInter]
      exact H_eq
  · tauto

theorem AlgebraicCentralizerBasis.mem_of_regularSupportBasis {S : Set α}
  (S_in_basis : S ∈ RegularSupportBasis G α) :
  (G•[S] : Set G) ∈ AlgebraicCentralizerBasis G :=
by
  rw [AlgebraicCentralizerBasis.subgroup_mem_iff]
  rw [RegularSupportBasis.mem_iff] at S_in_basis
  let ⟨S_nonempty, ⟨seed, S_eq⟩⟩ := S_in_basis

  have α_nonempty : Nonempty α := by
    by_contra α_empty
    rw [not_nonempty_iff] at α_empty
    rw [Set.nonempty_iff_ne_empty] at S_nonempty
    apply S_nonempty
    exact Set.eq_empty_of_isEmpty S

  constructor
  · rw [S_eq, rigidStabilizer_inter_eq_algebraicCentralizerInter]
    rw [regularSupportInter_nonEmpty_iff_neBot (α := α)]
    rw [<-S_eq]
    exact S_nonempty
  · use seed
    rw [S_eq]
    exact rigidStabilizer_inter_eq_algebraicCentralizerInter

@[simp]
theorem AlgebraicCentralizerBasis.eq_rist_image [Nonempty α]:
  (fun S => (G•[S] : Set G)) '' RegularSupportBasis G α = AlgebraicCentralizerBasis G :=
by
  ext H
  constructor
  · simp
    intro S S_in_basis H_eq
    rw [<-H_eq]
    apply mem_of_regularSupportBasis S_in_basis
  · intro H_in_basis
    simp

    let ⟨S, ⟨S_props, _⟩⟩ := AlgebraicCentralizerBasis.exists_rigidStabilizer_inv (α := α) H
    let ⟨S_in_basis, H_eq⟩ := S_props H_in_basis
    symm at H_eq
    use S

noncomputable def rigidStabilizer_inv [Nonempty α] (H : Set G) : Set α :=
  (AlgebraicCentralizerBasis.exists_rigidStabilizer_inv H).choose

theorem rigidStabilizer_inv_eq [Nonempty α] {H : Set G} (H_in_basis : H ∈ AlgebraicCentralizerBasis G) :
  H = G•[rigidStabilizer_inv (α := α) H] :=
by
  have spec := (AlgebraicCentralizerBasis.exists_rigidStabilizer_inv (α := α) H).choose_spec
  exact (spec.left H_in_basis).right

theorem rigidStabilizer_inv_in_basis [Nonempty α] (H : Set G) :
  H ∈ AlgebraicCentralizerBasis G ↔ rigidStabilizer_inv (α := α) H ∈ RegularSupportBasis G α :=
by
  have spec := (AlgebraicCentralizerBasis.exists_rigidStabilizer_inv (α := α) H).choose_spec
  constructor
  · intro H_in_basis
    exact (spec.left H_in_basis).left
  · intro iH_in_basis
    by_contra H_notin_basis
    unfold rigidStabilizer_inv at iH_in_basis
    rw [(spec.right H_notin_basis)] at iH_in_basis
    exact RegularSupportBasis.empty_not_mem G α iH_in_basis

theorem rigidStabilizer_inv_eq' [Nonempty α] {S : Set α} (S_in_basis : S ∈ RegularSupportBasis G α) :
  rigidStabilizer_inv (α := α) (G := G) G•[S] = S :=
by
  have GS_in_basis : (G•[S] : Set G) ∈ AlgebraicCentralizerBasis G := by
    exact AlgebraicCentralizerBasis.mem_of_regularSupportBasis S_in_basis

  have eq := rigidStabilizer_inv_eq GS_in_basis (α := α)
  rw [SetLike.coe_set_eq, rigidStabilizer_eq_iff] at eq
  · exact eq.symm
  · exact RegularSupportBasis.regular S_in_basis
  · exact RegularSupportBasis.regular ((rigidStabilizer_inv_in_basis _).mp GS_in_basis)

variable [Nonempty α] [HasNoIsolatedPoints α] [LocallyDense G α]

noncomputable def RigidStabilizer.order_iso_on (G α : Type _) [Group G] [Nonempty α] [TopologicalSpace α] [T2Space α]
  [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α]
  [HasNoIsolatedPoints α] [LocallyDense G α] : OrderIsoOn (Set α) (Set G) (RegularSupportBasis G α)
where
  toFun := fun S => G•[S]
  invFun := fun H => rigidStabilizer_inv (α := α) H

  leftInv_on := by
    intro S S_in_basis
    simp
    exact rigidStabilizer_inv_eq' S_in_basis

  rightInv_on := by
    intro H H_in_basis
    simp
    simp at H_in_basis
    symm
    exact rigidStabilizer_inv_eq H_in_basis

  toFun_doubleMonotone := by
    intro S S_in_basis T T_in_basis
    simp
    apply rigidStabilizer_subset_iff G (RegularSupportBasis.regular S_in_basis) (RegularSupportBasis.regular T_in_basis)

@[simp]
theorem RigidStabilizer.order_iso_on_toFun:
  (RigidStabilizer.order_iso_on G α).toFun = (fun S => (G•[S] : Set G)) :=
by
  simp [order_iso_on]

@[simp]
theorem RigidStabilizer.order_iso_on_invFun:
  (RigidStabilizer.order_iso_on G α).invFun = (fun S => rigidStabilizer_inv (α := α) S) :=
by
  simp [order_iso_on]

noncomputable def RigidStabilizer.inv_order_iso_on (G α : Type _) [Group G] [Nonempty α] [TopologicalSpace α] [T2Space α]
  [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α]
  [HasNoIsolatedPoints α] [LocallyDense G α] : OrderIsoOn (Set G) (Set α) (AlgebraicCentralizerBasis G) :=
  (RigidStabilizer.order_iso_on G α).inv.mk_of_subset
    (subset_of_eq (AlgebraicCentralizerBasis.eq_rist_image (α := α) (G := G)).symm)

@[simp]
theorem RigidStabilizer.inv_order_iso_on_toFun:
  (RigidStabilizer.inv_order_iso_on G α).toFun = (fun S => rigidStabilizer_inv (α := α) S) :=
by
  simp [inv_order_iso_on, order_iso_on]

@[simp]
theorem RigidStabilizer.inv_order_iso_on_invFun:
  (RigidStabilizer.inv_order_iso_on G α).invFun = (fun S => (G•[S] : Set G)) :=
by
  simp [inv_order_iso_on, order_iso_on]

-- TODO: mark simp theorems as local
@[simp]
theorem RegularSupportBasis.eq_inv_rist_image:
  (fun H => rigidStabilizer_inv (α := α) H) '' AlgebraicCentralizerBasis G = RegularSupportBasis G α :=
by
  rw [<-AlgebraicCentralizerBasis.eq_rist_image (α := α) (G := G)]
  rw [Set.image_image]
  nth_rw 2 [<-OrderIsoOn.leftInv_image (RigidStabilizer.order_iso_on G α)]
  rw [Function.comp_def]
  rw [RigidStabilizer.order_iso_on]

lemma RigidStabilizer_doubleMonotone : DoubleMonotoneOn (fun S => G•[S]) (RegularSupportBasis G α) := by
  have res := (RigidStabilizer.order_iso_on G α).toFun_doubleMonotone
  simp at res
  exact res

lemma RigidStabilizer_inv_doubleMonotone : DoubleMonotoneOn (fun S => rigidStabilizer_inv (α := α) S) (AlgebraicCentralizerBasis G) := by
  have res := (RigidStabilizer.order_iso_on G α).invFun_doubleMonotone
  simp at res
  exact res

lemma RigidStabilizer_rightInv {U : Set G} (U_in_basis : U ∈ AlgebraicCentralizerBasis G) :
  G•[rigidStabilizer_inv (α := α) U] = U :=
by
  have res := (RigidStabilizer.order_iso_on G α).rightInv_on U
  simp at res
  exact res U_in_basis

lemma RigidStabilizer_leftInv {U : Set α} (U_in_basis : U ∈ RegularSupportBasis G α) :
  rigidStabilizer_inv (α := α) (G•[U] : Set G) = U :=
by
  have res := (RigidStabilizer.order_iso_on G α).leftInv_on U
  simp at res
  exact res U_in_basis


theorem rigidStabilizer_subset_iff_subset_inv [Nonempty α] {S : Set α} (S_in_basis : S ∈ RegularSupportBasis G α) {T : Set G} (T_in_basis : T ∈ AlgebraicCentralizerBasis G):
  (G•[S] : Set G) ⊆ T ↔ S ⊆ rigidStabilizer_inv T :=
by
  nth_rw 1 [<-RigidStabilizer_rightInv (α := α) T_in_basis]
  rw [SetLike.coe_subset_coe]
  rw [rigidStabilizer_subset_iff (G := G)]
  · exact RegularSupportBasis.regular S_in_basis
  · apply RegularSupportBasis.regular (G := G)
    rw [<-rigidStabilizer_inv_in_basis T]
    assumption

theorem subset_rigidStabilizer_iff_inv_subset [Nonempty α] {S : Set G} (S_in_basis : S ∈ AlgebraicCentralizerBasis G) {T : Set α} (T_in_basis : T ∈ RegularSupportBasis G α):
  S ⊆ (G•[T] : Set G) ↔ rigidStabilizer_inv S ⊆ T :=
by
  nth_rw 1 [<-RigidStabilizer_rightInv (α := α) S_in_basis]
  rw [SetLike.coe_subset_coe]
  rw [rigidStabilizer_subset_iff (G := G)]
  · apply RegularSupportBasis.regular (G := G)
    rw [<-rigidStabilizer_inv_in_basis S]
    assumption
  · exact RegularSupportBasis.regular T_in_basis

theorem rigidStabilizer_inv_smulImage [Nonempty α] {S : Set G} (S_in_basis : S ∈ AlgebraicCentralizerBasis G) (h : G) :
  h •'' rigidStabilizer_inv S = rigidStabilizer_inv (α := α) ((fun g => h * g * h⁻¹) '' S) :=
by
  rw [smulImage_inv]
  rw [<-rigidStabilizer_eq_iff (G := G)]
  swap
  {
    apply RegularSupportBasis.regular (G := G)
    rw [<-rigidStabilizer_inv_in_basis S]
    exact S_in_basis
  }
  swap
  {
    rw [<-smulImage_regular]
    apply RegularSupportBasis.regular (G := G)
    rw [<-rigidStabilizer_inv_in_basis]
    apply AlgebraicCentralizerBasis.conj_mem
    assumption
  }
  rw [<-SetLike.coe_set_eq]
  rw [<-rigidStabilizer_conj_image_eq]
  repeat rw [RigidStabilizer_rightInv]
  · rw [Set.image_image]
    group
    simp
  · apply AlgebraicCentralizerBasis.conj_mem
    assumption
  · assumption

end RegularSupport

section HomeoGroup

open Topology

variable {G α : Type _} [Group G] [TopologicalSpace α] [T2Space α]
variable [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α] [LocallyMoving G α]

theorem exists_compact_closure_of_le_nhds {α : Type _} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] (F : Filter α):
  (∃ p : α, F ≤ 𝓝 p) → ∃ S ∈ F, IsCompact (closure S) :=
by
  intro ⟨p, p_le_nhds⟩
  have ⟨S, S_in_nhds, S_compact⟩ := (compact_basis_nhds p).ex_mem
  use S
  constructor
  exact p_le_nhds S_in_nhds
  rw [IsClosed.closure_eq S_compact.isClosed]
  exact S_compact

theorem clusterPt_of_exists_compact_closure {α : Type _} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] (F : Filter α) [Filter.NeBot F]:
  (∃ S ∈ F, IsCompact (closure S)) → ∃ p : α, ClusterPt p F :=
by
  intro ⟨S, S_in_F, clS_compact⟩
  have F_le_principal_S : F ≤ Filter.principal (closure S) := by
    rw [Filter.le_principal_iff]
    apply Filter.sets_of_superset
    exact S_in_F
    exact subset_closure
  let ⟨x, _, F_clusterPt⟩ := clS_compact F_le_principal_S
  use x

theorem proposition_3_4_2 {α : Type _} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] (F : Ultrafilter α):
  (∃ p : α, ClusterPt p F) ↔ ∃ S ∈ F, IsCompact (closure S) :=
by
  constructor
  · simp only [Ultrafilter.clusterPt_iff, <-Ultrafilter.mem_coe]
    exact exists_compact_closure_of_le_nhds (F : Filter α)
  · exact clusterPt_of_exists_compact_closure (F : Filter α)

end HomeoGroup


section Ultrafilter

variable {G α : Type _}
variable [Group G]
variable [TopologicalSpace α] [T2Space α]
variable [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α] [LocallyMoving G α]

def RSuppSubsets (G : Type _) {α : Type _} [Group G] [TopologicalSpace α] [MulAction G α] (V : Set α) : Set (Set α) :=
  {W ∈ RegularSupportBasis G α | W ⊆ V}

def RSuppOrbit {G α : Type _} [Group G] [TopologicalSpace α] [MulAction G α] (F : Filter α) (H : Subgroup G) : Set (Set α) :=
  { g •'' W | (g ∈ H) (W ∈ F) }

lemma moving_elem_of_open_subset_closure_orbit {U V : Set α} (U_open : IsOpen U) (U_nonempty : Set.Nonempty U)
  {p : α} (U_ss_clOrbit : U ⊆ closure (MulAction.orbit G•[V] p)) :
  ∃ h : G, h ∈ G•[V] ∧ h • p ∈ U :=
by
  have p_in_orbit : p ∈ MulAction.orbit G•[V] p := by simp

  have ⟨q, ⟨q_in_U, q_in_orbit⟩⟩ := inter_of_open_subset_of_closure
    U_open U_nonempty ⟨p, p_in_orbit⟩ U_ss_clOrbit

  rw [MulAction.mem_orbit_iff] at q_in_orbit
  let ⟨⟨h, h_in_orbit⟩, hq_eq_p⟩ := q_in_orbit
  simp at hq_eq_p

  use h
  constructor
  assumption
  rw [hq_eq_p]
  assumption

lemma compact_subset_of_rsupp_basis (G : Type _) {α : Type _}
  [Group G] [TopologicalSpace α] [T2Space α]
  [MulAction G α] [ContinuousConstSMul G α]
  [LocallyCompactSpace α] [HasNoIsolatedPoints α] [LocallyDense G α]
  {U : Set α} (U_in_basis : U ∈ RegularSupportBasis G α):
  ∃ V : RegularSupportBasis G α, (closure V.val) ⊆ U ∧ IsCompact (closure V.val) :=
by
  let ⟨⟨x, x_in_U⟩, _⟩ := (RegularSupportBasis.mem_iff U).mp U_in_basis
  have U_regular : Regular U := RegularSupportBasis.regular U_in_basis

  let ⟨W, W_compact, x_in_intW, W_ss_U⟩ := exists_compact_subset U_regular.isOpen x_in_U
  have ⟨V, V_in_basis, _, V_ss_intW⟩ := (RegularSupportBasis.isBasis G α).exists_subset_of_mem_open x_in_intW isOpen_interior

  have clV_ss_W : closure V ⊆ W := by
    calc
      closure V ⊆ closure (interior W) := by
        apply closure_mono
        exact V_ss_intW
      _ ⊆ closure W := by
        apply closure_mono
        exact interior_subset
      _ = W := by
        apply IsClosed.closure_eq
        exact W_compact.isClosed

  use ⟨V, V_in_basis⟩
  simp

  constructor
  · exact subset_trans clV_ss_W W_ss_U
  · exact IsCompact.of_isClosed_subset W_compact isClosed_closure clV_ss_W

variable [LocallyDense G α] [LocallyCompactSpace α] [HasNoIsolatedPoints α]

lemma proposition_3_5_1
  {U : Set α} (U_in_basis : U ∈ RegularSupportBasis G α) (F: Filter α):
  (∃ p ∈ U, F ≤ nhds p)
  → ∃ V : RegularSupportBasis G α, V.val ⊆ U ∧ RSuppSubsets G V.val ⊆ RSuppOrbit F G•[U] :=
by
  simp
  intro p p_in_U F_le_nhds_p
  have U_regular : Regular U := RegularSupportBasis.regular U_in_basis

  -- First, get a neighborhood of p that is a subset of the closure of the orbit of G_U
  have clOrbit_in_nhds := LocallyDense.rigidStabilizer_in_nhds G α U_regular.isOpen p_in_U
  rw [mem_nhds_iff] at clOrbit_in_nhds
  let ⟨V, V_ss_clOrbit, V_open, p_in_V⟩ := clOrbit_in_nhds
  clear clOrbit_in_nhds

  -- Then, get a nontrivial element from that set
  let ⟨g, g_in_rist, g_ne_one⟩ := LocallyMoving.get_nontrivial_rist_elem (G := G) V_open ⟨p, p_in_V⟩

  have V_ss_clU : V ⊆ closure U := by
    apply subset_trans
    exact V_ss_clOrbit
    apply closure_mono
    exact orbit_rigidStabilizer_subset p_in_U

  -- The regular support of g is within U
  have rsupp_ss_U : RegularSupport α g ⊆ U := by
    rw [RegularSupport]
    rw [rigidStabilizer_support] at g_in_rist
    calc
      InteriorClosure (Support α g) ⊆ InteriorClosure V := by
        apply interiorClosure_mono
        assumption
      _ ⊆ InteriorClosure (closure U) := by
        apply interiorClosure_mono
        assumption
      _ ⊆ InteriorClosure U := by
        simp
        rfl
      _ ⊆ _ := by
        apply subset_of_eq
        exact U_regular

  let T := RegularSupportBasis.fromSingleton (α := α) g g_ne_one
  have T_eq : T.val = RegularSupport α g := by
    unfold_let
    rw [RegularSupportBasis.fromSingleton_val]
  use T.val

  repeat' apply And.intro
  · -- This statement is equivalent to rsupp(g) ⊆ U
    rw [T_eq]
    exact rsupp_ss_U
  · exact T.prop.left
  · exact T.prop.right
  · intro W W_in_subsets
    simp [RSuppSubsets, T_eq] at W_in_subsets
    let ⟨W_in_basis, W_ss_W⟩ := W_in_subsets
    unfold RSuppOrbit
    simp

    -- We have that W is a subset of the closure of the orbit of G_U
    have W_ss_clOrbit : W ⊆ closure (MulAction.orbit G•[U] p) := by
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

    let ⟨W_nonempty, ⟨W_seed, W_eq⟩⟩ := W_in_basis
    have W_regular := RegularSupportBasis.regular W_in_basis

    -- So we can get an element `h` such that `h • p ∈ W` and `h ∈ G_U`
    let ⟨h, h_in_rist, hp_in_W⟩ := moving_elem_of_open_subset_closure_orbit W_regular.isOpen W_nonempty W_ss_clOrbit

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
    apply F_le_nhds_p

    have basis := (RegularSupportBasis.isBasis G α).nhds_hasBasis (a := p)
    rw [basis.mem_iff]
    use h⁻¹ •'' W
    repeat' apply And.intro
    · rw [smulImage_nonempty]
      assumption
    · simp only [smulImage_inv, inv_inv]
      have dec_eq : DecidableEq G := Classical.typeDecidableEq G
      use Finset.image (fun g => h⁻¹ * g * h) W_seed
      rw [<-RegularSupport.FiniteInter_conj, Finset.image_image]
      have fn_eq_id : (fun g => h * g * h⁻¹) ∘ (fun g => h⁻¹ * g * h) = id := by
        ext x
        simp
        group
      rw [fn_eq_id, Finset.image_id]
      exact W_eq
    · rw [mem_smulImage, inv_inv]
      exact hp_in_W
    · exact Eq.subset rfl

theorem proposition_3_5_2
  {U : Set α} (F: Filter α) [Filter.NeBot F]:
  (∃ V : RegularSupportBasis G α, V.val ⊆ U ∧ RSuppSubsets G V.val ⊆ RSuppOrbit F G•[U]) → ∃ p ∈ U, ClusterPt p F :=
by
  intro ⟨⟨V, V_in_basis⟩, ⟨V_ss_U, subsets_ss_orbit⟩⟩
  simp only at V_ss_U
  simp only at subsets_ss_orbit

  -- Obtain a compact subset of V' in the basis
  let ⟨V', clV'_ss_V, clV'_compact⟩ := compact_subset_of_rsupp_basis G V_in_basis

  have V'_in_subsets : V'.val ∈ RSuppSubsets G V := by
    unfold RSuppSubsets
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
    rw [smulImage_closure]
    apply smulImage_compact
    assumption

  have ⟨p, p_lim⟩ := clusterPt_of_exists_compact_closure _ ⟨g⁻¹ •'' V'.val, ⟨gV'_in_F, gV'_compact⟩⟩
  use p
  constructor
  swap
  assumption

  rw [clusterPt_iff_forall_mem_closure] at p_lim
  specialize p_lim (g⁻¹ •'' V') gV'_in_F
  rw [smulImage_closure, mem_smulImage, inv_inv] at p_lim

  rw [rigidStabilizer_support, <-support_inv] at g_in_rist
  rw [<-fixed_smulImage_in_support g⁻¹ g_in_rist]

  rw [mem_smulImage, inv_inv]
  apply V_ss_U
  apply clV'_ss_V
  exact p_lim

/--
# Proposition 3.5

This proposition gives an alternative definition for an ultrafilter to converge within a set `U`.
This alternative definition should be reconstructible entirely from the algebraic structure of `G`.
--/
theorem proposition_3_5 {U : Set α} (U_in_basis : U ∈ RegularSupportBasis G α) (F: Ultrafilter α):
  (∃ p ∈ U, ClusterPt p F)
  ↔ ∃ V : RegularSupportBasis G α, V.val ⊆ U ∧ RSuppSubsets G V.val ⊆ RSuppOrbit F G•[U] :=
by
  constructor
  · simp only [Ultrafilter.clusterPt_iff]
    exact proposition_3_5_1 U_in_basis (F : Filter α)
  · exact proposition_3_5_2 (F : Filter α)

theorem proposition_3_5' {U : Set α} (U_in_basis : U ∈ RegularSupportBasis G α)
  (F : UltrafilterInBasis (RegularSupportBasis G α)):
  (∃ p ∈ U, F ≤ nhds p)
  ↔ ∃ V ∈ RegularSupportBasis G α, V ⊆ U ∧ RSuppSubsets G V ⊆ RSuppOrbit F G•[U] :=
by
  constructor
  · intro ex_p
    let ⟨⟨V, V_in_basis⟩, V_ss_U, subsets_ss_orbit⟩ := proposition_3_5_1 U_in_basis (F : Filter α) ex_p
    exact ⟨V, V_in_basis, V_ss_U, subsets_ss_orbit⟩
  · intro ⟨V, V_in_basis, V_ss_U, subsets_ss_orbit⟩
    simp only [
      <-F.clusterPt_iff_le_nhds
        (RegularSupportBasis.isBasis G α)
        (RegularSupportBasis.closed_inter G α)
    ]
    exact proposition_3_5_2 (F : Filter α) ⟨⟨V, V_in_basis⟩, V_ss_U, subsets_ss_orbit⟩

end Ultrafilter

section RubinFilter

variable {G : Type _} [Group G]
variable {α : Type _} [Nonempty α] [TopologicalSpace α] [HasNoIsolatedPoints α] [T2Space α] [LocallyCompactSpace α]
variable [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α] [LocallyDense G α]

def AlgebraicSubsets (V : Set G) : Set (Set G) :=
  {W ∈ AlgebraicCentralizerBasis G | W ⊆ V}

def AlgebraicOrbit (F : Filter G) (U : Set G) : Set (Set G) :=
  { (fun h => g * h * g⁻¹) '' W | (g ∈ U) (W ∈ F.sets ∩ AlgebraicCentralizerBasis G) }

theorem AlgebraicOrbit.mem_iff (F : Filter G) (U : Set G) (S : Set G):
  S ∈ AlgebraicOrbit F U ↔ ∃ g ∈ U, ∃ W ∈ F, W ∈ AlgebraicCentralizerBasis G ∧ S = (fun h => g * h * g⁻¹) '' W :=
by
  simp [AlgebraicOrbit]
  simp only [and_assoc, eq_comm]

def AlgebraicConvergent {G : Type _} [Group G]
  (F : Filter G)
  (U : Set G) : Prop :=
  ∃ V ∈ AlgebraicCentralizerBasis G, V ⊆ U ∧ AlgebraicSubsets V ⊆ AlgebraicOrbit F U

structure RubinFilter (G : Type _) [Group G] :=
  filter : UltrafilterInBasis (AlgebraicCentralizerBasis G)

  converges : AlgebraicConvergent filter.filter Set.univ

lemma RegularSupportBasis.empty_not_mem' : ∅ ∉ (RigidStabilizer.inv_order_iso_on G α).toFun '' AlgebraicCentralizerBasis G := by
  simp
  exact RegularSupportBasis.empty_not_mem _ _

lemma AlgebraicCentralizerBasis.empty_not_mem' : ∅ ∉ (RigidStabilizer.order_iso_on G α).toFun '' RegularSupportBasis G α := by
  unfold RigidStabilizer.order_iso_on
  rw [AlgebraicCentralizerBasis.eq_rist_image]
  exact AlgebraicCentralizerBasis.empty_not_mem

def RubinFilter.map (F : RubinFilter G) (α : Type _)
  [TopologicalSpace α] [T2Space α] [Nonempty α] [HasNoIsolatedPoints α]
  [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α] [LocallyDense G α] : UltrafilterInBasis (RegularSupportBasis G α) :=
  (
    F.filter.map_basis
      AlgebraicCentralizerBasis.empty_not_mem
      (RigidStabilizer.inv_order_iso_on G α)
      RegularSupportBasis.empty_not_mem'
  ).cast (by simp)

def IsRubinFilterOf (A : UltrafilterInBasis (RegularSupportBasis G α)) (B : UltrafilterInBasis (AlgebraicCentralizerBasis G)) : Prop :=
  ∀ U ∈ RegularSupportBasis G α, U ∈ A ↔ (G•[U] : Set G) ∈ B

theorem RubinFilter.map_isRubinFilterOf (F : RubinFilter G) :
  IsRubinFilterOf (F.map α) F.filter :=
by
  intro U U_in_basis
  unfold map
  simp
  have ⟨U', U'_in_basis, U'_eq⟩ := (RegularSupportBasis.eq_inv_rist_image (G := G) (α := α)).symm ▸ U_in_basis
  simp only at U'_eq
  rw [<-U'_eq]
  rw [Filter.InBasis.map_mem_map_basis_of_basis_set _ RigidStabilizer_inv_doubleMonotone F.filter.in_basis U'_in_basis]
  rw [RigidStabilizer_rightInv U'_in_basis]
  rfl

theorem RubinFilter.from_isRubinFilterOf' (F : UltrafilterInBasis (RegularSupportBasis G α)) :
  IsRubinFilterOf F ((F.map_basis
    (RegularSupportBasis.empty_not_mem G α)
    (RigidStabilizer.order_iso_on G α)
    AlgebraicCentralizerBasis.empty_not_mem'
  ).cast (by simp)) :=
by
  intro U U_in_basis
  simp
  rw [Filter.InBasis.map_mem_map_basis_of_basis_set _ RigidStabilizer_doubleMonotone F.in_basis U_in_basis]
  rfl

theorem IsRubinFilterOf.mem_inv {A : UltrafilterInBasis (RegularSupportBasis G α)}
  {B : UltrafilterInBasis (AlgebraicCentralizerBasis G)}
  (filter_of : IsRubinFilterOf A B) {U : Set G} (U_in_basis : U ∈ AlgebraicCentralizerBasis G):
  U ∈ B ↔ rigidStabilizer_inv U ∈ A :=
by
  rw [<-AlgebraicCentralizerBasis.eq_rist_image (α := α)] at U_in_basis
  let ⟨V, V_in_basis, V_eq⟩ := U_in_basis
  rw [<-V_eq, RigidStabilizer_leftInv V_in_basis]
  symm
  exact filter_of V V_in_basis

theorem IsRubinFilterOf.mem_inter_inv {A : UltrafilterInBasis (RegularSupportBasis G α)}
  {B : UltrafilterInBasis (AlgebraicCentralizerBasis G)}
  (filter_of : IsRubinFilterOf A B) (U : Set G):
  U ∈ B.filter.sets ∩ AlgebraicCentralizerBasis G ↔ rigidStabilizer_inv U ∈ A.filter.sets ∩ RegularSupportBasis G α :=
by
  constructor
  · intro ⟨U_in_filter, U_in_basis⟩
    constructor
    simp
    rw [<-filter_of.mem_inv U_in_basis]
    exact U_in_filter
    rw [<-rigidStabilizer_inv_in_basis]
    assumption
  · intro ⟨iU_in_filter, U_in_basis⟩
    rw [<-rigidStabilizer_inv_in_basis] at U_in_basis
    constructor
    · simp
      rw [filter_of.mem_inv U_in_basis]
      exact iU_in_filter
    · assumption

theorem IsRubinFilterOf.subsets_ss_orbit {A : UltrafilterInBasis (RegularSupportBasis G α)}
  {B : UltrafilterInBasis (AlgebraicCentralizerBasis G)}
  (filter_of : IsRubinFilterOf A B)
  {V : Set α} -- (V_in_basis : V ∈ RegularSupportBasis G α)
  {W : Set α} (W_in_basis : W ∈ RegularSupportBasis G α) :
  RSuppSubsets G W ⊆ RSuppOrbit A G•[V] ↔ AlgebraicSubsets (G•[W]) ⊆ AlgebraicOrbit B.filter G•[V] :=
by
  have dec_eq : DecidableEq G := Classical.typeDecidableEq _

  constructor
  · intro rsupp_ss
    unfold AlgebraicSubsets AlgebraicOrbit
    intro U ⟨U_in_basis, U_ss_GW⟩
    let U' := rigidStabilizer_inv (α := α) U
    have U'_in_basis : U' ∈ RegularSupportBasis G α := (rigidStabilizer_inv_in_basis U).mp U_in_basis
    have U'_ss_W : U' ⊆ W := by
      rw [subset_rigidStabilizer_iff_inv_subset U_in_basis W_in_basis] at U_ss_GW
      exact U_ss_GW
    let ⟨g, g_in_GV, ⟨W, W_in_A, gW_eq_U⟩⟩ := rsupp_ss ⟨U'_in_basis, U'_ss_W⟩
    use g
    constructor
    {
      simp
      exact g_in_GV
    }

    have W_in_basis : W ∈ RegularSupportBasis G α := by
      rw [smulImage_inv] at gW_eq_U
      rw [gW_eq_U]
      apply RegularSupportBasis.smulImage_in_basis
      assumption

    use G•[W]
    rw [filter_of.mem_inter_inv]
    rw [RigidStabilizer_leftInv (G := G) (α := α) W_in_basis]
    refine ⟨⟨W_in_A, W_in_basis⟩, ?W_eq_U⟩
    rw [rigidStabilizer_conj_image_eq, gW_eq_U]
    unfold_let
    exact RigidStabilizer_rightInv U_in_basis
  · intro algsupp_ss
    unfold RSuppSubsets RSuppOrbit
    simp
    intro U U_in_basis U_ss_W
    let U' := (G•[U] : Set G)
    have U'_in_basis : U' ∈ AlgebraicCentralizerBasis G :=
      AlgebraicCentralizerBasis.mem_of_regularSupportBasis U_in_basis
    have U'_ss_GW : U' ⊆ G•[W] := by
      rw [SetLike.coe_subset_coe]
      rw [<-rigidStabilizer_subset_iff]
      · assumption
      · exact RegularSupportBasis.regular U_in_basis
      · exact RegularSupportBasis.regular W_in_basis

    let ⟨g, g_in_GV, ⟨X, X_in_inter, X_eq⟩⟩ := algsupp_ss ⟨U'_in_basis, U'_ss_GW⟩
    have X_in_basis := X_in_inter.right
    rw [filter_of.mem_inter_inv] at X_in_inter

    simp at g_in_GV
    use g
    refine ⟨g_in_GV, ⟨rigidStabilizer_inv X, X_in_inter.left, ?giX_eq_U⟩⟩

    apply (And.right) at X_in_inter
    rw [rigidStabilizer_inv_smulImage X_in_basis, X_eq]
    unfold_let
    rw [RigidStabilizer_leftInv U_in_basis]

theorem IsRubinFilterOf.converges_iff {A : UltrafilterInBasis (RegularSupportBasis G α)}
  {B : UltrafilterInBasis (AlgebraicCentralizerBasis G)}
  (filter_of : IsRubinFilterOf A B)
  {V : Set α} (V_in_basis : V ∈ RegularSupportBasis G α)
  :
  (∃ p ∈ V, A ≤ nhds p) ↔
  AlgebraicConvergent B.filter G•[V] :=
by
  unfold AlgebraicConvergent
  constructor
  · rw [proposition_3_5' V_in_basis]
    intro ⟨W, W_in_basis, W_ss_V, subsets_ss_orbit⟩
    use G•[W]
    rw [<-filter_of.subsets_ss_orbit W_in_basis]
    refine ⟨?GW_in_basis, ?GW_ss_GV, subsets_ss_orbit⟩
    exact AlgebraicCentralizerBasis.mem_of_regularSupportBasis W_in_basis
    simp
    rwa [<-rigidStabilizer_subset_iff _ (RegularSupportBasis.regular W_in_basis) (RegularSupportBasis.regular V_in_basis)]
  · intro ⟨W, W_in_basis, W_ss_GV, subsets_ss_orbit⟩
    rw [<-AlgebraicCentralizerBasis.eq_rist_image (α := α)] at W_in_basis
    let ⟨W', W'_in_basis, W'_eq⟩ := W_in_basis
    simp only at W'_eq
    rw [proposition_3_5' V_in_basis]
    use W'
    rw [filter_of.subsets_ss_orbit W'_in_basis, W'_eq]
    refine ⟨W'_in_basis, ?W'_ss_V, subsets_ss_orbit⟩
    rw [<-W'_eq] at W_ss_GV
    simp at W_ss_GV
    rwa [<-rigidStabilizer_subset_iff _ (RegularSupportBasis.regular W'_in_basis) (RegularSupportBasis.regular V_in_basis)] at W_ss_GV

def RubinFilter.from (F : UltrafilterInBasis (RegularSupportBasis G α)) (F_converges : ∃ p : α, F ≤ nhds p) : RubinFilter G where
  filter := (F.map_basis
    (RegularSupportBasis.empty_not_mem G α)
    (RigidStabilizer.order_iso_on G α)
    AlgebraicCentralizerBasis.empty_not_mem'
  ).cast (by simp)

  converges := by
    let ⟨p, F_le_nhds⟩ := F_converges

    have ⟨W, W_in_basis, _, W_subsets_ss_GV_orbit⟩ := (proposition_3_5' (RegularSupportBasis.univ_mem G α) F).mp ⟨p, (Set.mem_univ p), F_le_nhds⟩

    refine ⟨
      G•[W],
      by apply AlgebraicCentralizerBasis.mem_of_regularSupportBasis W_in_basis,
      by simp,
      ?subsets_ss_orbit
    ⟩

    rw [<-Subgroup.coe_top, <-rigidStabilizer_univ (α := α) (G := G)]
    rwa [<-(RubinFilter.from_isRubinFilterOf' F).subsets_ss_orbit W_in_basis]


theorem RubinFilter.from_isRubinFilterOf (F : UltrafilterInBasis (RegularSupportBasis G α)) (F_converges : ∃ p : α, F ≤ nhds p):
  IsRubinFilterOf F (RubinFilter.from F F_converges).filter := RubinFilter.from_isRubinFilterOf' F

theorem RubinFilter.map_from_eq (F : UltrafilterInBasis (RegularSupportBasis G α)) (F_converges : ∃ p : α, F ≤ nhds p):
  (RubinFilter.from F F_converges).map α = F :=
by
  apply UltrafilterInBasis.eq_of_le
  apply UltrafilterInBasis.le_of_basis_sets
  intro S S_in_B S_in_F

  rw [(RubinFilter.from_isRubinFilterOf F F_converges) S S_in_B] at S_in_F
  rw [(RubinFilter.map_isRubinFilterOf (RubinFilter.from F F_converges) (α := α)) S S_in_B]

  exact S_in_F

section Convergence

variable (α : Type _)
variable [Nonempty α] [TopologicalSpace α] [T2Space α] [HasNoIsolatedPoints α] [LocallyCompactSpace α]
variable [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α] [LocallyDense G α]

theorem RubinFilter.map_converges (F : RubinFilter G):
  ∃ p : α, (F.map α).filter ≤ nhds p :=
by
  suffices ∃ p ∈ Set.univ, (F.map α).filter ≤ nhds p by
    let ⟨p, _, f_le_nhds⟩ := this
    exact ⟨p, f_le_nhds⟩

  rw [proposition_3_5' (RegularSupportBasis.univ_mem G α)]
  let ⟨V, V_in_basis, _, subsets_ss_orbit⟩ := F.converges
  simp only [Set.subset_univ, true_and, Subtype.exists, exists_prop]
  use rigidStabilizer_inv V
  refine ⟨(rigidStabilizer_inv_in_basis V).mp V_in_basis, ?subsets_ss_orbit⟩
  rw [(RubinFilter.map_isRubinFilterOf F (α := α)).subsets_ss_orbit
    ((rigidStabilizer_inv_in_basis V).mp V_in_basis)
  ]
  rw [RigidStabilizer_rightInv V_in_basis]
  simp
  exact subsets_ss_orbit

theorem RubinFilter.from_map_eq (F : RubinFilter G):
  RubinFilter.from (F.map α) (RubinFilter.map_converges α F) = F :=
by
  rw [mk.injEq]
  apply UltrafilterInBasis.eq_of_le
  apply UltrafilterInBasis.le_of_basis_sets
  intro S S_in_B S_in_F

  rw [(RubinFilter.from_isRubinFilterOf (F.map α) (RubinFilter.map_converges α F)).mem_inv S_in_B]
  rw [<-(RubinFilter.map_isRubinFilterOf F (α := α)).mem_inv S_in_B]
  exact S_in_F

noncomputable def RubinFilter.lim (F : RubinFilter G)
  : α := Exists.choose (RubinFilter.map_converges F (α := α))

theorem RubinFilter.le_nhds_lim (F : RubinFilter G) :
  F.map α ≤ nhds (F.lim α) := (RubinFilter.map_converges F (α := α)).choose_spec

theorem RubinFilter.le_nhds_eq_lim (F : RubinFilter G) (p : α) :
  F.map α ≤ nhds p → p = F.lim α :=
by
  intro F_le_p
  have F_le_lim := F.le_nhds_lim (α := α)
  by_contra p_ne_lim
  rw [<-ne_eq, <-disjoint_nhds_nhds] at p_ne_lim
  apply (map F α).ne_bot.ne
  exact Filter.empty_mem_iff_bot.mp (p_ne_lim F_le_p F_le_lim trivial)

lemma RubinFilter.lim_mem_iff (F : RubinFilter G) {T : Set α} (T_in_basis : T ∈ RegularSupportBasis G α) :
  F.lim α ∈ T ↔ ∃ V ∈ RegularSupportBasis G α, V ⊆ T ∧ RSuppSubsets G V ⊆ RSuppOrbit (F.map α) G•[T] :=
by
  rw [<-proposition_3_5' T_in_basis]

  constructor
  · intro lim_in_T
    use lim α F
    exact ⟨lim_in_T, le_nhds_lim α F⟩
  · intro ⟨p, p_in_T, le_nhds_p⟩
    exact (F.le_nhds_eq_lim α p le_nhds_p) ▸ p_in_T

lemma RubinFilter.exists_nhds_iff_lim_in_set (F : RubinFilter G) (T : Set α) :
  (∃ p ∈ T, F.map α ≤ nhds p) ↔ F.lim α ∈ T :=
by
  constructor
  · intro ⟨p, p_in_T, F_le_nhds⟩
    convert p_in_T
    exact (F.le_nhds_eq_lim α p F_le_nhds).symm
  · intro lim_in_T
    exact ⟨lim α F, lim_in_T, le_nhds_lim α F⟩

end Convergence

section Setoid

/--
Two rubin filters are equivalent if they share the same behavior in regards to which set their converging point `p` lies in.
--/
instance RubinFilterSetoid (G : Type _) [Group G] : Setoid (RubinFilter G) where
  r F F' := ∀ (U : Set G), U ∈ AlgebraicCentralizerBasis G →
    (AlgebraicConvergent F.filter U ↔ AlgebraicConvergent F'.filter U)
  iseqv := by
    constructor
    · intros
      simp
    · intro F F' h
      intro U U_rigid
      symm
      exact h U U_rigid
    · intro F₁ F₂ F₃
      intro h₁₂ h₂₃
      intro U U_rigid
      specialize h₁₂ U U_rigid
      specialize h₂₃ U U_rigid
      exact Iff.trans h₁₂ h₂₃

lemma RubinFilter.lim_mem_iff_of_eqv {F₁ F₂ : RubinFilter G} (F_equiv : F₁ ≈ F₂)
  {S : Set α} (S_in_basis : S ∈ RegularSupportBasis G α) :
  F₁.lim α ∈ S ↔ F₂.lim α ∈ S
:= by
  have F₁_rubinFilterOf := (RubinFilter.map_isRubinFilterOf F₁ (α := α))
  have F₂_rubinFilterOf := (RubinFilter.map_isRubinFilterOf F₂ (α := α))

  rw [F₁.lim_mem_iff α S_in_basis, <-proposition_3_5' S_in_basis]
  rw [F₁_rubinFilterOf.converges_iff S_in_basis]
  rw [F_equiv _ (AlgebraicCentralizerBasis.mem_of_regularSupportBasis S_in_basis)]
  rw [<-F₂_rubinFilterOf.converges_iff S_in_basis]
  rw [F₂.lim_mem_iff α S_in_basis, <-proposition_3_5' S_in_basis]

lemma RubinFilter.mem_nhds_lim_iff_of_eqv {F₁ F₂ : RubinFilter G} (F_equiv : F₁ ≈ F₂)
  (S : Set α) : S ∈ nhds (F₁.lim α) ↔ S ∈ nhds (F₂.lim α) :=
by
  suffices ∀ F₁ F₂ : RubinFilter G, F₁ ≈ F₂ → ∀ S : Set α, S ∈ nhds (F₁.lim α) → S ∈ nhds (F₂.lim α) by
    constructor
    apply this _ _ F_equiv
    apply this _ _ (Setoid.symm F_equiv)

  have basis := RegularSupportBasis.isBasis G α

  intro F₁ F₂ F_equiv S S_in_nhds_F₁
  rw [basis.mem_nhds_iff] at S_in_nhds_F₁
  let ⟨T, T_in_basis, lim₁_in_T, T_ss_S⟩ := S_in_nhds_F₁

  rw [basis.mem_nhds_iff]
  use T
  refine ⟨T_in_basis, ?lim₂_in_T, T_ss_S⟩

  rw [lim_mem_iff_of_eqv F_equiv T_in_basis] at lim₁_in_T
  exact lim₁_in_T

theorem RubinFilter.lim_eq_of_eqv {F₁ F₂ : RubinFilter G} (F_equiv : F₁ ≈ F₂) :
  F₁.lim α = F₂.lim α :=
by
  apply RubinFilter.le_nhds_eq_lim
  have nhds_lim_in_basis := nhds_in_basis (lim α F₁) (RegularSupportBasis.isBasis G α)

  apply UltrafilterInBasis.le_of_inf_neBot _ (RegularSupportBasis.closed_inter G α) nhds_lim_in_basis

  constructor
  intro eq_bot

  rw [Filter.inf_eq_bot_iff] at eq_bot
  let ⟨U, U_in_F₂, V, V_in_nhds, UV_empty⟩ := eq_bot

  rw [mem_nhds_lim_iff_of_eqv F_equiv] at V_in_nhds
  apply (F₂.map α).ne_bot.ne
  rw [<-inf_eq_left.mpr (F₂.le_nhds_lim α)]
  rw [Filter.inf_eq_bot_iff]
  exact ⟨U, U_in_F₂, V, V_in_nhds, UV_empty⟩

theorem RubinFilter.eqv_of_map_converges (F₁ F₂ : RubinFilter G) (p : α):
  F₁.map α ≤ nhds p → F₂.map α ≤ nhds p → F₁ ≈ F₂ :=
by
  intro F₁_le_nhds F₂_le_nhds
  intro S S_in_basis

  have F₁_rubinFilterOf := (RubinFilter.map_isRubinFilterOf F₁ (α := α))
  have F₂_rubinFilterOf := (RubinFilter.map_isRubinFilterOf F₂ (α := α))

  rw [<-AlgebraicCentralizerBasis.eq_rist_image (α := α)] at S_in_basis
  let ⟨S', S'_in_basis, S'_eq⟩ := S_in_basis
  simp only at S'_eq
  rw [<-S'_eq]

  rw [<-F₁_rubinFilterOf.converges_iff S'_in_basis]
  rw [<-F₂_rubinFilterOf.converges_iff S'_in_basis]

  rw [F₁.exists_nhds_iff_lim_in_set α S']
  rw [F₂.exists_nhds_iff_lim_in_set α S']
  rw [<-F₁.le_nhds_eq_lim _ _ F₁_le_nhds]
  rw [<-F₂.le_nhds_eq_lim _ _ F₂_le_nhds]


lemma RubinFilter.fromPoint_converges' (p : α) :
  ∃ q : α, (
  UltrafilterInBasis.of
    (RegularSupportBasis.closed_inter G α)
    (nhds_in_basis p (RegularSupportBasis.isBasis G α))
  ).filter ≤ nhds q :=
by
  use p
  apply UltrafilterInBasis.of_le

def RubinFilter.fromPoint (p : α) : RubinFilter G :=
  RubinFilter.from (
    UltrafilterInBasis.of
      (RegularSupportBasis.closed_inter G α)
      (nhds_in_basis p (RegularSupportBasis.isBasis G α))
    )
    (RubinFilter.fromPoint_converges' p)

@[simp]
theorem RubinFilter.fromPoint_lim (p : α) :
  (RubinFilter.fromPoint (G := G) p).lim α = p :=
by
  symm
  apply RubinFilter.le_nhds_eq_lim
  unfold fromPoint
  rw [RubinFilter.map_from_eq]
  apply UltrafilterInBasis.of_le

theorem RubinFilter.lim_fromPoint_eqv (F : RubinFilter G) :
  RubinFilter.fromPoint (F.lim α) ≈ F :=
by
  apply eqv_of_map_converges _ _ (F.lim α)
  · unfold fromPoint
    rw [RubinFilter.map_from_eq]
    apply UltrafilterInBasis.of_le
  · exact le_nhds_lim α F

def RubinFilterBasis (G : Type _) [Group G] : Set (Set (RubinFilter G)) :=
  (fun S : Set G => { F : RubinFilter G | AlgebraicConvergent F.filter S }) '' AlgebraicCentralizerBasis G

instance : TopologicalSpace (RubinFilter G) := TopologicalSpace.generateFrom (RubinFilterBasis G)

theorem RubinFilterBasis.mem_iff (S : Set (RubinFilter G)) :
  S ∈ RubinFilterBasis G ↔ ∃ B ∈ AlgebraicCentralizerBasis G, ∀ F : RubinFilter G, F ∈ S ↔ AlgebraicConvergent F.filter B :=
by
  unfold RubinFilterBasis
  simp
  conv => {
    lhs; congr; intro B; rhs
    rw [eq_comm, Set.ext_iff]
  }

def RubinSpace (G : Type _) [Group G] := Quotient (RubinFilterSetoid G)

def RubinSpace.fromPoint (p : α) : RubinSpace G :=
  ⟦RubinFilter.fromPoint p⟧

instance : Membership (RubinFilter G) (RubinSpace G) where
  mem := fun F Q => ⟦F⟧ = Q

theorem RubinSpace.mem_iff (F : RubinFilter G) (Q : RubinSpace G) :
  F ∈ Q ↔ ⟦F⟧ = Q := by rfl

theorem RubinSpace.fromPoint_converges (p : α) :
  ∀ F : RubinFilter G, F ∈ RubinSpace.fromPoint (G := G) p → F.lim α = p :=
by
  intro F
  unfold fromPoint
  rw [mem_iff, Quotient.eq]
  intro F_eqv_from
  convert RubinFilter.lim_eq_of_eqv F_eqv_from
  clear F_eqv_from
  simp

noncomputable def RubinSpace.lim (Q : RubinSpace G) : α :=
  Q.liftOn (RubinFilter.lim α) (fun _a _b eqv => RubinFilter.lim_eq_of_eqv eqv)

theorem RubinSpace.lim_fromPoint (p : α) :
  RubinSpace.lim (RubinSpace.fromPoint (G := G) p) = p :=
by
  unfold lim
  let ⟨Q, Q_eq⟩ := (RubinSpace.fromPoint (G := G) p).exists_rep
  rw [<-Q_eq]
  simp
  apply RubinSpace.fromPoint_converges p Q
  rwa [mem_iff]

theorem RubinSpace.fromPoint_lim (Q : RubinSpace G) :
  RubinSpace.fromPoint (Q.lim (α := α)) = Q :=
by
  let ⟨Q', Q'_eq⟩ := Q.exists_rep
  rw [<-Q'_eq, lim, fromPoint]
  simp
  rw [Quotient.eq]
  apply RubinFilter.lim_fromPoint_eqv

instance : TopologicalSpace (RubinSpace G) := by
  unfold RubinSpace
  infer_instance

theorem RubinSpace.lim_continuous : Continuous (RubinSpace.lim (G := G) (α := α)) := by
  sorry

theorem RubinSpace.fromPoint_continuous : Continuous (RubinSpace.fromPoint (G := G) (α := α)) := by
  sorry

/--
The canonical homeomorphism from a topological space that a rubin action acts on to
the rubin space.
--/
noncomputable def RubinSpace.homeomorph : Homeomorph (RubinSpace G) α where
  toFun := RubinSpace.lim
  invFun := RubinSpace.fromPoint

  left_inv := RubinSpace.fromPoint_lim
  right_inv := RubinSpace.lim_fromPoint

  continuous_toFun := RubinSpace.lim_continuous
  continuous_invFun := RubinSpace.fromPoint_continuous

instance : MulAction G (RubinSpace G) := sorry

end Setoid

-- theorem rubin' (hα : RubinAction G α) : EquivariantHomeomorph G α (RubinSpace G) where
--   toFun := fun x => ⟦⟧
--   invFun := fun S => sorry



end RubinFilter

/-
variable {β : Type _}
variable [TopologicalSpace β] [MulAction G β] [ContinuousConstSMul G β]

theorem rubin (hα : RubinAction G α) (hβ : RubinAction G β) : EquivariantHomeomorph G α β := by
  -- by composing rubin' hα
  sorry
-/

end Rubin

end Rubin
