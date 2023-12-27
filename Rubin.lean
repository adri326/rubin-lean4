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

end Ultrafilter

variable {G α : Type _}
variable [Group G]

variable [TopologicalSpace α] [MulAction G α] [ContinuousConstSMul G α]

def IsRigidSubgroup (S : Set G) :=
  S ≠ {1} ∧ ∃ T : Finset G, S = ⨅ (f ∈ T), AlgebraicCentralizer f

def IsRigidSubgroup.toSubgroup {S : Set G} (S_rigid : IsRigidSubgroup S) : Subgroup G where
  carrier := S
  mul_mem' := by
    let ⟨_, T, S_eq⟩ := S_rigid
    simp only [S_eq, SetLike.mem_coe]
    apply Subgroup.mul_mem
  one_mem' := by
    let ⟨_, T, S_eq⟩ := S_rigid
    simp only [S_eq, SetLike.mem_coe]
    apply Subgroup.one_mem
  inv_mem' := by
    let ⟨_, T, S_eq⟩ := S_rigid
    simp only [S_eq, SetLike.mem_coe]
    apply Subgroup.inv_mem

@[simp]
theorem IsRigidSubgroup.mem_subgroup {S : Set G} (S_rigid : IsRigidSubgroup S) (g : G):
  g ∈ S_rigid.toSubgroup ↔ g ∈ S := by rfl

theorem IsRigidSubgroup.toSubgroup_neBot {S : Set G} (S_rigid : IsRigidSubgroup S) :
  S_rigid.toSubgroup ≠ ⊥ :=
by
  intro eq_bot
  rw [Subgroup.eq_bot_iff_forall] at eq_bot
  simp only [mem_subgroup] at eq_bot
  apply S_rigid.left
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · let ⟨S', S'_eq⟩ := S_rigid.right
    rw [S'_eq, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · assumption

lemma Subgroup.coe_eq (S T : Subgroup G) :
  (S : Set G) = (T : Set G) ↔ S = T :=
by
  constructor
  · intro h
    ext x
    repeat rw [<-Subgroup.mem_carrier]
    have h₁ : ∀ S : Subgroup G, (S : Set G) = S.carrier := by intro h; rfl
    repeat rw [h₁] at h
    rw [h]
  · intro h
    rw [h]

def IsRigidSubgroup.algebraicCentralizerBasis {S : Set G} (S_rigid : IsRigidSubgroup S) : AlgebraicCentralizerBasis G := ⟨
  S_rigid.toSubgroup,
  by
    rw [AlgebraicCentralizerBasis.mem_iff' _ (IsRigidSubgroup.toSubgroup_neBot S_rigid)]
    let ⟨S', S'_eq⟩ := S_rigid.right
    use S'
    unfold AlgebraicCentralizerInter₀
    rw [<-Subgroup.coe_eq, <-S'_eq]
    rfl
⟩

theorem IsRigidSubgroup.algebraicCentralizerBasis_val {S : Set G} (S_rigid : IsRigidSubgroup S) :
  S_rigid.algebraicCentralizerBasis.val = S_rigid.toSubgroup := rfl

section toRegularSupportBasis

variable (α : Type _)
variable [TopologicalSpace α] [MulAction G α] [ContinuousConstSMul G α]
variable [FaithfulSMul G α] [T2Space α] [LocallyMoving G α]

theorem IsRigidSubgroup.has_regularSupportBasis {S : Set G} (S_rigid : IsRigidSubgroup S) :
  ∃ (U : RegularSupportBasis G α), G•[U.val] = S :=
by
  let ⟨S_ne_bot, ⟨T, S_eq⟩⟩ := S_rigid
  rw [S_eq]
  simp only [Subgroup.coe_eq]
  rw [S_eq, <-Subgroup.coe_bot, ne_eq, Subgroup.coe_eq, <-ne_eq] at S_ne_bot



  -- let T' : Finset (HomeoGroup α) := Finset.map (HomeoGroup.fromContinuous_embedding α) T

  let T' := RegularSupport.FiniteInter α T

  have T'_nonempty : Set.Nonempty T' := by
    simp only [RegularSupport.FiniteInter, proposition_2_1 (G := G) (α := α)] at S_ne_bot
    rw [ne_eq, <-rigidStabilizer_iInter_regularSupport', <-ne_eq] at S_ne_bot
    exact rigidStabilizer_neBot S_ne_bot

  have T'_in_basis : T' ∈ RegularSupportBasis G α := by
    constructor
    assumption
    use T

  use ⟨T', T'_in_basis⟩
  simp [RegularSupport.FiniteInter]
  rw [rigidStabilizer_iInter_regularSupport']
  simp only [<-proposition_2_1]

noncomputable def IsRigidSubgroup.toRegularSupportBasis {S : Set G} (S_rigid : IsRigidSubgroup S) :
  RegularSupportBasis G α
:= Exists.choose (IsRigidSubgroup.has_regularSupportBasis α S_rigid)

theorem IsRigidSubgroup.toRegularSupportBasis_eq {S : Set G} (S_rigid : IsRigidSubgroup S):
  G•[(S_rigid.toRegularSupportBasis α).val] = S :=
by
  exact Exists.choose_spec (IsRigidSubgroup.has_regularSupportBasis α S_rigid)

theorem IsRigidSubgroup.toRegularSupportBasis_regular {S : Set G} (S_rigid : IsRigidSubgroup S):
  Regular (S_rigid.toRegularSupportBasis α).val :=
by
  apply RegularSupportBasis.regular (G := G)
  exact (toRegularSupportBasis α S_rigid).prop

theorem IsRigidSubgroup.toRegularSupportBasis_nonempty {S : Set G} (S_rigid : IsRigidSubgroup S):
  Set.Nonempty (S_rigid.toRegularSupportBasis α).val :=
by
  exact (Subtype.prop (S_rigid.toRegularSupportBasis α)).left

theorem IsRigidSubgroup.toRegularSupportBasis_mono {S T : Set G} (S_rigid : IsRigidSubgroup S)
  (T_rigid : IsRigidSubgroup T) :
  S ⊆ T ↔ (S_rigid.toRegularSupportBasis α : Set α) ⊆ T_rigid.toRegularSupportBasis α :=
by
  rw [rigidStabilizer_subset_iff G (toRegularSupportBasis_regular _ S_rigid) (toRegularSupportBasis_regular _ T_rigid)]
  constructor
  · intro S_ss_T
    rw [<-IsRigidSubgroup.toRegularSupportBasis_eq (α := α) S_rigid] at S_ss_T
    rw [<-IsRigidSubgroup.toRegularSupportBasis_eq (α := α) T_rigid] at S_ss_T
    simp at S_ss_T
    exact S_ss_T
  · intro Sr_ss_Tr
    -- TODO: clean that up
    have Sr_ss_Tr' : (G•[(toRegularSupportBasis α S_rigid).val] : Set G)
      ⊆ G•[(toRegularSupportBasis α T_rigid).val] :=
    by
      simp
      assumption
    rw [IsRigidSubgroup.toRegularSupportBasis_eq (α := α) S_rigid] at Sr_ss_Tr'
    rw [IsRigidSubgroup.toRegularSupportBasis_eq (α := α) T_rigid] at Sr_ss_Tr'
    assumption

theorem IsRigidSubgroup.toRegularSupportBasis_mono' {S T : Set G} (S_rigid : IsRigidSubgroup S)
  (T_rigid : IsRigidSubgroup T) :
  S ⊆ T ↔ (S_rigid.toRegularSupportBasis α : Set α) ⊆ (T_rigid.toRegularSupportBasis α : Set α) :=
by
  rw [<-IsRigidSubgroup.toRegularSupportBasis_mono]

@[simp]
theorem IsRigidSubgroup.toRegularSupportBasis_rigidStabilizer {S : Set G} (S_rigid : IsRigidSubgroup S) :
  G•[(S_rigid.toRegularSupportBasis α : Set α)] = S :=
by
  sorry
  -- TODO: prove that `G•[S_rigid.toRegularSupportBasis] = S`

@[simp]
theorem IsRigidSubgroup.toRegularSupportBasis_rigidStabilizer' {S : Set G} (S_rigid : IsRigidSubgroup S) (g : G):
  g ∈ G•[(S_rigid.toRegularSupportBasis α : Set α)] ↔ g ∈ S :=
by
  rw [<-SetLike.mem_coe, IsRigidSubgroup.toRegularSupportBasis_rigidStabilizer]

end toRegularSupportBasis

theorem IsRigidSubgroup.conj {U : Set G} (U_rigid : IsRigidSubgroup U) (g : G) : IsRigidSubgroup ((fun h => g * h * g⁻¹) '' U) := by
  have conj_bijective : ∀ g : G, Function.Bijective (fun h => g * h * g⁻¹) := by
    intro g
    constructor
    · intro x y; simp
    · intro x
      use g⁻¹ * x * g
      group

  constructor
  · intro H
    apply U_rigid.left
    have h₁ : (fun h => g * h * g⁻¹) '' {1} = {1} := by simp
    rw [<-h₁] at H
    apply (Set.image_eq_image (conj_bijective g).left).mp H
  · let ⟨S, S_eq⟩ := U_rigid.right
    have dec_eq : DecidableEq G := Classical.typeDecidableEq G
    use Finset.image (fun h => g * h * g⁻¹) S
    rw [S_eq]
    simp
    simp only [Set.image_iInter (conj_bijective _), AlgebraicCentralizer.conj]

def AlgebraicSubsets (V : Set G) : Set (Subgroup G) :=
  {W ∈ AlgebraicCentralizerBasis G | W ≤ V}

def AlgebraicOrbit (F : Filter G) (U : Set G) : Set (Subgroup G) :=
  { (W_rigid.conj g).toSubgroup | (g ∈ U) (W ∈ F) (W_rigid : IsRigidSubgroup W) }

structure RubinFilter (G : Type _) [Group G] where
  -- Issue: It's *really hard* to generate ultrafilters on G that satisfy the other conditions of this rubinfilter
  filter : Ultrafilter G

  -- Note: the following condition cannot be met by ultrafilters in G,
  -- and doesn't seem to be necessary
  -- rigid_basis : ∀ S ∈ filter, ∃ T ⊆ S, IsRigidSubgroup T

  -- Equivalent formulation of convergence
  converges : ∀ U ∈ filter,
    IsRigidSubgroup U →
    ∃ V : Set G, IsRigidSubgroup V ∧ V ⊆ U ∧ AlgebraicSubsets V ⊆ AlgebraicOrbit filter U

  -- Only really used to prove that ∀ S : Rigid, T : Rigid, S T ∈ F, S ∩ T : Rigid
  ne_bot : {1} ∉ filter

instance : Coe (RubinFilter G) (Ultrafilter G) where
  coe := RubinFilter.filter

section Equivalence
open Topology

variable {G : Type _} [Group G]
variable (α : Type _)
variable [TopologicalSpace α] [T2Space α] [MulAction G α] [ContinuousConstSMul G α]
variable [FaithfulSMul G α] [LocallyDense G α] [LocallyCompactSpace α] [HasNoIsolatedPoints α]

-- TODO: either see whether we actually need this step, or change these names to something memorable
-- This is an attempt to convert a RubinFilter G back to an Ultrafilter α
def RubinFilter.to_action_filter (F : RubinFilter G) : Filter α :=
  ⨅ (S : { S : Set G // S ∈ F.filter ∧ IsRigidSubgroup S }), (Filter.principal (S.prop.right.toRegularSupportBasis α))


instance RubinFilter.to_action_filter_neBot {F : RubinFilter G} [Nonempty α] : Filter.NeBot (F.to_action_filter α) :=
  by
    unfold to_action_filter
    rw [Filter.iInf_neBot_iff_of_directed]
    · intro ⟨S, S_in_F, S_rigid⟩
      simp
      apply IsRigidSubgroup.toRegularSupportBasis_nonempty
    · intro ⟨S, S_in_F, S_rigid⟩ ⟨T, T_in_F, T_rigid⟩
      simp
      use S ∩ T
      have ST_in_F : (S ∩ T) ∈ F.filter := by
        -- rw [<-Ultrafilter.mem_coe]
        apply Filter.inter_mem <;> assumption
      have ST_subgroup : IsRigidSubgroup (S ∩ T) := by
        constructor
        swap
        · let ⟨S_seed, S_eq⟩ := S_rigid.right
          let ⟨T_seed, T_eq⟩ := T_rigid.right
          have dec_eq : DecidableEq G := Classical.typeDecidableEq G
          use S_seed ∪ T_seed
          rw [Finset.iInf_union, S_eq, T_eq]
          simp
        · -- TODO: check if we can't prove this without using F.ne_bot;
          -- we might be able to use convergence
          intro ST_eq_bot
          apply F.ne_bot
          rw [<-ST_eq_bot]
          exact ST_in_F
          -- sorry
      use ⟨ST_in_F, ST_subgroup⟩

      repeat rw [<-IsRigidSubgroup.toRegularSupportBasis_mono' (α := α)]
      constructor
      exact Set.inter_subset_left S T
      exact Set.inter_subset_right S T

-- theorem RubinFilter.to_action_filter_converges' (F : RubinFilter G) :
--   ∀ U : Set α, U ∈ RegularSupportBasis G α → U ∈ F.to_action_filter →
--   ∃ V ⊆ F.to_action_filter, V ⊆ U ∧

theorem RubinFilter.to_action_filter_mem {F : RubinFilter G} {U : Set G} (U_rigid : IsRigidSubgroup U) :
  U ∈ F.filter ↔ (U_rigid.toRegularSupportBasis α : Set α) ∈ F.to_action_filter α :=
by
  sorry

theorem RubinFilter.to_action_filter_mem' {F : RubinFilter G} {U : Set α} (U_in_basis : U ∈ RegularSupportBasis G α) :
  U ∈ F.to_action_filter α ↔ (G•[U] : Set G) ∈ F.filter :=
by
  -- trickier to prove but should be possible
  sorry

theorem RubinFilter.to_action_filter_clusterPt [Nonempty α] (F : RubinFilter G) :
  ∃ p : α, ClusterPt p (F.to_action_filter α) :=
by
  have univ_in_basis : Set.univ ∈ RegularSupportBasis G α := by
    rw [RegularSupportBasis.mem_iff]
    simp
    use {}
    simp [RegularSupport.FiniteInter]

  have univ_rigid : IsRigidSubgroup (G := G) Set.univ := by
    constructor
    simp [Set.eq_singleton_iff_unique_mem]
    exact LocallyMoving.nontrivial_elem G α
    use {}
    simp

  suffices ∃ p ∈ Set.univ, ClusterPt p (F.to_action_filter α) by
    let ⟨p, _, clusterPt⟩ := this
    use p

  apply proposition_3_5_2 (G := G) (α := α)
  simp
  let ⟨S, S_rigid, _, S_subsets_ss_orbit⟩ := F.converges _ Filter.univ_mem univ_rigid

  use S_rigid.toRegularSupportBasis α
  constructor
  simp

  unfold RSuppSubsets RSuppOrbit
  simp
  intro T T_in_basis T_ss_S


  let T' := G•[T]
  have T_regular : Regular T := sorry -- easy
  have T'_rigid : IsRigidSubgroup (T' : Set G) := sorry -- provable
  have T'_ss_S : (T' : Set G) ⊆ S := sorry -- using one of our lovely theorems

  have T'_in_subsets : T' ∈ AlgebraicSubsets S := by
    unfold AlgebraicSubsets
    simp
    constructor
    sorry -- prove that rigid subgroups are in the algebraic centralizer basis
    exact T'_ss_S

  let ⟨g, _, W, W_in_F, W_rigid, W_conj⟩ := S_subsets_ss_orbit T'_in_subsets

  use g
  constructor
  sorry -- TODO: G•[univ] = top

  let W' := W_rigid.toRegularSupportBasis α
  have W'_regular : Regular (W' : Set α) := by
    apply RegularSupportBasis.regular (G := G)
    simp
  use W'

  constructor
  rw [<-RubinFilter.to_action_filter_mem]
  assumption

  rw [<-rigidStabilizer_eq_iff (α := α) (G := G) ((smulImage_regular _ _).mp W'_regular) T_regular]

  ext i
  rw [rigidStabilizer_smulImage]
  unfold_let at W_conj
  rw [<-W_conj]
  simp
  constructor
  · intro
    use g⁻¹ * i * g
    constructor
    assumption
    group
  · intro ⟨j, j_in_W, gjg_eq_i⟩
    rw [<-gjg_eq_i]
    group
    assumption

-- theorem RubinFilter.to_action_filter_le_nhds [Nonempty α] (F : RubinFilter G) :
--   ∃ p : α, (F.to_action_filter α) ≤ 𝓝 p :=
-- by
--   let ⟨p, p_clusterPt⟩ := to_action_filter_clusterPt α F
--   use p
--   intro S S_in_nhds
--   rw [(RegularSupportBasis.isBasis G α).mem_nhds_iff] at S_in_nhds
--   let ⟨T, T_in_basis, p_in_T, T_ss_S⟩ := S_in_nhds

--   suffices T ∈ F.to_action_filter α by
--     apply Filter.sets_of_superset (F.to_action_filter α) this T_ss_S

--   rw [RubinFilter.to_action_filter_mem' _ T_in_basis]

--   intro S p_in_S S_open
--   sorry

lemma RubinFilter.mem_to_action_filter (F : RubinFilter G) {U : Set G} (U_rigid : IsRigidSubgroup U) :
  U ∈ F.filter ↔ (U_rigid.toRegularSupportBasis α : Set α) ∈ F.to_action_filter α :=
by
  unfold to_action_filter
  constructor
  · intro U_in_filter
    apply Filter.mem_iInf_of_mem ⟨U, U_in_filter, U_rigid⟩
    intro x
    simp
  · sorry -- pain

noncomputable def RubinFilter.to_action_ultrafilter (F : RubinFilter G) [Nonempty α]: Ultrafilter α :=
  Ultrafilter.of (F.to_action_filter α)

theorem RubinFilter.to_action_ultrafilter_converges (F : RubinFilter G) [Nonempty α] [LocallyDense G α] [HasNoIsolatedPoints α] [LocallyCompactSpace α] {U : Set G}
  (U_in_F : U ∈ F.filter) (U_rigid : IsRigidSubgroup U):
  ∃ p ∈ (U_rigid.toRegularSupportBasis α).val, ClusterPt p (F.to_action_ultrafilter α) :=
by
  rw [proposition_3_5 (G := G)]
  swap
  {
    apply Subtype.prop (IsRigidSubgroup.toRegularSupportBasis α U_rigid)
  }

  let ⟨V, V_rigid, V_ss_U, algsubs_ss_algorb⟩ := F.converges U U_in_F U_rigid
  -- let V' := V_rigid.toSubgroup
  -- TODO: subst V' to simplify the proof?

  use V_rigid.toRegularSupportBasis α
  constructor
  {
    rw [<-IsRigidSubgroup.toRegularSupportBasis_mono]
    exact V_ss_U
  }

  unfold RSuppSubsets RSuppOrbit
  simp
  intro S S_in_basis S_ss_V
  -- let ⟨S', S'_eq⟩ := S_in_basis.right

  have S_regular : Regular S := RegularSupportBasis.regular S_in_basis

  have S_nonempty : Set.Nonempty S := S_in_basis.left

  have GS_ss_V : G•[S] ≤ V := by
    rw [<-V_rigid.toRegularSupportBasis_eq (α := α)]
    simp only [Set.le_eq_subset, SetLike.coe_subset_coe]
    rw [<-rigidStabilizer_subset_iff G (α := α) S_regular (IsRigidSubgroup.toRegularSupportBasis_regular _ V_rigid)]
    assumption

  -- TODO: show that G•[S] ∈ AlgebraicSubsets V
  have GS_in_algsubs_V : G•[S] ∈ AlgebraicSubsets V := by
    unfold AlgebraicSubsets
    simp
    constructor
    · rw [rigidStabilizerBasis_eq_algebraicCentralizerBasis (α := α)]
      let ⟨S', S'_eq⟩ := S_in_basis.right
      rw [RigidStabilizerBasis.mem_iff' _ (LocallyMoving.locally_moving _ S_regular.isOpen S_nonempty)]
      use S'
      rw [RigidStabilizerInter₀, S'_eq, RegularSupport.FiniteInter, rigidStabilizer_iInter_regularSupport']
    · exact GS_ss_V

  let ⟨g, g_in_U, W, W_in_F, W_rigid, Wconj_eq_GS⟩ := algsubs_ss_algorb GS_in_algsubs_V

  use g
  constructor
  {

    assumption
  }

  use W_rigid.toRegularSupportBasis α
  constructor
  · apply Ultrafilter.of_le
    rw [<-RubinFilter.mem_to_action_filter]
    assumption
  · rw [<-rigidStabilizer_eq_iff G]
    swap
    {
      rw [<-smulImage_regular (G := G)]
      apply IsRigidSubgroup.toRegularSupportBasis_regular
    }
    swap
    exact S_regular

    ext i
    rw [rigidStabilizer_smulImage, <-Wconj_eq_GS]
    simp
    constructor
    · intro gig_in_W
      use g⁻¹ * i * g
      constructor; exact gig_in_W
      group
    · intro ⟨j, j_in_W, gjg_eq_i⟩
      rw [<-gjg_eq_i]
      group
      assumption

-- Idea: prove that for every rubinfilter, there exists an associated ultrafilter on α that converges

instance RubinFilterSetoid (G : Type _) [Group G] : Setoid (RubinFilter G) where
  r F F' := ∀ (U : Set G), IsRigidSubgroup U →
    ((∃ V : Set G, V ≤ U ∧ AlgebraicSubsets V ⊆ AlgebraicOrbit F.filter U)
    ↔ (∃ V' : Set G, V' ≤ U ∧ AlgebraicSubsets V' ⊆ AlgebraicOrbit F'.filter U))
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

def RubinFilterBasis : Set (Set (RubinFilter G)) :=
  (fun S : Subgroup G => { F : RubinFilter G | (S : Set G) ∈ F.filter }) '' AlgebraicCentralizerBasis G

instance : TopologicalSpace (RubinFilter G) := TopologicalSpace.generateFrom RubinFilterBasis

def RubinSpace (G : Type _) [Group G] := Quotient (RubinFilterSetoid G)

instance : TopologicalSpace (RubinSpace G) := by
  unfold RubinSpace
  infer_instance

instance : MulAction G (RubinSpace G) := sorry

end Equivalence

section Convert
open Topology

variable (G α : Type _)
variable [Group G]
variable [TopologicalSpace α] [Nonempty α] [T2Space α] [HasNoIsolatedPoints α] [LocallyCompactSpace α]
variable [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α] [LocallyMoving G α] [LocallyDense G α]

instance RubinFilter.fromElement_neBot (x : α) : Filter.NeBot (⨅ (S ∈ 𝓝 x), Filter.principal (G•[S] : Set G)) := by sorry

noncomputable def RubinFilter.fromElement (x : α) : RubinFilter G where
  filter := @Ultrafilter.of _ (⨅ (S ∈ 𝓝 x), Filter.principal (G•[S] : Set G)) (RubinFilter.fromElement_neBot G α x)
  converges := by
    sorry
  ne_bot := by
    sorry -- this will be fun to try and prove

-- Alternate idea: don't try to compute the associated ultrafilter, and only define a predicate?
theorem RubinFilter.converging_element (F : RubinFilter G) :
  ∃ p : α, ClusterPt p (F.to_action_ultrafilter α) :=
by
  have univ_in_F : Set.univ ∈ F.filter := Filter.univ_mem
  have univ_in_basis : IsRigidSubgroup (G := G) Set.univ := by
    constructor
    sorry -- TODO: prove that Set.univ ≠ {1}, from locallydense
    use {}
    simp

  let ⟨p, p_in_basis, clusterPt_p⟩ := RubinFilter.to_action_ultrafilter_converges α F univ_in_F univ_in_basis

  use p

noncomputable def RubinFilter.toElement (F : RubinFilter G) : α :=
  (F.converging_element G α).choose

theorem RubinFilter.toElement_equiv (F F' : RubinFilter G) (equiv : F ≈ F'):
  F.toElement G α = F'.toElement G α :=
by

  sorry

theorem rubin' (hα : RubinAction G α) : EquivariantHomeomorph G α (RubinSpace G) where
  toFun := fun x => ⟦RubinFilter.fromElement (G := G) α x⟧
  invFun := fun f => f.liftOn (RubinFilter.toElement G α) (RubinFilter.toElement_equiv G α)
  continuous_toFun := by
    simp
    constructor
    intro S S_open
    rw [<-isOpen_coinduced]
    -- Note the sneaky different IsOpen's
    -- TODO: apply topologicalbasis on both isopen
    sorry
  continuous_invFun := by
    simp
    sorry
  left_inv := by
    intro x
    simp
    sorry
  right_inv := by
    intro F
    nth_rw 2 [<-Quotient.out_eq F]
    rw [Quotient.eq]
    simp
    sorry
  equivariant := by
    simp
    sorry

end Convert



-- Topology can be generated from the disconnectedness of the filters

variable {β : Type _}
variable [TopologicalSpace β] [MulAction G β] [ContinuousConstSMul G β]

#check IsOpen.smul


theorem rubin (hα : RubinAction G α) (hβ : RubinAction G β) : EquivariantHomeomorph G α β := by
  -- by composing rubin' hα
  sorry

end Rubin

end Rubin
