import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Actions
import Mathlib.Topology.Basic
import Mathlib.Tactic.FinCases

import Rubin.RigidStabilizer
import Rubin.SmulImage
import Rubin.Topological
import Rubin.FaithfulAction

namespace Rubin

class LocallyMoving (G α : Type _) [Group G] [TopologicalSpace α] [MulAction G α] :=
  locally_moving: ∀ U : Set α, IsOpen U → Set.Nonempty U → RigidStabilizer G U ≠ ⊥
#align is_locally_moving Rubin.LocallyMoving

namespace LocallyMoving

theorem get_nontrivial_rist_elem {G α : Type _}
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

end LocallyMoving

def AlgebraicallyDisjoint {G : Type _} [Group G] (f g : G) :=
  ∀ h : G,
    ¬Commute f h →
      ∃ f₁ f₂ : G, Commute f₁ g ∧ Commute f₂ g ∧ Commute ⁅f₁, ⁅f₂, h⁆⁆ g ∧ ⁅f₁, ⁅f₂, h⁆⁆ ≠ 1
#align is_algebraically_disjoint Rubin.AlgebraicallyDisjoint

@[simp]
theorem orbit_bot (G : Type _) [Group G] [MulAction G α] (p : α) :
    MulAction.orbit (⊥ : Subgroup G) p = {p} :=
  by
  ext1
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨_, g_bot⟩, g_to_x⟩
    rw [← g_to_x, Set.mem_singleton_iff, Subgroup.mk_smul]
    exact (Subgroup.mem_bot.mp g_bot).symm ▸ one_smul _ _
  exact fun h => ⟨1, Eq.trans (one_smul _ p) (Set.mem_singleton_iff.mp h).symm⟩
#align orbit_bot Rubin.orbit_bot

variable {G α : Type _}
variable [Group G]
variable [TopologicalSpace α]
variable [ContinuousMulAction G α]
variable [FaithfulSMul G α]

instance dense_locally_moving [T2Space α]
  (H_nip : has_no_isolated_points α)
  (H_ld : LocallyDense G α) :
  LocallyMoving G α
where
  locally_moving := by
    intros U _ H_nonempty
    by_contra h_rs
    have ⟨elem, ⟨_, some_in_orbit⟩⟩ := H_ld.nonEmpty H_nonempty
    have H_nebot := has_no_isolated_points_neBot H_nip elem
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

-- Kind of a boring lemma but okay
lemma rewrite_Union (f : Fin 2 × Fin 2 → Set α) :
  (⋃(i : Fin 2 × Fin 2), f i) = (f (0,0) ∪ f (0,1)) ∪ (f (1,0) ∪ f (1,1)) :=
by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rewrite [forall_exists_index]
    intro i
    fin_cases i
      <;> simp only [Fin.zero_eta, Fin.mk_one]
      <;> intro h
      <;> simp only [h, true_or, or_true]
  · rintro ((h|h)|(h|h)) <;> exact ⟨_, h⟩

-- TODO: modify the proof to be less "let everything"-y, especially the first half
lemma proposition_1_1_1 [h_lm : LocallyMoving G α] [T2Space α] (f g : G) (supp_disjoint : Disjoint (Support α f) (Support α g)) : AlgebraicallyDisjoint f g := by
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
  have y_in_V := (rist_supported_in_set f₂_in_rist_V) (mem_support.mpr y_moved)
  let ⟨W, W_open, y_in_W, W_in_V, disjoint_img_W⟩ := disjoint_nbhd_in V_open y_in_V y_moved

  -- Let f₁ be a nontrivial element of RigidStabilizer G W
  let ⟨f₁, f₁_in_rist_W, f₁_ne_one⟩ := h_lm.get_nontrivial_rist_elem W_open (Set.nonempty_of_mem y_in_W)

  use f₁
  use f₂
  constructor <;> try constructor
  · apply disjoint_commute (α := α)
    apply Set.disjoint_of_subset_left _ supp_disjoint
    calc
      Support α f₁ ⊆ W := rist_supported_in_set f₁_in_rist_W
      W ⊆ V := W_in_V
      V ⊆ Support α f := V_in_support
  · apply disjoint_commute (α := α)
    apply Set.disjoint_of_subset_left _ supp_disjoint
    calc
      Support α f₂ ⊆ V := rist_supported_in_set f₂_in_rist_V
      V ⊆ Support α f := V_in_support

  -- We claim that [f₁, [f₂, h]] is a nontrivial elelement of Centralizer G g
  let k := ⁅f₂, h⁆
  have h₂ : ∀ z ∈ W, f₂ • z = k • z := by
    intro z z_in_W
    simp
    symm
    apply disjoint_support_comm f₂ h _ disjoint_img_V
    · exact W_in_V z_in_W
    · exact rist_supported_in_set f₂_in_rist_V

  constructor
  · -- then `k*f₁⁻¹*k⁻¹` is supported on k W = f₂ W,
    -- so [f₁,k] is supported on W ∪ f₂ W ⊆ V ⊆ support f, so commutes with g.
    apply disjoint_commute (α := α)
    apply Set.disjoint_of_subset_left _ supp_disjoint
    have supp_f₁_subset_W := (rist_supported_in_set f₁_in_rist_W)

    show Support α ⁅f₁, ⁅f₂, h⁆⁆ ⊆ Support α f
    calc
      Support α ⁅f₁, k⁆ = Support α ⁅k, f₁⁆ := by rw [<-commutatorElement_inv, support_inv]
      _ ⊆ Support α f₁ ∪ (k •'' Support α f₁) := support_comm α k f₁
      _ ⊆ W ∪ (k •'' Support α f₁) := Set.union_subset_union_left _ supp_f₁_subset_W
      _ ⊆ W ∪ (k •'' W) := by
        apply Set.union_subset_union_right
        exact (smulImage_subset k supp_f₁_subset_W)
      _ = W ∪ (f₂ •'' W) := by rw [<-smulImage_eq_of_smul_eq h₂]
      _ ⊆ V ∪ (f₂ •'' W) := Set.union_subset_union_left _ W_in_V
      _ ⊆ V ∪ V := by
        apply Set.union_subset_union_right
        apply smulImage_subset_in_support f₂ W V W_in_V
        exact rist_supported_in_set f₂_in_rist_V
      _ ⊆ V := by rw [Set.union_self]
      _ ⊆ Support α f := V_in_support

  · -- finally, [f₁,k] agrees with f₁ on W, so is not the identity.
    have h₄: ∀ z ∈ W, ⁅f₁, k⁆ • z = f₁ • z := by
      apply disjoint_support_comm f₁ k
      exact rist_supported_in_set f₁_in_rist_W
      rw [<-smulImage_eq_of_smul_eq h₂]
      exact disjoint_img_W
    let ⟨z, z_in_W, z_moved⟩ := faithful_rigid_stabilizer_moves_point f₁_in_rist_W f₁_ne_one

    by_contra h₅
    rw [<-h₄ z z_in_W] at z_moved
    have h₆ : ⁅f₁, ⁅f₂, h⁆⁆ • z = z := by rw [h₅, one_smul]
    exact z_moved h₆
#align proposition_1_1_1 Rubin.proposition_1_1_1

@[simp] lemma smulImage_mul {g h : G} {U : Set α} : g •'' (h •'' U) = (g*h) •'' U :=
  (mul_smulImage g h U)

#check isOpen_iInter_of_finite

lemma smul_inj_moves {ι : Type*} [Fintype ι] [T2Space α]
  {f : ι → G} {x : α} {i j : ι} (i_ne_j : i ≠ j)
  (f_smul_inj : Function.Injective (fun i : ι => (f i) • x)) :
  ((f j)⁻¹ * f i) • x ≠ x := by
    by_contra h
    apply i_ne_j
    apply f_smul_inj
    group_action
    group_action at h
    exact h

def smul_inj_nbhd {ι : Type*} [Fintype ι] [T2Space α]
  {f : ι → G} {x : α} {i j : ι} (i_ne_j : i ≠ j)
  (f_smul_inj : Function.Injective (fun i : ι => (f i) • x)) :
  Set α :=
  (disjoint_nbhd (smul_inj_moves i_ne_j f_smul_inj)).choose

lemma smul_inj_nbhd_open {ι : Type*} [Fintype ι] [T2Space α]
  {f : ι → G} {x : α} {i j : ι} (i_ne_j : i ≠ j)
  (f_smul_inj : Function.Injective (fun i : ι => (f i) • x)) :
  IsOpen (smul_inj_nbhd i_ne_j f_smul_inj) :=
by
  exact (disjoint_nbhd (smul_inj_moves i_ne_j f_smul_inj)).choose_spec.1

lemma smul_inj_nbhd_mem {ι : Type*} [Fintype ι] [T2Space α]
  {f : ι → G} {x : α} {i j : ι} (i_ne_j : i ≠ j)
  (f_smul_inj : Function.Injective (fun i : ι => (f i) • x)) :
  x ∈ (smul_inj_nbhd i_ne_j f_smul_inj) :=
by
  exact (disjoint_nbhd (smul_inj_moves i_ne_j f_smul_inj)).choose_spec.2.1

lemma smul_inj_nbhd_disjoint {ι : Type*} [Fintype ι] [T2Space α]
  {f : ι → G} {x : α} {i j : ι} (i_ne_j : i ≠ j)
  (f_smul_inj : Function.Injective (fun i : ι => (f i) • x)) :
  Disjoint
    (smul_inj_nbhd i_ne_j f_smul_inj)
    ((f j)⁻¹ * f i •'' (smul_inj_nbhd i_ne_j f_smul_inj)) :=
by
  exact (disjoint_nbhd (smul_inj_moves i_ne_j f_smul_inj)).choose_spec.2.2


lemma disjoint_nbhd_fin {ι : Type*} [Fintype ι] [T2Space α]
  {f : ι → G} {x : α} (f_smul_inj : Function.Injective (fun i : ι => (f i) • x)):
  ∃ U : Set α,
  IsOpen U ∧ x ∈ U ∧ (∀ (i j : ι), i ≠ j → Disjoint (f i •'' U) (f j •'' U)) :=
by
  let ι₂ := { p : ι × ι | p.1 ≠ p.2 }
  let U := ⋂(p : ι₂), smul_inj_nbhd p.prop f_smul_inj
  use U

  -- The notations provided afterwards tend to be quite ugly because we used `Exists.choose`,
  -- but the idea is that this all boils down to applying `Exists.choose_spec`, except in the disjointness case,
  -- where we transform `Disjoint (f i •'' U) (f j •'' U)` into `Disjoint U ((f i)⁻¹ * f j •'' U)`
  -- and transform both instances of `U` into `N`, the neighborhood of the chosen `(i, j) ∈ ι₂`
  repeat' constructor
  · apply isOpen_iInter_of_finite
    intro ⟨⟨i, j⟩, i_ne_j⟩
    apply smul_inj_nbhd_open
  · apply Set.mem_iInter.mpr
    intro ⟨⟨i, j⟩, i_ne_j⟩
    apply smul_inj_nbhd_mem
  · intro i j i_ne_j
    let N := smul_inj_nbhd i_ne_j f_smul_inj
    have U_subset_N : U ⊆ N := Set.iInter_subset
      (fun (⟨⟨i, j⟩, i_ne_j⟩ : ι₂) => (smul_inj_nbhd i_ne_j f_smul_inj))
      ⟨⟨i, j⟩, i_ne_j⟩

    rw [disjoint_comm, smulImage_disjoint_mul]

    apply Set.disjoint_of_subset U_subset_N
    · apply smulImage_subset
      exact U_subset_N
    · exact smul_inj_nbhd_disjoint i_ne_j f_smul_inj


-- lemma moves_inj {g : G} {x : α} {n : ℕ} (period_ge_n : ∀ (k : ℤ), 1 ≤ k → k < n → g ^ k • x ≠ x) : function.injective (λ (i : fin n), g ^ (i : ℤ) • x) := begin
--     intros i j same_img,
--     by_contra i_ne_j,
--     let same_img' := congr_arg ((•) (g ^ (-(j : ℤ)))) same_img,
--     simp only [inv_smul_smul] at same_img',
--     rw [← mul_smul,← mul_smul,← zpow_add,← zpow_add,add_comm] at same_img',
--     simp only [add_left_neg, zpow_zero, one_smul] at same_img',
--     let ij := |(i:ℤ) - (j:ℤ)|,
--     rw ← sub_eq_add_neg at same_img',
--     have xfixed : g^ij • x = x := begin
--       cases abs_cases ((i:ℤ) - (j:ℤ)),
--       { rw ← h.1 at same_img', exact same_img' },
--       { rw [smul_eq_iff_inv_smul_eq,← zpow_neg,← h.1] at same_img', exact same_img' }
--     end,
--     have ij_ge_1 : 1 ≤ ij := int.add_one_le_iff.mpr (abs_pos.mpr $ sub_ne_zero.mpr $ norm_num.nat_cast_ne i j ↑i ↑j rfl rfl (fin.vne_of_ne i_ne_j)),
--     let neg_le := int.sub_lt_sub_of_le_of_lt (nat.cast_nonneg i) (nat.cast_lt.mpr (fin.prop _)),
--     rw zero_sub at neg_le,
--     let le_pos := int.sub_lt_sub_of_lt_of_le (nat.cast_lt.mpr (fin.prop _)) (nat.cast_nonneg j),
--     rw sub_zero at le_pos,
--     have ij_lt_n : ij < n := abs_lt.mpr ⟨ neg_le, le_pos ⟩,
--     exact period_ge_n ij ij_ge_1 ij_lt_n xfixed,
-- end
-- lemma int_to_nat (k : ℤ) (k_pos : k ≥ 1) : k = k.nat_abs := begin
--   cases (int.nat_abs_eq k),
--   { exact h },
--   { have : -(k.nat_abs : ℤ) ≤ 0 := neg_nonpos.mpr (int.nat_abs k).cast_nonneg,
--     rw ← h at this, by_contra, linarith }
-- end
-- lemma moves_inj_N {g : G} {x : α} {n : ℕ} (period_ge_n' : ∀ (k : ℕ), 1 ≤ k → k < n → g ^ k • x ≠ x) : function.injective (λ (i : fin n), g ^ (i : ℕ) • x) := begin
--   have period_ge_n : ∀ (k : ℤ), 1 ≤ k → k < n → g ^ k • x ≠ x,
--   { intros k one_le_k k_lt_n,
--     have one_le_k_nat : 1 ≤ k.nat_abs := ((int.coe_nat_le_coe_nat_iff 1 k.nat_abs).1 ((int_to_nat k one_le_k) ▸ one_le_k)),
--     have k_nat_lt_n : k.nat_abs < n := ((int.coe_nat_lt_coe_nat_iff k.nat_abs n).1 ((int_to_nat k one_le_k) ▸ k_lt_n)),
--     have := period_ge_n' k.nat_abs one_le_k_nat k_nat_lt_n,
--     rw [(zpow_coe_nat g k.nat_abs).symm, (int_to_nat k one_le_k).symm] at this,
--     exact this },
--   have := moves_inj period_ge_n,
--   done
-- end
-- lemma moves_1234_of_moves_12 {g : G} {x : α} (xmoves : g^12 • x ≠ x) : function.injective (λi : fin 5, g^(i:ℤ) • x) := begin
--     apply moves_inj,
--     intros k k_ge_1 k_lt_5,
--     by_contra xfixed,
--     have k_div_12 : k * (12 / k) = 12 := begin
--       interval_cases using k_ge_1 k_lt_5; norm_num
--     end,
--     have veryfixed : g^12 • x = x := begin
--       let := smul_zpow_eq_of_smul_eq (12/k) xfixed,
--       rw [← zpow_mul,k_div_12] at this,
--       norm_cast at this
--     end,
--     exact xmoves veryfixed
-- end
-- lemma proposition_1_1_2 (f g : G) [t2_space α] : is_locally_moving G α → is_algebraically_disjoint f g → disjoint (support α f) (support α (g^12)) := begin
--   intros locally_moving alg_disjoint,
-- -- suppose to the contrary that the set U = supp(f) ∩ supp(g^12) is nonempty
--   by_contra not_disjoint,
--   let U := support α f ∩ support α (g^12),
--   have U_nonempty : U.nonempty := Set.not_disjoint_iff_nonempty_inter.mp not_disjoint,
-- -- since X is Hausdorff, we can find a nonempty open set V ⊆ U such that f(V) is disjoint from V and the sets {g^i(V): i=0..4} are pairwise disjoint
--   let x := U_nonempty.some,
--   have five_points : function.injective (λi : fin 5, g^(i:ℤ) • x) := moves_1234_of_moves_12 (mem_support.mp $ (Set.inter_subset_right _ _) U_nonempty.some_mem),
--   rcases disjoint_nbhd_in (is_open.inter (support_open f) (support_open $ g^12)) U_nonempty.some_mem ((Set.inter_subset_left _ _) U_nonempty.some_mem) with ⟨V₀,open_V₀,x_in_V₀,V₀_in_support,disjoint_img_V₀⟩,
--   rcases disjoint_nbhd_fin five_points with ⟨V₁,open_V₁,x_in_V₁,disjoint_img_V₁⟩,
--   simp only at disjoint_img_V₁,
--   let V := V₀ ∩ V₁,
-- -- let h be a nontrivial element of rigid_stabilizer G V, and note that [f,h]≠1 since f(V) is disjoint from V
--   let ristV_ne_bot := locally_moving V (is_open.inter open_V₀ open_V₁) (Set.nonempty_of_mem ⟨x_in_V₀,x_in_V₁⟩),
--   rcases (or_iff_right ristV_ne_bot).mp (Subgroup.bot_or_exists_ne_one _) with ⟨h,h_in_ristV,h_ne_one⟩,
--   have comm_non_trivial : ¬commute f h := begin
--     by_contra comm_trivial,
--     rcases faithful_rist_moves_point h_in_ristV h_ne_one with ⟨z,z_in_V,z_moved⟩,
--     let act_comm := disjoint_support_comm h f (rist_supported_in_set h_in_ristV) (Set.disjoint_of_subset (Set.inter_subset_left V₀ V₁) (smul''_subset f (Set.inter_subset_left V₀ V₁)) disjoint_img_V₀) z z_in_V,
--     rw [commutator_element_eq_one_iff_commute.mpr comm_trivial.symm,one_smul] at act_comm,
--     exact z_moved act_comm.symm,
--   end,
-- -- since g is algebraically disjoint from f, there exist f₁,f₂ ∈ C_G(g) so that the commutator h' = [f1,[f2,h]] is a nontrivial element of C_G(g)
--   rcases alg_disjoint h comm_non_trivial with ⟨f₁,f₂,f₁_commutes,f₂_commutes,h'_commutes,h'_non_trivial⟩,
--   let h' := ⁅f₁,⁅f₂,h⁆⁆,
-- -- now observe that supp([f₂, h]) ⊆ V ∪ f₂(V), and by the same reasoning supp(h')⊆V∪f₁(V)∪f₂(V)∪f₁f₂(V)
--   have support_f₂h : support α ⁅f₂,h⁆ ⊆ V ∪ (f₂ •'' V) := (support_comm α f₂ h).trans (Set.union_subset_union (rist_supported_in_set h_in_ristV) $ smul''_subset f₂ $ rist_supported_in_set h_in_ristV),
--   have support_h' : support α h' ⊆ ⋃(i : fin 2 × fin 2), (f₁^i.1.val*f₂^i.2.val) •'' V := begin
--     let this := (support_comm α f₁ ⁅f₂,h⁆).trans (Set.union_subset_union support_f₂h (smul''_subset f₁ support_f₂h)),
--     rw [smul''_union,← one_smul'' V,← mul_smul'',← mul_smul'',← mul_smul'',mul_one,mul_one] at this,
--     let rw_u := rewrite_Union (λi : fin 2 × fin 2, (f₁^i.1.val*f₂^i.2.val) •'' V),
--     simp only [fin.val_eq_coe, fin.val_zero', pow_zero, mul_one, fin.val_one, pow_one, one_mul] at rw_u,
--     exact rw_u.symm ▸ this,
--   end,
-- -- since h' is nontrivial, it has at least one point p in its support
--   cases faithful_moves_point' α h'_non_trivial with p p_moves,
-- -- since g commutes with h', all five of the points {gi(p):i=0..4} lie in supp(h')
--   have gi_in_support : ∀i : fin 5, g^i.val • p ∈ support α h' := begin
--     intro i,
--     rw mem_support,
--     by_contra p_fixed,
--     rw [← mul_smul,(h'_commutes.pow_right i.val).eq,mul_smul,smul_left_cancel_iff] at p_fixed,
--     exact p_moves p_fixed,
--   end,
-- -- by the pigeonhole principle, one of the four sets V, f₁(V), f₂(V), f₁f₂(V) must contain two of these points, say g^i(p),g^j(p) ∈ k(V) for some 0 ≤ i < j ≤ 4 and k ∈ {1,f₁,f₂,f₁f₂}
--   let pigeonhole : fintype.card (fin 5) > fintype.card (fin 2 × fin 2) := dec_trivial,
--   let choice := λi : fin 5, (Set.mem_Union.mp $ support_h' $ gi_in_support i).some,
--   rcases finset.exists_ne_map_eq_of_card_lt_of_maps_to pigeonhole (λ(i : fin 5) _, finset.mem_univ (choice i)) with ⟨i,_,j,_,i_ne_j,same_choice⟩,
--   clear h_1_w h_1_h_h_w pigeonhole,
--   let k := f₁^(choice i).1.val*f₂^(choice i).2.val,
--   have same_k : f₁^(choice j).1.val*f₂^(choice j).2.val = k := by { simp only at same_choice,
-- rw ← same_choice },
--   have g_i : g^i.val • p ∈ k •'' V := (Set.mem_Union.mp $ support_h' $ gi_in_support i).some_spec,
--   have g_j : g^j.val • p ∈ k •'' V := same_k ▸ (Set.mem_Union.mp $ support_h' $ gi_in_support j).some_spec,
-- -- but since g^(j−i)(V) is disjoint from V and k commutes with g, we know that g^(j−i)k(V) is disjoint from k(V), a contradiction since g^i(p) and g^j(p) both lie in k(V).
--   have g_disjoint : disjoint ((g^i.val)⁻¹ •'' V) ((g^j.val)⁻¹ •'' V) := begin
--     let := (disjoint_smul'' (g^(-(i.val+j.val : ℤ))) (disjoint_img_V₁ i j i_ne_j)).symm,
--     rw [← mul_smul'',← mul_smul'',← zpow_add,← zpow_add] at this,
--     simp only [fin.val_eq_coe, neg_add_rev, coe_coe, neg_add_cancel_right, zpow_neg, zpow_coe_nat, neg_add_cancel_comm] at this,
--     from Set.disjoint_of_subset (smul''_subset _ (Set.inter_subset_right V₀ V₁)) (smul''_subset _ (Set.inter_subset_right V₀ V₁)) this
--   end,
--   have k_commutes : commute k g := commute.mul_left (f₁_commutes.pow_left (choice i).1.val) (f₂_commutes.pow_left (choice i).2.val),
--   have g_k_disjoint : disjoint ((g^i.val)⁻¹ •'' (k •'' V)) ((g^j.val)⁻¹ •'' (k •'' V)) := begin
--     let this := disjoint_smul'' k g_disjoint,
--     rw [← mul_smul'',← mul_smul'',← inv_pow g i.val,← inv_pow g j.val,
--         ← (k_commutes.symm.inv_left.pow_left i.val).eq,
--         ← (k_commutes.symm.inv_left.pow_left j.val).eq,
--        mul_smul'',inv_pow g i.val,mul_smul'' (g⁻¹^j.val) k V,inv_pow g j.val] at this,
--     from this
--   end,
--   exact Set.disjoint_left.mp g_k_disjoint (mem_inv_smul''.mpr g_i) (mem_inv_smul''.mpr g_j)
-- end
-- lemma remark_1_2 (f g : G) : is_algebraically_disjoint f g → commute f g := begin
--   intro alg_disjoint,
--   by_contra non_commute,
--   rcases alg_disjoint g non_commute with ⟨_,_,_,b,_,d⟩,
--   rw [commutator_element_eq_one_iff_commute.mpr b,commutator_element_one_right] at d,
--   tauto
-- end
-- section remark_1_3
-- def G := equiv.perm (fin 2)
-- def σ := equiv.swap (0 : fin 2) (1 : fin 2)
-- example : is_algebraically_disjoint σ σ := begin
--   intro h,
--   fin_cases h,
--   intro hyp1,
--   exfalso,
--   swap, intro hyp2, exfalso,
-- -- is commute decidable? cc,
-- sorry -- dec_trivial
-- sorry -- second sorry needed
-- end
-- end remark_1_3

end Rubin
