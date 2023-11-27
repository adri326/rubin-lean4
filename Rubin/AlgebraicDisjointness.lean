import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Actions
import Mathlib.GroupTheory.Commutator
import Mathlib.Topology.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

import Rubin.RigidStabilizer
import Rubin.SmulImage
import Rubin.Topological
import Rubin.FaithfulAction
import Rubin.Period

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

structure AlgebraicallyDisjointElem {G : Type _} [Group G] (f g h : G) :=
  non_commute: ¬Commute f h
  fst : G
  snd : G
  fst_commute : Commute fst g
  snd_commute : Commute snd g
  comm_elem_commute : Commute ⁅fst, ⁅snd, h⁆⁆ g
  comm_elem_nontrivial : ⁅fst, ⁅snd, h⁆⁆ ≠ 1

namespace AlgebraicallyDisjointElem

def comm_elem {G : Type _} [Group G] {f g h : G} (disj_elem : AlgebraicallyDisjointElem f g h) : G :=
  ⁅disj_elem.fst, ⁅disj_elem.snd, h⁆⁆

@[simp]
theorem comm_elem_eq {G : Type _} [Group G] {f g h : G} (disj_elem : AlgebraicallyDisjointElem f g h) :
  disj_elem.comm_elem = ⁅disj_elem.fst, ⁅disj_elem.snd, h⁆⁆ :=
by
  unfold comm_elem
  simp

end AlgebraicallyDisjointElem

/--
A pair (f, g) is said to be "algebraically disjoint" if it can produce an instance of
[`AlgebraicallyDisjointElem`] for any element `h ∈ G` such that `f` and `h` don't commute.

In other words, `g` is algebraically disjoint from `f` if `∀ h ∈ G`, with `⁅f, h⁆ ≠ 1`,
there exists a pair `f₁, f₂ ∈ Centralizer(g, G)`,
so that `⁅f₁, ⁅f₂, h⁆⁆` is a nontrivial element of `Centralizer(g, G)`.

Here the definition of `k ∈ Centralizer(g, G)` is directly unrolled as `Commute k g`.

This is a slightly stronger proposition that plain disjointness, a
-/
def AlgebraicallyDisjoint {G : Type _} [Group G] (f g : G) :=
  ∀ (h : G), ¬Commute f h → AlgebraicallyDisjointElem f g h

theorem AlgebraicallyDisjoint_mk {G : Type _} [Group G] {f g : G}
  (mk_thm : ∀ h : G, ¬Commute f h →
    ∃ f₁ f₂ : G, Commute f₁ g ∧ Commute f₂ g ∧ Commute ⁅f₁, ⁅f₂, h⁆⁆ g ∧ ⁅f₁, ⁅f₂, h⁆⁆ ≠ 1
  ) : AlgebraicallyDisjoint f g :=
fun (h : G) (nc : ¬Commute f h) => {
  non_commute := nc,
  fst := (mk_thm h nc).choose
  snd := (mk_thm h nc).choose_spec.choose
  fst_commute := (mk_thm h nc).choose_spec.choose_spec.left
  snd_commute := (mk_thm h nc).choose_spec.choose_spec.right.left
  comm_elem_commute := (mk_thm h nc).choose_spec.choose_spec.right.right.left
  comm_elem_nontrivial := by
    exact (mk_thm h nc).choose_spec.choose_spec.right.right.right
}

-- This is an idea of having a Prop version of AlgebraicallyDisjoint, but it sounds painful to work with
def IsAlgebraicallyDisjoint {G : Type _} [Group G] (f g : G): Prop :=
  ∀ (h : G), ¬Commute f h → ∃ (f₁ f₂ : G), ∃ (elem : AlgebraicallyDisjointElem f g h), elem.fst = f₁ ∧ elem.snd = f₂

namespace IsAlgebraicallyDisjoint

variable {G : Type _} [Group G]
variable {f g: G}

noncomputable def elim
  (is_alg_disj: IsAlgebraicallyDisjoint f g) :
  AlgebraicallyDisjoint f g :=
fun h nc => (is_alg_disj h nc).choose_spec.choose_spec.choose

def mk (alg_disj : AlgebraicallyDisjoint f g) : IsAlgebraicallyDisjoint f g :=
fun h nc =>
  let elem := alg_disj h nc
  ⟨
    elem.fst,
    elem.snd,
    elem,
    rfl,
    rfl
  ⟩

noncomputable instance coeFnAlgebraicallyDisjoint : CoeFun
  (IsAlgebraicallyDisjoint f g)
  (fun _ => AlgebraicallyDisjoint f g) where
  coe := elim

instance coeAlgebraicallyDisjoint : Coe (AlgebraicallyDisjoint f g) (IsAlgebraicallyDisjoint f g) where
  coe := mk

end IsAlgebraicallyDisjoint

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

-- TODO: move to Rubin.lean
-- TODO: modify the proof to be less "let everything"-y, especially the first half
-- TODO: use the new class thingy to write a cleaner proof?
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
        exact (smulImage_subset k supp_f₁_subset_W)
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

@[simp] lemma smulImage_mul {g h : G} {U : Set α} : g •'' (h •'' U) = (g*h) •'' U :=
  (mul_smulImage g h U)

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

lemma moves_inj {g : G} {x : α} {n : ℕ} (period_ge_n : ∀ (k : ℤ), 1 ≤ k → k < n → g^k • x ≠ x) :
  Function.Injective (fun (i : Fin n) => g^(i : ℤ) • x) :=
by
  intro a b same_img
  by_contra a_ne_b

  let abs_diff := |(a : ℤ) - (b : ℤ)|

  apply period_ge_n abs_diff _ _ _
  {
    show 1 ≤ abs_diff
    unfold_let
    rw [<-zero_add 1, Int.add_one_le_iff]
    apply abs_pos.mpr
    apply sub_ne_zero.mpr
    simp
    apply Fin.vne_of_ne
    apply a_ne_b
  }
  {
    show abs_diff < (n : ℤ)
    apply abs_lt.mpr
    constructor
    · rw [<-zero_sub]
      apply Int.sub_lt_sub_of_le_of_lt <;> simp
    · rw [<-sub_zero (n : ℤ)]
      apply Int.sub_lt_sub_of_lt_of_le <;> simp
  }
  {
    show g^abs_diff • x = x

    simp at same_img
    group_action at same_img
    rw [neg_add_eq_sub] at same_img

    cases abs_cases ((a : ℤ) - (b : ℤ)) with
    | inl h =>
      unfold_let
      rw [h.1]
      exact same_img
    | inr h =>
      unfold_let
      rw [h.1]
      rw [smul_eq_iff_eq_inv_smul]
      group_action
      symm
      exact same_img
  }

-- Note: this can be strengthened to `k ≥ 0`
lemma natAbs_eq_of_pos' (k : ℤ) (k_ge_one : k ≥ 1) : k = k.natAbs := by
  cases Int.natAbs_eq k with
  | inl _ => assumption
  | inr h =>
    exfalso
    have k_lt_one : k < 1 := by
      calc
        k ≤ 0 := by
          rw [h]
          apply nonpos_of_neg_nonneg
          rw [neg_neg]
          apply Int.ofNat_nonneg
        _ < 1 := by norm_num
    exact ((lt_iff_not_ge _ _).mp k_lt_one) k_ge_one

lemma period_ge_n_cast {g : G} {x : α} {n : ℕ} :
  (∀ (k : ℕ), 1 ≤ k → k < n → g ^ k • x ≠ x) →
  (∀ (k : ℤ), 1 ≤ k → k < n → g ^ k • x ≠ x) :=
by
  intro period_ge_n'
  intro k one_le_k k_lt_n

  have one_le_abs_k : 1 ≤ k.natAbs := by
    rw [<-Nat.cast_le (α := ℤ)]
    norm_num
    calc
      1 ≤ k := one_le_k
      _ ≤ |k| := le_abs_self k
  have abs_k_lt_n : k.natAbs < n := by
    rw [<-Nat.cast_lt (α := ℤ)]
    norm_num
    calc
      |k| = k := abs_of_pos one_le_k
      _ < n := k_lt_n
  have res := period_ge_n' k.natAbs one_le_abs_k abs_k_lt_n

  rw [<-zpow_ofNat, Int.coe_natAbs, abs_of_pos _] at res
  exact res
  exact one_le_k

instance {g : G} {x : α} {n : ℕ} :
  Coe
    (∀ (k : ℕ), 1 ≤ k → k < n → g ^ k • x ≠ x)
    (∀ (k : ℤ), 1 ≤ k → k < n → g ^ k • x ≠ x)
where
  coe := period_ge_n_cast

-- TODO: remove the unneeded `n` parameter
theorem smul_injective_within_period {g : G} {p : α} {n : ℕ}
  (period_eq_n : Period.period p g = n) :
  Function.Injective (fun (i : Fin n) => g ^ (i : ℕ) • p) :=
by
  have zpow_fix : (fun (i : Fin n) => g ^ (i : ℕ) • p) = (fun (i : Fin n) => g ^ (i : ℤ) • p) := by
    ext x
    simp
  rw [zpow_fix]
  apply moves_inj
  intro k one_le_k k_lt_n

  apply Period.moves_within_period'
  exact one_le_k
  rw [period_eq_n]
  exact k_lt_n
#align moves_inj_period Rubin.smul_injective_within_period

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
    · apply smulImage_subset
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
        apply smulImage_subset
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
        apply smulImage_subset f₁
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
    repeat rw [mul_smulImage]
    repeat rw [<-inv_pow]
    repeat rw [k_commutes.symm.inv_left.pow_left]
    repeat rw [<-mul_smulImage k]
    repeat rw [inv_pow]
    exact disjoint_smulImage k g_disjoint

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

end Rubin
