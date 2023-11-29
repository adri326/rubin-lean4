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

This is a slightly weaker proposition than plain disjointness,
but it is easier to derive from the hypothesis of Rubin's theorem.
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

/--
This definition simply wraps `AlgebraicallyDisjoint` as a `Prop`.
It is equivalent to it, although since `AlgebraicallyDisjoint` isn't a `Prop`,
an `↔` (iff) statement joining the two cannot be written.

You should consider using it when proving `↔`/`∧` kinds of theorems, or when tools like `cases` are needed,
as the base `AlgebraicallyDisjoint` isn't a `Prop` and won't work with those.

The two `Coe` and `CoeFn` instances provided around this type make it essentially transparent —
you can use an instance of `AlgebraicallyDisjoint` in place of a `IsAlgebraicallyDisjoint` and vice-versa.
You might need to add the odd `↑` (coe) operator to make Lean happy.
--/
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
  [H_nip : HasNoIsolatedPoints α]
  (H_ld : LocallyDense G α) :
  LocallyMoving G α
where
  locally_moving := by
    intros U _ H_nonempty
    by_contra h_rs
    have ⟨elem, ⟨_, some_in_orbit⟩⟩ := H_ld.nonEmpty H_nonempty
    -- Note: This is automatic now :)
    -- have H_nebot := has_no_isolated_points_neBot elem
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

end Rubin
