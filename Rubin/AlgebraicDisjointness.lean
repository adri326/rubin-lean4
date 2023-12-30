import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Actions
import Mathlib.GroupTheory.Commutator
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

import Rubin.RigidStabilizer
import Rubin.SmulImage
import Rubin.Topology
import Rubin.FaithfulAction
import Rubin.Period
import Rubin.LocallyDense

namespace Rubin

variable {G : Type _} [Group G]

theorem Commute.conj (f g h : G) : Commute (f * g * f⁻¹) h ↔ Commute g (f⁻¹ * h * f) := by
  suffices ∀ (f g h : G), Commute (f * g * f⁻¹) h → Commute g (f⁻¹ * h * f) by
    constructor
    · apply this
    · intro cg
      symm
      nth_rw 1 [<-inv_inv f]
      apply this
      symm
      rw [inv_inv]
      exact cg

  intro f g h fgf_h_comm
  unfold Commute SemiconjBy at *
  rw [<-mul_assoc, <-mul_assoc]
  rw [<-mul_assoc, <-mul_assoc] at fgf_h_comm
  have gfh_eq : g * f⁻¹ * h = f⁻¹ * h * f * g * f⁻¹ := by
    repeat rw [mul_assoc f⁻¹]
    rw [<-fgf_h_comm]
    group
  rw [gfh_eq]
  group

theorem Commute.conj' (f g h : G) : Commute (f⁻¹ * g * f) h ↔ Commute g (f * h * f⁻¹) := by
  nth_rw 2 [<-inv_inv f]
  nth_rw 3 [<-inv_inv f]
  apply Commute.conj


structure AlgebraicallyDisjointElem (f g h : G) :=
  non_commute: ¬Commute f h
  fst : G
  snd : G
  fst_commute : Commute fst g
  snd_commute : Commute snd g
  comm_elem_commute : Commute ⁅fst, ⁅snd, h⁆⁆ g
  comm_elem_nontrivial : ⁅fst, ⁅snd, h⁆⁆ ≠ 1

namespace AlgebraicallyDisjointElem

def comm_elem {f g h : G} (disj_elem : AlgebraicallyDisjointElem f g h) : G :=
  ⁅disj_elem.fst, ⁅disj_elem.snd, h⁆⁆

@[simp]
theorem comm_elem_eq {f g h : G} (disj_elem : AlgebraicallyDisjointElem f g h) :
  disj_elem.comm_elem = ⁅disj_elem.fst, ⁅disj_elem.snd, h⁆⁆ :=
by
  unfold comm_elem
  simp

lemma comm_elem_conj (f g h i : G) :
  ⁅i * f * i⁻¹, ⁅i * g * i⁻¹, i * h * i⁻¹⁆⁆ = i * ⁅f, ⁅g, h⁆⁆ * i⁻¹ := by group

theorem conj {f g h : G} (disj_elem : AlgebraicallyDisjointElem f g h) (i : G): AlgebraicallyDisjointElem (i * f * i⁻¹) (i * g * i⁻¹) (i * h * i⁻¹) where
  non_commute := by
    rw [Commute.conj]
    group
    exact disj_elem.non_commute
  fst := i * disj_elem.fst * i⁻¹
  snd := i * disj_elem.snd * i⁻¹
  fst_commute := by
    rw [Commute.conj]
    group
    exact disj_elem.fst_commute
  snd_commute := by
    rw [Commute.conj]
    group
    exact disj_elem.snd_commute
  comm_elem_nontrivial := by
    intro eq_one
    apply disj_elem.comm_elem_nontrivial
    rw [comm_elem_conj, <-mul_right_inv i] at eq_one
    apply mul_right_cancel at eq_one
    nth_rw 2 [<-mul_one i] at eq_one
    apply mul_left_cancel at eq_one
    exact eq_one
  comm_elem_commute := by
    rw [comm_elem_conj, Commute.conj]
    rw [(by group : i⁻¹ * (i * g * i⁻¹) * i = g)]
    exact disj_elem.comm_elem_commute

end AlgebraicallyDisjointElem

-- Also known as `η_G(f)`.

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

theorem conj (is_alg_disj : IsAlgebraicallyDisjoint f g) (h : G) :
  IsAlgebraicallyDisjoint (h * f * h⁻¹) (h * g * h⁻¹) :=
by
  apply elim at is_alg_disj
  apply mk
  intro i nc
  rw [Commute.conj] at nc
  rw [(by group : i = h * (h⁻¹ * i * h) * h⁻¹)]
  exact (is_alg_disj (h⁻¹ * i * h) nc).conj h

end IsAlgebraicallyDisjoint

-- TODO: find a better home for these lemmas
variable {G α : Type _}
variable [Group G]
variable [TopologicalSpace α]
variable [MulAction G α]
variable [ContinuousConstSMul G α]
variable [FaithfulSMul G α]

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
    group at h
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

  repeat' apply And.intro
  · apply isOpen_iInter_of_finite
    intro ⟨⟨i, j⟩, i_ne_j⟩
    apply smul_inj_nbhd_open
  · apply Set.mem_iInter.mpr
    intro ⟨⟨i, j⟩, i_ne_j⟩
    apply smul_inj_nbhd_mem
  · intro i j i_ne_j

    -- We transform `Disjoint (f i •'' U) (f j •'' U)` into `Disjoint N ((f i)⁻¹ * f j •'' N)`
    let N := smul_inj_nbhd i_ne_j f_smul_inj
    have U_subset_N : U ⊆ N := Set.iInter_subset
      (fun (⟨⟨i, j⟩, i_ne_j⟩ : ι₂) => (smul_inj_nbhd i_ne_j f_smul_inj))
      ⟨⟨i, j⟩, i_ne_j⟩

    rw [disjoint_comm, smulImage_disjoint_mul]

    apply Set.disjoint_of_subset U_subset_N
    · apply smulImage_mono
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
      group
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
  simp only [<-zpow_coe_nat]
  apply moves_inj
  intro k one_le_k k_lt_n

  apply Period.moves_within_period'
  exact one_le_k
  rw [period_eq_n]
  exact k_lt_n
#align moves_inj_period Rubin.smul_injective_within_period


/-
The algebraic centralizer (and its associated basis) allow for a purely group-theoretic construction of the
`RegularSupport` sets.
They are defined as the centralizers of the subgroups `{g^12 | g ∈ G ∧ AlgebraicallyDisjoint f g}`
-/
section AlgebraicCentralizer

variable {G : Type _}
variable [Group G]

-- TODO: prove this is a subgroup?
-- This is referred to as `ξ_G^12(f)`
def AlgebraicSubgroup (f : G) : Set G :=
  (fun g : G => g^12) '' { g : G | IsAlgebraicallyDisjoint f g }

def AlgebraicCentralizer (f : G) : Subgroup G :=
  Subgroup.centralizer (AlgebraicSubgroup f)

theorem AlgebraicSubgroup.conj (f g : G) :
  (fun h => g * h * g⁻¹) '' AlgebraicSubgroup f = AlgebraicSubgroup (g * f * g⁻¹) :=
by
  unfold AlgebraicSubgroup
  rw [Set.image_image]
  have gxg12_eq : ∀ x : G, g * x^12 * g⁻¹ = (g * x * g⁻¹)^12 := by
    simp
  simp only [gxg12_eq]
  ext x
  simp
  constructor
  · intro ⟨y, y_disj, x_eq⟩
    use g * y * g⁻¹
    rw [<-gxg12_eq]
    exact ⟨y_disj.conj g, x_eq⟩
  · intro ⟨y, y_disj, x_eq⟩
    use g⁻¹ * y * g
    constructor
    · convert y_disj.conj g⁻¹ using 1
      all_goals group
    · nth_rw 3 [<-inv_inv g]
      simp only [conj_pow]
      rw [x_eq]
      group

@[simp]
theorem AlgebraicCentralizer.conj (f g : G) :
  (fun h => g * h * g⁻¹) '' AlgebraicCentralizer f = AlgebraicCentralizer (g * f * g⁻¹) :=
by
  unfold AlgebraicCentralizer

  ext x
  simp [Subgroup.mem_centralizer_iff]

  constructor
  · intro ⟨y, ⟨x_comm, x_eq⟩⟩
    intro h h_in_alg
    rw [<-AlgebraicSubgroup.conj] at h_in_alg
    simp at h_in_alg
    let ⟨i, i_in_alg, gig_eq_h⟩ := h_in_alg
    specialize x_comm i i_in_alg
    rw [<-gig_eq_h, <-x_eq]
    group
    rw [mul_assoc _ i, x_comm, <-mul_assoc]
  · intro x_comm
    use g⁻¹ * x * g
    group
    simp
    intro h h_in_alg
    simp [<-AlgebraicSubgroup.conj] at x_comm
    specialize x_comm h h_in_alg
    have h₁ : g⁻¹ * x * g * h = g⁻¹ * (g * h * g⁻¹ * x) * g := by
      rw [x_comm]
      group
    rw [h₁]
    group

/--
Finite intersections of [`AlgebraicCentralizer`].
--/
def AlgebraicCentralizerInter (S : Finset G) : Subgroup G :=
  ⨅ (g ∈ S), AlgebraicCentralizer g

def AlgebraicCentralizerBasis (G : Type _) [Group G] : Set (Set G) :=
  { S : Set G | S ≠ {1} ∧ ∃ seed : Finset G,
    S = AlgebraicCentralizerInter seed
  }

theorem AlgebraicCentralizerBasis.mem_iff (S : Set G) :
  S ∈ AlgebraicCentralizerBasis G ↔
    S ≠ {1} ∧ ∃ seed : Finset G, S = AlgebraicCentralizerInter seed
:= by rfl

theorem AlgebraicCentralizerBasis.subgroup_mem_iff (S : Subgroup G) :
  (S : Set G) ∈ AlgebraicCentralizerBasis G ↔
    S ≠ ⊥ ∧ ∃ seed : Finset G, S = AlgebraicCentralizerInter seed :=
by
  rw [mem_iff, <-Subgroup.coe_bot, ne_eq, SetLike.coe_set_eq]
  simp

theorem AlgebraicCentralizerBasis.empty_not_mem : ∅ ∉ AlgebraicCentralizerBasis G := by
  simp [AlgebraicCentralizerBasis]
  intro _ _
  rw [<-ne_eq]
  symm
  rw [<-Set.nonempty_iff_ne_empty]
  exact Subgroup.coe_nonempty _

theorem AlgebraicCentralizerBasis.to_subgroup {S : Set G} (S_in_basis : S ∈ AlgebraicCentralizerBasis G):
  ∃ S' : Subgroup G, S = S' :=
by
  rw [mem_iff] at S_in_basis
  let ⟨_, ⟨seed, S_eq⟩⟩ := S_in_basis
  use AlgebraicCentralizerInter seed

theorem Set.image_equiv_eq {α β : Type _} (S : Set α) (T : Set β) (f : α ≃ β) :
  f '' S = T ↔ S = f.symm '' T :=
by
  constructor
  · intro fS_eq_T
    ext x
    rw [<-fS_eq_T]
    simp
  · intro S_eq_fT
    ext x
    rw [S_eq_fT]
    simp

theorem AlgebraicCentralizerBasis.conj_mem {S : Set G} (S_in_basis : S ∈ AlgebraicCentralizerBasis G)
  (h : G) : (fun g => h * g * h⁻¹) '' S ∈ AlgebraicCentralizerBasis G :=
by
  let ⟨S', S_eq⟩ := to_subgroup S_in_basis
  rw [S_eq]
  rw [S_eq, subgroup_mem_iff] at S_in_basis
  rw [mem_iff]

  have conj_eq : (fun g => h * g * h⁻¹) = (MulAut.conj h).toEquiv := by
    ext x
    simp

  constructor
  · rw [conj_eq]
    rw [ne_eq, Set.image_equiv_eq]
    simp
    rw [<-Subgroup.coe_bot, SetLike.coe_set_eq]
    exact S_in_basis.left
  · let ⟨seed, S'_eq⟩ := S_in_basis.right
    have dec_eq : DecidableEq G := Classical.typeDecidableEq _
    use Finset.image (fun g => h * g * h⁻¹) seed
    rw [S'_eq]
    unfold AlgebraicCentralizerInter
    ext g
    rw [conj_eq]
    rw [Set.mem_image_equiv]
    simp
    conv => {
      rhs
      intro
      intro
      rw [<-SetLike.mem_coe, <-AlgebraicCentralizer.conj, conj_eq, Set.mem_image_equiv]
    }


end AlgebraicCentralizer

end Rubin
