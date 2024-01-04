import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Exponent

import Rubin.Tactic

namespace Rubin.Period

variable {G a : Type _}
variable [Group G]
variable [MulAction G α]

-- TODO: move to Rubin.Period
noncomputable def period (p : α) (g : G) : ℕ :=
  sInf {n : ℕ | n > 0 ∧ g ^ n • p = p}
#align period Rubin.Period.period

theorem period_le_fix {p : α} {g : G} {m : ℕ} (m_pos : m > 0)
    (gmp_eq_p : g ^ m • p = p) : 0 < Rubin.Period.period p g ∧ Rubin.Period.period p g ≤ m :=
  by
  constructor
  · by_contra h'
    have period_zero : Rubin.Period.period p g = 0 := by linarith
    rcases Nat.sInf_eq_zero.1 period_zero with ⟨cont, _⟩ | h
    · linarith
    · exact Set.eq_empty_iff_forall_not_mem.mp h ↑m ⟨m_pos, gmp_eq_p⟩
  exact Nat.sInf_le ⟨m_pos, gmp_eq_p⟩
#align period_le_fix Rubin.Period.period_le_fix

theorem notfix_le_period {p : α} {g : G} {n : ℕ}
    (period_pos : Rubin.Period.period p g > 0) (pmoves : ∀ i : ℕ, 0 < i → i < n → g ^ i • p ≠ p) :
    n ≤ Rubin.Period.period p g := by
  by_contra period_le
  exact
    (pmoves (Rubin.Period.period p g) period_pos (not_le.mp period_le))
      (Nat.sInf_mem (Nat.nonempty_of_pos_sInf period_pos)).2
#align notfix_le_period Rubin.Period.notfix_le_period

theorem notfix_le_period' {p : α} {g : G} {n : ℕ}
    (period_pos : 0 < Rubin.Period.period p g)
    (pmoves : ∀ i : Fin n, 0 < (i : ℕ) → g ^ (i : ℕ) • p ≠ p) : n ≤ Rubin.Period.period p g :=
  Rubin.Period.notfix_le_period period_pos fun (i : ℕ) (i_pos : 0 < i) (i_lt_n : i < n) =>
    pmoves (⟨i, i_lt_n⟩ : Fin n) i_pos
#align notfix_le_period' Rubin.Period.notfix_le_period'

theorem period_neutral_eq_one (p : α) : Rubin.Period.period p (1 : G) = 1 :=
  by
  have : 0 < Rubin.Period.period p (1 : G) ∧ Rubin.Period.period p (1 : G) ≤ 1 :=
    Rubin.Period.period_le_fix (by norm_num : 1 > 0)
      (by group_action :
        (1 : G) ^ 1 • p = p)
  linarith
#align period_neutral_eq_one Rubin.Period.period_neutral_eq_one

theorem moves_within_period {n : ℕ} (g : G) (x : α) :
  0 < n → n < period x g → g^n • x ≠ x :=
by
  intro n_pos n_lt_period
  unfold period at n_lt_period
  apply Nat.not_mem_of_lt_sInf at n_lt_period
  simp at n_lt_period
  apply n_lt_period
  exact n_pos

-- Variant of moves_within_period, which works with integers
theorem moves_within_period' {z : ℤ} (g : G) (x : α) :
  0 < z → z < period x g → g^z • x ≠ x :=
by
  intro n_pos n_lt_period
  rw [<-Int.natAbs_of_nonneg (Int.le_of_lt n_pos)]
  rw [zpow_ofNat]
  apply moves_within_period
  · rw [<-Int.natAbs_zero]
    apply Int.natAbs_lt_natAbs_of_nonneg_of_lt
    rfl
    assumption
  · rw [<-Int.natAbs_cast (period x g)]
    apply Int.natAbs_lt_natAbs_of_nonneg_of_lt
    exact Int.le_of_lt n_pos
    assumption

def periods (U : Set α) (H : Subgroup G) : Set ℕ :=
  {n : ℕ | ∃ (p : α) (g : H), p ∈ U ∧ Rubin.Period.period (p : α) (g : G) = n}
#align periods Rubin.Period.periods

-- TODO: split into multiple lemmas
theorem periods_lemmas {U : Set α} (U_nonempty : Set.Nonempty U) {H : Subgroup G}
    (exp_ne_zero : Monoid.exponent H ≠ 0) :
    (Rubin.Period.periods U H).Nonempty ∧
      BddAbove (Rubin.Period.periods U H) ∧
        ∃ (m : ℕ), m > 0 ∧ ∀ (p : α) (g : H), g ^ m • p = p :=
by
  rcases Monoid.exponentExists_iff_ne_zero.2 exp_ne_zero with ⟨m, m_pos, gm_eq_one⟩
  have gmp_eq_p : ∀ (p : α) (g : H), g ^ m • p = p := by
    intro p g; rw [gm_eq_one g];
    group_action
  have periods_nonempty : (Rubin.Period.periods U H).Nonempty := by
    use 1
    let p := Set.Nonempty.some U_nonempty; use p
    use 1
    constructor
    · exact Set.Nonempty.some_mem U_nonempty
    · exact Rubin.Period.period_neutral_eq_one p

  have periods_bounded : BddAbove (Rubin.Period.periods U H) := by
    use m; intro some_period hperiod;
    rcases hperiod with ⟨p, g, hperiod⟩
    rw [← hperiod.2]
    exact (Rubin.Period.period_le_fix m_pos (gmp_eq_p p g)).2
  exact ⟨periods_nonempty, periods_bounded, m, m_pos, gmp_eq_p⟩
#align period_lemma Rubin.Period.periods_lemmas

theorem period_from_exponent (U : Set α) (U_nonempty : U.Nonempty) {H : Subgroup G}
    (exp_ne_zero : Monoid.exponent H ≠ 0) :
    ∃ (p : α) (g : H) (n : ℕ),
      p ∈ U ∧ n > 0 ∧ Rubin.Period.period (p : α) (g : G) = n ∧ n = sSup (Rubin.Period.periods U H) :=
by
  rcases Rubin.Period.periods_lemmas U_nonempty exp_ne_zero with
    ⟨periods_nonempty, periods_bounded, m, m_pos, gmp_eq_p⟩
  rcases Nat.sSup_mem periods_nonempty periods_bounded with ⟨p, g, hperiod⟩
  use p
  use g
  use sSup (Rubin.Period.periods U H)
  -- TODO: cleanup?
  exact ⟨
    hperiod.1,
    hperiod.2 ▸ (Rubin.Period.period_le_fix m_pos (gmp_eq_p p g)).1,
    hperiod.2,
    rfl
  ⟩
#align period_from_exponent Rubin.Period.period_from_exponent

theorem zero_lt_period_le_Sup_periods {U : Set α} (U_nonempty : U.Nonempty)
    {H : Subgroup G} (exp_ne_zero : Monoid.exponent H ≠ 0) :
    ∀ (p : U) (g : H),
      0 < Rubin.Period.period (p : α) (g : G) ∧
        Rubin.Period.period (p : α) (g : G) ≤ sSup (Rubin.Period.periods U H) :=
by
  rcases Rubin.Period.periods_lemmas U_nonempty exp_ne_zero with
    ⟨_periods_nonempty, periods_bounded, m, m_pos, gmp_eq_p⟩
  intro p g
  have period_in_periods : Rubin.Period.period (p : α) (g : G) ∈ Rubin.Period.periods U H := by
    use p; use g
    simp
  exact
    ⟨(Rubin.Period.period_le_fix m_pos (gmp_eq_p p g)).1,
      le_csSup periods_bounded period_in_periods⟩
#align zero_lt_period_le_Sup_periods Rubin.Period.zero_lt_period_le_Sup_periods

theorem period_pos {U : Set α} (U_nonempty : U.Nonempty) {H : Subgroup G}
  (exp_ne_zero : Monoid.exponent H ≠ 0) :
  ∀ (p : U) (g : H), 0 < Rubin.Period.period (p : α) (g : G) :=
fun p g =>
  (zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero p g).1

theorem period_pos' {U : Set α} (U_nonempty : U.Nonempty) {H : Subgroup G}
  (exp_ne_zero : Monoid.exponent H ≠ 0) :
  ∀ (p : α) (g : G), p ∈ U → g ∈ H → 0 < Rubin.Period.period (p : α) (g : G) :=
fun p g p_in_U g_in_H => period_pos U_nonempty exp_ne_zero ⟨p, p_in_U⟩ ⟨g, g_in_H⟩

theorem period_le_Sup_periods {U : Set α} (U_nonempty : U.Nonempty)
  {H : Subgroup G} (exp_ne_zero : Monoid.exponent H ≠ 0) :
  ∀ (p : U) (g : H), Rubin.Period.period (p : α) (g : G) ≤ sSup (Rubin.Period.periods U H) :=
fun p g =>
  (zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero p g).2

theorem period_le_Sup_periods' {U : Set α} (U_nonempty : U.Nonempty)
  {H : Subgroup G} (exp_ne_zero : Monoid.exponent H ≠ 0) :
  ∀ (p : α) (g : G), p ∈ U → g ∈ H → Rubin.Period.period p g ≤ sSup (Rubin.Period.periods U H) :=
fun p g p_in_U g_in_H => period_le_Sup_periods U_nonempty exp_ne_zero ⟨p, p_in_U⟩ ⟨g, g_in_H⟩

-- TODO: rename to pow_period_fixes
theorem pow_period_fix (p : α) (g : G) : g ^ Rubin.Period.period p g • p = p := by
  cases eq_zero_or_neZero (Rubin.Period.period p g) with
  | inl h => rw [h]; simp
  | inr h =>
    exact
      (Nat.sInf_mem
          (Nat.nonempty_of_pos_sInf
            (Nat.pos_of_ne_zero (@NeZero.ne _ _ (Rubin.Period.period p g) h)))).2
#align pow_period_fix Rubin.Period.pow_period_fix

end Rubin.Period
