import Mathlib.GroupTheory.GroupAction.Basic

namespace Rubin

variable {G α β : Type _} [Group G]
variable [MulAction G α]

theorem smul_congr (g : G) {x y : α} (h : x = y) : g • x = g • y :=
  congr_arg ((· • ·) g) h
#align smul_congr Rubin.smul_congr

theorem smul_eq_iff_inv_smul_eq {x : α} {g : G} : g • x = x ↔ g⁻¹ • x = x :=
  ⟨fun h => (smul_congr g⁻¹ h).symm.trans (inv_smul_smul g x), fun h =>
    (smul_congr g h).symm.trans (smul_inv_smul g x)⟩
#align smul_eq_iff_inv_smul_eq Rubin.smul_eq_iff_inv_smul_eq

theorem smul_pow_eq_of_smul_eq {x : α} {g : G} (n : ℕ) :
    g • x = x → g ^ n • x = x := by
  induction n with
  | zero => simp only [pow_zero, one_smul, eq_self_iff_true, imp_true_iff]
  | succ n n_ih =>
    intro h
    nth_rw 2 [← (smul_congr g (n_ih h)).trans h]
    rw [← mul_smul, ← pow_succ]
#align smul_pow_eq_of_smul_eq Rubin.smul_pow_eq_of_smul_eq

theorem smul_zpow_eq_of_smul_eq {x : α} {g : G} (n : ℤ) :
    g • x = x → g ^ n • x = x := by
  intro h
  cases n with
  | ofNat n => let res := smul_pow_eq_of_smul_eq n h; simp; exact res
  | negSucc n =>
    let res :=
      smul_eq_iff_inv_smul_eq.mp (smul_pow_eq_of_smul_eq (1 + n) h);
    simp
    rw [add_comm]
    exact res
#align smul_zpow_eq_of_smul_eq Rubin.smul_zpow_eq_of_smul_eq

def is_equivariant (G : Type _) {β : Type _} [Group G] [MulAction G α]
    [MulAction G β] (f : α → β) :=
  ∀ g : G, ∀ x : α, f (g • x) = g • f x
#align is_equivariant Rubin.is_equivariant

end Rubin