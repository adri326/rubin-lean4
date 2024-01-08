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

-- TODO: turn this into a structure?
def is_equivariant (G : Type _) {β : Type _} [Group G] [MulAction G α]
    [MulAction G β] (f : α → β) :=
  ∀ g : G, ∀ x : α, f (g • x) = g • f x
#align is_equivariant Rubin.is_equivariant

lemma is_equivariant_refl {G : Type _} [Group G] [MulAction G α] : is_equivariant G (id : α → α) :=
  fun _ _ => rfl

lemma is_equivariant_trans {G : Type _} [Group G] [MulAction G α] [MulAction G β] [MulAction G γ]
  (h₁ : α → β) (h₂ : β → γ) (e₁ : is_equivariant G h₁) (e₂ : is_equivariant G h₂) :
    is_equivariant G (h₂ ∘ h₁) := by
   intro g x
   rw [Function.comp_apply, Function.comp_apply, e₁, e₂]

lemma disjoint_not_mem {α : Type _} {U V : Set α} (disj: Disjoint U V) :
  ∀ {x : α}, x ∈ U → x ∉ V :=
by
  intro x x_in_U x_in_V
  apply disj <;> try simp
  · exact Set.singleton_subset_iff.mpr x_in_U
  · rw [Set.singleton_subset_iff]
    exact x_in_V
  · rfl

lemma disjoint_not_mem₂ {α : Type _} {U V : Set α} (disj: Disjoint U V) :
  ∀ {x : α}, x ∈ V → x ∉ U := disjoint_not_mem disj.symm

lemma fixes_inv {G α : Type _} [Group G] [MulAction G α] {g : G} {x : α}:
  g • x = x ↔ g⁻¹ • x = x :=
by
  constructor
  {
    intro h
    nth_rw 1 [<-h]
    rw [<-mul_smul, mul_left_inv, one_smul]
  }
  {
    intro h
    nth_rw 1 [<-h]
    rw [<-mul_smul, mul_right_inv, one_smul]
  }

lemma exists_smul_ne {G : Type _} (α : Type _) [Group G] [MulAction G α] [h_f : FaithfulSMul G α]
  {f g : G} (f_ne_g : f ≠ g) : ∃ (x : α), f • x ≠ g • x :=
by
  by_contra h
  rw [Classical.not_exists_not] at h
  apply f_ne_g
  apply h_f.eq_of_smul_eq_smul
  exact h

@[simp]
theorem orbit_bot {G : Type _} [Group G] {H : Subgroup G} (H_eq_bot : H = ⊥):
  ∀ (g : G), MulAction.orbit H g = {g} :=
by
  intro g
  ext x
  rw [MulAction.mem_orbit_iff]
  simp
  rw [H_eq_bot]
  simp
  constructor <;> tauto

@[simp]
theorem orbit_bot₂ {G : Type _} [Group G] {α : Type _} [MulAction G α] (H : Subgroup G) (H_eq_bot : H = ⊥):
  ∀ (x : α), MulAction.orbit H x = {x} :=
by
  intro g
  ext x
  rw [MulAction.mem_orbit_iff]
  simp
  rw [H_eq_bot]
  simp
  constructor <;> tauto

end Rubin
