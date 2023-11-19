/-
Copyright (c) 2023 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Laurent Bartholdi
-/

import tactic

--import group_action_tactic.lean

import data.finset.basic
import data.finset.card
import data.fintype.perm

import group_theory.subgroup.basic
import group_theory.commutator
import group_theory.group_action.basic
import group_theory.exponent
import group_theory.perm.basic

import topology.basic
import topology.subset_properties
import topology.separation
import topology.homeomorph

--@[simp]
lemma smul_smul' {G α : Type*} [group G] [mul_action G α] {g h : G} {x : α} : g • h • x = (g*h) • x := (mul_smul g h x).symm

--@[simp]
lemma smul_eq_smul {G α : Type*} [group G] [mul_action G α] {g h : G} {x y : α} : g • x = h • y ↔ (h⁻¹*g) • x = y := begin
  split,
  { intro hyp,
    let := congr_arg ((•) h⁻¹) hyp,
    rw [← mul_smul,← mul_smul,mul_left_inv,one_smul] at this,
    from this },
  { intro hyp,
    let := congr_arg ((•) h) hyp,
    rw [← mul_smul,← mul_assoc,mul_right_inv,one_mul] at this,
    from this }
end

lemma smul_succ {G α : Type*} (n : ℕ) [group G] [mul_action G α] {g : G} {x : α} : g ^ n.succ • x = g • g ^ n • x := begin
  have := tactic.ring.pow_add_rev g 1 n,
  rw [pow_one, ← nat.succ_eq_one_add] at this,
  rw [← this, smul_smul]
end


section group_action_tactic

namespace tactic.interactive
setup_tactic_parser
open tactic

setup_tactic_parser

open tactic.simp_arg_type interactive tactic.group

/-- Auxiliary tactic for the `group_action` tactic. Calls the simplifier only. -/
meta def aux_group_action (locat : loc) : tactic unit :=
tactic.interactive.simp_core { fail_if_unchanged := ff } skip tt [
  expr ``(smul_smul'),
  expr ``(smul_eq_smul),
  expr ``(smul_succ),
  expr ``(one_smul),
  expr ``(commutator_element_def),
  expr ``(mul_one),
  expr ``(one_mul),
  expr ``(one_pow),
  expr ``(one_zpow),
  expr ``(sub_self),
  expr ``(add_neg_self),
  expr ``(neg_add_self),
  expr ``(neg_neg),
  expr ``(tsub_self),
  expr ``(int.coe_nat_add),
  expr ``(int.coe_nat_mul),
  expr ``(int.coe_nat_zero),
  expr ``(int.coe_nat_one),
  expr ``(int.coe_nat_bit0),
  expr ``(int.coe_nat_bit1),
  expr ``(int.mul_neg_eq_neg_mul_symm),
  expr ``(int.neg_mul_eq_neg_mul_symm),
  symm_expr ``(zpow_coe_nat),
  symm_expr ``(zpow_neg_one),
  symm_expr ``(zpow_mul),
  symm_expr ``(zpow_add_one),
  symm_expr ``(zpow_one_add),
  symm_expr ``(zpow_add),
  expr ``(mul_zpow_neg_one),
  expr ``(zpow_zero),
  expr ``(mul_zpow),
  symm_expr ``(mul_assoc),
  expr ``(zpow_trick),
  expr ``(zpow_trick_one),
  expr ``(zpow_trick_one'),
  expr ``(zpow_trick_sub),
  expr ``(mul_one),
  expr ``(one_mul),
  expr ``(one_pow),
  expr ``(one_zpow),
  expr ``(sub_self),
  expr ``(add_neg_self),
  expr ``(neg_add_self),
  expr ``(neg_neg),
  expr ``(tsub_self),
  expr ``(int.coe_nat_add),
  expr ``(int.coe_nat_mul),
  expr ``(int.coe_nat_zero),
  expr ``(int.coe_nat_one),
  expr ``(int.coe_nat_bit0),
  expr ``(int.coe_nat_bit1),
  expr ``(int.mul_neg_eq_neg_mul_symm),
  expr ``(int.neg_mul_eq_neg_mul_symm),
  symm_expr ``(zpow_coe_nat),
  symm_expr ``(zpow_neg_one),
  symm_expr ``(zpow_mul),
  symm_expr ``(zpow_add_one),
  symm_expr ``(zpow_one_add),
  symm_expr ``(zpow_add),
  expr ``(mul_zpow_neg_one),
  expr ``(zpow_zero),
  expr ``(mul_zpow),
  symm_expr ``(mul_assoc),
  expr ``(zpow_trick),
  expr ``(zpow_trick_one),
  expr ``(zpow_trick_one'),
  expr ``(zpow_trick_sub),
expr ``(tactic.ring.horner)]
  [] locat >> skip

/--
Tactic for normalizing expressions in group actions, without assuming
commutativity, using only the group axioms without any information about
which group is manipulated.
Example:
```lean
example {G α : Type} [group G] [mul_action G α] (a b : G) (x y : α) (h : a • b • x = a • y) : b⁻¹ • y = x :=
begin
  group_action at h, -- normalizes `h` which becomes `h : c = d`
  rw ← h,            -- the goal is now `a*d*d⁻¹ = a`
  group_action       -- which then normalized and closed
end
```
-/
meta def group_action (locat : parse location) : tactic unit :=
do aux_group_action locat,
   repeat (aux_group₂ locat ; aux_group_action locat)

end tactic.interactive

add_tactic_doc
{ name := "group_action",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.group_action],
  tags := ["decision procedure", "simplification"] }

end group_action_tactic

example (G α : Type*) [group G] (a b c : G) [mul_action G α] (x : α) : ⁅a*b,c⁆ • x = (a*⁅b,c⁆*a⁻¹*⁅a,c⁆) • x := begin
  group_action,
end

lemma equiv.congr_ne {ι ι' : Type*} (e : ι ≃ ι') {x y : ι} : x ≠ y → e x ≠ e y := begin
  intro x_ne_y,
  by_contra h,
  apply x_ne_y,
  convert congr_arg e.symm h;
  simp only [equiv.symm_apply_apply]
end

-- this definitely should be added to mathlib!
@[simp, to_additive] lemma subgroup.mk_smul {G α : Type*} [group G] [mul_action G α]
  {S : subgroup G} {g : G} (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

----------------------------------------------------------------
section rubin

variables {G α β : Type*} [group G]

----------------------------------------------------------------
section groups

lemma bracket_mul {f g : G} : ⁅f,g⁆ = f*g*f⁻¹*g⁻¹ := by tauto

def is_algebraically_disjoint (f g : G) := ∀h : G, ¬commute f h → ∃f₁ f₂ : G, commute  f₁ g ∧ commute f₂ g ∧ commute ⁅f₁,⁅f₂,h⁆⁆ g ∧ ⁅f₁,⁅f₂,h⁆⁆≠1

end groups

----------------------------------------------------------------
section actions

variable [mul_action G α]

@[simp] lemma orbit_bot (G : Type*) [group G] [mul_action G α] (p : α) : mul_action.orbit (⊥ : subgroup G) p = {p} := begin
  ext1,
  rw mul_action.mem_orbit_iff,
  split,
  { rintro ⟨⟨_,g_bot⟩,g_to_x⟩,
    rw [← g_to_x,set.mem_singleton_iff,subgroup.mk_smul],
    exact (subgroup.mem_bot.mp g_bot).symm ▸ (one_smul _ _) },
  exact λ h, ⟨1,eq.trans (one_smul _ p) (set.mem_singleton_iff.mp h).symm⟩
end

--------------------------------
section smul''

lemma smul_congr (g : G) {x y : α} (h : x = y) : g • x = g • y := congr_arg ((•) g) h

lemma smul_eq_iff_inv_smul_eq {x : α} {g : G} : g • x = x ↔ g⁻¹ • x = x :=
  ⟨λ h, (smul_congr g⁻¹ h).symm.trans (inv_smul_smul g x),λ h, (smul_congr g h).symm.trans (smul_inv_smul g x)⟩

lemma smul_pow_eq_of_smul_eq {x : α} {g : G} (n : ℕ) : g • x = x → g^n • x = x := begin
  induction n,
  simp only [pow_zero, one_smul, eq_self_iff_true, implies_true_iff],
  { intro h,
    nth_rewrite 1 ← (smul_congr g (n_ih h)).trans h,
    rw [← mul_smul,← pow_succ]
  }
end

lemma smul_zpow_eq_of_smul_eq {x : α} {g : G} (n : ℤ) : g • x = x → g^n • x = x := begin
  intro h,
  cases n,
  { let := smul_pow_eq_of_smul_eq n h, finish },
  { let := smul_eq_iff_inv_smul_eq.mp (smul_pow_eq_of_smul_eq (1+n) h), finish }
end

def is_equivariant (G : Type*) {β : Type*} [group G] [mul_action G α] [mul_action G β] (f : α → β) :=
  ∀g : G, ∀x : α, f (g • x) = g • (f x)

def subset_img' (g : G) (U : set α) := { x | g⁻¹ • x ∈ U }
def subset_preimg' (g : G) (U : set α) := { x | g • x ∈ U }

def subset_img (g : G) (U : set α) := (•) g '' U
infix `•''`:60 := subset_img
lemma subset_img_def {g : G} {U : set α} : g •'' U = ((•) g) '' U := rfl

lemma mem_smul'' {x : α} {g : G} {U : set α} : x ∈ g •'' U ↔ g⁻¹ • x ∈ U := begin
  rw [subset_img_def,set.mem_image ((•) g) U x],
  split,
  { rintro ⟨y,yU,gyx⟩,
    let ygx : y = g⁻¹ • x := inv_smul_smul g y ▸ smul_congr g⁻¹ gyx,
    exact ygx ▸ yU
  },
  { intro h,
    use ⟨g⁻¹ • x,set.mem_preimage.mp h,smul_inv_smul g x⟩,
  }
end

lemma mem_inv_smul'' {x : α} {g : G} {U : set α} : x ∈ g⁻¹ •'' U ↔ g • x ∈ U := begin
  let msi := @mem_smul'' _ _ _ _ x g⁻¹ U,
  rw inv_inv at msi,
  exact msi
end

lemma mul_smul'' (g h : G) (U : set α) : (g*h) •'' U = (g •'' (h •'' U)) := begin
  ext,
  rw [mem_smul'',mem_smul'',mem_smul'',← mul_smul,mul_inv_rev]
end

@[simp] lemma smul''_smul'' {g h : G} {U : set α} : (g •'' (h •'' U)) = (g*h) •'' U := (mul_smul'' g h U).symm

@[simp] lemma one_smul'' (U : set α) : (1:G) •'' U = U := begin
  ext,
  rw [mem_smul'',inv_one,one_smul]
end

lemma disjoint_smul'' (g : G) {U V : set α} : disjoint U V → disjoint (g •'' U) (g •'' V) := begin
  intro disjoint_U_V,
  rw set.disjoint_left,
  rw set.disjoint_left at disjoint_U_V,
  intros x x_in_gU,
  by_contra h,
  exact (disjoint_U_V (mem_smul''.mp x_in_gU)) (mem_smul''.mp h)
end

lemma smul''_congr (g : G) {U V : set α} : U = V → g •'' U = g •'' V := congr_arg (λ(W : set α), g •'' W)

lemma smul''_subset (g : G) {U V : set α} : U ⊆ V → g •'' U ⊆ g •'' V := begin
  intros h1 x,
  rw [mem_smul'',mem_smul''],
  exact λ h2, h1 h2
end

lemma smul''_union (g : G) {U V : set α} : g •'' (U ∪ V) = (g •'' U) ∪ (g •'' V) := begin
  ext,
  rw [mem_smul'',set.mem_union,set.mem_union,mem_smul'',mem_smul''],
end

lemma smul''_inter (g : G) {U V : set α} : g •'' (U ∩ V) = (g •'' U) ∩ (g •'' V) := begin
  ext,
  rw [set.mem_inter_iff,mem_smul'',mem_smul'',mem_smul'',set.mem_inter_iff]
end

lemma smul''_eq_inv_preimage {g : G} {U : set α} : g •'' U = (•) g⁻¹ ⁻¹' U :=
begin
  ext,
  split,
  { intro h, rw [set.mem_preimage], exact mem_smul''.mp h },
  { intro h, rw mem_smul'', exact set.mem_preimage.mp h }
end

lemma smul''_eq_of_smul_eq {g h : G} {U : set α} : (∀x ∈ U, g • x = h • x) → g •'' U = h •'' U := begin
  intros hU,
  ext,
  rw [mem_smul'',mem_smul''],
  split,
  { intro k, let a := congr_arg ((•) h⁻¹) (hU (g⁻¹ • x) k), simp only [smul_inv_smul,inv_smul_smul] at a, exact set.mem_of_eq_of_mem a k },
  { intro k, let a := congr_arg ((•) g⁻¹) (hU (h⁻¹ • x) k), simp only [smul_inv_smul,inv_smul_smul] at a, exact set.mem_of_eq_of_mem a.symm k }
end

end smul''

--------------------------------
section support

def support (α : Type*) [mul_action G α] (g : G) := { x : α | g • x ≠ x }

lemma support_eq_not_fixed_by {g : G} : support α g = (mul_action.fixed_by G α g)ᶜ := by tauto

lemma mem_support {x : α} {g : G} : x ∈ support α g ↔ g • x ≠ x := by tauto
lemma mem_not_support {x : α} {g : G} : x ∉ support α g ↔ g • x = x := by rw [mem_support,not_not]

lemma smul_in_support {g : G} {x : α} : x ∈ support α g → g • x ∈ support α g := λ h, h ∘ (smul_left_cancel g)

lemma inv_smul_in_support {g : G} {x : α} : x ∈ support α g → g⁻¹ • x ∈ support α g := λ h k, h (smul_inv_smul g x ▸ smul_congr g k)

lemma fixed_of_disjoint {g : G} {x : α} {U : set α} : x ∈ U → disjoint U (support α g) → g • x = x :=
  λ x_in_U disjoint_U_support, mem_not_support.mp (set.disjoint_left.mp disjoint_U_support x_in_U)

lemma fixes_subset_within_support (g : G) {U : set α} : support α g ⊆ U → g •'' U = U := begin
  intros support_in_U,
  ext x,
  cases @or_not (x ∈ support α g) with xmoved xfixed,
  exact ⟨λ _, support_in_U xmoved,
    λ _, mem_smul''.mpr (support_in_U (inv_smul_in_support xmoved))⟩,
  rw [mem_smul'',smul_eq_iff_inv_smul_eq.mp (mem_not_support.mp xfixed)]
end

lemma moves_subset_within_support (g : G) (U V : set α) : U ⊆ V → support α g ⊆ V → g •'' U ⊆ V :=
  λ U_in_V support_in_V, fixes_subset_within_support g support_in_V ▸ smul''_subset g U_in_V

lemma support_mul (g h : G) (α : Type*) [mul_action G α] : support α (g*h) ⊆ support α g ∪ support α h := begin
  intros x x_in_support,
  by_contra h_support,
  let := not_or_distrib.mp h_support,
  from x_in_support ((mul_smul g h x).trans ((congr_arg ((•) g) (mem_not_support.mp this.2)).trans $ mem_not_support.mp this.1)),
end

lemma support_conjugate (α : Type*) [mul_action G α] (g h : G) : support α (h*g*h⁻¹) = h •'' (support α g) := begin
  ext,
  rw [mem_support,mem_smul'',mem_support,mul_smul,mul_smul],
  split,
  { intro h1, by_contra h2, exact h1 ((congr_arg ((•) h) h2).trans (smul_inv_smul _ _)) },
  { intro h1, by_contra h2, exact h1 ((inv_smul_smul h (g • h⁻¹ • x)) ▸ (congr_arg ((•) h⁻¹) h2)) }
end

lemma support_inv (α : Type*) [mul_action G α] (g : G) : support α g⁻¹ = support α g := begin
  ext,
  rw [mem_support,mem_support],
  split,
  { intro h1, by_contra h2, exact h1 (smul_eq_iff_inv_smul_eq.mp h2) },
  { intro h1, by_contra h2, exact h1 (smul_eq_iff_inv_smul_eq.mpr h2) }
end

lemma support_pow (α : Type*) [mul_action G α] (g : G) (j : ℕ) : support α (g^j) ⊆ support α g := begin
  intros x xmoved,
  by_contra xfixed,
  rw mem_support at xmoved,
  induction j,
  { apply xmoved, rw [pow_zero g,one_smul] },
  { apply xmoved,
    let j_ih := (congr_arg ((•) g) (not_not.mp j_ih)).trans (mem_not_support.mp xfixed),
    rw [← mul_smul,← pow_succ] at j_ih,
    exact j_ih
  }
end

lemma support_comm (α : Type*) [mul_action G α] (g h : G) : support α ⁅g,h⁆ ⊆ support α h ∪ (g •'' (support α h)) := begin
  intros x x_in_support,
  by_contra all_fixed,
  rw set.mem_union at all_fixed,
  cases @or_not (h • x = x) with xfixed xmoved,
  { rw [mem_support,bracket_mul,mul_smul,smul_eq_iff_inv_smul_eq.mp xfixed,← mem_support] at x_in_support,
    exact ((support_conjugate α h g).symm ▸ (not_or_distrib.mp all_fixed).2) x_in_support
  },
  { exact all_fixed (or.inl xmoved) },
end

lemma disjoint_support_comm (f g : G) {U : set α} : support α f ⊆ U → disjoint U (g •'' U) → ∀x ∈ U, ⁅f,g⁆ • x = f • x := begin
  intros support_in_U disjoint_U x x_in_U,

  have support_conj : support α (g*f⁻¹*g⁻¹) ⊆ g •'' U := ((support_conjugate α f⁻¹ g).trans (smul''_congr g (support_inv α f))).symm ▸ (smul''_subset g support_in_U),

  have goal := (congr_arg ((•) f) (fixed_of_disjoint x_in_U (set.disjoint_of_subset_right support_conj disjoint_U))).symm,
  rw [← mul_smul,← mul_assoc,← mul_assoc] at goal,
  exact goal.symm,
end

end support

-- comment by Cedric: would be nicer to define just a subset, and then show it is a subgroup
def rigid_stabilizer' (G : Type*) [group G] [mul_action G α] (U : set α) : set G := {g : G | ∀x : α, g • x = x ∨ x ∈ U}

def rigid_stabilizer (G : Type*) [group G] [mul_action G α] (U : set α) : subgroup G := {
carrier := {g : G | ∀x ∉ U, g • x = x},
mul_mem' := λ a b ha hb x x_notin_U, by rw [mul_smul a b x,hb x x_notin_U,ha x x_notin_U],
inv_mem' := λ _ hg x x_notin_U, smul_eq_iff_inv_smul_eq.mp (hg x x_notin_U),
one_mem' := λ x _, one_smul G x
}

lemma rist_supported_in_set {g : G} {U : set α} : g ∈ rigid_stabilizer G U → support α g ⊆ U :=
  λ h x x_in_support, by_contradiction (x_in_support ∘ (h x))

lemma rist_ss_rist {U V : set α} (V_ss_U : V ⊆ U) : (rigid_stabilizer G V : set G) ⊆ (rigid_stabilizer G U : set G) := begin
  intros g g_in_ristV x x_notin_U,
  have x_notin_V : x ∉ V, { intro x_in_V, exact x_notin_U (V_ss_U x_in_V) },
  exact g_in_ristV x x_notin_V
end

end actions

----------------------------------------------------------------
section topological_actions

variables [topological_space α] [topological_space β]

class continuous_mul_action (G α : Type*) [group G] [topological_space α] extends mul_action G α :=
  (continuous : ∀g : G, continuous (@has_smul.smul G α _ g))

structure equivariant_homeomorph (G α β : Type*) [group G] [topological_space α] [topological_space β] [mul_action G α] [mul_action G β] extends homeomorph α β :=
(equivariant : is_equivariant G to_fun)

lemma equivariant_fun [mul_action G α] [mul_action G β] (h : equivariant_homeomorph G α β) : is_equivariant G h.to_fun := h.equivariant

lemma equivariant_inv [mul_action G α] [mul_action G β] (h : equivariant_homeomorph G α β) : is_equivariant G h.inv_fun := begin
intros g x,
let e := congr_arg h.inv_fun (h.equivariant g (h.inv_fun x)),
rw [h.left_inv _,h.right_inv _] at e,
exact e.symm,
end

variables [continuous_mul_action G α]

lemma img_open_open (g : G) (U : set α) (h : is_open U) [continuous_mul_action G α] : is_open (g •'' U) :=
begin
  rw smul''_eq_inv_preimage,
  exact continuous.is_open_preimage (continuous_mul_action.continuous g⁻¹) U h
end

lemma support_open (g : G) [topological_space α] [t2_space α] [continuous_mul_action G α] : is_open (support α g) := begin
  apply is_open_iff_forall_mem_open.mpr,
  intros x xmoved,
  rcases t2_space.t2 (g • x) x xmoved with ⟨U,V,open_U,open_V,gx_in_U,x_in_V,disjoint_U_V⟩,
  exact ⟨V ∩ (g⁻¹ •'' U),
    λ y yW, @disjoint.ne_of_mem α U V disjoint_U_V (g•y) y (mem_inv_smul''.mp (set.mem_of_mem_inter_right yW)) (set.mem_of_mem_inter_left yW),
    is_open.inter open_V (img_open_open g⁻¹ U open_U),
    ⟨x_in_V,mem_inv_smul''.mpr gx_in_U⟩⟩
end

end topological_actions

----------------------------------------------------------------
section faithful_actions

variables [mul_action G α] [has_faithful_smul G α]

lemma faithful_moves_point {g : G} (h2 : ∀x : α, g • x = x) : g = 1 := begin
  have h3 : ∀x : α, g • x = (1:G) • x := λ x, (h2 x).symm ▸ (one_smul G x).symm,
  exact eq_of_smul_eq_smul h3,
end

lemma faithful_moves_point' {g : G} (α : Type*) [mul_action G α] [has_faithful_smul G α] : g ≠ 1 → ∃x : α, g • x ≠ x :=
  λ k, by_contradiction (λ h, k $ faithful_moves_point $ not_exists_not.mp h)

lemma faithful_rist_moves_point {g : G} {U : set α} : g ∈ rigid_stabilizer G U → g ≠ 1 → ∃x ∈ U, g • x ≠ x := begin
  intros g_rigid g_ne_one,
  rcases faithful_moves_point' α g_ne_one with ⟨x,xmoved⟩,
  exact ⟨x,rist_supported_in_set g_rigid xmoved,xmoved⟩
end

lemma ne_one_support_nempty {g : G} : g ≠ 1 → (support α g).nonempty := begin
  intro h1,
  cases (faithful_moves_point' α h1) with x _,
  use x
end

lemma disjoint_commute {f g : G} : disjoint (support α f) (support α g) → commute f g := begin
  intro hdisjoint,
  rw ← commutator_element_eq_one_iff_commute,
  apply (@faithful_moves_point _ α),
  intro x,
  rw [bracket_mul,mul_smul,mul_smul,mul_smul],
  cases @or_not (x ∈ support α f) with hfmoved hffixed,
  { rw [smul_eq_iff_inv_smul_eq.mp (mem_not_support.mp (set.disjoint_left.mp hdisjoint hfmoved)),
        mem_not_support.mp (set.disjoint_left.mp hdisjoint (inv_smul_in_support hfmoved)),smul_inv_smul] },
  cases @or_not (x ∈ support α g) with hgmoved hgfixed,
  { rw [smul_eq_iff_inv_smul_eq.mp (mem_not_support.mp $ set.disjoint_right.mp hdisjoint (inv_smul_in_support hgmoved)),
        smul_inv_smul,mem_not_support.mp hffixed] },
  { rw [smul_eq_iff_inv_smul_eq.mp (mem_not_support.mp hgfixed),smul_eq_iff_inv_smul_eq.mp (mem_not_support.mp hffixed),
        mem_not_support.mp hgfixed,mem_not_support.mp hffixed] }
end

end faithful_actions

----------------------------------------------------------------
section rubin_actions

variables [topological_space α] [topological_space β]

def has_no_isolated_points (α : Type*) [topological_space α] := ∀x : α, (nhds_within x {x}ᶜ).ne_bot

def is_locally_dense (G α : Type*) [group G] [topological_space α] [mul_action G α] :=
  ∀U : set α, ∀p ∈ U, p ∈ interior (closure (mul_action.orbit (rigid_stabilizer G U) p))

structure rubin_action (G α : Type*) extends group G, topological_space α, mul_action G α, has_faithful_smul G α :=
(locally_compact : locally_compact_space α)
(hausdorff : t2_space α)
(no_isolated_points : has_no_isolated_points α)
(locally_dense : is_locally_dense G α)

end rubin_actions

----------------------------------------------------------------
section period

variables [mul_action G α]

noncomputable def period (p : α) (g : G) : ℕ :=
Inf { n : ℕ | n > 0 ∧ g ^ n • p = p }

lemma period_le_fix {p : α} {g : G} {m : ℕ} (m_pos : m > 0) (gmp_eq_p : g ^ m • p = p) : 0 < period p g ∧ period p g ≤ m := begin
  split,
  { by_contra h', have period_zero : period p g = 0, linarith, rcases (nat.Inf_eq_zero.1 period_zero) with ⟨ cont, h_1 ⟩, linarith, exact set.eq_empty_iff_forall_not_mem.mp h ↑m ⟨ m_pos, gmp_eq_p ⟩ },
  exact nat.Inf_le ⟨ m_pos, gmp_eq_p ⟩
end

lemma notfix_le_period {p : α} {g : G} {n : ℕ} (n_pos : n > 0) (period_pos : period p g > 0) (pmoves : ∀ (i : ℕ), 0 < i → i < n → g ^ i • p ≠ p) : n ≤ period p g := begin
  by_contra period_le,
  exact (pmoves (period p g) period_pos (not_le.mp period_le)) (nat.Inf_mem (nat.nonempty_of_pos_Inf period_pos)).2
end

lemma notfix_le_period' {p : α} {g : G} {n : ℕ} (n_pos : n > 0) (period_pos : period p g > 0) (pmoves : ∀ (i : fin n), 0 < (i : ℕ) → g ^ (i : ℕ) • p ≠ p) : n ≤ period p g :=
  notfix_le_period n_pos period_pos (λ (i : ℕ) (i_pos : 0 < i) (i_lt_n : i < n), pmoves (⟨ i, i_lt_n ⟩ : fin n) i_pos )

lemma period_neutral_eq_one (p : α) : period p (1 : G) = 1 := begin
  have : 0 < period p (1 : G) ∧ period p (1 : G) ≤ 1,
  { exact period_le_fix (by norm_num : 1 > 0) (by group_action : (1 : G) ^ 1 • p = p) },
  linarith
end


def periods (U : set α) (H : subgroup G) : set ℕ :=
{ n : ℕ | ∃ (p : U) (g : H), period (p : α) (g : G) = n }

lemma period_lemma
  {U : set α} (U_nonempty : U.nonempty)
  {H : subgroup G} (exp_ne_zero : monoid.exponent H ≠ 0) :
  (periods U H).nonempty ∧
  bdd_above (periods U H) ∧
  ∃ (m : ℕ) (m_pos : m > 0),
  ∀ (p : α) (g : H), g ^ m • p = p :=
begin
  rcases (monoid.exponent_exists_iff_ne_zero.2 exp_ne_zero) with ⟨ m, m_pos, gm_eq_one ⟩,
  have gmp_eq_p : ∀ (p : α) (g : H), g ^ m • p = p,
  { intros p g, rw gm_eq_one g, group_action },
  have periods_nonempty : (periods U H).nonempty,
  { use 1, let p := U_nonempty.some, use p, exact set.nonempty.some_mem U_nonempty, use 1, exact period_neutral_eq_one p },
  have periods_bounded : bdd_above (periods U H),
  { use m, intros some_period hperiod, rcases hperiod with ⟨ p, g, hperiod ⟩, rw ← hperiod, exact (period_le_fix m_pos (gmp_eq_p p g)).2 },
  exact ⟨ periods_nonempty, periods_bounded, m, m_pos, gmp_eq_p ⟩
end

lemma period_from_exponent
  (U : set α) (U_nonempty : U.nonempty)
  {H : subgroup G} (exp_ne_zero : monoid.exponent H ≠ 0) :
  ∃ (p : U) (g : H) (n : ℕ), n > 0 ∧ period (p : α) (g : G) = n ∧ n = Sup (periods U H) :=
begin
  rcases period_lemma U_nonempty exp_ne_zero with ⟨ periods_nonempty, periods_bounded, m, m_pos, gmp_eq_p ⟩,
  rcases nat.Sup_mem periods_nonempty periods_bounded with ⟨ p, g, hperiod ⟩,
  exact ⟨ p, g, Sup (periods U H), hperiod ▸ (period_le_fix m_pos (gmp_eq_p p g)).1, hperiod, rfl ⟩
end

lemma zero_lt_period_le_Sup_periods
  {U : set α} (U_nonempty : U.nonempty)
  {H : subgroup G} (exp_ne_zero : monoid.exponent H ≠ 0) :
  ∀ (p : U) (g : H),
  (0 < period (p : α) (g : G)) ∧ (period (p : α) (g : G) ≤ Sup (periods U H)) :=
begin
  rcases period_lemma U_nonempty exp_ne_zero with ⟨ periods_nonempty, periods_bounded, m, m_pos, gmp_eq_p ⟩,
  intros p g,
  have period_in_periods : period (p : α) (g : G) ∈ periods U H,
  { use p, use g },
  exact ⟨ (period_le_fix m_pos (gmp_eq_p p g)).1, le_cSup periods_bounded period_in_periods ⟩,
end

lemma pow_period_fix (p : α) (g : G) : g ^ (period p g) • p = p := begin
  cases eq_zero_or_ne_zero (period p g),
  { rw h, finish },
  { exact (nat.Inf_mem (nat.nonempty_of_pos_Inf (nat.pos_of_ne_zero (@ne_zero.ne _ _ (period p g) h)))).2 }
end

end period

----------------------------------------------------------------
section algebraic_disjointness

variables [topological_space α] [continuous_mul_action G α] [has_faithful_smul G α]

def is_locally_moving (G α : Type*) [group G] [topological_space α] [mul_action G α] :=
  ∀U : set α, is_open U → set.nonempty U → rigid_stabilizer G U ≠ ⊥

lemma dense_locally_moving : t2_space α ∧ has_no_isolated_points α ∧ is_locally_dense G α → is_locally_moving G α := begin
  rintros ⟨t2α,nipα,ildGα⟩ U ioU neU,
  by_contra,
  have some_in_U := ildGα U neU.some neU.some_mem,
  rw [h,orbit_bot G neU.some,@closure_singleton α _ (@t2_space.t1_space α _ t2α) neU.some,@interior_singleton α _ neU.some (nipα neU.some)] at some_in_U,
  tauto
end

lemma disjoint_nbhd {g : G} {x : α} [t2_space α] : g • x ≠ x → ∃U : set α, is_open U ∧ x ∈ U ∧ disjoint U (g •'' U) := begin
  intro xmoved,
  rcases t2_space.t2 (g • x) x xmoved with ⟨V,W,open_V,open_W,gx_in_V,x_in_W,disjoint_V_W⟩,
  let U := (g⁻¹ •'' V) ∩ W,
  use U,
  split,
  exact is_open.inter (img_open_open g⁻¹ V open_V) open_W,
  split,
  exact ⟨mem_inv_smul''.mpr gx_in_V,x_in_W⟩,
  exact set.disjoint_of_subset
    (set.inter_subset_right (g⁻¹•''V) W)
    (λ y hy, smul_inv_smul g y ▸ mem_inv_smul''.mp (set.mem_of_mem_inter_left (mem_smul''.mp hy)) : g•''U ⊆ V)
    disjoint_V_W.symm
end

lemma disjoint_nbhd_in {g : G} {x : α} [t2_space α] {V : set α} : is_open V → x ∈ V → g • x ≠ x → ∃U : set α, is_open U ∧ x ∈ U ∧ U ⊆ V ∧ disjoint U (g •'' U) := begin
  intros open_V x_in_V xmoved,
  rcases disjoint_nbhd xmoved with ⟨W,open_W,x_in_W,disjoint_W⟩,
  let U := W ∩ V,
  use U,
  split,
  exact is_open.inter open_W open_V,
  split,
  exact ⟨x_in_W,x_in_V⟩,
  split,
  exact set.inter_subset_right W V,
  exact set.disjoint_of_subset
    (set.inter_subset_left W V)
    ((@smul''_inter _ _ _ _ g W V).symm ▸ set.inter_subset_left (g•''W) (g•''V) : g•''U ⊆ g•''W)
    disjoint_W
end

lemma rewrite_Union (f : fin 2 × fin 2 → set α) : (⋃(i : fin 2 × fin 2), f i) = (f (0,0) ∪ f (0,1)) ∪ (f (1,0) ∪ f (1,1)) := begin
  ext,
  simp only [set.mem_Union, set.mem_union],
  split,
  { simp only [forall_exists_index],
    intro i,
    fin_cases i; simp {contextual := tt}, },
  { rintro ((h|h)|(h|h)); exact ⟨_, h⟩, },
end

lemma proposition_1_1_1 (f g : G) (locally_moving : is_locally_moving G α) [t2_space α] : disjoint (support α f) (support α g) → is_algebraically_disjoint f g := begin
  intros disjoint_f_g h hfh,
  let support_f := support α f,
-- h is not the identity on support α f
  cases set.not_disjoint_iff.mp (mt (@disjoint_commute G α _ _ _ _ _) hfh) with x hx,
  let x_in_support_f := hx.1,
  let hx_ne_x := mem_support.mp hx.2,
-- so since α is Hausdoff there is V nonempty ⊆ support α f with h•''V disjoint from V
  rcases disjoint_nbhd_in (support_open f) x_in_support_f hx_ne_x with ⟨V,open_V,x_in_V,V_in_support,disjoint_img_V⟩,
  let ristV_ne_bot := locally_moving V open_V (set.nonempty_of_mem x_in_V),
-- let f₂ be a nontrivial element of rigid_stabilizer G V
  rcases (or_iff_right ristV_ne_bot).mp (subgroup.bot_or_exists_ne_one _) with ⟨f₂,f₂_in_ristV,f₂_ne_one⟩,
-- again since α is Hausdorff there is W nonempty ⊆ V with f₂•''W disjoint from W
  rcases faithful_moves_point' α f₂_ne_one with ⟨y,ymoved⟩,
  let y_in_V : y ∈ V := (rist_supported_in_set f₂_in_ristV) (mem_support.mpr ymoved),
  rcases disjoint_nbhd_in open_V y_in_V ymoved with ⟨W,open_W,y_in_W,W_in_V,disjoint_img_W⟩,
-- let f₁ be a nontrivial element of rigid_stabilizer G W
  let ristW_ne_bot := locally_moving W open_W (set.nonempty_of_mem y_in_W),
  rcases (or_iff_right ristW_ne_bot).mp (subgroup.bot_or_exists_ne_one _) with ⟨f₁,f₁_in_ristW,f₁_ne_one⟩,
  use f₁, use f₂,
-- note that f₁,f₂ commute with g since their support is in support α f
  split,
  exact disjoint_commute (set.disjoint_of_subset_left (set.subset.trans (set.subset.trans (rist_supported_in_set f₁_in_ristW) W_in_V) V_in_support) disjoint_f_g),
  split,
  exact disjoint_commute (set.disjoint_of_subset_left (set.subset.trans (rist_supported_in_set f₂_in_ristV) V_in_support) disjoint_f_g),
-- we claim that [f₁,[f₂,h]] is a nontrivial element of centralizer G g
  let k := ⁅f₂,h⁆,
-- first, h*f₂⁻¹*h⁻¹ is supported on h V, so k := [f₂,h] agrees with f₂ on V
  have h2 : ∀z ∈ W, f₂•z = k•z := λ z z_in_W,
    (disjoint_support_comm f₂ h (rist_supported_in_set f₂_in_ristV) disjoint_img_V z (W_in_V z_in_W)).symm,
-- then k*f₁⁻¹*k⁻¹ is supported on k W = f₂ W, so [f₁,k] is supported on W ∪ f₂ W ⊆ V ⊆ support f, so commutes with g.
  have h3 : support α ⁅f₁,k⁆ ⊆ support α f := begin
    let := (support_comm α k f₁).trans (set.union_subset_union (rist_supported_in_set f₁_in_ristW) (smul''_subset k $ rist_supported_in_set f₁_in_ristW)),
    rw [← commutator_element_inv,support_inv,(smul''_eq_of_smul_eq h2).symm] at this,
    exact (this.trans $ (set.union_subset_union W_in_V (moves_subset_within_support f₂ W V W_in_V $ rist_supported_in_set f₂_in_ristV)).trans $ eq.subset V.union_self).trans V_in_support
end,
  split,
  exact disjoint_commute (set.disjoint_of_subset_left h3 disjoint_f_g),
-- finally, [f₁,k] agrees with f₁ on W, so is not the identity.
  have h4 : ∀z ∈ W, ⁅f₁,k⁆•z = f₁•z :=
    disjoint_support_comm f₁ k (rist_supported_in_set f₁_in_ristW) (smul''_eq_of_smul_eq h2 ▸ disjoint_img_W),
  rcases faithful_rist_moves_point f₁_in_ristW f₁_ne_one with ⟨z,z_in_W,z_moved⟩,
  by_contra h5,
  exact ((h4 z z_in_W).symm ▸ z_moved : ⁅f₁, k⁆ • z ≠ z) ((congr_arg (λg : G, g•z) h5).trans (one_smul G z)),
end

@[simp] lemma smul''_mul {g h : G} {U : set α} : g •'' (h •'' U) = (g*h) •'' U :=
  (mul_smul'' g h U).symm

lemma disjoint_nbhd_fin {ι : Type*} [fintype ι] {f : ι → G} {x : α} [t2_space α] : (λi : ι, f i • x).injective → ∃U : set α, is_open U ∧ x ∈ U ∧ (∀i j : ι, i ≠ j → disjoint (f i •'' U) (f j •'' U)) := begin
  intro f_injective,
  let disjoint_hyp := λi j (i_ne_j : i≠j), let x_moved : ((f j)⁻¹ * f i) • x ≠ x := begin
    by_contra,
    let := smul_congr (f j) h,
    rw [mul_smul, ← mul_smul,mul_right_inv,one_smul] at this,
    from i_ne_j (f_injective this),
  end in disjoint_nbhd x_moved,
  let ι2 := { p : ι×ι // p.1 ≠ p.2 },
  let U := ⋂(p : ι2), (disjoint_hyp p.1.1 p.1.2 p.2).some,
  use U,
  split,
  exact is_open_Inter (λp : ι2, (disjoint_hyp p.1.1 p.1.2 p.2).some_spec.1),
  split,
  exact set.mem_Inter.mpr (λp : ι2, (disjoint_hyp p.1.1 p.1.2 p.2).some_spec.2.1),
  intros i j i_ne_j,
  let U_inc := set.Inter_subset (λ p : ι2, (disjoint_hyp p.1.1 p.1.2 p.2).some) ⟨⟨i,j⟩,i_ne_j⟩,
  let := (disjoint_smul'' (f j) (set.disjoint_of_subset U_inc (smul''_subset ((f j)⁻¹ * (f i)) U_inc) (disjoint_hyp i j i_ne_j).some_spec.2.2)).symm,
  simp only [subtype.val_eq_coe, smul''_mul, mul_inv_cancel_left] at this,
  from this
end


lemma moves_inj {g : G} {x : α} {n : ℕ} (period_ge_n : ∀ (k : ℤ), 1 ≤ k → k < n → g ^ k • x ≠ x) : function.injective (λ (i : fin n), g ^ (i : ℤ) • x) := begin
    intros i j same_img,
    by_contra i_ne_j,

    let same_img' := congr_arg ((•) (g ^ (-(j : ℤ)))) same_img,
    simp only [inv_smul_smul] at same_img',
    rw [← mul_smul,← mul_smul,← zpow_add,← zpow_add,add_comm] at same_img',
    simp only [add_left_neg, zpow_zero, one_smul] at same_img',

    let ij := |(i:ℤ) - (j:ℤ)|,
    rw ← sub_eq_add_neg at same_img',
    have xfixed : g^ij • x = x := begin
      cases abs_cases ((i:ℤ) - (j:ℤ)),
      { rw ← h.1 at same_img', exact same_img' },
      { rw [smul_eq_iff_inv_smul_eq,← zpow_neg,← h.1] at same_img', exact same_img' }
    end,

    have ij_ge_1 : 1 ≤ ij := int.add_one_le_iff.mpr (abs_pos.mpr $ sub_ne_zero.mpr $ norm_num.nat_cast_ne i j ↑i ↑j rfl rfl (fin.vne_of_ne i_ne_j)),
    let neg_le := int.sub_lt_sub_of_le_of_lt (nat.cast_nonneg i) (nat.cast_lt.mpr (fin.prop _)),
    rw zero_sub at neg_le,
    let le_pos := int.sub_lt_sub_of_lt_of_le (nat.cast_lt.mpr (fin.prop _)) (nat.cast_nonneg j),
    rw sub_zero at le_pos,
    have ij_lt_n : ij < n := abs_lt.mpr ⟨ neg_le, le_pos ⟩,
    exact period_ge_n ij ij_ge_1 ij_lt_n xfixed,
end

lemma int_to_nat (k : ℤ) (k_pos : k ≥ 1) : k = k.nat_abs := begin
  cases (int.nat_abs_eq k),
  { exact h },
  { have : -(k.nat_abs : ℤ) ≤ 0 := neg_nonpos.mpr (int.nat_abs k).cast_nonneg,
    rw ← h at this, by_contra, linarith }
end

lemma moves_inj_N {g : G} {x : α} {n : ℕ} (period_ge_n' : ∀ (k : ℕ), 1 ≤ k → k < n → g ^ k • x ≠ x) : function.injective (λ (i : fin n), g ^ (i : ℕ) • x) := begin
  have period_ge_n : ∀ (k : ℤ), 1 ≤ k → k < n → g ^ k • x ≠ x,
  { intros k one_le_k k_lt_n,
    have one_le_k_nat : 1 ≤ k.nat_abs := ((int.coe_nat_le_coe_nat_iff 1 k.nat_abs).1 ((int_to_nat k one_le_k) ▸ one_le_k)),
    have k_nat_lt_n : k.nat_abs < n := ((int.coe_nat_lt_coe_nat_iff k.nat_abs n).1 ((int_to_nat k one_le_k) ▸ k_lt_n)),
    have := period_ge_n' k.nat_abs one_le_k_nat k_nat_lt_n,
    rw [(zpow_coe_nat g k.nat_abs).symm, (int_to_nat k one_le_k).symm] at this,
    exact this },
  have := moves_inj period_ge_n,
  finish
end


lemma moves_1234_of_moves_12 {g : G} {x : α} (xmoves : g^12 • x ≠ x) : function.injective (λi : fin 5, g^(i:ℤ) • x) := begin
    apply moves_inj,
    intros k k_ge_1 k_lt_5,
    by_contra xfixed,
    have k_div_12 : k * (12 / k) = 12 := begin
      interval_cases using k_ge_1 k_lt_5; norm_num
    end,
    have veryfixed : g^12 • x = x := begin
      let := smul_zpow_eq_of_smul_eq (12/k) xfixed,
      rw [← zpow_mul,k_div_12] at this,
      norm_cast at this
    end,
    exact xmoves veryfixed
end

lemma proposition_1_1_2 (f g : G) [t2_space α] : is_locally_moving G α → is_algebraically_disjoint f g → disjoint (support α f) (support α (g^12)) := begin
  intros locally_moving alg_disjoint,
-- suppose to the contrary that the set U = supp(f) ∩ supp(g^12) is nonempty
  by_contra not_disjoint,
  let U := support α f ∩ support α (g^12),
  have U_nonempty : U.nonempty := set.not_disjoint_iff_nonempty_inter.mp not_disjoint,
-- since X is Hausdorff, we can find a nonempty open set V ⊆ U such that f(V) is disjoint from V and the sets {g^i(V): i=0..4} are pairwise disjoint
  let x := U_nonempty.some,
  have five_points : function.injective (λi : fin 5, g^(i:ℤ) • x) := moves_1234_of_moves_12 (mem_support.mp $ (set.inter_subset_right _ _) U_nonempty.some_mem),
  rcases disjoint_nbhd_in (is_open.inter (support_open f) (support_open $ g^12)) U_nonempty.some_mem ((set.inter_subset_left _ _) U_nonempty.some_mem) with ⟨V₀,open_V₀,x_in_V₀,V₀_in_support,disjoint_img_V₀⟩,
  rcases disjoint_nbhd_fin five_points with ⟨V₁,open_V₁,x_in_V₁,disjoint_img_V₁⟩,
  simp only at disjoint_img_V₁,
  let V := V₀ ∩ V₁,
-- let h be a nontrivial element of rigid_stabilizer G V, and note that [f,h]≠1 since f(V) is disjoint from V
  let ristV_ne_bot := locally_moving V (is_open.inter open_V₀ open_V₁) (set.nonempty_of_mem ⟨x_in_V₀,x_in_V₁⟩),
  rcases (or_iff_right ristV_ne_bot).mp (subgroup.bot_or_exists_ne_one _) with ⟨h,h_in_ristV,h_ne_one⟩,
  have comm_non_trivial : ¬commute f h := begin
    by_contra comm_trivial,
    rcases faithful_rist_moves_point h_in_ristV h_ne_one with ⟨z,z_in_V,z_moved⟩,
    let act_comm := disjoint_support_comm h f (rist_supported_in_set h_in_ristV) (set.disjoint_of_subset (set.inter_subset_left V₀ V₁) (smul''_subset f (set.inter_subset_left V₀ V₁)) disjoint_img_V₀) z z_in_V,
    rw [commutator_element_eq_one_iff_commute.mpr comm_trivial.symm,one_smul] at act_comm,
    exact z_moved act_comm.symm,
  end,
-- since g is algebraically disjoint from f, there exist f₁,f₂ ∈ C_G(g) so that the commutator h' = [f1,[f2,h]] is a nontrivial element of C_G(g)
  rcases alg_disjoint h comm_non_trivial with ⟨f₁,f₂,f₁_commutes,f₂_commutes,h'_commutes,h'_non_trivial⟩,
  let h' := ⁅f₁,⁅f₂,h⁆⁆,
-- now observe that supp([f₂, h]) ⊆ V ∪ f₂(V), and by the same reasoning supp(h')⊆V∪f₁(V)∪f₂(V)∪f₁f₂(V)
  have support_f₂h : support α ⁅f₂,h⁆ ⊆ V ∪ (f₂ •'' V) := (support_comm α f₂ h).trans (set.union_subset_union (rist_supported_in_set h_in_ristV) $ smul''_subset f₂ $ rist_supported_in_set h_in_ristV),
  have support_h' : support α h' ⊆ ⋃(i : fin 2 × fin 2), (f₁^i.1.val*f₂^i.2.val) •'' V := begin
    let this := (support_comm α f₁ ⁅f₂,h⁆).trans (set.union_subset_union support_f₂h (smul''_subset f₁ support_f₂h)),
    rw [smul''_union,← one_smul'' V,← mul_smul'',← mul_smul'',← mul_smul'',mul_one,mul_one] at this,
    let rw_u := rewrite_Union (λi : fin 2 × fin 2, (f₁^i.1.val*f₂^i.2.val) •'' V),
    simp only [fin.val_eq_coe, fin.val_zero', pow_zero, mul_one, fin.val_one, pow_one, one_mul] at rw_u,
    exact rw_u.symm ▸ this,
  end,
-- since h' is nontrivial, it has at least one point p in its support
  cases faithful_moves_point' α h'_non_trivial with p p_moves,
-- since g commutes with h', all five of the points {gi(p):i=0..4} lie in supp(h')
  have gi_in_support : ∀i : fin 5, g^i.val • p ∈ support α h' := begin
    intro i,
    rw mem_support,
    by_contra p_fixed,
    rw [← mul_smul,(h'_commutes.pow_right i.val).eq,mul_smul,smul_left_cancel_iff] at p_fixed,
    exact p_moves p_fixed,
  end,
-- by the pigeonhole principle, one of the four sets V, f₁(V), f₂(V), f₁f₂(V) must contain two of these points, say g^i(p),g^j(p) ∈ k(V) for some 0 ≤ i < j ≤ 4 and k ∈ {1,f₁,f₂,f₁f₂}
  let pigeonhole : fintype.card (fin 5) > fintype.card (fin 2 × fin 2) := dec_trivial,
  let choice := λi : fin 5, (set.mem_Union.mp $ support_h' $ gi_in_support i).some,
  rcases finset.exists_ne_map_eq_of_card_lt_of_maps_to pigeonhole (λ(i : fin 5) _, finset.mem_univ (choice i)) with ⟨i,_,j,_,i_ne_j,same_choice⟩,
  clear h_1_w h_1_h_h_w pigeonhole,
  let k := f₁^(choice i).1.val*f₂^(choice i).2.val,
  have same_k : f₁^(choice j).1.val*f₂^(choice j).2.val = k := by { simp only at same_choice,
rw ← same_choice },
  have g_i : g^i.val • p ∈ k •'' V := (set.mem_Union.mp $ support_h' $ gi_in_support i).some_spec,
  have g_j : g^j.val • p ∈ k •'' V := same_k ▸ (set.mem_Union.mp $ support_h' $ gi_in_support j).some_spec,
-- but since g^(j−i)(V) is disjoint from V and k commutes with g, we know that g^(j−i)k(V) is disjoint from k(V), a contradiction since g^i(p) and g^j(p) both lie in k(V).
  have g_disjoint : disjoint ((g^i.val)⁻¹ •'' V) ((g^j.val)⁻¹ •'' V) := begin
    let := (disjoint_smul'' (g^(-(i.val+j.val : ℤ))) (disjoint_img_V₁ i j i_ne_j)).symm,
    rw [← mul_smul'',← mul_smul'',← zpow_add,← zpow_add] at this,
    simp only [fin.val_eq_coe, neg_add_rev, coe_coe, neg_add_cancel_right, zpow_neg, zpow_coe_nat, neg_add_cancel_comm] at this,
    from set.disjoint_of_subset (smul''_subset _ (set.inter_subset_right V₀ V₁)) (smul''_subset _ (set.inter_subset_right V₀ V₁)) this
  end,
  have k_commutes : commute k g := commute.mul_left (f₁_commutes.pow_left (choice i).1.val) (f₂_commutes.pow_left (choice i).2.val),
  have g_k_disjoint : disjoint ((g^i.val)⁻¹ •'' (k •'' V)) ((g^j.val)⁻¹ •'' (k •'' V)) := begin
    let this := disjoint_smul'' k g_disjoint,
    rw [← mul_smul'',← mul_smul'',← inv_pow g i.val,← inv_pow g j.val,
        ← (k_commutes.symm.inv_left.pow_left i.val).eq,
        ← (k_commutes.symm.inv_left.pow_left j.val).eq,
       mul_smul'',inv_pow g i.val,mul_smul'' (g⁻¹^j.val) k V,inv_pow g j.val] at this,
    from this
  end,
  exact set.disjoint_left.mp g_k_disjoint (mem_inv_smul''.mpr g_i) (mem_inv_smul''.mpr g_j)
end

lemma remark_1_2 (f g : G) : is_algebraically_disjoint f g → commute f g := begin
  intro alg_disjoint,
  by_contra non_commute,
  rcases alg_disjoint g non_commute with ⟨_,_,_,b,_,d⟩,
  rw [commutator_element_eq_one_iff_commute.mpr b,commutator_element_one_right] at d,
  tauto
end

section remark_1_3

def G := equiv.perm (fin 2)
def σ := equiv.swap (0 : fin 2) (1 : fin 2)

-- example : is_algebraically_disjoint σ σ := begin

--   intro h,
--   fin_cases h,
--   intro hyp1,
--   exfalso,
--   swap, intro hyp2, exfalso,

-- -- is commute decidable? cc,
-- sorry -- dec_trivial

-- end

end remark_1_3

end algebraic_disjointness

----------------------------------------------------------------
section regular_support

variables [topological_space α] [continuous_mul_action G α]

def interior_closure (U : set α) := interior (closure U)

lemma is_open_interior_closure (U : set α) : is_open (interior_closure U) := is_open_interior

lemma interior_closure_mono {U V : set α} : U ⊆ V → interior_closure U ⊆ interior_closure V :=
  interior_mono ∘ closure_mono

def set.is_regular_open (U : set α) := interior_closure U = U

lemma set.is_regular_def (U : set α) : U.is_regular_open ↔ interior_closure U = U := by refl

lemma is_open.in_closure {U : set α} : is_open U → U ⊆ interior (closure U) := begin
  intros U_open x x_in_U,
  apply interior_mono subset_closure,
  rw U_open.interior_eq,
  exact x_in_U
end

lemma is_open.interior_closure_subset {U : set α} : is_open U → U ⊆ interior_closure U :=
  λ h, (subset_interior_iff_is_open.mpr h).trans (interior_mono subset_closure)

lemma regular_interior_closure (U : set α) : (interior_closure U).is_regular_open := begin
  rw set.is_regular_def,
  apply set.subset.antisymm,
  exact interior_mono ((closure_mono interior_subset).trans (subset_of_eq closure_closure)),
  exact (subset_of_eq interior_interior.symm).trans (interior_mono subset_closure)
end

def regular_support (α : Type*) [topological_space α] [mul_action G α] (g : G) := interior_closure (support α g)

lemma regular_regular_support {g : G} : (regular_support α g).is_regular_open := regular_interior_closure _

lemma support_in_regular_support [t2_space α] (g : G) : support α g ⊆ regular_support α g := is_open.interior_closure_subset (support_open g)

lemma mem_regular_support (g : G) (U : set α) : U.is_regular_open → g ∈ rigid_stabilizer G U → regular_support α g ⊆ U :=
  λ U_ro g_moves, (set.is_regular_def _).mp U_ro ▸ (interior_closure_mono (rist_supported_in_set g_moves))

def algebraic_centralizer (f : G) : set G := { h | ∃g, h = g^12 ∧ is_algebraically_disjoint f g }

end regular_support

----------------------------------------------------------------
section finite_exponent

lemma coe_nat_fin {n i : ℕ} (h : i < n) : ∃ (i' : fin n), i = i' := ⟨ ⟨ i, h ⟩, rfl ⟩

variables [topological_space α] [continuous_mul_action G α] [has_faithful_smul G α]

lemma distinct_images_from_disjoint {g : G} {V : set α} {n : ℕ}
  (n_pos : 0 < n)
  (h_disj : ∀ (i j : fin n) (i_ne_j : i ≠ j), disjoint (g ^ (i : ℕ) •'' V) (g ^ (j : ℕ) •'' V)) :
  ∀ (q : α) (hq : q ∈ V) (i : fin n), (i : ℕ) > 0 → g ^ (i : ℕ) • (q : α) ∉ V :=
begin
  intros q hq i i_pos hcontra,
  have i_ne_zero : i ≠ (⟨ 0, n_pos ⟩ : fin n), { intro, finish },
  have hcontra' : g ^ (i : ℕ) • (q : α) ∈ g ^ (i : ℕ) •'' V, exact ⟨ q, hq, rfl ⟩,
  have giq_notin_V := set.disjoint_left.mp (h_disj i (⟨ 0, n_pos ⟩ : fin n) i_ne_zero) hcontra',
  exact ((by finish : g ^ 0•''V = V) ▸ giq_notin_V) hcontra
end

lemma moves_inj_period {g : G} {p : α} {n : ℕ} (period_eq_n : period p g = n) : function.injective (λ (i : fin n), g ^ (i : ℕ) • p) := begin
  have period_ge_n : ∀ (k : ℕ), 1 ≤ k → k < n → g ^ k • p ≠ p,
  { intros k one_le_k k_lt_n gkp_eq_p,
    have := period_le_fix (nat.succ_le_iff.mp one_le_k) gkp_eq_p,
    rw period_eq_n at this,
    linarith },
  exact moves_inj_N period_ge_n
end


lemma lemma_2_2 {α : Type u_2} [topological_space α] [continuous_mul_action G α] [has_faithful_smul G α] [t2_space α]
  (U : set α) (U_open : is_open U) (locally_moving : is_locally_moving G α) :
  U.nonempty → monoid.exponent (rigid_stabilizer G U) = 0 :=
begin
  intro U_nonempty,
  by_contra exp_ne_zero,
  rcases (period_from_exponent U U_nonempty exp_ne_zero) with ⟨ p, g, n, n_pos, hpgn, n_eq_Sup ⟩,
  rcases disjoint_nbhd_fin (moves_inj_period hpgn) with ⟨ V', V'_open, p_in_V', disj' ⟩,
  dsimp at disj',

  let V := U ∩ V',
  have V_ss_U : V ⊆ U := set.inter_subset_left U V',
  have V'_ss_V : V ⊆ V' := set.inter_subset_right U V',
  have V_open : is_open V := is_open.inter U_open V'_open,
  have p_in_V : (p : α) ∈ V := ⟨ subtype.mem p, p_in_V' ⟩,
  have disj : ∀ (i j : fin n), ¬ i = j → disjoint (↑g ^ ↑i•''V) (↑g ^ ↑j•''V),
  { intros i j i_ne_j W W_ss_giV W_ss_gjV,
    exact disj' i j i_ne_j
    (set.subset.trans W_ss_giV (smul''_subset (↑g ^ ↑i) V'_ss_V))
    (set.subset.trans W_ss_gjV (smul''_subset (↑g ^ ↑j) V'_ss_V)) },
  have ristV_ne_bot := locally_moving V V_open (set.nonempty_of_mem p_in_V),
  rcases (or_iff_right ristV_ne_bot).mp (subgroup.bot_or_exists_ne_one _) with ⟨h,h_in_ristV,h_ne_one⟩,
  rcases faithful_rist_moves_point h_in_ristV h_ne_one with ⟨ q, q_in_V, hq_ne_q ⟩,

  have hg_in_ristU : (h : G) * (g : G) ∈ rigid_stabilizer G U := (rigid_stabilizer G U).mul_mem' (rist_ss_rist V_ss_U h_in_ristV) (subtype.mem g),

  have giq_notin_V : ∀ (i : fin n), (i : ℕ) > 0 → g ^ (i : ℕ) • (q : α) ∉ V := distinct_images_from_disjoint n_pos disj q q_in_V,
  have giq_ne_q : ∀ (i : fin n), (i : ℕ) > 0 → g ^ (i : ℕ) • (q : α) ≠ (q : α),
  { intros i i_pos giq_eq_q, exact (giq_eq_q ▸ (giq_notin_V i i_pos)) q_in_V, },
  have q_in_U : q ∈ U, { have : q ∈ U ∩ V' := q_in_V, exact this.1 },

  -- We have (hg)^i q = g^i q for all 0 < i < n
  have pow_hgq_eq_pow_gq : ∀ (i : fin n), (i : ℕ) < n → (h * g) ^ (i : ℕ) • q = (g : G) ^ (i : ℕ) • q,
  { intros i, induction (i : ℕ) with i',
    { intro, repeat {rw pow_zero} },
    { intro succ_i'_lt_n,
      rw [smul_succ, ih (nat.lt_of_succ_lt succ_i'_lt_n), smul_smul, mul_assoc, ← smul_smul, ← smul_smul, ← smul_succ],
      have image_q_notin_V : g ^ i'.succ • q ∉ V,
      { have i'succ_ne_zero := ne_zero.pos i'.succ,
        exact giq_notin_V (⟨ i'.succ, succ_i'_lt_n ⟩ : fin n) i'succ_ne_zero },
      exact by_contradiction (λ c, c (by_contradiction (λ c', image_q_notin_V ((rist_supported_in_set h_in_ristV) c')))) } },

  -- Combined with g^i q ≠ q, this yields (hg)^i q ≠ q for all 0 < i < n
  have hgiq_ne_q : ∀ (i : fin n), (i : ℕ) > 0 → (h * g) ^ (i : ℕ) • q ≠ q,
  { intros i i_pos, rw pow_hgq_eq_pow_gq i (fin.is_lt i), by_contra c, exact (giq_notin_V i i_pos) (c.symm ▸ q_in_V) },

  -- This even holds for i = n
  have hgnq_ne_q : (h * g) ^ n • q ≠ q,
  { -- Rewrite (hg)^n q = hg^n q
    have npred_lt_n : n.pred < n, exact (nat.succ_pred_eq_of_pos n_pos) ▸ (lt_add_one n.pred),
    rcases coe_nat_fin npred_lt_n with ⟨ i', i'_eq_pred_n ⟩,
    have hgi'q_eq_gi'q := pow_hgq_eq_pow_gq i' (i'_eq_pred_n ▸ npred_lt_n),
    have : n = (i' : ℕ).succ := i'_eq_pred_n ▸ (nat.succ_pred_eq_of_pos n_pos).symm,
    rw [this, smul_succ, hgi'q_eq_gi'q, ← smul_smul, ← smul_succ, ← this],

    -- Now it follows from g^n q = q and h q ≠ q
    have n_le_period_qg := notfix_le_period' n_pos ((zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero (⟨ q, q_in_U ⟩ : U) g)).1 giq_ne_q,
    have period_qg_le_n := (zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero (⟨ q, q_in_U ⟩ : U) g).2, rw ← n_eq_Sup at period_qg_le_n,
    exact (ge_antisymm period_qg_le_n n_le_period_qg).symm ▸ ((pow_period_fix q (g : G)).symm ▸ hq_ne_q) },

  -- Finally, we derive a contradiction
  have period_pos_le_n := zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero (⟨ q, q_in_U ⟩ : U) (⟨ h * g, hg_in_ristU ⟩ : rigid_stabilizer G U),
  rw ← n_eq_Sup at period_pos_le_n,
  cases (lt_or_eq_of_le period_pos_le_n.2),
  { exact (hgiq_ne_q (⟨ (period (q : α) ((h : G) * (g : G))), h_1 ⟩ : fin n) period_pos_le_n.1) (pow_period_fix (q : α) ((h : G) * (g : G))) },
  { exact hgnq_ne_q (h_1 ▸ (pow_period_fix (q : α) ((h : G) * (g : G)))) }
end


lemma proposition_2_1 [t2_space α] (f : G) : is_locally_moving G α → (algebraic_centralizer f).centralizer = rigid_stabilizer G (regular_support α f) := sorry

end finite_exponent

variables [topological_space α] [topological_space β] [continuous_mul_action G α] [continuous_mul_action G β]

noncomputable theorem rubin (hα : rubin_action G α) (hβ : rubin_action G β) : equivariant_homeomorph G α β := sorry

end rubin
