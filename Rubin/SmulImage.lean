import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic

import Rubin.MulActionExt

namespace Rubin

/--
The image of a group action (here generalized to any pair `(G, α)` implementing `SMul`)
is the image of the elements of `U` under the `g • u` operation.

An alternative definition (which is available through the [`mem_smulImage`] theorem and the [`smulImage_set`] equality) would be:
`SmulImage g U = {x | g⁻¹ • x ∈ U}`.

The notation used for this operator is `g •'' U`.
-/
def SmulImage {G α : Type _} [SMul G α] (g : G) (U : Set α) :=
  (g • ·) '' U
#align subset_img Rubin.SmulImage

infixl:60 " •'' " => Rubin.SmulImage

/--
The pre-image of a group action (here generalized to any pair `(G, α)` implementing `SMul`)
is the set of values `x: α` such that `g • x ∈ U`.

Unlike [`SmulImage`], no notation is defined for this operator.
--/
def SmulPreImage {G α : Type _} [SMul G α] (g : G) (U : Set α) :=
  {x | g • x ∈ U}
#align subset_preimg' Rubin.SmulPreImage

variable {G α : Type _}
variable [Group G]
variable [MulAction G α]

theorem smulImage_def {g : G} {U : Set α} : g •'' U = (· • ·) g '' U :=
  rfl
#align subset_img_def Rubin.smulImage_def

theorem mem_smulImage {x : α} {g : G} {U : Set α} : x ∈ g •'' U ↔ g⁻¹ • x ∈ U :=
  by
  rw [Rubin.smulImage_def, Set.mem_image (g • ·) U x]
  constructor
  · rintro ⟨y, yU, gyx⟩
    let ygx : y = g⁻¹ • x := inv_smul_smul g y ▸ Rubin.smul_congr g⁻¹ gyx
    exact ygx ▸ yU
  · intro h
    exact ⟨g⁻¹ • x, ⟨Set.mem_preimage.mp h, smul_inv_smul g x⟩⟩
#align mem_smul'' Rubin.mem_smulImage

-- Provides a way to express a [`SmulImage`] as a `Set`;
-- this is simply [`mem_smulImage`] paired with set extensionality.
theorem smulImage_set {g: G} {U: Set α} : g •'' U = {x | g⁻¹ • x ∈ U} := Set.ext (fun _x => mem_smulImage)

theorem mem_inv_smulImage {x : α} {g : G} {U : Set α} : x ∈ g⁻¹ •'' U ↔ g • x ∈ U :=
  by
  let msi := @Rubin.mem_smulImage _ _ _ _ x g⁻¹ U
  rw [inv_inv] at msi
  exact msi
#align mem_inv_smul'' Rubin.mem_inv_smulImage

theorem mem_smulImage' {x : α} (g : G) {U : Set α} : x ∈ U ↔ g • x ∈ g •'' U :=
by
  rw [mem_smulImage]
  rw [<-mul_smul, mul_left_inv, one_smul]

-- TODO: rename to smulImage_mul
@[simp]
theorem mul_smulImage (g h : G) (U : Set α) : g •'' (h •'' U) = (g * h) •'' U :=
  by
  ext
  rw [Rubin.mem_smulImage, Rubin.mem_smulImage, Rubin.mem_smulImage, ←
    mul_smul, mul_inv_rev]
#align mul_smul'' Rubin.mul_smulImage

@[simp]
theorem one_smulImage (U : Set α) : (1 : G) •'' U = U :=
  by
  ext
  rw [Rubin.mem_smulImage, inv_one, one_smul]
#align one_smul'' Rubin.one_smulImage

theorem disjoint_smulImage (g : G) {U V : Set α} :
    Disjoint U V → Disjoint (g •'' U) (g •'' V) :=
  by
  intro disjoint_U_V
  rw [Set.disjoint_left]
  rw [Set.disjoint_left] at disjoint_U_V
  intro x x_in_gU
  by_contra h
  exact (disjoint_U_V (mem_smulImage.mp x_in_gU)) (mem_smulImage.mp h)
#align disjoint_smul'' Rubin.disjoint_smulImage

namespace SmulImage
theorem congr (g : G) {U V : Set α} : U = V → g •'' U = g •'' V :=
  congr_arg fun W : Set α => g •'' W
#align smul''_congr Rubin.SmulImage.congr
end SmulImage

theorem smulImage_subset (g : G) {U V : Set α} : U ⊆ V → g •'' U ⊆ g •'' V :=
  by
  intro h1 x
  rw [Rubin.mem_smulImage, Rubin.mem_smulImage]
  exact fun h2 => h1 h2
#align smul''_subset Rubin.smulImage_subset

theorem smulImage_union (g : G) {U V : Set α} : g •'' U ∪ V = (g •'' U) ∪ (g •'' V) :=
  by
  ext
  rw [Rubin.mem_smulImage, Set.mem_union, Set.mem_union, Rubin.mem_smulImage,
    Rubin.mem_smulImage]
#align smul''_union Rubin.smulImage_union

theorem smulImage_inter (g : G) {U V : Set α} : g •'' U ∩ V = (g •'' U) ∩ (g •'' V) :=
  by
  ext
  rw [Set.mem_inter_iff, Rubin.mem_smulImage, Rubin.mem_smulImage,
    Rubin.mem_smulImage, Set.mem_inter_iff]
#align smul''_inter Rubin.smulImage_inter

theorem smulImage_eq_inv_preimage {g : G} {U : Set α} : g •'' U = (g⁻¹ • ·) ⁻¹' U :=
  by
  ext
  constructor
  · intro h; rw [Set.mem_preimage]; exact mem_smulImage.mp h
  · intro h; rw [Rubin.mem_smulImage]; exact Set.mem_preimage.mp h
#align smul''_eq_inv_preimage Rubin.smulImage_eq_inv_preimage

theorem smulImage_eq_of_smul_eq {g h : G} {U : Set α} :
    (∀ x ∈ U, g • x = h • x) → g •'' U = h •'' U :=
  by
  intro hU
  ext x
  rw [Rubin.mem_smulImage, Rubin.mem_smulImage]
  constructor
  · intro k; let a := congr_arg (h⁻¹ • ·) (hU (g⁻¹ • x) k);
    simp only [smul_inv_smul, inv_smul_smul] at a ; exact Set.mem_of_eq_of_mem a k
  · intro k; let a := congr_arg (g⁻¹ • ·) (hU (h⁻¹ • x) k);
    simp only [smul_inv_smul, inv_smul_smul] at a ; exact Set.mem_of_eq_of_mem a.symm k
#align smul''_eq_of_smul_eq Rubin.smulImage_eq_of_smul_eq


theorem smulImage_subset_inv {G α : Type _} [Group G] [MulAction G α]
  (f : G) (U V : Set α) :
  f •'' U ⊆ V ↔ U ⊆ f⁻¹ •'' V :=
by
  constructor
  · intro h
    apply smulImage_subset f⁻¹ at h
    rw [mul_smulImage] at h
    rw [mul_left_inv, one_smulImage] at h
    exact h
  · intro h
    apply smulImage_subset f at h
    rw [mul_smulImage] at h
    rw [mul_right_inv, one_smulImage] at h
    exact h

theorem smulImage_subset_inv' {G α : Type _} [Group G] [MulAction G α]
  (f : G) (U V : Set α) :
  f⁻¹ •'' U ⊆ V ↔ U ⊆ f •'' V :=
by
  nth_rewrite 2 [<-inv_inv f]
  exact smulImage_subset_inv f⁻¹ U V

theorem smulImage_disjoint_mul {G α : Type _} [Group G] [MulAction G α]
  (f g : G) (U V : Set α) :
  Disjoint (f •'' U) (g •'' V) ↔ Disjoint U ((f⁻¹ * g) •'' V) := by
  constructor
  · intro h
    apply disjoint_smulImage f⁻¹ at h
    repeat rw [mul_smulImage] at h
    rw [mul_left_inv, one_smulImage] at h
    exact h

  · intro h
    apply disjoint_smulImage f at h
    rw [mul_smulImage] at h
    rw [<-mul_assoc] at h
    rw [mul_right_inv, one_mul] at h
    exact h

theorem smulImage_disjoint_inv_pow {G α : Type _} [Group G] [MulAction G α]
  (g : G) (i j : ℤ) (U V : Set α) :
  Disjoint (g^i •'' U) (g^j •'' V) ↔ Disjoint (g^(-j) •'' U) (g^(-i) •'' V) :=
by
  rw [smulImage_disjoint_mul]
  rw [<-zpow_neg, <-zpow_add, add_comm, zpow_add, zpow_neg]
  rw [<-inv_inv (g^j)]
  rw [<-smulImage_disjoint_mul]
  simp

theorem smulImage_disjoint_subset {G α : Type _} [Group G] [MulAction G α]
  {f g : G} {U V : Set α} (h_sub: U ⊆ V):
  Disjoint (f •'' V) (g •'' V) → Disjoint (f •'' U) (g •'' U) :=
by
  apply Set.disjoint_of_subset (smulImage_subset _ h_sub) (smulImage_subset _ h_sub)

-- States that if `g^i •'' V` and `g^j •'' V` are disjoint for any `i ≠ j` and `x ∈ V`
-- then `g^i • x` will always lie outside of `V`.
lemma smulImage_distinct_of_disjoint_exp {G α : Type _} [Group G] [MulAction G α] {g : G} {V : Set α} {n : ℕ}
  (n_pos : 0 < n)
  (h_disj : ∀ (i j : Fin n), i ≠ j → Disjoint (g ^ (i : ℕ) •'' V) (g ^ (j : ℕ) •'' V)) :
  ∀ (x : α) (_hx : x ∈ V) (i : Fin n), 0 < (i : ℕ) → g ^ (i : ℕ) • (x : α) ∉ V :=
by
  intro x hx i i_pos
  have i_ne_zero : i ≠ (⟨ 0, n_pos ⟩ : Fin n) := by
    intro h
    rw [h] at i_pos
    simp at i_pos

  have h_contra : g ^ (i : ℕ) • (x : α) ∈ g ^ (i : ℕ) •'' V := by use x

  have h_notin_V := Set.disjoint_left.mp (h_disj i (⟨0, n_pos⟩ : Fin n) i_ne_zero) h_contra
  simp only [pow_zero, one_smulImage] at h_notin_V
  exact h_notin_V
#align distinct_images_from_disjoint Rubin.smulImage_distinct_of_disjoint_exp

end Rubin
