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
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation
import Mathlib.Topology.Homeomorph

import Rubin.Tactic

#align_import rubin

namespace Rubin
open Rubin.Tactic

-- TODO: remove
--@[simp]
theorem GroupActionExt.smul_smul' {G α : Type _} [Group G] [MulAction G α] {g h : G} {x : α} :
    g • h • x = (g * h) • x :=
  smul_smul g h x
#align smul_smul' Rubin.GroupActionExt.smul_smul'

theorem equiv_congr_ne {ι ι' : Type _} (e : ι ≃ ι') {x y : ι} : x ≠ y → e x ≠ e y :=
  by
  intro x_ne_y
  by_contra h
  apply x_ne_y
  convert congr_arg e.symm h <;> simp only [Equiv.symm_apply_apply]
#align equiv.congr_ne Rubin.equiv_congr_ne

-- this definitely should be added to mathlib!
@[simp, to_additive]
theorem GroupActionExt.subgroup_mk_smul {G α : Type _} [Group G] [MulAction G α]
    {S : Subgroup G} {g : G} (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a :=
  rfl
#align Subgroup.mk_smul Rubin.GroupActionExt.subgroup_mk_smul
#align add_subgroup.mk_vadd AddSubgroup.mk_vadd

----------------------------------------------------------------
section Rubin

variable {G α β : Type _} [Group G]

----------------------------------------------------------------
section Groups

theorem bracket_mul {f g : G} : ⁅f, g⁆ = f * g * f⁻¹ * g⁻¹ := by tauto
#align bracket_mul Rubin.bracket_mul

def is_algebraically_disjoint (f g : G) :=
  ∀ h : G,
    ¬Commute f h →
      ∃ f₁ f₂ : G, Commute f₁ g ∧ Commute f₂ g ∧ Commute ⁅f₁, ⁅f₂, h⁆⁆ g ∧ ⁅f₁, ⁅f₂, h⁆⁆ ≠ 1
#align is_algebraically_disjoint Rubin.is_algebraically_disjoint

end Groups

----------------------------------------------------------------
section Actions

variable [MulAction G α]

@[simp]
theorem orbit_bot (G : Type _) [Group G] [MulAction G α] (p : α) :
    MulAction.orbit (⊥ : Subgroup G) p = {p} :=
  by
  ext1
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨_, g_bot⟩, g_to_x⟩
    rw [← g_to_x, Set.mem_singleton_iff, Rubin.GroupActionExt.subgroup_mk_smul]
    exact (Subgroup.mem_bot.mp g_bot).symm ▸ one_smul _ _
  exact fun h => ⟨1, Eq.trans (one_smul _ p) (Set.mem_singleton_iff.mp h).symm⟩
#align orbit_bot Rubin.orbit_bot

--------------------------------
section SmulImage

theorem GroupActionExt.smul_congr (g : G) {x y : α} (h : x = y) : g • x = g • y :=
  congr_arg ((· • ·) g) h
#align smul_congr Rubin.GroupActionExt.smul_congr

theorem GroupActionExt.smul_eq_iff_inv_smul_eq {x : α} {g : G} : g • x = x ↔ g⁻¹ • x = x :=
  ⟨fun h => (Rubin.GroupActionExt.smul_congr g⁻¹ h).symm.trans (inv_smul_smul g x), fun h =>
    (Rubin.GroupActionExt.smul_congr g h).symm.trans (smul_inv_smul g x)⟩
#align smul_eq_iff_inv_smul_eq Rubin.GroupActionExt.smul_eq_iff_inv_smul_eq

theorem GroupActionExt.smul_pow_eq_of_smul_eq {x : α} {g : G} (n : ℕ) :
    g • x = x → g ^ n • x = x := by
  induction n with
  | zero => simp only [pow_zero, one_smul, eq_self_iff_true, imp_true_iff]
  | succ n n_ih =>
    intro h
    nth_rw 2 [← (Rubin.GroupActionExt.smul_congr g (n_ih h)).trans h]
    rw [← mul_smul, ← pow_succ]
#align smul_pow_eq_of_smul_eq Rubin.GroupActionExt.smul_pow_eq_of_smul_eq

theorem GroupActionExt.smul_zpow_eq_of_smul_eq {x : α} {g : G} (n : ℤ) :
    g • x = x → g ^ n • x = x := by
  intro h
  cases n with
  | ofNat n => let res := Rubin.GroupActionExt.smul_pow_eq_of_smul_eq n h; simp; exact res
  | negSucc n =>
    let res :=
      smul_eq_iff_inv_smul_eq.mp (Rubin.GroupActionExt.smul_pow_eq_of_smul_eq (1 + n) h);
    simp
    rw [add_comm]
    exact res
#align smul_zpow_eq_of_smul_eq Rubin.GroupActionExt.smul_zpow_eq_of_smul_eq

def GroupActionExt.is_equivariant (G : Type _) {β : Type _} [Group G] [MulAction G α]
    [MulAction G β] (f : α → β) :=
  ∀ g : G, ∀ x : α, f (g • x) = g • f x
#align is_equivariant Rubin.GroupActionExt.is_equivariant

def SmulImage.smulImage' (g : G) (U : Set α) :=
  {x | g⁻¹ • x ∈ U}
#align subset_img' Rubin.SmulImage.smulImage'

def SmulImage.smul_preimage' (g : G) (U : Set α) :=
  {x | g • x ∈ U}
#align subset_preimg' Rubin.SmulImage.smul_preimage'

def SmulImage.SmulImage (g : G) (U : Set α) :=
  (· • ·) g '' U
#align subset_img Rubin.SmulImage.SmulImage

infixl:60 "•''" => Rubin.SmulImage.SmulImage

theorem SmulImage.smulImage_def {g : G} {U : Set α} : g•''U = (· • ·) g '' U :=
  rfl
#align subset_img_def Rubin.SmulImage.smulImage_def

theorem SmulImage.mem_smulImage {x : α} {g : G} {U : Set α} : x ∈ g•''U ↔ g⁻¹ • x ∈ U :=
  by
  rw [Rubin.SmulImage.smulImage_def, Set.mem_image ((· • ·) g) U x]
  constructor
  · rintro ⟨y, yU, gyx⟩
    let ygx : y = g⁻¹ • x := inv_smul_smul g y ▸ Rubin.GroupActionExt.smul_congr g⁻¹ gyx
    exact ygx ▸ yU
  · intro h
    exact ⟨g⁻¹ • x, ⟨Set.mem_preimage.mp h, smul_inv_smul g x⟩⟩
#align mem_smul'' Rubin.SmulImage.mem_smulImage

theorem SmulImage.mem_inv_smulImage {x : α} {g : G} {U : Set α} : x ∈ g⁻¹•''U ↔ g • x ∈ U :=
  by
  let msi := @Rubin.SmulImage.mem_smulImage _ _ _ _ x g⁻¹ U
  rw [inv_inv] at msi
  exact msi
#align mem_inv_smul'' Rubin.SmulImage.mem_inv_smulImage

theorem SmulImage.mul_smulImage (g h : G) (U : Set α) : g * h•''U = g•''(h•''U) :=
  by
  ext
  rw [Rubin.SmulImage.mem_smulImage, Rubin.SmulImage.mem_smulImage, Rubin.SmulImage.mem_smulImage, ←
    mul_smul, mul_inv_rev]
#align mul_smul'' Rubin.SmulImage.mul_smulImage

@[simp]
theorem SmulImage.smulImage_smulImage {g h : G} {U : Set α} : g•''(h•''U) = g * h•''U :=
  (Rubin.SmulImage.mul_smulImage g h U).symm
#align smul''_smul'' Rubin.SmulImage.smulImage_smulImage

@[simp]
theorem SmulImage.one_smulImage (U : Set α) : (1 : G)•''U = U :=
  by
  ext
  rw [Rubin.SmulImage.mem_smulImage, inv_one, one_smul]
#align one_smul'' Rubin.SmulImage.one_smulImage

theorem SmulImage.disjoint_smulImage (g : G) {U V : Set α} :
    Disjoint U V → Disjoint (g•''U) (g•''V) :=
  by
  intro disjoint_U_V
  rw [Set.disjoint_left]
  rw [Set.disjoint_left] at disjoint_U_V
  intro x x_in_gU
  by_contra h
  exact (disjoint_U_V (mem_smulImage.mp x_in_gU)) (mem_smulImage.mp h)
#align disjoint_smul'' Rubin.SmulImage.disjoint_smulImage

-- TODO: check if this is actually needed
theorem SmulImage.smulImage_congr (g : G) {U V : Set α} : U = V → g•''U = g•''V :=
  congr_arg fun W : Set α => g•''W
#align smul''_congr Rubin.SmulImage.smulImage_congr

theorem SmulImage.smulImage_subset (g : G) {U V : Set α} : U ⊆ V → g•''U ⊆ g•''V :=
  by
  intro h1 x
  rw [Rubin.SmulImage.mem_smulImage, Rubin.SmulImage.mem_smulImage]
  exact fun h2 => h1 h2
#align smul''_subset Rubin.SmulImage.smulImage_subset

theorem SmulImage.smulImage_union (g : G) {U V : Set α} : g•''U ∪ V = (g•''U) ∪ (g•''V) :=
  by
  ext
  rw [Rubin.SmulImage.mem_smulImage, Set.mem_union, Set.mem_union, Rubin.SmulImage.mem_smulImage,
    Rubin.SmulImage.mem_smulImage]
#align smul''_union Rubin.SmulImage.smulImage_union

theorem SmulImage.smulImage_inter (g : G) {U V : Set α} : g•''U ∩ V = (g•''U) ∩ (g•''V) :=
  by
  ext
  rw [Set.mem_inter_iff, Rubin.SmulImage.mem_smulImage, Rubin.SmulImage.mem_smulImage,
    Rubin.SmulImage.mem_smulImage, Set.mem_inter_iff]
#align smul''_inter Rubin.SmulImage.smulImage_inter

theorem SmulImage.smulImage_eq_inv_preimage {g : G} {U : Set α} : g•''U = (· • ·) g⁻¹ ⁻¹' U :=
  by
  ext
  constructor
  · intro h; rw [Set.mem_preimage]; exact mem_smulImage.mp h
  · intro h; rw [Rubin.SmulImage.mem_smulImage]; exact Set.mem_preimage.mp h
#align smul''_eq_inv_preimage Rubin.SmulImage.smulImage_eq_inv_preimage

theorem SmulImage.smulImage_eq_of_smul_eq {g h : G} {U : Set α} :
    (∀ x ∈ U, g • x = h • x) → g•''U = h•''U :=
  by
  intro hU
  ext x
  rw [Rubin.SmulImage.mem_smulImage, Rubin.SmulImage.mem_smulImage]
  constructor
  · intro k; let a := congr_arg ((· • ·) h⁻¹) (hU (g⁻¹ • x) k);
    simp only [smul_inv_smul, inv_smul_smul] at a ; exact Set.mem_of_eq_of_mem a k
  · intro k; let a := congr_arg ((· • ·) g⁻¹) (hU (h⁻¹ • x) k);
    simp only [smul_inv_smul, inv_smul_smul] at a ; exact Set.mem_of_eq_of_mem a.symm k
#align smul''_eq_of_smul_eq Rubin.SmulImage.smulImage_eq_of_smul_eq

end SmulImage

--------------------------------
section Support

def SmulSupport.Support (α : Type _) [MulAction G α] (g : G) :=
  {x : α | g • x ≠ x}
#align support Rubin.SmulSupport.Support

theorem SmulSupport.support_eq_not_fixed_by {g : G}:
    Rubin.SmulSupport.Support α g = (MulAction.fixedBy α g)ᶜ := by tauto
#align support_eq_not_fixed_by Rubin.SmulSupport.support_eq_not_fixed_by

theorem SmulSupport.mem_support {x : α} {g : G} :
    x ∈ Rubin.SmulSupport.Support α g ↔ g • x ≠ x := by tauto
#align mem_support Rubin.SmulSupport.mem_support

theorem SmulSupport.not_mem_support {x : α} {g : G} :
    x ∉ Rubin.SmulSupport.Support α g ↔ g • x = x := by
  rw [Rubin.SmulSupport.mem_support, Classical.not_not]
#align mem_not_support Rubin.SmulSupport.not_mem_support

theorem SmulSupport.smul_mem_support {g : G} {x : α} :
    x ∈ Rubin.SmulSupport.Support α g → g • x ∈ Rubin.SmulSupport.Support α g := fun h =>
  h ∘ smul_left_cancel g
#align smul_in_support Rubin.SmulSupport.smul_mem_support

theorem SmulSupport.inv_smul_mem_support {g : G} {x : α} :
    x ∈ Rubin.SmulSupport.Support α g → g⁻¹ • x ∈ Rubin.SmulSupport.Support α g := fun h k =>
  h (smul_inv_smul g x ▸ Rubin.GroupActionExt.smul_congr g k)
#align inv_smul_in_support Rubin.SmulSupport.inv_smul_mem_support

theorem SmulSupport.fixed_of_disjoint {g : G} {x : α} {U : Set α} :
    x ∈ U → Disjoint U (Rubin.SmulSupport.Support α g) → g • x = x :=
  fun x_in_U disjoint_U_support =>
  Rubin.SmulSupport.not_mem_support.mp (Set.disjoint_left.mp disjoint_U_support x_in_U)
#align fixed_of_disjoint Rubin.SmulSupport.fixed_of_disjoint

theorem SmulSupport.fixed_smulImage_in_support (g : G) {U : Set α} :
    Rubin.SmulSupport.Support α g ⊆ U → g•''U = U :=
  by
  intro support_in_U
  ext x
  cases' @or_not (x ∈ Rubin.SmulSupport.Support α g) with xmoved xfixed
  exact
    ⟨fun _ => support_in_U xmoved, fun _ =>
      SmulImage.mem_smulImage.mpr (support_in_U (Rubin.SmulSupport.inv_smul_mem_support xmoved))⟩
  rw [Rubin.SmulImage.mem_smulImage, GroupActionExt.smul_eq_iff_inv_smul_eq.mp (not_mem_support.mp xfixed)]
#align fixes_subset_within_support Rubin.SmulSupport.fixed_smulImage_in_support

theorem SmulSupport.smulImage_subset_in_support (g : G) (U V : Set α) :
    U ⊆ V → Rubin.SmulSupport.Support α g ⊆ V → g•''U ⊆ V := fun U_in_V support_in_V =>
  Rubin.SmulSupport.fixed_smulImage_in_support g support_in_V ▸
    Rubin.SmulImage.smulImage_subset g U_in_V
#align moves_subset_within_support Rubin.SmulSupport.smulImage_subset_in_support

theorem SmulSupport.support_mul (g h : G) (α : Type _) [MulAction G α] :
    Rubin.SmulSupport.Support α (g * h) ⊆
      Rubin.SmulSupport.Support α g ∪ Rubin.SmulSupport.Support α h :=
  by
  intro x x_in_support
  by_contra h_support

  let res := not_or.mp h_support
  exact
    x_in_support
      ((mul_smul g h x).trans
        ((congr_arg ((· • ·) g) (not_mem_support.mp res.2)).trans <| not_mem_support.mp res.1))
#align support_mul Rubin.SmulSupport.support_mul

theorem SmulSupport.support_conjugate (α : Type _) [MulAction G α] (g h : G) :
    Rubin.SmulSupport.Support α (h * g * h⁻¹) = h•''Rubin.SmulSupport.Support α g :=
  by
  ext x
  rw [Rubin.SmulSupport.mem_support, Rubin.SmulImage.mem_smulImage, Rubin.SmulSupport.mem_support,
    mul_smul, mul_smul]
  constructor
  · intro h1; by_contra h2; exact h1 ((congr_arg ((· • ·) h) h2).trans (smul_inv_smul _ _))
  · intro h1; by_contra h2; exact h1 (inv_smul_smul h (g • h⁻¹ • x) ▸ congr_arg ((· • ·) h⁻¹) h2)
#align support_conjugate Rubin.SmulSupport.support_conjugate

theorem SmulSupport.support_inv (α : Type _) [MulAction G α] (g : G) :
    Rubin.SmulSupport.Support α g⁻¹ = Rubin.SmulSupport.Support α g :=
  by
  ext x
  rw [Rubin.SmulSupport.mem_support, Rubin.SmulSupport.mem_support]
  constructor
  · intro h1; by_contra h2; exact h1 (GroupActionExt.smul_eq_iff_inv_smul_eq.mp h2)
  · intro h1; by_contra h2; exact h1 (GroupActionExt.smul_eq_iff_inv_smul_eq.mpr h2)
#align support_inv Rubin.SmulSupport.support_inv

theorem SmulSupport.support_pow (α : Type _) [MulAction G α] (g : G) (j : ℕ) :
    Rubin.SmulSupport.Support α (g ^ j) ⊆ Rubin.SmulSupport.Support α g :=
  by
  intro x xmoved
  by_contra xfixed
  rw [Rubin.SmulSupport.mem_support] at xmoved
  induction j with
  | zero => apply xmoved; rw [pow_zero g, one_smul]
  | succ j j_ih =>
    apply xmoved
    let j_ih := (congr_arg ((· • ·) g) (not_not.mp j_ih)).trans (not_mem_support.mp xfixed)
    simp at j_ih
    rw [← mul_smul, ← pow_succ] at j_ih
    exact j_ih
#align support_pow Rubin.SmulSupport.support_pow

theorem SmulSupport.support_comm (α : Type _) [MulAction G α] (g h : G) :
    Rubin.SmulSupport.Support α ⁅g, h⁆ ⊆
      Rubin.SmulSupport.Support α h ∪ (g•''Rubin.SmulSupport.Support α h) :=
  by
  intro x x_in_support
  by_contra all_fixed
  rw [Set.mem_union] at all_fixed
  cases' @or_not (h • x = x) with xfixed xmoved
  · rw [Rubin.SmulSupport.mem_support, Rubin.bracket_mul, mul_smul,
      GroupActionExt.smul_eq_iff_inv_smul_eq.mp xfixed, ← Rubin.SmulSupport.mem_support] at x_in_support
    exact
      ((Rubin.SmulSupport.support_conjugate α h g).symm ▸ (not_or.mp all_fixed).2)
        x_in_support
  · exact all_fixed (Or.inl xmoved)
#align support_comm Rubin.SmulSupport.support_comm

theorem SmulSupport.disjoint_support_comm (f g : G) {U : Set α} :
    Rubin.SmulSupport.Support α f ⊆ U → Disjoint U (g•''U) → ∀ x ∈ U, ⁅f, g⁆ • x = f • x :=
  by
  intro support_in_U disjoint_U x x_in_U
  have support_conj : Rubin.SmulSupport.Support α (g * f⁻¹ * g⁻¹) ⊆ g•''U :=
    ((Rubin.SmulSupport.support_conjugate α f⁻¹ g).trans
          (Rubin.SmulImage.smulImage_congr g (Rubin.SmulSupport.support_inv α f))).symm ▸
      Rubin.SmulImage.smulImage_subset g support_in_U
  have goal :=
    (congr_arg ((· • ·) f)
        (Rubin.SmulSupport.fixed_of_disjoint x_in_U
          (Set.disjoint_of_subset_right support_conj disjoint_U))).symm
  simp at goal
  sorry
  -- rw [mul_smul, mul_smul] at goal

  -- exact goal.symm
#align disjoint_support_comm Rubin.SmulSupport.disjoint_support_comm

end Support

-- comment by Cedric: would be nicer to define just a subset, and then show it is a subgroup
def rigidStabilizer' (G : Type _) [Group G] [MulAction G α] (U : Set α) : Set G :=
  {g : G | ∀ x : α, g • x = x ∨ x ∈ U}
#align rigid_stabilizer' Rubin.rigidStabilizer'

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (x «expr ∉ » U) -/
def rigidStabilizer (G : Type _) [Group G] [MulAction G α] (U : Set α) : Subgroup G
    where
  carrier := {g : G | ∀ (x) (_ : x ∉ U), g • x = x}
  mul_mem' ha hb x x_notin_U := by rw [mul_smul, hb x x_notin_U, ha x x_notin_U]
  inv_mem' hg x x_notin_U := Rubin.GroupActionExt.smul_eq_iff_inv_smul_eq.mp (hg x x_notin_U)
  one_mem' x _ := one_smul G x
#align rigid_stabilizer Rubin.rigidStabilizer

theorem rist_supported_in_set {g : G} {U : Set α} :
    g ∈ rigidStabilizer G U → Rubin.SmulSupport.Support α g ⊆ U := fun h x x_in_support =>
  by_contradiction (x_in_support ∘ h x)
#align rist_supported_in_set Rubin.rist_supported_in_set

theorem rist_ss_rist {U V : Set α} (V_ss_U : V ⊆ U) :
    (rigidStabilizer G V : Set G) ⊆ (rigidStabilizer G U : Set G) :=
  by
  intro g g_in_ristV x x_notin_U
  have x_notin_V : x ∉ V := by intro x_in_V; exact x_notin_U (V_ss_U x_in_V)
  exact g_in_ristV x x_notin_V
#align rist_ss_rist Rubin.rist_ss_rist

end Actions

----------------------------------------------------------------
section TopologicalActions

variable [TopologicalSpace α] [TopologicalSpace β]

class Topological.ContinuousMulAction (G α : Type _) [Group G] [TopologicalSpace α] extends
    MulAction G α where
  continuous : ∀ g : G, Continuous (@SMul.smul G α _ g)
#align continuous_mul_action Rubin.Topological.ContinuousMulAction

structure Topological.equivariant_homeomorph (G α β : Type _) [Group G] [TopologicalSpace α]
    [TopologicalSpace β] [MulAction G α] [MulAction G β] extends Homeomorph α β where
  equivariant : GroupActionExt.is_equivariant G toFun
#align equivariant_homeomorph Rubin.Topological.equivariant_homeomorph

theorem Topological.equivariant_fun [MulAction G α] [MulAction G β]
    (h : Rubin.Topological.equivariant_homeomorph G α β) :
    Rubin.GroupActionExt.is_equivariant G h.toFun :=
  h.equivariant
#align equivariant_fun Rubin.Topological.equivariant_fun

theorem Topological.equivariant_inv [MulAction G α] [MulAction G β]
    (h : Rubin.Topological.equivariant_homeomorph G α β) :
    Rubin.GroupActionExt.is_equivariant G h.invFun :=
  by
  intro g x
  symm
  let e := congr_arg h.invFun (h.equivariant g (h.invFun x))
  rw [h.left_inv _, h.right_inv _] at e
  exact e
#align equivariant_inv Rubin.Topological.equivariant_inv

variable [Rubin.Topological.ContinuousMulAction G α]

theorem Topological.img_open_open (g : G) (U : Set α) (h : IsOpen U)
    [Rubin.Topological.ContinuousMulAction G α] : IsOpen (g•''U) :=
  by
  rw [Rubin.SmulImage.smulImage_eq_inv_preimage]
  exact Continuous.isOpen_preimage (Rubin.Topological.ContinuousMulAction.continuous g⁻¹) U h
#align img_open_open Rubin.Topological.img_open_open

theorem Topological.support_open (g : G) [TopologicalSpace α] [T2Space α]
    [Rubin.Topological.ContinuousMulAction G α] : IsOpen (Rubin.SmulSupport.Support α g) :=
  by
  apply isOpen_iff_forall_mem_open.mpr
  intro x xmoved
  rcases T2Space.t2 (g • x) x xmoved with ⟨U, V, open_U, open_V, gx_in_U, x_in_V, disjoint_U_V⟩
  exact
    ⟨V ∩ (g⁻¹•''U), fun y yW =>
      -- TODO: don't use @-notation here
      @Disjoint.ne_of_mem α U V disjoint_U_V (g • y)
      (SmulImage.mem_inv_smulImage.mp (Set.mem_of_mem_inter_right yW))
      y
      (Set.mem_of_mem_inter_left yW),
      IsOpen.inter open_V (Rubin.Topological.img_open_open g⁻¹ U open_U),
      ⟨x_in_V, SmulImage.mem_inv_smulImage.mpr gx_in_U⟩⟩
#align support_open Rubin.Topological.support_open

end TopologicalActions

----------------------------------------------------------------
section FaithfulActions

variable [MulAction G α] [FaithfulSMul G α]

theorem faithful_moves_point₁ {g : G} (h2 : ∀ x : α, g • x = x) : g = 1 :=
  haveI h3 : ∀ x : α, g • x = (1 : G) • x := fun x => (h2 x).symm ▸ (one_smul G x).symm
  eq_of_smul_eq_smul h3
#align faithful_moves_point Rubin.faithful_moves_point₁

theorem faithful_moves_point'₁ {g : G} (α : Type _) [MulAction G α] [FaithfulSMul G α] :
    g ≠ 1 → ∃ x : α, g • x ≠ x := fun k =>
  by_contradiction fun h => k <| Rubin.faithful_moves_point₁ <| Classical.not_exists_not.mp h
#align faithful_moves_point' Rubin.faithful_moves_point'₁

theorem faithful_rigid_stabilizer_moves_point {g : G} {U : Set α} :
    g ∈ rigidStabilizer G U → g ≠ 1 → ∃ x ∈ U, g • x ≠ x :=
  by
  intro g_rigid g_ne_one
  rcases Rubin.faithful_moves_point'₁ α g_ne_one with ⟨x, xmoved⟩
  exact ⟨x, rist_supported_in_set g_rigid xmoved, xmoved⟩
#align faithful_rist_moves_point Rubin.faithful_rigid_stabilizer_moves_point

theorem ne_one_support_nonempty {g : G} : g ≠ 1 → (Rubin.SmulSupport.Support α g).Nonempty :=
  by
  intro h1
  cases' Rubin.faithful_moves_point'₁ α h1 with x h
  use x
  exact h
#align ne_one_support_nempty Rubin.ne_one_support_nonempty

-- FIXME: somehow clashes with another definition
theorem disjoint_commute₁ {f g : G} :
    Disjoint (Rubin.SmulSupport.Support α f) (Rubin.SmulSupport.Support α g) → Commute f g :=
  by
  intro hdisjoint
  rw [← commutatorElement_eq_one_iff_commute]
  apply @Rubin.faithful_moves_point₁ _ α
  intro x
  rw [Rubin.bracket_mul, mul_smul, mul_smul, mul_smul]
  cases' @or_not (x ∈ Rubin.SmulSupport.Support α f) with hfmoved hffixed
  ·
    rw [GroupActionExt.smul_eq_iff_inv_smul_eq.mp (SmulSupport.not_mem_support.mp (Set.disjoint_left.mp hdisjoint hfmoved)),
      SmulSupport.not_mem_support.mp
        (Set.disjoint_left.mp hdisjoint (Rubin.SmulSupport.inv_smul_mem_support hfmoved)),
      smul_inv_smul]
  cases' @or_not (x ∈ Rubin.SmulSupport.Support α g) with hgmoved hgfixed
  ·
    rw [GroupActionExt.smul_eq_iff_inv_smul_eq.mp
        (SmulSupport.not_mem_support.mp <|
          Set.disjoint_right.mp hdisjoint (Rubin.SmulSupport.inv_smul_mem_support hgmoved)),
      smul_inv_smul, SmulSupport.not_mem_support.mp hffixed]
  ·
    rw [
      GroupActionExt.smul_eq_iff_inv_smul_eq.mp (SmulSupport.not_mem_support.mp hgfixed),
      GroupActionExt.smul_eq_iff_inv_smul_eq.mp (SmulSupport.not_mem_support.mp hffixed),
      SmulSupport.not_mem_support.mp hgfixed,
      SmulSupport.not_mem_support.mp hffixed
    ]
#align disjoint_commute Rubin.disjoint_commute₁

end FaithfulActions

----------------------------------------------------------------
section RubinActions

variable [TopologicalSpace α] [TopologicalSpace β]

def has_no_isolated_points (α : Type _) [TopologicalSpace α] :=
  ∀ x : α, (nhdsWithin x ({x}ᶜ)) ≠ ⊥
#align has_no_isolated_points Rubin.has_no_isolated_points

def is_locally_dense (G α : Type _) [Group G] [TopologicalSpace α] [MulAction G α] :=
  ∀ U : Set α, ∀ p ∈ U, p ∈ interior (closure (MulAction.orbit (rigidStabilizer G U) p))
#align is_locally_dense Rubin.is_locally_dense

structure RubinAction (G α : Type _) extends Group G, TopologicalSpace α, MulAction G α,
    FaithfulSMul G α where
  locally_compact : LocallyCompactSpace α
  hausdorff : T2Space α
  no_isolated_points : Rubin.has_no_isolated_points α
  locallyDense : Rubin.is_locally_dense G α
#align rubin_action Rubin.RubinAction

end RubinActions

----------------------------------------------------------------
section Rubin.Period.period

variable [MulAction G α]

noncomputable def Period.period (p : α) (g : G) : ℕ :=
  sInf {n : ℕ | n > 0 ∧ g ^ n • p = p}
#align period Rubin.Period.period

theorem Period.period_le_fix {p : α} {g : G} {m : ℕ} (m_pos : m > 0)
    (gmp_eq_p : g ^ m • p = p) : 0 < Rubin.Period.period p g ∧ Rubin.Period.period p g ≤ m :=
  by
  constructor
  · by_contra h'; have period_zero : Rubin.Period.period p g = 0; linarith;
    rcases Nat.sInf_eq_zero.1 period_zero with ⟨cont, h_1⟩ | h; linarith;
    exact Set.eq_empty_iff_forall_not_mem.mp h ↑m ⟨m_pos, gmp_eq_p⟩
  exact Nat.sInf_le ⟨m_pos, gmp_eq_p⟩
#align period_le_fix Rubin.Period.period_le_fix

theorem Period.notfix_le_period {p : α} {g : G} {n : ℕ} (n_pos : n > 0)
    (period_pos : Rubin.Period.period p g > 0) (pmoves : ∀ i : ℕ, 0 < i → i < n → g ^ i • p ≠ p) :
    n ≤ Rubin.Period.period p g := by
  by_contra period_le
  exact
    (pmoves (Rubin.Period.period p g) period_pos (not_le.mp period_le))
      (Nat.sInf_mem (Nat.nonempty_of_pos_sInf period_pos)).2
#align notfix_le_period Rubin.Period.notfix_le_period

theorem Period.notfix_le_period' {p : α} {g : G} {n : ℕ} (n_pos : n > 0)
    (period_pos : Rubin.Period.period p g > 0)
    (pmoves : ∀ i : Fin n, 0 < (i : ℕ) → g ^ (i : ℕ) • p ≠ p) : n ≤ Rubin.Period.period p g :=
  Rubin.Period.notfix_le_period n_pos period_pos fun (i : ℕ) (i_pos : 0 < i) (i_lt_n : i < n) =>
    pmoves (⟨i, i_lt_n⟩ : Fin n) i_pos
#align notfix_le_period' Rubin.Period.notfix_le_period'

theorem Period.period_neutral_eq_one (p : α) : Rubin.Period.period p (1 : G) = 1 :=
  by
  have : 0 < Rubin.Period.period p (1 : G) ∧ Rubin.Period.period p (1 : G) ≤ 1 :=
    Rubin.Period.period_le_fix (by norm_num : 1 > 0)
      (by group_action :
        (1 : G) ^ 1 • p = p)
  linarith
#align period_neutral_eq_one Rubin.Period.period_neutral_eq_one

def Period.periods (U : Set α) (H : Subgroup G) : Set ℕ :=
  {n : ℕ | ∃ (p : α) (g : H), p ∈ U ∧ Rubin.Period.period (p : α) (g : G) = n}
#align periods Rubin.Period.periods

-- TODO: split into multiple lemmas
theorem Period.periods_lemmas {U : Set α} (U_nonempty : Set.Nonempty U) {H : Subgroup G}
    (exp_ne_zero : Monoid.exponent H ≠ 0) :
    (Rubin.Period.periods U H).Nonempty ∧
      BddAbove (Rubin.Period.periods U H) ∧
        ∃ (m : ℕ) (m_pos : m > 0), ∀ (p : α) (g : H), g ^ m • p = p :=
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

theorem Period.period_from_exponent (U : Set α) (U_nonempty : U.Nonempty) {H : Subgroup G}
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

theorem Period.zero_lt_period_le_Sup_periods {U : Set α} (U_nonempty : U.Nonempty)
    {H : Subgroup G} (exp_ne_zero : Monoid.exponent H ≠ 0) :
    ∀ (p : U) (g : H),
      0 < Rubin.Period.period (p : α) (g : G) ∧
        Rubin.Period.period (p : α) (g : G) ≤ sSup (Rubin.Period.periods U H) :=
  by
  rcases Rubin.Period.periods_lemmas U_nonempty exp_ne_zero with
    ⟨periods_nonempty, periods_bounded, m, m_pos, gmp_eq_p⟩
  intro p g
  have period_in_periods : Rubin.Period.period (p : α) (g : G) ∈ Rubin.Period.periods U H := by
    use p; use g
    simp
  exact
    ⟨(Rubin.Period.period_le_fix m_pos (gmp_eq_p p g)).1,
      le_csSup periods_bounded period_in_periods⟩
#align zero_lt_period_le_Sup_periods Rubin.Period.zero_lt_period_le_Sup_periods

theorem Period.pow_period_fix (p : α) (g : G) : g ^ Rubin.Period.period p g • p = p :=
  by
  cases eq_zero_or_neZero (Rubin.Period.period p g) with
  | inl h => rw [h]; simp
  | inr h =>
    exact
      (Nat.sInf_mem
          (Nat.nonempty_of_pos_sInf
            (Nat.pos_of_ne_zero (@NeZero.ne _ _ (Rubin.Period.period p g) h)))).2
#align pow_period_fix Rubin.Period.pow_period_fix

end Rubin.Period.period

----------------------------------------------------------------
section AlgebraicDisjointness

variable [TopologicalSpace α] [Rubin.Topological.ContinuousMulAction G α] [FaithfulSMul G α]

def Disjointness.IsLocallyMoving (G α : Type _) [Group G] [TopologicalSpace α]
    [MulAction G α] :=
  ∀ U : Set α, IsOpen U → Set.Nonempty U → rigidStabilizer G U ≠ ⊥
#align is_locally_moving Rubin.Disjointness.IsLocallyMoving

-- lemma dense_locally_moving : t2_space α ∧ has_no_isolated_points α ∧ is_locally_dense G α → is_locally_moving G α := begin
--   rintros ⟨t2α,nipα,ildGα⟩ U ioU neU,
--   by_contra,
--   have some_in_U := ildGα U neU.some neU.some_mem,
--   rw [h,orbit_bot G neU.some,@closure_singleton α _ (@t2_space.t1_space α _ t2α) neU.some,@interior_singleton α _ neU.some (nipα neU.some)] at some_in_U,
--   tauto
-- end
-- lemma disjoint_nbhd {g : G} {x : α} [t2_space α] : g • x ≠ x → ∃U : set α, is_open U ∧ x ∈ U ∧ disjoint U (g •'' U) := begin
--   intro xmoved,
--   rcases t2_space.t2 (g • x) x xmoved with ⟨V,W,open_V,open_W,gx_in_V,x_in_W,disjoint_V_W⟩,
--   let U := (g⁻¹ •'' V) ∩ W,
--   use U,
--   split,
--   exact is_open.inter (img_open_open g⁻¹ V open_V) open_W,
--   split,
--   exact ⟨mem_inv_smul''.mpr gx_in_V,x_in_W⟩,
--   exact Set.disjoint_of_subset
--     (Set.inter_subset_right (g⁻¹•''V) W)
--     (λ y hy, smul_inv_smul g y ▸ mem_inv_smul''.mp (Set.mem_of_mem_inter_left (mem_smulImage.mp hy)) : g•''U ⊆ V)
--     disjoint_V_W.symm
-- end
-- lemma disjoint_nbhd_in {g : G} {x : α} [t2_space α] {V : set α} : is_open V → x ∈ V → g • x ≠ x → ∃U : set α, is_open U ∧ x ∈ U ∧ U ⊆ V ∧ disjoint U (g •'' U) := begin
--   intros open_V x_in_V xmoved,
--   rcases disjoint_nbhd xmoved with ⟨W,open_W,x_in_W,disjoint_W⟩,
--   let U := W ∩ V,
--   use U,
--   split,
--   exact is_open.inter open_W open_V,
--   split,
--   exact ⟨x_in_W,x_in_V⟩,
--   split,
--   exact Set.inter_subset_right W V,
--   exact Set.disjoint_of_subset
--     (Set.inter_subset_left W V)
--     ((@smul''_inter _ _ _ _ g W V).symm ▸ Set.inter_subset_left (g•''W) (g•''V) : g•''U ⊆ g•''W)
--     disjoint_W
-- end
-- lemma rewrite_Union (f : fin 2 × fin 2 → set α) : (⋃(i : fin 2 × fin 2), f i) = (f (0,0) ∪ f (0,1)) ∪ (f (1,0) ∪ f (1,1)) := begin
--   ext,
--   simp only [Set.mem_Union, Set.mem_union],
--   split,
--   { simp only [forall_exists_index],
--     intro i,
--     fin_cases i; simp {contextual := tt}, },
--   { rintro ((h|h)|(h|h)); exact ⟨_, h⟩, },
-- end
-- lemma proposition_1_1_1 (f g : G) (locally_moving : is_locally_moving G α) [t2_space α] : disjoint (support α f) (support α g) → is_algebraically_disjoint f g := begin
--   intros disjoint_f_g h hfh,
--   let support_f := support α f,
-- -- h is not the identity on support α f
--   cases Set.not_disjoint_iff.mp (mt (@disjoint_commute G α _ _ _ _ _) hfh) with x hx,
--   let x_in_support_f := hx.1,
--   let hx_ne_x := mem_support.mp hx.2,
-- -- so since α is Hausdoff there is V nonempty ⊆ support α f with h•''V disjoint from V
--   rcases disjoint_nbhd_in (support_open f) x_in_support_f hx_ne_x with ⟨V,open_V,x_in_V,V_in_support,disjoint_img_V⟩,
--   let ristV_ne_bot := locally_moving V open_V (Set.nonempty_of_mem x_in_V),
-- -- let f₂ be a nontrivial element of rigid_stabilizer G V
--   rcases (or_iff_right ristV_ne_bot).mp (Subgroup.bot_or_exists_ne_one _) with ⟨f₂,f₂_in_ristV,f₂_ne_one⟩,
-- -- again since α is Hausdorff there is W nonempty ⊆ V with f₂•''W disjoint from W
--   rcases faithful_moves_point' α f₂_ne_one with ⟨y,ymoved⟩,
--   let y_in_V : y ∈ V := (rist_supported_in_set f₂_in_ristV) (mem_support.mpr ymoved),
--   rcases disjoint_nbhd_in open_V y_in_V ymoved with ⟨W,open_W,y_in_W,W_in_V,disjoint_img_W⟩,
-- -- let f₁ be a nontrivial element of rigid_stabilizer G W
--   let ristW_ne_bot := locally_moving W open_W (Set.nonempty_of_mem y_in_W),
--   rcases (or_iff_right ristW_ne_bot).mp (Subgroup.bot_or_exists_ne_one _) with ⟨f₁,f₁_in_ristW,f₁_ne_one⟩,
--   use f₁, use f₂,
-- -- note that f₁,f₂ commute with g since their support is in support α f
--   split,
--   exact disjoint_commute (Set.disjoint_of_subset_left (Set.subset.trans (Set.subset.trans (rist_supported_in_set f₁_in_ristW) W_in_V) V_in_support) disjoint_f_g),
--   split,
--   exact disjoint_commute (Set.disjoint_of_subset_left (Set.subset.trans (rist_supported_in_set f₂_in_ristV) V_in_support) disjoint_f_g),
-- -- we claim that [f₁,[f₂,h]] is a nontrivial element of centralizer G g
--   let k := ⁅f₂,h⁆,
-- -- first, h*f₂⁻¹*h⁻¹ is supported on h V, so k := [f₂,h] agrees with f₂ on V
--   have h2 : ∀z ∈ W, f₂•z = k•z := λ z z_in_W,
--     (disjoint_support_comm f₂ h (rist_supported_in_set f₂_in_ristV) disjoint_img_V z (W_in_V z_in_W)).symm,
-- -- then k*f₁⁻¹*k⁻¹ is supported on k W = f₂ W, so [f₁,k] is supported on W ∪ f₂ W ⊆ V ⊆ support f, so commutes with g.
--   have h3 : support α ⁅f₁,k⁆ ⊆ support α f := begin
--     let := (support_comm α k f₁).trans (Set.union_subset_union (rist_supported_in_set f₁_in_ristW) (smul''_subset k $ rist_supported_in_set f₁_in_ristW)),
--     rw [← commutator_element_inv,support_inv,(smul''_eq_of_smul_eq h2).symm] at this,
--     exact (this.trans $ (Set.union_subset_union W_in_V (moves_subset_within_support f₂ W V W_in_V $ rist_supported_in_set f₂_in_ristV)).trans $ eq.subset V.union_self).trans V_in_support
-- end,
--   split,
--   exact disjoint_commute (Set.disjoint_of_subset_left h3 disjoint_f_g),
-- -- finally, [f₁,k] agrees with f₁ on W, so is not the identity.
--   have h4 : ∀z ∈ W, ⁅f₁,k⁆•z = f₁•z :=
--     disjoint_support_comm f₁ k (rist_supported_in_set f₁_in_ristW) (smul''_eq_of_smul_eq h2 ▸ disjoint_img_W),
--   rcases faithful_rist_moves_point f₁_in_ristW f₁_ne_one with ⟨z,z_in_W,z_moved⟩,
--   by_contra h5,
--   exact ((h4 z z_in_W).symm ▸ z_moved : ⁅f₁, k⁆ • z ≠ z) ((congr_arg (λg : G, g•z) h5).trans (one_smul G z)),
-- end
-- @[simp] lemma smul''_mul {g h : G} {U : set α} : g •'' (h •'' U) = (g*h) •'' U :=
--   (mul_smul'' g h U).symm
-- lemma disjoint_nbhd_fin {ι : Type*} [fintype ι] {f : ι → G} {x : α} [t2_space α] : (λi : ι, f i • x).injective → ∃U : set α, is_open U ∧ x ∈ U ∧ (∀i j : ι, i ≠ j → disjoint (f i •'' U) (f j •'' U)) := begin
--   intro f_injective,
--   let disjoint_hyp := λi j (i_ne_j : i≠j), let x_moved : ((f j)⁻¹ * f i) • x ≠ x := begin
--     by_contra,
--     let := smul_congr (f j) h,
--     rw [mul_smul, ← mul_smul,mul_right_inv,one_smul] at this,
--     from i_ne_j (f_injective this),
--   end in disjoint_nbhd x_moved,
--   let ι2 := { p : ι×ι // p.1 ≠ p.2 },
--   let U := ⋂(p : ι2), (disjoint_hyp p.1.1 p.1.2 p.2).some,
--   use U,
--   split,
--   exact is_open_Inter (λp : ι2, (disjoint_hyp p.1.1 p.1.2 p.2).some_spec.1),
--   split,
--   exact Set.mem_Inter.mpr (λp : ι2, (disjoint_hyp p.1.1 p.1.2 p.2).some_spec.2.1),
--   intros i j i_ne_j,
--   let U_inc := Set.Inter_subset (λ p : ι2, (disjoint_hyp p.1.1 p.1.2 p.2).some) ⟨⟨i,j⟩,i_ne_j⟩,
--   let := (disjoint_smul'' (f j) (Set.disjoint_of_subset U_inc (smul''_subset ((f j)⁻¹ * (f i)) U_inc) (disjoint_hyp i j i_ne_j).some_spec.2.2)).symm,
--   simp only [subtype.val_eq_coe, smul''_mul, mul_inv_cancel_left] at this,
--   from this
-- end
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
end AlgebraicDisjointness

----------------------------------------------------------------
section Rubin.RegularSupport.RegularSupport

variable [TopologicalSpace α] [Rubin.Topological.ContinuousMulAction G α]

def RegularSupport.InteriorClosure (U : Set α) :=
  interior (closure U)
#align interior_closure Rubin.RegularSupport.InteriorClosure

theorem RegularSupport.is_open_interiorClosure (U : Set α) :
    IsOpen (Rubin.RegularSupport.InteriorClosure U) :=
  isOpen_interior
#align is_open_interior_closure Rubin.RegularSupport.is_open_interiorClosure

theorem RegularSupport.interiorClosure_mono {U V : Set α} :
    U ⊆ V → Rubin.RegularSupport.InteriorClosure U ⊆ Rubin.RegularSupport.InteriorClosure V :=
  interior_mono ∘ closure_mono
#align interior_closure_mono Rubin.RegularSupport.interiorClosure_mono

def is_regular_open (U : Set α) :=
  Rubin.RegularSupport.InteriorClosure U = U
#align set.is_regular_open Rubin.is_regular_open

theorem is_regular_def (U : Set α) :
    is_regular_open U ↔ Rubin.RegularSupport.InteriorClosure U = U := by rfl
#align set.is_regular_def Rubin.is_regular_def

theorem RegularSupport.IsOpen.in_closure {U : Set α} : IsOpen U → U ⊆ interior (closure U) :=
  by
  intro U_open x x_in_U
  apply interior_mono subset_closure
  rw [U_open.interior_eq]
  exact x_in_U
#align is_open.in_closure Rubin.RegularSupport.IsOpen.in_closure

theorem RegularSupport.IsOpen.interiorClosure_subset {U : Set α} :
    IsOpen U → U ⊆ Rubin.RegularSupport.InteriorClosure U := fun h =>
  (subset_interior_iff_isOpen.mpr h).trans (interior_mono subset_closure)
#align is_open.interior_closure_subset Rubin.RegularSupport.IsOpen.interiorClosure_subset

theorem RegularSupport.regular_interior_closure (U : Set α) :
    is_regular_open (Rubin.RegularSupport.InteriorClosure U) :=
  by
  rw [is_regular_def]
  apply Set.Subset.antisymm
  exact interior_mono ((closure_mono interior_subset).trans (subset_of_eq closure_closure))
  exact (subset_of_eq interior_interior.symm).trans (interior_mono subset_closure)
#align regular_interior_closure Rubin.RegularSupport.regular_interior_closure

def RegularSupport.RegularSupport (α : Type _) [TopologicalSpace α] [MulAction G α] (g : G) :=
  Rubin.RegularSupport.InteriorClosure (Rubin.SmulSupport.Support α g)
#align regular_support Rubin.RegularSupport.RegularSupport

theorem RegularSupport.regularSupport_regular {g : G} :
    is_regular_open (Rubin.RegularSupport.RegularSupport α g) :=
  Rubin.RegularSupport.regular_interior_closure _
#align regular_regular_support Rubin.RegularSupport.regularSupport_regular

theorem RegularSupport.support_subset_regularSupport [T2Space α] (g : G) :
    Rubin.SmulSupport.Support α g ⊆ Rubin.RegularSupport.RegularSupport α g :=
  Rubin.RegularSupport.IsOpen.interiorClosure_subset (Rubin.Topological.support_open g)
#align support_in_regular_support Rubin.RegularSupport.support_subset_regularSupport

theorem RegularSupport.mem_regularSupport (g : G) (U : Set α) :
    is_regular_open U → g ∈ rigidStabilizer G U → Rubin.RegularSupport.RegularSupport α g ⊆ U :=
  fun U_ro g_moves =>
  (is_regular_def _).mp U_ro ▸
    Rubin.RegularSupport.interiorClosure_mono (rist_supported_in_set g_moves)
#align mem_regular_support Rubin.RegularSupport.mem_regularSupport

-- FIXME: Weird naming?
def RegularSupport.AlgebraicCentralizer (f : G) : Set G :=
  {h | ∃ g, h = g ^ 12 ∧ Rubin.is_algebraically_disjoint f g}
#align algebraic_centralizer Rubin.RegularSupport.AlgebraicCentralizer

end Rubin.RegularSupport.RegularSupport

-- ----------------------------------------------------------------
-- section finite_exponent
-- lemma coe_nat_fin {n i : ℕ} (h : i < n) : ∃ (i' : fin n), i = i' := ⟨ ⟨ i, h ⟩, rfl ⟩
-- variables [topological_space α] [continuous_mul_action G α] [has_faithful_smul G α]
-- lemma distinct_images_from_disjoint {g : G} {V : set α} {n : ℕ}
--   (n_pos : 0 < n)
--   (h_disj : ∀ (i j : fin n) (i_ne_j : i ≠ j), disjoint (g ^ (i : ℕ) •'' V) (g ^ (j : ℕ) •'' V)) :
--   ∀ (q : α) (hq : q ∈ V) (i : fin n), (i : ℕ) > 0 → g ^ (i : ℕ) • (q : α) ∉ V :=
-- begin
--   intros q hq i i_pos hcontra,
--   have i_ne_zero : i ≠ (⟨ 0, n_pos ⟩ : fin n), { intro, done },
--   have hcontra' : g ^ (i : ℕ) • (q : α) ∈ g ^ (i : ℕ) •'' V, exact ⟨ q, hq, rfl ⟩,
--   have giq_notin_V := Set.disjoint_left.mp (h_disj i (⟨ 0, n_pos ⟩ : fin n) i_ne_zero) hcontra',
--   exact ((by done : g ^ 0•''V = V) ▸ giq_notin_V) hcontra
-- end
-- lemma moves_inj_period {g : G} {p : α} {n : ℕ} (period_eq_n : period p g = n) : function.injective (λ (i : fin n), g ^ (i : ℕ) • p) := begin
--   have period_ge_n : ∀ (k : ℕ), 1 ≤ k → k < n → g ^ k • p ≠ p,
--   { intros k one_le_k k_lt_n gkp_eq_p,
--     have := period_le_fix (nat.succ_le_iff.mp one_le_k) gkp_eq_p,
--     rw period_eq_n at this,
--     linarith },
--   exact moves_inj_N period_ge_n
-- end
-- lemma lemma_2_2 {α : Type u_2} [topological_space α] [continuous_mul_action G α] [has_faithful_smul G α] [t2_space α]
--   (U : set α) (U_open : is_open U) (locally_moving : is_locally_moving G α) :
--   U.nonempty → monoid.exponent (rigid_stabilizer G U) = 0 :=
-- begin
--   intro U_nonempty,
--   by_contra exp_ne_zero,
--   rcases (period_from_exponent U U_nonempty exp_ne_zero) with ⟨ p, g, n, n_pos, hpgn, n_eq_Sup ⟩,
--   rcases disjoint_nbhd_fin (moves_inj_period hpgn) with ⟨ V', V'_open, p_in_V', disj' ⟩,
--   dsimp at disj',
--   let V := U ∩ V',
--   have V_ss_U : V ⊆ U := Set.inter_subset_left U V',
--   have V'_ss_V : V ⊆ V' := Set.inter_subset_right U V',
--   have V_open : is_open V := is_open.inter U_open V'_open,
--   have p_in_V : (p : α) ∈ V := ⟨ subtype.mem p, p_in_V' ⟩,
--   have disj : ∀ (i j : fin n), ¬ i = j → disjoint (↑g ^ ↑i•''V) (↑g ^ ↑j•''V),
--   { intros i j i_ne_j W W_ss_giV W_ss_gjV,
--     exact disj' i j i_ne_j
--     (Set.subset.trans W_ss_giV (smul''_subset (↑g ^ ↑i) V'_ss_V))
--     (Set.subset.trans W_ss_gjV (smul''_subset (↑g ^ ↑j) V'_ss_V)) },
--   have ristV_ne_bot := locally_moving V V_open (Set.nonempty_of_mem p_in_V),
--   rcases (or_iff_right ristV_ne_bot).mp (Subgroup.bot_or_exists_ne_one _) with ⟨h,h_in_ristV,h_ne_one⟩,
--   rcases faithful_rist_moves_point h_in_ristV h_ne_one with ⟨ q, q_in_V, hq_ne_q ⟩,
--   have hg_in_ristU : (h : G) * (g : G) ∈ rigid_stabilizer G U := (rigid_stabilizer G U).mul_mem' (rist_ss_rist V_ss_U h_in_ristV) (subtype.mem g),
--   have giq_notin_V : ∀ (i : fin n), (i : ℕ) > 0 → g ^ (i : ℕ) • (q : α) ∉ V := distinct_images_from_disjoint n_pos disj q q_in_V,
--   have giq_ne_q : ∀ (i : fin n), (i : ℕ) > 0 → g ^ (i : ℕ) • (q : α) ≠ (q : α),
--   { intros i i_pos giq_eq_q, exact (giq_eq_q ▸ (giq_notin_V i i_pos)) q_in_V, },
--   have q_in_U : q ∈ U, { have : q ∈ U ∩ V' := q_in_V, exact this.1 },
--   -- We have (hg)^i q = g^i q for all 0 < i < n
--   have pow_hgq_eq_pow_gq : ∀ (i : fin n), (i : ℕ) < n → (h * g) ^ (i : ℕ) • q = (g : G) ^ (i : ℕ) • q,
--   { intros i, induction (i : ℕ) with i',
--     { intro, repeat {rw pow_zero} },
--     { intro succ_i'_lt_n,
--       rw [smul_succ, ih (nat.lt_of_succ_lt succ_i'_lt_n), smul_smul, mul_assoc, ← smul_smul, ← smul_smul, ← smul_succ],
--       have image_q_notin_V : g ^ i'.succ • q ∉ V,
--       { have i'succ_ne_zero := ne_zero.pos i'.succ,
--         exact giq_notin_V (⟨ i'.succ, succ_i'_lt_n ⟩ : fin n) i'succ_ne_zero },
--       exact by_contradiction (λ c, c (by_contradiction (λ c', image_q_notin_V ((rist_supported_in_set h_in_ristV) c')))) } },
--   -- Combined with g^i q ≠ q, this yields (hg)^i q ≠ q for all 0 < i < n
--   have hgiq_ne_q : ∀ (i : fin n), (i : ℕ) > 0 → (h * g) ^ (i : ℕ) • q ≠ q,
--   { intros i i_pos, rw pow_hgq_eq_pow_gq i (fin.is_lt i), by_contra c, exact (giq_notin_V i i_pos) (c.symm ▸ q_in_V) },
--   -- This even holds for i = n
--   have hgnq_ne_q : (h * g) ^ n • q ≠ q,
--   { -- Rewrite (hg)^n q = hg^n q
--     have npred_lt_n : n.pred < n, exact (nat.succ_pred_eq_of_pos n_pos) ▸ (lt_add_one n.pred),
--     rcases coe_nat_fin npred_lt_n with ⟨ i', i'_eq_pred_n ⟩,
--     have hgi'q_eq_gi'q := pow_hgq_eq_pow_gq i' (i'_eq_pred_n ▸ npred_lt_n),
--     have : n = (i' : ℕ).succ := i'_eq_pred_n ▸ (nat.succ_pred_eq_of_pos n_pos).symm,
--     rw [this, smul_succ, hgi'q_eq_gi'q, ← smul_smul, ← smul_succ, ← this],
--     -- Now it follows from g^n q = q and h q ≠ q
--     have n_le_period_qg := notfix_le_period' n_pos ((zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero (⟨ q, q_in_U ⟩ : U) g)).1 giq_ne_q,
--     have period_qg_le_n := (zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero (⟨ q, q_in_U ⟩ : U) g).2, rw ← n_eq_Sup at period_qg_le_n,
--     exact (ge_antisymm period_qg_le_n n_le_period_qg).symm ▸ ((pow_period_fix q (g : G)).symm ▸ hq_ne_q) },
--   -- Finally, we derive a contradiction
--   have period_pos_le_n := zero_lt_period_le_Sup_periods U_nonempty exp_ne_zero (⟨ q, q_in_U ⟩ : U) (⟨ h * g, hg_in_ristU ⟩ : rigid_stabilizer G U),
--   rw ← n_eq_Sup at period_pos_le_n,
--   cases (lt_or_eq_of_le period_pos_le_n.2),
--   { exact (hgiq_ne_q (⟨ (period (q : α) ((h : G) * (g : G))), h_1 ⟩ : fin n) period_pos_le_n.1) (pow_period_fix (q : α) ((h : G) * (g : G))) },
--   { exact hgnq_ne_q (h_1 ▸ (pow_period_fix (q : α) ((h : G) * (g : G)))) }
-- end
-- lemma proposition_2_1 [t2_space α] (f : G) : is_locally_moving G α → (algebraic_centralizer f).centralizer = rigid_stabilizer G (regular_support α f) := sorry
-- end finite_exponent
-- variables [topological_space α] [topological_space β] [continuous_mul_action G α] [continuous_mul_action G β]
-- noncomputable theorem rubin (hα : rubin_action G α) (hβ : rubin_action G β) : equivariant_homeomorph G α β := sorry
end Rubin

end Rubin
