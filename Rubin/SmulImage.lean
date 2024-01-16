import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Basic

import Rubin.MulActionExt
import Rubin.Topology

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

@[simp]
theorem smulImage_preImage (g: G) (U: Set α) : (fun p => g • p) ⁻¹' U = g⁻¹ •'' U := by
  ext x
  simp
  rw [mem_smulImage, inv_inv]

theorem mem_inv_smulImage {x : α} {g : G} {U : Set α} : x ∈ g⁻¹ •'' U ↔ g • x ∈ U :=
  by
  let msi := @Rubin.mem_smulImage _ _ _ _ x g⁻¹ U
  rw [inv_inv] at msi
  exact msi
#align mem_inv_smul'' Rubin.mem_inv_smulImage

@[simp]
theorem mem_smulImage' {x : α} (g : G) {U : Set α} : g • x ∈ g •'' U ↔ x ∈ U :=
by
  rw [mem_smulImage]
  rw [←mul_smul, mul_left_inv, one_smul]

@[simp]
theorem smulImage_mul (g h : G) (U : Set α) : g •'' (h •'' U) = (g * h) •'' U :=
  by
  ext
  rw [Rubin.mem_smulImage, Rubin.mem_smulImage, Rubin.mem_smulImage, ←
    mul_smul, mul_inv_rev]
#align mul_smul'' Rubin.smulImage_mul

@[simp]
theorem one_smulImage (U : Set α) : (1 : G) •'' U = U :=
  by
  ext
  rw [Rubin.mem_smulImage, inv_one, one_smul]
#align one_smul'' Rubin.one_smulImage

theorem smulImage_disjoint (g : G) {U V : Set α} :
    Disjoint U V → Disjoint (g •'' U) (g •'' V) :=
  by
  intro disjoint_U_V
  rw [Set.disjoint_left]
  rw [Set.disjoint_left] at disjoint_U_V
  intro x x_in_gU
  by_contra h
  exact (disjoint_U_V (mem_smulImage.mp x_in_gU)) (mem_smulImage.mp h)
#align disjoint_smul'' Rubin.smulImage_disjoint

theorem SmulImage.congr (g : G) {U V : Set α} : U = V → g •'' U = g •'' V :=
  congr_arg fun W : Set α => g •'' W
#align smul''_congr Rubin.SmulImage.congr

theorem SmulImage.inv_congr (g: G) {U V : Set α} : g •'' U = g •'' V → U = V :=
by
  intro h
  rw [←one_smulImage (G := G) U]
  rw [←one_smulImage (G := G) V]
  rw [←mul_left_inv g]
  repeat rw [←smulImage_mul]
  exact SmulImage.congr g⁻¹ h

theorem smulImage_inv (g: G) (U V : Set α) : g •'' U = V ↔ U = g⁻¹ •'' V := by
  nth_rw 2 [←one_smulImage (G := G) U]
  rw [←mul_left_inv g, ←smulImage_mul]
  constructor
  · intro h
    rw [SmulImage.congr]
    exact h
  · intro h
    apply SmulImage.inv_congr at h
    exact h

theorem smulImage_mono (g : G) {U V : Set α} : U ⊆ V → g •'' U ⊆ g •'' V := by
  intro h1 x
  rw [Rubin.mem_smulImage, Rubin.mem_smulImage]
  exact fun h2 => h1 h2
#align smul''_subset Rubin.smulImage_mono

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

@[simp]
theorem smulImage_sUnion (g : G) {S : Set (Set α)} : g •'' (⋃₀ S) = ⋃₀ {g •'' T | T ∈ S} :=
by
  ext x
  constructor
  · intro h
    rw [mem_smulImage, Set.mem_sUnion] at h
    rw [Set.mem_sUnion]
    let ⟨T, ⟨T_in_S, ginv_x_in_T⟩⟩ := h
    simp
    use T
    constructor; trivial
    rw [mem_smulImage]
    exact ginv_x_in_T
  · intro h
    rw [Set.mem_sUnion] at h
    rw [mem_smulImage, Set.mem_sUnion]
    simp at h
    let ⟨T, ⟨T_in_S, x_in_gT⟩⟩ := h
    use T
    constructor; trivial
    rw [←mem_smulImage]
    exact x_in_gT

@[simp]
theorem smulImage_sInter (g : G) {S : Set (Set α)} : g •'' (⋂₀ S) = ⋂₀ {g •'' T | T ∈ S} := by
  ext x
  constructor
  · intro h
    rw [mem_smulImage, Set.mem_sInter] at h
    rw [Set.mem_sInter]
    simp
    intro T T_in_S
    rw [mem_smulImage]
    exact h T T_in_S
  · intro h
    rw [Set.mem_sInter] at h
    rw [mem_smulImage, Set.mem_sInter]
    intro T T_in_S
    rw [←mem_smulImage]
    simp at h
    exact h T T_in_S

@[simp]
theorem smulImage_iInter {β : Type _} (g : G) (S : Set β) (f : β → Set α) :
  g •'' (⋂ x ∈ S, f x) = ⋂ x ∈ S, g •'' (f x) :=
by
  ext x
  constructor
  · intro h
    rw [mem_smulImage] at h
    simp
    simp at h
    intro i i_in_S
    rw [mem_smulImage]
    exact h i i_in_S
  · intro h
    simp at h
    rw [mem_smulImage]
    simp
    intro i i_in_S
    rw [←mem_smulImage]
    exact h i i_in_S

@[simp]
theorem smulImage_iInter_fin {β : Type _} (g : G) (S : Finset β) (f : β → Set α) :
  g •'' (⋂ x ∈ S, f x) = ⋂ x ∈ S, g •'' (f x) :=
by
  -- For some strange reason I can't use the above theorem
  ext x
  rw [mem_smulImage, Set.mem_iInter, Set.mem_iInter]
  simp
  conv => {
    rhs
    ext; ext
    rw [mem_smulImage]
  }

@[simp]
theorem smulImage_compl (g : G) (U : Set α) : (g •'' U)ᶜ = g •'' Uᶜ :=
by
  ext x
  rw [Set.mem_compl_iff]
  repeat rw [mem_smulImage]
  rw [Set.mem_compl_iff]

@[simp]
theorem smulImage_nonempty (g: G) {U : Set α} : Set.Nonempty (g •'' U) ↔ Set.Nonempty U :=
by
  constructor
  · intro ⟨x, x_in_gU⟩
    use g⁻¹•x
    rw [←mem_smulImage]
    assumption
  · intro ⟨x, x_in_U⟩
    use g•x
    simp
    assumption

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
    apply smulImage_mono f⁻¹ at h
    rw [smulImage_mul] at h
    rw [mul_left_inv, one_smulImage] at h
    exact h
  · intro h
    apply smulImage_mono f at h
    rw [smulImage_mul] at h
    rw [mul_right_inv, one_smulImage] at h
    exact h

theorem smulImage_subset_inv' {G α : Type _} [Group G] [MulAction G α]
  (f : G) (U V : Set α) :
  f⁻¹ •'' U ⊆ V ↔ U ⊆ f •'' V :=
by
  nth_rewrite 2 [←inv_inv f]
  exact smulImage_subset_inv f⁻¹ U V

theorem smulImage_disjoint_mul {G α : Type _} [Group G] [MulAction G α]
  (f g : G) (U V : Set α) :
  Disjoint (f •'' U) (g •'' V) ↔ Disjoint U ((f⁻¹ * g) •'' V) := by
  constructor
  · intro h
    apply smulImage_disjoint f⁻¹ at h
    repeat rw [smulImage_mul] at h
    rw [mul_left_inv, one_smulImage] at h
    exact h

  · intro h
    apply smulImage_disjoint f at h
    rw [smulImage_mul] at h
    rw [←mul_assoc] at h
    rw [mul_right_inv, one_mul] at h
    exact h

theorem smulImage_disjoint_inv_pow {G α : Type _} [Group G] [MulAction G α]
  (g : G) (i j : ℤ) (U V : Set α) :
  Disjoint (g^i •'' U) (g^j •'' V) ↔ Disjoint (g^(-j) •'' U) (g^(-i) •'' V) :=
by
  rw [smulImage_disjoint_mul]
  rw [←zpow_neg, ←zpow_add, add_comm, zpow_add, zpow_neg]
  rw [←inv_inv (g^j)]
  rw [←smulImage_disjoint_mul]
  simp

theorem smulImage_disjoint_subset {G α : Type _} [Group G] [MulAction G α]
  {f g : G} {U V : Set α} (h_sub: U ⊆ V):
  Disjoint (f •'' V) (g •'' V) → Disjoint (f •'' U) (g •'' U) :=
Set.disjoint_of_subset (smulImage_mono _ h_sub) (smulImage_mono _ h_sub)

-- States that if `g^i •'' V` and `g^j •'' V` are disjoint for any `i ≠ j` and `x ∈ V`
-- then `g^i • x` will always lie outside of `V` if `x ∈ V`.
lemma smulImage_distinct_of_disjoint_pow {G α : Type _} [Group G] [MulAction G α] {g : G} {V : Set α} {n : ℕ}
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
#align distinct_images_from_disjoint Rubin.smulImage_distinct_of_disjoint_pow

theorem smulImage_isOpen {G α : Type _}
  [Group G] [TopologicalSpace α] [MulAction G α] [ContinuousConstSMul G α] (g : G)
  {S : Set α} (S_open : IsOpen S) : IsOpen (g •'' S) :=
by
  rw [smulImage_eq_inv_preimage]
  exact (continuous_id.const_smul g⁻¹).isOpen_preimage S S_open

theorem smulImage_isClosed {G α : Type _}
  [Group G] [TopologicalSpace α] [MulAction G α] [ContinuousConstSMul G α] (g : G)
  {S : Set α} (S_open : IsClosed S) : IsClosed (g •'' S) :=
by
  rw [←isOpen_compl_iff]
  rw [←isOpen_compl_iff] at S_open
  rw [smulImage_compl]
  apply smulImage_isOpen
  assumption

theorem smulImage_interior {G α : Type _} [Group G] [TopologicalSpace α] [MulAction G α]
  [hc : ContinuousConstSMul G α] (g : G) (U : Set α) :
  interior (g •'' U) = g •'' interior U :=
by
  unfold interior
  rw [smulImage_sUnion]
  simp
  ext x
  simp
  constructor
  · intro ⟨T, ⟨T_open, T_sub⟩, x_in_T⟩
    use g⁻¹ •'' T
    repeat' apply And.intro
    · exact smulImage_isOpen g⁻¹ T_open
    · rw [smulImage_subset_inv]
      rw [inv_inv]
      exact T_sub
    · rw [smulImage_mul, mul_right_inv, one_smulImage]
      exact x_in_T
  · intro ⟨T, ⟨T_open, T_sub⟩, x_in_T⟩
    use g •'' T
    repeat' apply And.intro
    ·  exact smulImage_isOpen g T_open
    · apply smulImage_mono
      exact T_sub
    · exact x_in_T

theorem smulImage_closure {G α : Type _} [Group G] [TopologicalSpace α] [MulAction G α]
  [ContinuousConstSMul G α] (g : G) (U : Set α) :
  closure (g •'' U) = g •'' closure U :=
by
  unfold closure
  rw [smulImage_sInter]
  simp
  ext x
  simp
  constructor
  · intro IH T' T T_closed U_ss_T T'_eq
    rw [←T'_eq]
    clear T' T'_eq
    apply IH
    · exact smulImage_isClosed g T_closed
    · apply smulImage_mono
      exact U_ss_T
  · intro IH T T_closed gU_ss_T
    apply IH
    · exact smulImage_isClosed g⁻¹ T_closed
    · rw [←smulImage_subset_inv]
      exact gU_ss_T
    · simp

section Filters

open Topology

variable {G α : Type _}
variable [Group G] [MulAction G α]

/--
An SMul can be extended to filters, while preserving the properties of `MulAction`.

To avoid polluting the `SMul` instances for filters, those properties are made separate,
instead of implementing `MulAction G (Filter α)`.
--/
def SmulFilter {G α : Type _} [SMul G α] (g : G) (F : Filter α) : Filter α :=
  Filter.map (fun p => g • p) F

infixl:60 " •ᶠ " => Rubin.SmulFilter

theorem smulFilter_def {G α : Type _} [SMul G α] (g : G) (F : Filter α) :
  Filter.map (fun p => g • p) F = g •ᶠ F := rfl

theorem smulFilter_neBot {G α : Type _} [SMul G α] (g : G) {F : Filter α} (F_neBot : Filter.NeBot F) :
  Filter.NeBot (g •ᶠ F) :=
by
  rw [←smulFilter_def]
  exact Filter.map_neBot

instance smulFilter_neBot' {G α : Type _} [SMul G α] {g : G} {F : Filter α} [F_neBot : Filter.NeBot F] :
  Filter.NeBot (g •ᶠ F) := smulFilter_neBot g F_neBot

theorem smulFilter_principal (g : G) (S : Set α) :
  g •ᶠ Filter.principal S = Filter.principal (g •'' S) :=
by
  rw [←smulFilter_def]
  rw [Filter.map_principal]
  rfl

theorem mul_smulFilter (g h: G) (F : Filter α) :
  (g * h) •ᶠ F = g •ᶠ (h •ᶠ F) :=
by
  repeat rw [←smulFilter_def]
  simp only [mul_smul]
  rw [Filter.map_map]
  rfl

theorem one_smulFilter (G : Type _) [Group G] [MulAction G α] (F : Filter α) :
  (1 : G) •ᶠ F = F :=
by
  rw [←smulFilter_def]
  simp only [one_smul]
  exact Filter.map_id

theorem mem_smulFilter_iff (g : G) (F : Filter α) (U : Set α) :
  U ∈ g •ᶠ F ↔ g⁻¹ •'' U ∈ F :=
by
  rw [←smulFilter_def, Filter.mem_map, smulImage_eq_inv_preimage, inv_inv]

theorem smulFilter_mono (g : G) (F F' : Filter α) :
  F ≤ F' ↔ g •ᶠ F ≤ g •ᶠ F' :=
by
  suffices ∀ (g : G) (F F' : Filter α), F ≤ F' → g •ᶠ F ≤ g •ᶠ F' by
    constructor
    apply this
    intro H
    specialize this g⁻¹ _ _ H
    repeat rw [←mul_smulFilter] at this
    rw [mul_left_inv] at this
    repeat rw [one_smulFilter] at this
    exact this
  intro g F F' F_le_F'
  intro U U_in_gF
  rw [mem_smulFilter_iff] at U_in_gF
  rw [mem_smulFilter_iff]
  apply F_le_F'
  assumption

theorem smulFilter_le_iff_le_inv (g : G) (F F' : Filter α) :
  F ≤ g •ᶠ F' ↔ g⁻¹ •ᶠ F ≤ F' :=
by
  nth_rw 2 [←one_smulFilter G F']
  rw [←mul_left_inv g, mul_smulFilter]
  exact smulFilter_mono g⁻¹ _ _

variable [TopologicalSpace α]

theorem smulFilter_nhds (g : G) (p : α) [ContinuousConstSMul G α]:
  g •ᶠ 𝓝 p = 𝓝 (g • p) :=
by
  ext S
  rw [←smulFilter_def, Filter.mem_map, mem_nhds_iff, mem_nhds_iff]
  simp
  constructor
  · intro ⟨T, T_ss_smulImage, T_open, p_in_T⟩
    use g •'' T
    repeat' apply And.intro
    · rw [smulImage_subset_inv]
      assumption
    · exact smulImage_isOpen g T_open
    · simp
      assumption
  · intro ⟨T, T_ss_S, T_open, gp_in_T⟩
    use g⁻¹ •'' T
    repeat' apply And.intro
    · apply smulImage_mono
      assumption
    · exact smulImage_isOpen g⁻¹ T_open
    · rw [mem_smulImage, inv_inv]
      assumption

theorem smulFilter_clusterPt (g : G) (F : Filter α) (x : α) [ContinuousConstSMul G α] :
  ClusterPt x (g •ᶠ F) ↔ ClusterPt (g⁻¹ • x) F :=
by
  suffices ∀ (g : G) (F : Filter α) (x : α), ClusterPt x (g •ᶠ F) → ClusterPt (g⁻¹ • x) F by
    constructor
    apply this
    intro gx_clusterPt_F

    rw [←one_smul G x, ←mul_right_inv g, mul_smul]
    nth_rw 1 [←inv_inv g]
    apply this
    rw [←mul_smulFilter, mul_left_inv, one_smulFilter]
    assumption
  intro g F x x_cp_gF
  rw [clusterPt_iff_forall_mem_closure]
  rw [clusterPt_iff_forall_mem_closure] at x_cp_gF
  simp only [mem_smulFilter_iff] at x_cp_gF
  intro S S_in_F

  rw [←mem_inv_smulImage]
  rw [←smulImage_closure]

  apply x_cp_gF
  rw [inv_inv, smulImage_mul, mul_left_inv, one_smulImage]
  assumption

theorem smulImage_compact [ContinuousConstSMul G α] (g : G) {U : Set α} (U_compact : IsCompact U) :
  IsCompact (g •'' U) :=
by
  intro F F_neBot F_le_principal
  rw [←smulFilter_principal, smulFilter_le_iff_le_inv] at F_le_principal
  let ⟨x, x_in_U, x_clusterPt⟩ := U_compact F_le_principal
  use g • x
  constructor
  · rw [mem_smulImage']
    assumption
  · rw [smulFilter_clusterPt, inv_inv] at x_clusterPt
    assumption

end Filters
end Rubin
