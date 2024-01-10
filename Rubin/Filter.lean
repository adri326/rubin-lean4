import Mathlib.Order.Filter.Basic
import Mathlib.Order.Hom.CompleteLattice

import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation

section Order

variable {α : Type _} {β : Type _}

def DoubleMonotoneOn [Preorder α] [Preorder β] (f: α → β) (B : Set α): Prop :=
  ∀ x, x ∈ B → ∀ y, y ∈ B → (x ≤ y ↔ f x ≤ f y)

variable {f : α → β} {B : Set α}

theorem DoubleMonotoneOn.monotoneOn [Preorder α] [Preorder β] (f_double_mono : DoubleMonotoneOn f B) :
  MonotoneOn f B :=
by
  intro x x_in_B y y_in_B
  rw [f_double_mono x x_in_B y y_in_B]
  tauto

theorem DoubleMonotoneOn.injective [PartialOrder α] [Preorder β] (f_double_mono : DoubleMonotoneOn f B) :
  Function.Injective (Set.restrict B f) :=
by
  intro ⟨x, x_in_B⟩ ⟨y, y_in_B⟩
  simp
  intro fx_eq_fy
  apply le_antisymm
  swap
  symm at fx_eq_fy
  all_goals apply le_of_eq at fx_eq_fy
  all_goals rw [f_double_mono]
  all_goals assumption

theorem DoubleMonotoneOn.injective' [PartialOrder α] [Preorder β] (f_double_mono : DoubleMonotoneOn f B) :
  ∀ x ∈ B, ∀ y ∈ B,
  f x = f y → x = y :=
by
  intro x x_in_B y y_in_B fx_eq_fy
  have fx_eq : f x = Set.restrict B f ⟨x, x_in_B⟩ := by simp
  have fy_eq : f y = Set.restrict B f ⟨y, y_in_B⟩ := by simp

  rw [fx_eq, fy_eq] at fx_eq_fy
  apply (injective f_double_mono) at fx_eq_fy
  simp at fx_eq_fy
  exact fx_eq_fy

theorem DoubleMonotoneOn.subset_iff {B : Set (Set α)} {f : Set α → Set β} (f_double_mono : DoubleMonotoneOn f B) :
  ∀ s ∈ B, ∀ t ∈ B, s ⊆ t ↔ f s ⊆ f t :=
by
  simp only [<-Set.le_eq_subset]
  exact f_double_mono

structure OrderIsoOn (α : Type _) (β : Type _) [Preorder α] [Preorder β] (S : Set α) :=
  toFun : α → β
  invFun : β → α

  leftInv_on : ∀ a ∈ S, invFun (toFun a) = a
  rightInv_on : ∀ b ∈ toFun '' S, toFun (invFun b) = b

  toFun_doubleMonotone : DoubleMonotoneOn toFun S

theorem OrderIsoOn.mk_of_subset [Preorder α] [Preorder β] (F : OrderIsoOn α β S)
  {T : Set α} (T_ss_S : T ⊆ S) : OrderIsoOn α β T
where
  toFun := F.toFun
  invFun := F.invFun

  leftInv_on := by
    intro a a_in_T
    rw [F.leftInv_on a (T_ss_S a_in_T)]

  rightInv_on := by
    intro b b_in_mT
    have b_in_mS : b ∈ F.toFun '' S := Set.image_subset _ T_ss_S b_in_mT
    rw [F.rightInv_on b b_in_mS]

  toFun_doubleMonotone := by
    intro a a_in_T b b_in_T
    rw [F.toFun_doubleMonotone a (T_ss_S a_in_T) b (T_ss_S b_in_T)]

@[simp]
theorem OrderIsoOn.mk_of_subset_toFun [Preorder α] [Preorder β] (F : OrderIsoOn α β S)
  {T : Set α} (T_ss_S : T ⊆ S) : (F.mk_of_subset T_ss_S).toFun = F.toFun :=
by
  unfold mk_of_subset
  rfl

@[simp]
theorem OrderIsoOn.mk_of_subset_invFun [Preorder α] [Preorder β] (F : OrderIsoOn α β S)
  {T : Set α} (T_ss_S : T ⊆ S) : (F.mk_of_subset T_ss_S).invFun = F.invFun :=
by
  unfold mk_of_subset
  rfl

theorem OrderIsoOn.invFun_doubleMonotone [Preorder α] [Preorder β] (F : OrderIsoOn α β S) :
  DoubleMonotoneOn F.invFun (F.toFun '' S) :=
by
  intro x ⟨x', x'_in_S, x_eq⟩ y ⟨y', y'_in_S, y_eq⟩
  rw [<-x_eq, <-y_eq]
  (repeat rw [F.leftInv_on]) <;> try assumption
  symm
  apply toFun_doubleMonotone <;> assumption

instance [Preorder α] [Preorder β] : CoeOut (OrderIsoOn α β S) (α → β) where
  coe := fun F x => F.toFun x

variable [Preorder α] [Preorder β]

theorem OrderIsoOn.toFun_injective (F : OrderIsoOn α β S) :
  Function.Injective (Set.restrict S F.toFun) :=
by
  intro ⟨x, x_in_S⟩ ⟨y, y_in_S⟩
  simp
  intro fX_eq_fY
  rw [<-F.leftInv_on _ x_in_S]
  rw [<-F.leftInv_on _ y_in_S]
  rw [fX_eq_fY]

theorem OrderIsoOn.toFun_inj (F : OrderIsoOn α β S) :
  ∀ x ∈ S, ∀ y ∈ S, F.toFun x = F.toFun y → x = y :=
by
  intro x xs y ys fx_eq_fy
  have res := F.toFun_injective (by
    show Set.restrict S F.toFun ⟨x, xs⟩ = Set.restrict S F.toFun ⟨y, ys⟩
    simp
    exact fx_eq_fy
  )
  simp at res
  exact res

theorem OrderIsoOn.mem_toFun_image (F : OrderIsoOn α β S) (y : β):
  y ∈ F.toFun '' S → F.invFun y ∈ S :=
by
  simp
  intro x x_in_S y_eq
  rw [<-y_eq]
  rw [F.leftInv_on x x_in_S]
  assumption

theorem OrderIsoOn.toFun_eq_to_invFun (F : OrderIsoOn α β S) :
  ∀ x ∈ S, ∀ y, F.toFun x = y → x = F.invFun y :=
by
  intro x x_in_S y y_eq
  have y_in_mS : y ∈ F.toFun '' S := by use x
  rw [<-F.rightInv_on y y_in_mS] at y_eq
  apply F.toFun_inj <;> try assumption
  apply mem_toFun_image
  assumption

theorem OrderIsoOn.toFun_eq_iff (F : OrderIsoOn α β S) :
  ∀ x ∈ S, ∀ y ∈ F.toFun '' S, F.toFun x = y ↔ x = F.invFun y :=
by
  intro x x_in_S y y_in_fS
  constructor
  · apply toFun_eq_to_invFun
    assumption
  · intro x_eq
    rw [x_eq]
    apply F.rightInv_on
    assumption

@[simp]
theorem OrderIsoOn.leftInv_image (F : OrderIsoOn α β S) :
  (F.invFun ∘ F.toFun) '' S = S :=
by
  ext x
  simp
  constructor
  · intro ⟨y, y_in_S, y_eq⟩
    rw [F.leftInv_on y y_in_S] at y_eq
    exact y_eq ▸ y_in_S
  · intro x_in_S
    use x
    exact ⟨x_in_S, F.leftInv_on x x_in_S⟩

@[simp]
theorem OrderIsoOn.leftInv_image' (F : OrderIsoOn α β S) :
  F.invFun '' (F.toFun '' S) = S := by rw [Set.image_image, <-Function.comp_def, leftInv_image]

def OrderIsoOn.comp {γ : Type _} [Preorder γ] (F : OrderIsoOn α β S)
  (G : OrderIsoOn β γ (F.toFun '' S)) : OrderIsoOn α γ S where
  toFun := G.toFun ∘ F.toFun
  invFun := F.invFun ∘ G.invFun

  leftInv_on := by
    intro x x_in_S
    simp
    rw [G.leftInv_on _ (by use x)]
    rw [F.leftInv_on x x_in_S]

  rightInv_on := by
    intro y y_in_img
    simp
    rw [Function.comp_def, <-Set.image_image G.toFun F.toFun] at y_in_img
    let ⟨z, z_in_fS, fz_eq_y⟩ := y_in_img
    have z_eq_fy : z = G.invFun y := G.toFun_eq_to_invFun z z_in_fS y fz_eq_y
    rw [<-z_eq_fy, <-fz_eq_y]
    rw [F.rightInv_on]
    assumption

  toFun_doubleMonotone := by
    intro x x_in_S y y_in_S
    simp
    apply Iff.trans
    exact F.toFun_doubleMonotone x x_in_S y y_in_S
    apply G.toFun_doubleMonotone
    use x
    use y

@[simp]
theorem OrderIsoOn.comp_toFun {γ : Type _} [Preorder γ] (F : OrderIsoOn α β S) (G : OrderIsoOn β γ (F.toFun '' S)) :
  (F.comp G).toFun = G.toFun ∘ F.toFun := rfl

def OrderIsoOn.inv (F : OrderIsoOn α β S) : OrderIsoOn β α (F.toFun '' S) where
  toFun := F.invFun
  invFun := F.toFun

  leftInv_on := F.rightInv_on
  rightInv_on := by
    simp
    exact F.leftInv_on

  toFun_doubleMonotone := F.invFun_doubleMonotone

@[simp]
theorem OrderIsoOn.inv_toFun (F : OrderIsoOn α β S) : F.inv.toFun = F.invFun := rfl

@[simp]
theorem OrderIsoOn.inv_invFun (F : OrderIsoOn α β S) : F.inv.invFun = F.toFun := rfl

def OrderIso.orderIsoOn (F : α ≃o β) (S : Set α) : OrderIsoOn α β S where
  toFun := F.toFun
  invFun := F.invFun

  leftInv_on := by
    intro a _
    apply Equiv.left_inv
  rightInv_on := by
    intro b _
    apply Equiv.right_inv

  toFun_doubleMonotone := by
    intro a _ b _
    exact Iff.symm (RelIso.map_rel_iff F)

-- instance : Coe (α ≃o β) (OrderIsoOn α β S) where
--   coe := fun f => OrderIso.orderIsoOn f S

@[simp]
theorem OrderIso.orderIsoOn_toFun (F : α ≃o β) (S : Set α) :
  (OrderIso.orderIsoOn F S).toFun = F.toFun := rfl

@[simp]
theorem OrderIso.orderIsoOn_invFun (F : α ≃o β) (S : Set α) :
  (OrderIso.orderIsoOn F S).invFun = F.invFun := rfl

theorem OrderIso.orderIsoOn_image (F : α ≃o β) (S T : Set α) :
  (OrderIso.orderIsoOn F S).toFun '' T = F '' T := rfl

def OrderIsoOn.identity (α : Type _) [Preorder α] (S : Set α) : OrderIsoOn α α S where
  toFun := id
  invFun := id
  leftInv_on := by simp
  rightInv_on := by simp
  toFun_doubleMonotone := by simp [DoubleMonotoneOn]

@[simp]
theorem OrderIsoOn.comp_inv (F : OrderIsoOn α β S) : ∀ x ∈ S, (F.comp (F.inv)).toFun x = x := by
  simp
  exact F.leftInv_on

end Order

def Filter.InBasis {α : Type _} (F : Filter α) (B : Set (Set α)) : Prop :=
  ∀ (S : Set α), S ∈ F → ∃ T ∈ F, T ∈ B ∧ T ⊆ S

theorem Filter.InBasis.from_hasBasis {α ι : Type _} {F : Filter α} {pi : ι → Prop} {si : ι → Set α}
  (F_basis: Filter.HasBasis F pi si)
  {B : Set (Set α)}
  (basis_subset : ∀ i : ι, pi i → si i ∈ B) :
  Filter.InBasis F B :=
by
  intro S S_in_F
  let ⟨i, pi_i, si_i_ss⟩ := (F_basis.mem_iff' _).mp S_in_F
  use si i
  repeat' apply And.intro
  · rw [F_basis.mem_iff']
    use i
  · apply basis_subset
    assumption
  · assumption

variable {α : Type _} {F : Filter α} {B : Set (Set α)}

theorem Filter.InBasis.mono {C : Set (Set α)} (F_basis : F.InBasis B) (B_ss_C : B ⊆ C) :
  F.InBasis C :=
by
  intro S S_in_F
  let ⟨T, T_in_F, T_in_B, T_ss_S⟩ := F_basis S S_in_F
  use T
  repeat' apply And.intro
  any_goals apply B_ss_C
  all_goals assumption

theorem Filter.InBasis.inf_eq_bot_iff {F G : Filter α} (F_in_basis : F.InBasis B) (G_in_basis : G.InBasis B) :
  F ⊓ G = ⊥ ↔ ∃ U ∈ B, ∃ V ∈ B, U ∈ F ∧ V ∈ G ∧ U ∩ V = ∅ :=
by
  rw [Filter.inf_eq_bot_iff]
  constructor
  · intro ⟨U, U_in_F, V, V_in_G, UV_empty⟩
    let ⟨U', U'_in_F, U'_in_B, U'_ss_U⟩ := F_in_basis U U_in_F
    let ⟨V', V'_in_G, V'_in_B, V'_ss_V⟩ := G_in_basis V V_in_G
    refine ⟨U', U'_in_B, V', V'_in_B, U'_in_F, V'_in_G, ?inter_empty⟩
    apply Set.eq_empty_of_subset_empty
    apply subset_trans _ (subset_of_eq UV_empty)
    exact Set.inter_subset_inter U'_ss_U V'_ss_V
  · intro ⟨U, _, V, _, U_in_F, V_in_G, UV_empty⟩
    exact ⟨U, U_in_F, V, V_in_G, UV_empty⟩

def Filter.InBasis.basis {α : Type _} (F : Filter α) (B : Set (Set α)): Set (Set α) :=
  { S : Set α | S ∈ F ∧ S ∈ B }

theorem Filter.InBasis.basis_subset : Filter.InBasis.basis F B ⊆ B := fun _ ⟨_, S_in_B⟩ => S_in_B

theorem Filter.InBasis.basis_nonempty (F_basis : Filter.InBasis F B): Set.Nonempty (Filter.InBasis.basis F B) :=
by
  let ⟨T, T_in_F, T_in_B, _⟩ := F_basis Set.univ Filter.univ_mem
  exact ⟨T, T_in_F, T_in_B⟩

theorem Filter.InBasis.basis_nonempty' (F_basis : Filter.InBasis F B): Nonempty (Filter.InBasis.basis F B) :=
by
  rw [Set.nonempty_coe_sort]
  exact Filter.InBasis.basis_nonempty F_basis

theorem Filter.InBasis.principal {S : Set α} (S_in_B : S ∈ B) :
  (Filter.principal S).InBasis B :=
by
  intro T
  simp only [mem_principal]
  intro T_in_pS
  use S

theorem Filter.InBasis.basis_hasBasis (F_basis : Filter.InBasis F B):
  F.HasBasis (fun S => S ∈ Filter.InBasis.basis F B) id :=
by
  constructor
  intro T
  simp [basis, and_assoc]
  constructor
  · intro T_in_F
    exact F_basis T T_in_F
  · intro ⟨S, S_in_F, _, S_ss_T⟩
    exact mem_of_superset S_in_F S_ss_T

theorem Filter.InBasis.mem_image_basis_of_injective_on (F : Filter α) (B : Set (Set α))
  {f : Set α → Set β} (f_injective_on : Function.Injective (Set.restrict B f))
  {S : Set α} (S_in_B : S ∈ B) : f S ∈ f '' (basis F B) ↔ S ∈ basis F B :=
by
  simp
  constructor
  · intro ⟨T, T_in_basis, fT_eq_fS⟩
    have T_eq_S : (⟨T, T_in_basis.right⟩ : { s // s ∈ B }) = ⟨S, S_in_B⟩ := by
      apply f_injective_on
      simp
      exact fT_eq_fS
    simp at T_eq_S
    rw [<-T_eq_S]
    assumption
  · intro S_in_basis
    use S

def Filter.InBasis.map_basis {α β : Type _} (F : Filter α) (B : Set (Set α))
  (map : Set α → Set β): Filter β :=
  ⨅ (S : Filter.InBasis.basis F B), Filter.principal (map S)

lemma Filter.InBasis.map_directed {β : Type _} (F_basis : F.InBasis B)
  (map : Set α → Set β) (map_mono : MonotoneOn map B) :
  Directed (fun S T => S ≥ T) fun S : Filter.InBasis.basis F B => Filter.principal (map S.val) :=
by
  intro ⟨S, S_in_F, S_in_B⟩ ⟨T, T_in_F, T_in_B⟩
  have S_int_T_in_F : S ∩ T ∈ F := inter_mem S_in_F T_in_F
  let ⟨U, U_in_F, U_in_B, U_ss_ST⟩ := F_basis _ S_int_T_in_F
  let ⟨U_ss_S, U_ss_T⟩ := Set.subset_inter_iff.mp U_ss_ST
  use ⟨U, U_in_F, U_in_B⟩
  simp
  constructor <;> apply map_mono <;> assumption

theorem Filter.InBasis.map_basis_neBot {β : Type _} [Nonempty β] (F_basis : F.InBasis B)
  (map : Set α → Set β) (map_mono : MonotoneOn map B) (map_nonempty : ∀ S ∈ B, Set.Nonempty (map S)) :
  Filter.NeBot (Filter.InBasis.map_basis F B map) :=
by
  apply Filter.iInf_neBot_of_directed
  · exact Filter.InBasis.map_directed F_basis map map_mono
  · intro ⟨S, S_in_F, S_in_B⟩
    simp
    exact map_nonempty _ S_in_B

theorem Filter.InBasis.map_basis_neBot_of_neBot {β : Type _} [Nonempty β] [Filter.NeBot F] (F_basis : F.InBasis B)
  (map : Set α → Set β) (map_mono : MonotoneOn map B) (map_nonempty : ∀ S ∈ B, S.Nonempty → Set.Nonempty (map S)) :
  Filter.NeBot (Filter.InBasis.map_basis F B map) :=
by
  apply Filter.iInf_neBot_of_directed
  · exact Filter.InBasis.map_directed F_basis map map_mono
  · intro ⟨S, S_in_F, S_in_B⟩
    simp
    exact map_nonempty _ S_in_B (nonempty_of_mem S_in_F)

theorem Filter.InBasis.map_basis_hasBasis {β : Type _} (F_basis : F.InBasis B)
  (map : Set α → Set β) (map_mono : MonotoneOn map B):
  (Filter.InBasis.map_basis F B map).HasBasis (fun T : Set α => T ∈ F ∧ T ∈ B) map :=
by
  unfold map_basis
  constructor
  intro T

  have basis_nonempty := Filter.InBasis.basis_nonempty' F_basis

  rw [Filter.mem_iInf_of_directed]
  · simp [basis, <-and_assoc]
  · exact Filter.InBasis.map_directed F_basis map map_mono

theorem Filter.InBasis.map_basis_inBasis (F_basis : Filter.InBasis F B)
  (map : Set α → Set β) (map_mono : MonotoneOn map B) :
  (Filter.InBasis.map_basis F B map).InBasis (map '' B) :=
by
  intro S S_in_map

  have has_basis := Filter.InBasis.map_basis_hasBasis F_basis map map_mono

  rw [has_basis.mem_iff'] at S_in_map
  let ⟨T, ⟨T_in_F, T_in_B⟩, mapT_ss_S⟩ := S_in_map

  use map T
  repeat' apply And.intro
  · rw [has_basis.mem_iff']
    use T
  · simp
    use T
  · assumption

theorem Filter.InBasis.map_basis_id (F_basis : F.InBasis B) (f : Set α → Set α) (f_idlike : ∀ S ∈ B, f S = S):
  Filter.InBasis.map_basis F B f = F :=
by
  simp [map_basis]
  ext S
  have basis_nonempty := Filter.InBasis.basis_nonempty' F_basis
  have basis_directed := Filter.InBasis.map_directed F_basis id (monotone_id.monotoneOn B)
  simp only [id_eq] at basis_directed

  conv => {
    lhs
    rhs
    congr; intro x
    rw [f_idlike _ x.prop.right]
  }

  rw [mem_iInf_of_directed basis_directed]
  rw [(F_basis.basis_hasBasis).mem_iff]
  simp

theorem Filter.InBasis.mem_map_basis
  (map : Set α → Set β) (map_mono : MonotoneOn map B)
  (F_basis : Filter.InBasis F B) (x : Set β) :
  x ∈ (Filter.InBasis.map_basis F B map) ↔ ∃ y : Set α, y ∈ F ∧ y ∈ B ∧ map y ⊆ x :=
by
  rw [(Filter.InBasis.map_basis_hasBasis F_basis map map_mono).mem_iff]
  simp only [and_assoc]

theorem nhds_in_basis [TopologicalSpace α] (p : α) (B_basis : TopologicalSpace.IsTopologicalBasis B):
  (nhds p).InBasis B :=
  Filter.InBasis.from_hasBasis B_basis.nhds_hasBasis (fun _ ⟨in_B, _⟩ => in_B)

theorem Filter.InBasis.basis_map_basis (map : Set α → Set β)
  (map_double_mono : DoubleMonotoneOn map B) {F : Filter α} (F_basis : F.InBasis B):
  Filter.InBasis.basis (Filter.InBasis.map_basis F B map) (map '' B) = map '' (Filter.InBasis.basis F B) :=
by
  ext x
  simp [basis]
  rw [Filter.InBasis.mem_map_basis map map_double_mono.monotoneOn F_basis]
  constructor
  · intro ⟨⟨y1, y1_in_F, _, y1_ss_x⟩, ⟨y2, y2_in_B, y2_eq⟩⟩
    use y2
    rw [<-y2_eq] at y1_ss_x
    repeat' apply And.intro
    apply Filter.mem_of_superset y1_in_F
    rw [map_double_mono.subset_iff]
    all_goals assumption
  · intro ⟨S, ⟨S_in_F, S_in_B⟩, x_eq⟩
    constructor
    all_goals use S
    repeat' apply And.intro
    any_goals apply subset_of_eq
    all_goals assumption

theorem Filter.InBasis.mem_basis_iff_of_basis_set (F : Filter α) {S : Set α} (S_in_B : S ∈ B):
  S ∈ basis F B ↔ S ∈ F :=
by
  unfold basis
  simp
  tauto

theorem Filter.InBasis.map_mem_map_basis_of_basis_set (map : Set α → Set β) (map_double_mono : DoubleMonotoneOn map B)
  {F : Filter α} (F_basis : F.InBasis B) {S : Set α} (S_in_B : S ∈ B):
  map S ∈ Filter.InBasis.map_basis F B map ↔ S ∈ F :=
by
  suffices S ∈ basis F B ↔ map S ∈ map '' (basis F B) by
    rw [mem_basis_iff_of_basis_set _ S_in_B] at this
    rw [this]
    have mS_in_mB : map S ∈ map '' B := by
      simp
      use S
    rw [<-basis_map_basis map map_double_mono F_basis]
    rw [mem_basis_iff_of_basis_set _ mS_in_mB]

  rw [Filter.InBasis.mem_image_basis_of_injective_on _ _ map_double_mono.injective S_in_B]


theorem Filter.InBasis.mem_map_basis'
  (map : Set α → Set β) (map_double_mono : DoubleMonotoneOn map B)
  (F_basis : Filter.InBasis F B) {x : Set β} (x_in_basis : x ∈ map '' B):
  x ∈ (Filter.InBasis.map_basis F B map) ↔ ∃ y : Set α, y ∈ F ∧ y ∈ B ∧ map y = x :=
by
  let ⟨y, y_in_B, y_eq⟩ := x_in_basis
  rw [<-y_eq]
  rw [map_mem_map_basis_of_basis_set map map_double_mono F_basis y_in_B]
  constructor
  · intro y_in_F
    use y
  · intro ⟨z, z_in_F, z_in_B, z_eq_y⟩
    apply (map_double_mono.injective' z z_in_B y y_in_B) at z_eq_y
    exact z_eq_y ▸ z_in_F

-- TODO: clean this up :c
theorem Filter.InBasis.map_basis_comp {γ : Type _} (m₁ : OrderIsoOn (Set α) (Set β) B)
  (m₂ : OrderIsoOn (Set β) (Set γ) (m₁.toFun '' B))
  {F : Filter α} (F_basis : F.InBasis B):
  Filter.InBasis.map_basis (Filter.InBasis.map_basis F B m₁) (m₁.toFun '' B) m₂.toFun = Filter.InBasis.map_basis F B (m₁.comp m₂).toFun :=
by

  unfold map_basis
  rw [iInf_subtype]
  simp [basis_map_basis]
  rw [<-iInf_subtype (f := fun i => Filter.principal (m₂.toFun i.val))]

  have F'_basis := (Filter.InBasis.map_basis_inBasis F_basis m₁.toFun m₁.toFun_doubleMonotone.monotoneOn)
  have basis_nonempty : Nonempty { i // i ∈ basis (⨅ S : basis F B, Filter.principal (m₁.toFun ↑S)) (m₁.toFun '' B) } :=
    (Filter.InBasis.basis_nonempty' F'_basis).elim (fun p => ⟨p.val, p.prop⟩)

  have basis_nonempty' := Filter.InBasis.basis_nonempty' F_basis

  have m₁_directed := Filter.InBasis.map_directed F_basis m₁.toFun m₁.toFun_doubleMonotone.monotoneOn
  have m₂_directed := Filter.InBasis.map_directed F'_basis m₂.toFun m₂.toFun_doubleMonotone.monotoneOn

  have m₁₂_directed := Filter.InBasis.map_directed F_basis (m₁.comp m₂).toFun (m₁.comp m₂).toFun_doubleMonotone.monotoneOn
  simp only [OrderIsoOn.comp_toFun, Function.comp_apply] at m₁₂_directed

  ext S
  rw [mem_iInf_of_directed]
  swap
  assumption

  constructor
  · intro ⟨⟨T, ⟨T_in_basis, T_in_m₁B⟩⟩, m₂T_ss_S⟩
    simp at m₂T_ss_S
    apply Filter.mem_of_superset _ m₂T_ss_S
    rw [mem_iInf_of_directed]
    rw [mem_iInf_of_directed] at T_in_basis
    any_goals assumption

    let ⟨⟨U, ⟨U_in_F, U_in_B⟩⟩, m₁U_ss_T⟩ := T_in_basis
    simp at m₁U_ss_T
    use ⟨U, ⟨U_in_F, U_in_B⟩⟩

    simp
    apply m₂.toFun_doubleMonotone.monotoneOn
    use U
    all_goals assumption
  · intro S_in_iInf
    rw [mem_iInf_of_directed] at S_in_iInf
    any_goals assumption
    let ⟨⟨U, ⟨U_in_F, U_in_B⟩⟩, m₁₂U_ss_S⟩ := S_in_iInf
    simp at m₁₂U_ss_S

    have m₁U_in_basis : m₁.toFun U ∈ basis (map_basis F B m₁.toFun) (m₁.toFun '' B) := by
      constructor
      swap
      use U
      rw [map_mem_map_basis_of_basis_set m₁.toFun m₁.toFun_doubleMonotone]
      all_goals assumption

    use ⟨m₁.toFun U, m₁U_in_basis⟩
    assumption

theorem Filter.InBasis.map_basis_inv (map : OrderIsoOn (Set α) (Set β) B)
  {F : Filter α} (F_basis : F.InBasis B):
  Filter.InBasis.map_basis (Filter.InBasis.map_basis F B map) (map.toFun '' B) map.invFun = F :=
by
  rw [<-map.inv_toFun, map_basis_comp _ _ F_basis, map_basis_id F_basis]
  exact OrderIsoOn.comp_inv map

theorem Filter.InBasis.map_basis_inv' (map : OrderIsoOn (Set α) (Set β) B)
  {F : Filter β} (F_basis : F.InBasis (map.toFun '' B)):
  Filter.InBasis.map_basis (Filter.InBasis.map_basis F (map.toFun '' B) map.invFun) B map.toFun = F :=
by
  nth_rw 4 [<-OrderIsoOn.leftInv_image' map]
  rw [<-map.inv_toFun]
  nth_rw 5 [<-map.inv_invFun]
  rw [<-map.inv.inv_toFun]

  rw [map_basis_comp map.inv map.inv.inv F_basis, map_basis_id F_basis]

  simp
  intro a a_in_B
  rw [map.leftInv_on a a_in_B]


theorem Filter.InBasis.map_basis_mono (map : OrderIsoOn (Set α) (Set β) B)
  {F G : Filter α} (F_basis : F.InBasis B) (G_basis : G.InBasis B):
  Filter.InBasis.map_basis F B map.toFun ≤ Filter.InBasis.map_basis G B map.toFun → F ≤ G :=
by
  intro mF_le_mG S S_in_G
  let ⟨T, T_in_G, T_in_B, T_ss_S⟩ := G_basis S S_in_G
  have mT_in_mG : map.toFun T ∈ map_basis G B map.toFun := by
    rw [map_mem_map_basis_of_basis_set map.toFun map.toFun_doubleMonotone]
    all_goals assumption
  have mT_in_mF := mF_le_mG mT_in_mG
  rw [map_mem_map_basis_of_basis_set map.toFun map.toFun_doubleMonotone] at mT_in_mF
  apply Filter.mem_of_superset mT_in_mF
  all_goals assumption

theorem Filter.InBasis.map_basis_le_iff (map : OrderIsoOn (Set α) (Set β) B)
  {F G : Filter α} (F_basis : F.InBasis B) (G_basis : G.InBasis B):
  Filter.InBasis.map_basis F B map.toFun ≤ Filter.InBasis.map_basis G B map.toFun ↔ F ≤ G :=
by
  constructor
  · exact map_basis_mono map F_basis G_basis
  · nth_rw 1 [<-map_basis_inv map F_basis]
    nth_rw 1 [<-map_basis_inv map G_basis]
    rw [<-OrderIsoOn.inv_toFun]
    apply map_basis_mono
    all_goals apply map_basis_inBasis
    any_goals assumption
    all_goals exact map.toFun_doubleMonotone.monotoneOn

theorem Filter.InBasis.map_basis_inBasis' (map : OrderIsoOn (Set α) (Set β) B)
  {F : Filter α} (F_basis : F.InBasis B) :
  (Filter.InBasis.map_basis F B map.toFun).InBasis (map.toFun '' B) :=
by
  apply map_basis_inBasis
  assumption
  exact map.toFun_doubleMonotone.monotoneOn

theorem Filter.InBasis.map_basis_inBasis₂ (map : OrderIsoOn (Set α) (Set β) B)
  {F : Filter β} (F_basis : F.InBasis (map.toFun '' B)) :
  (Filter.InBasis.map_basis F (map.toFun '' B) map.invFun).InBasis B :=
by
  nth_rw 4 [<-OrderIsoOn.leftInv_image map]
  rw [Function.comp_def, <-Set.image_image map.invFun]
  apply map_basis_inBasis
  assumption
  exact map.invFun_doubleMonotone.monotoneOn

theorem Filter.InBasis.map_basis_le_inv (map : OrderIsoOn (Set α) (Set β) B)
  {F : Filter α} (F_basis : F.InBasis B) {G : Filter β} (G_basis : G.InBasis (map.toFun '' B)) :
  F ≤ Filter.InBasis.map_basis G (map.toFun '' B) map.invFun ↔ Filter.InBasis.map_basis F B map.toFun ≤ G :=
by
  suffices ∀ map : OrderIsoOn (Set α) (Set β) B, ∀ F : Filter α, F.InBasis B → ∀ G : Filter β, G.InBasis (map.toFun '' B) →
    F ≤ Filter.InBasis.map_basis G (map.toFun '' B) map.invFun →
    Filter.InBasis.map_basis F B map.toFun ≤ G
  by
    constructor
    · apply this
      all_goals assumption
    · intro mF_le_G

      nth_rw 1 [<-map_basis_inv map F_basis]
      apply map_basis_mono map
      rw [map_basis_inv _ F_basis]
      any_goals assumption
      apply map_basis_inBasis₂
      assumption

      apply this
      rw [map_basis_inv _ F_basis]
      assumption
      apply map_basis_inBasis'
      apply map_basis_inBasis₂
      assumption

      rw [<-OrderIsoOn.inv_toFun, map_basis_le_iff]

      · simp
        rw [map_basis_inv']
        exact mF_le_G
        assumption
      · apply map_basis_inBasis'
        assumption
      · simp
        rw [map_basis_inv']
        all_goals assumption

  intro map F F_basis G G_basis F_le_mG
  intro S S_in_G
  let ⟨T, T_in_G, T_in_mB, T_ss_S⟩ := G_basis S S_in_G
  let ⟨U, U_in_B, T_eq⟩ := T_in_mB
  have mT_in_F : map.invFun T ∈ F := by
    apply F_le_mG
    rw [map_mem_map_basis_of_basis_set]
    any_goals assumption
    exact map.invFun_doubleMonotone
  have U_in_F : U ∈ F := by
    rw [<-T_eq] at mT_in_F
    rw [map.leftInv_on U U_in_B] at mT_in_F
    exact mT_in_F

  apply Filter.mem_of_superset
  · show map.toFun U ∈ map_basis F B map.toFun
    rw [map_mem_map_basis_of_basis_set]
    any_goals assumption
    exact map.toFun_doubleMonotone
  · rw [T_eq]
    assumption

theorem Filter.InBasis.map_basis_le_inv' (map : OrderIsoOn (Set α) (Set β) B)
  {F : Filter α} (F_basis : F.InBasis B) {G : Filter β} (G_basis : G.InBasis (map.toFun '' B)) :
  G ≤ Filter.InBasis.map_basis F B map.toFun ↔ Filter.InBasis.map_basis G (map.toFun '' B) map.invFun ≤ F :=
by
  nth_rw 1 [<-map.leftInv_image']
  rw [<-map.inv_invFun, <-map.inv_toFun]

  rw [<-map.leftInv_image', <-map.inv_toFun] at F_basis
  nth_rw 1 [map.inv_invFun]
  rw [Filter.InBasis.map_basis_le_inv _ G_basis F_basis]
  simp

@[simp]
theorem Filter.InBasis.map_basis_toOrderIsoSet {M : Type*} (map : M) [EquivLike M α β]
  {F : Filter α} (F_basis : F.InBasis B) :
  Filter.InBasis.map_basis F B (EquivLike.toEquiv map).toOrderIsoSet =
  F.map map :=
by
  simp
  ext S
  rw [mem_map_basis _ _ F_basis, Filter.mem_map, F_basis.basis_hasBasis.mem_iff, basis]
  swap
  {
    apply Monotone.monotoneOn
    exact OrderHomClass.mono _
  }
  simp
  rw [(by rfl : map ⁻¹' S = (EquivLike.toEquiv map) ⁻¹' S)]
  rw [Set.preimage_equiv_eq_image_symm]
  conv => {
    lhs; congr; intro y
    rw [Equiv.toOrderIsoSet_apply]
  }
  conv => {
    rhs; congr; intro y
    rw [<-Equiv.subset_image, and_assoc]
  }

instance Filter.InBasis.order_bot : OrderBot { F : Filter α // F.InBasis B ∨ F = ⊥ } where
  bot := ⟨⊥, by right; rfl ⟩
  bot_le := by
    intro ⟨F, _⟩
    simp

theorem Filter.InBasis.inf {F₁ F₂ : Filter α}
  (basis_closed : ∀ b1 b2 : Set α, b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  (F₁_basis : F₁.InBasis B) (F₂_basis : F₂.InBasis B) (nebot : Filter.NeBot (F₁ ⊓ F₂)):
  Filter.InBasis (F₁ ⊓ F₂) B :=
by
  intro T T_in_inf

  let ⟨T₁, T₁_in_F₁, T₂, T₂_in_F₂, T_eq⟩ := Filter.mem_inf_iff.mp T_in_inf

  let ⟨S₁, S₁_in_F₁, S₁_in_B, S₁_ss_T₁⟩ := F₁_basis T₁ T₁_in_F₁
  let ⟨S₂, S₂_in_F₂, S₂_in_B, S₂_ss_T₂⟩ := F₂_basis T₂ T₂_in_F₂

  let S := S₁ ∩ S₂
  have S_in_inf : S ∈ F₁ ⊓ F₂ := by
    rw [Filter.mem_inf_iff]
    exact ⟨S₁, S₁_in_F₁, S₂, S₂_in_F₂, rfl⟩

  use S
  repeat' apply And.intro
  · assumption
  · apply basis_closed S₁ S₂ S₁_in_B S₂_in_B
    apply Filter.nonempty_of_mem S_in_inf
  · rw [T_eq]
    exact Set.inter_subset_inter S₁_ss_T₁ S₂_ss_T₂

theorem Finset.Nonempty.induction {α : Type*} {p : ∀ (F : Finset α), F.Nonempty → Prop} [DecidableEq α] (initial : ∀ a : α, p {a} (Finset.singleton_nonempty a))
  (insert : ∀ ⦃a : α⦄ {s : Finset α} (ne : s.Nonempty), a ∉ s → p s ne → p (insert a s) (Finset.insert_nonempty _ _)) : ∀ s, ∀ ne : s.Nonempty, p s ne :=
by
  intro S S_nonempty
  apply Finset.Nonempty.cons_induction
  exact initial
  intro a s a_notin_s s_nonempty p_rec
  simp
  apply insert <;> assumption

theorem Finset.Nonempty.induction_on' {α : Type*} {p : ∀ (F : Finset α), F.Nonempty → Prop} [DecidableEq α] {I : Finset α} (I_nonempty : I.Nonempty)
  (initial : ∀ a : α, a ∈ I → p {a} (Finset.singleton_nonempty a))
  (insert : ∀ ⦃a : α⦄ {s : Finset α} (ne : s.Nonempty), a ∈ I → a ∉ s → (s ⊆ I) → p s ne → p (insert a s) (Finset.insert_nonempty _ _)) :
  p I I_nonempty :=
by
  suffices ∀ (s : Finset α) (ne : Finset.Nonempty s), s ⊆ I → p s ne by
    exact this I I_nonempty (subset_refl _)
  apply Finset.Nonempty.induction
  · simp only [singleton_subset_iff]
    exact initial
  · intro a s ne a_notin_s h_ind insert_subset
    have ⟨a_in_I, s_ss_I⟩ := Finset.insert_subset_iff.mp insert_subset
    specialize h_ind s_ss_I
    apply insert <;> try assumption

theorem Filter.InBasis.sInf_finset_closed
  (basis_closed : ∀ b1 b2 : Set α, b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  (I : Finset (Filter α))
  (I_nonempty : Finset.Nonempty I)
  (in_basis : ∀ (F : Filter α), F ∈ I → F.InBasis B)
  (inf_nebot : Filter.NeBot (⨅ f ∈ I, f)) :
  Filter.InBasis (sInf I) B := by
  rw [sInf_eq_iInf]
  have dec_eq: DecidableEq (Filter α) := Classical.typeDecidableEq _

  apply Finset.Nonempty.induction_on' I_nonempty (p := fun i _ => InBasis (⨅ a ∈ i, a) B)
  · simp
    exact in_basis
  · intro F I' _ F_in_I _ I'_ss_I I'_basis
    simp only [Finset.mem_insert_coe]
    rw [iInf_insert (s := I') (b := F)]
    apply Filter.InBasis.inf basis_closed _ I'_basis
    · simp only [<-Finset.mem_coe]
      show NeBot (id F ⊓ ⨅ f ∈ (I' : Set (Filter α)), id f)
      rw [<-iInf_insert]
      apply Filter.neBot_of_le (f := ⨅ f ∈ I, f)
      simp only [id_eq, <-Finset.mem_coe]
      apply iInf_le_iInf_of_subset
      exact Set.insert_subset F_in_I I'_ss_I
    · exact in_basis _ F_in_I

theorem Filter.InBasis.sInf_closed
  (basis_closed : ∀ b1 b2 : Set α, b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  (I : Set (Filter α))
  (I_nonempty : I.Nonempty)
  (in_basis : ∀ (F : Filter α), F ∈ I → F.InBasis B)
  (inf_nebot : Filter.NeBot (⨅ f ∈ I, f)) :
  Filter.InBasis (sInf I) B :=
by
  rw [sInf_eq_iInf]

  have iInf_I_eq := iInf_subtype (p := fun x => x ∈ I) (f := fun x => x.val)
  simp only at iInf_I_eq

  intro T T_in_sinf
  rw [<-iInf_I_eq] at T_in_sinf
  rw [Filter.mem_iInf_finite] at T_in_sinf
  let ⟨S, T_in_inf⟩ := T_in_sinf
  clear T_in_sinf
  have dec_eq: DecidableEq (Filter α) := Classical.typeDecidableEq _

  let S' := Finset.image (Subtype.val) S

  have S'_eq : ⨅ i ∈ S, i.val = sInf S' := by
    rw [sInf_eq_iInf]
    simp
    rw [iInf_subtype]

  by_cases S_empty? : S.Nonempty
  swap
  {
    rw [Finset.not_nonempty_iff_eq_empty] at S_empty?
    rw [S_empty?] at T_in_inf
    simp at T_in_inf
    let ⟨F, F_in_I⟩ := I_nonempty
    rw [T_in_inf]
    simp
    let ⟨U, U_in_F, U_in_B, _⟩ := in_basis F F_in_I Set.univ Filter.univ_mem
    use U
    constructor
    · rw [<-iInf_I_eq]
      apply Filter.mem_iInf_of_mem ⟨F, F_in_I⟩
      exact U_in_F
    · assumption
  }

  have S_basis : Filter.InBasis (⨅ i ∈ S, i.val) B := by
    rw [S'_eq]
    apply Filter.InBasis.sInf_finset_closed basis_closed
    · simp
      assumption
    · unfold_let
      simp only [Finset.mem_image]
      intro F ⟨F', _, F'_eq⟩
      apply in_basis
      rw [<-F'_eq]
      exact Subtype.mem F'
    · simp only [<-Finset.mem_coe]
      apply Filter.neBot_of_le (f := ⨅ f ∈ I, f)
      apply iInf_le_iInf_of_subset
      simp

  have S_inf_le_I_inf : ⨅ i ∈ I, i ≤ ⨅ i ∈ S, i.val := by
    rw [S'_eq, sInf_eq_iInf]
    apply iInf_le_iInf_of_subset
    simp

  let ⟨U, U_in_inf, U_in_B, U_ss_T⟩ := S_basis T T_in_inf
  use U
  repeat' apply And.intro
  apply S_inf_le_I_inf
  all_goals assumption

theorem Filter.InBasis.is_atomic
  (basis_closed : ∀ b1 b2 : Set α, b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  : IsAtomic { F : Filter α // F.InBasis B ∨ F = ⊥ } :=
by
  by_cases α_nonempty? : Nonempty α
  swap
  {
    rw [not_nonempty_iff] at α_nonempty?
    constructor
    intro ⟨F, _⟩
    left
    simp
    exact filter_eq_bot_of_isEmpty F
  }

  apply IsAtomic.of_isChain_bounded
  intro ch ch_chain ch_nonempty bot_notin_ch

  let ch' : Set (Filter α) := { F : Filter α | ∃ F' ∈ ch, F'.val = F }

  have ch'_chain : IsChain (fun x y => x ≥ y) ch' := by
    intro f f_in_ch' g g_in_ch' f_ne_g
    let ⟨f', f'_in_ch, f'_eq⟩ := f_in_ch'
    let ⟨g', g'_in_ch, g'_eq⟩ := g_in_ch'
    rw [<-f'_eq, <-g'_eq]
    simp
    have f'_ne_g' : f' ≠ g' := by
      intro eq
      rw [eq] at f'_eq
      rw [<-f'_eq, <-g'_eq] at f_ne_g
      exact f_ne_g rfl
    symm at f'_ne_g'
    apply ch_chain <;> assumption

  have bot_notin_ch' : ⊥ ∉ ch' := by
    intro ⟨f, f_in_ch, f_eq_bot⟩
    simp at f_eq_bot
    rw [f_eq_bot] at f_in_ch
    exact bot_notin_ch f_in_ch

  let sch := sInf ch'
  have sch_neBot : Filter.NeBot sch := by
    apply Filter.sInf_neBot_of_directed
    apply ch'_chain.directedOn
    exact bot_notin_ch'

  have sch_basis : InBasis sch B := by
    apply Filter.InBasis.sInf_closed basis_closed
    · let ⟨x, x_in_ch⟩ := ch_nonempty
      use x
      simp only [Subtype.exists, exists_and_right, exists_eq_right, Set.mem_setOf_eq,
        Subtype.coe_eta, or_true, exists_prop]
      exact ⟨x.prop, x_in_ch⟩
    · intro F F_in_ch
      simp at F_in_ch
      let ⟨F_basis, F_in_ch⟩ := F_in_ch
      apply F_basis.elim id
      intro F_eq_bot
      exfalso
      simp [F_eq_bot] at F_in_ch
      exact bot_notin_ch F_in_ch
    · rw [<-sInf_eq_iInf]
      exact sch_neBot

  let sch' : { F // InBasis F B ∨ F = ⊥ } := ⟨sch, Or.intro_left _ sch_basis⟩
  have sch'_ne_bot : sch' ≠ ⊥ := by
    unfold_let
    intro eq_bot
    rw [Subtype.mk_eq_bot_iff] at eq_bot
    apply sch_neBot.ne
    exact eq_bot
    right; rfl

  use sch'
  use sch'_ne_bot
  unfold lowerBounds
  simp
  intro F F_basis F_in_ch
  apply sInf_le
  simp
  use F_basis

/--
This is a formulation for prefilters in a basis that are ultra.
It is a weaker statement than regular ultrafilters,
but it allows for some nice properties, like the equivalence of cluster points and neighborhoods.
--/
structure UltrafilterInBasis {α : Type _} (B : Set (Set α)) :=
  filter : Filter α

  in_basis : Filter.InBasis filter B

  ne_bot : Filter.NeBot filter

  ultra : ∀ (F' : Filter α), F'.InBasis B → F'.NeBot → F' ≤ filter → filter ≤ F'

instance : CoeOut (@UltrafilterInBasis α B) (Filter α) where
  coe := fun U => U.filter

instance : Membership (Set α) (UltrafilterInBasis B) where
  mem := fun s U => s ∈ U.filter

@[simp]
theorem UltrafilterInBasis.mem_coe (U : UltrafilterInBasis B) (S : Set α):
  S ∈ U.filter ↔ S ∈ U := by rfl

instance (U : UltrafilterInBasis B): Filter.NeBot (U.filter) where
  ne' := U.ne_bot.ne

theorem UltrafilterInBasis.exists_le {α: Type _} {F : Filter α} {B : Set (Set α)}
  (basis_closed : ∀ b1 b2 : Set α, b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  (F_basis : Filter.InBasis F B) (F_nebot : Filter.NeBot F) :
  ∃ U : UltrafilterInBasis B, U.filter ≤ F :=
by
  have atomic := Filter.InBasis.is_atomic basis_closed
  let ⟨⟨U, U_basis⟩, U_atom, U_le_F⟩ := (atomic.eq_bot_or_exists_atom_le ⟨F, Or.intro_left _ F_basis⟩).resolve_left (by simp; exact F_nebot.ne)

  have U_neBot : Filter.NeBot U := by
    constructor
    have U_atom := U_atom.left
    simp at U_atom
    exact U_atom

  have U_basis := U_basis.resolve_right U_neBot.ne

  simp at U_le_F

  have U_ultra : ∀ (F' : Filter α), F'.InBasis B → F'.NeBot → F' ≤ U → U ≤ F' := by
    intro F' F'_basis F'_neBot F'_le
    have U_atom := U_atom.right
    simp at U_atom
    cases le_iff_lt_or_eq.mp F'_le with
    | inl F'_lt_U =>
      exfalso
      apply F'_neBot.ne
      apply U_atom
      left
      all_goals assumption
    | inr F'_eq_U =>
      symm at F'_eq_U
      exact le_of_eq F'_eq_U

  use ⟨U, U_basis, U_neBot, U_ultra⟩

noncomputable def UltrafilterInBasis.of {α: Type _} {F : Filter α} {B : Set (Set α)}
  (basis_closed : ∀ b1 b2 : Set α, b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  (F_basis : Filter.InBasis F B) [F_neBot : Filter.NeBot F]:
  UltrafilterInBasis B := Exists.choose $ UltrafilterInBasis.exists_le basis_closed F_basis F_neBot

theorem UltrafilterInBasis.of_le {α: Type _} {F : Filter α} {B : Set (Set α)}
  (basis_closed : ∀ b1 b2 : Set α, b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  (F_basis : Filter.InBasis F B) [F_neBot : Filter.NeBot F]:
  UltrafilterInBasis.of basis_closed F_basis ≤ F :=
by
  exact Exists.choose_spec $ UltrafilterInBasis.exists_le basis_closed F_basis F_neBot

theorem UltrafilterInBasis.coe_in_basis (U : UltrafilterInBasis B) : Filter.InBasis U B := U.in_basis

theorem UltrafilterInBasis.map_basis_ultra {β : Type _}
  (empty_notin_B : ∅ ∉ B)
  (map : OrderIsoOn (Set α) (Set β) B)
  (U : UltrafilterInBasis B) :
  ∀ (F : Filter β), F.InBasis (map.toFun '' B) → F.NeBot →
  F ≤ Filter.InBasis.map_basis U B map → Filter.InBasis.map_basis U B map ≤ F :=
by
  have α_nonempty: Nonempty α := by
    by_contra α_trivial
    rw [not_nonempty_iff] at α_trivial
    apply U.ne_bot.ne
    exact Filter.filter_eq_bot_of_isEmpty U.filter

  intro F F_in_basis F_neBot F_le_map
  intro S S_in_F

  have U_le_mF : U ≤ Filter.InBasis.map_basis F (map.toFun '' B) map.invFun := by
    apply U.ultra
    apply Filter.InBasis.map_basis_inBasis₂
    · assumption
    · apply Filter.InBasis.map_basis_neBot_of_neBot F_in_basis
      exact map.invFun_doubleMonotone.monotoneOn
      intro S ⟨T, T_in_B, T_eq⟩ _
      rw [<-T_eq, map.leftInv_on T T_in_B]
      rw [Set.nonempty_iff_ne_empty]
      intro T_empty
      exact empty_notin_B (T_empty ▸ T_in_B)
    · rw [Filter.InBasis.map_basis_le_inv' map U.in_basis F_in_basis] at F_le_map
      exact F_le_map

  rw [Filter.InBasis.mem_map_basis map.toFun map.toFun_doubleMonotone.monotoneOn U.in_basis]
  let ⟨T, T_in_F, T_in_mB, T_ss_S⟩ := F_in_basis S S_in_F

  use map.invFun T
  repeat' apply And.intro
  · apply U_le_mF
    rw [Filter.InBasis.map_mem_map_basis_of_basis_set]
    any_goals assumption
    exact map.invFun_doubleMonotone
  · apply map.mem_toFun_image
    assumption
  · rw [map.rightInv_on T T_in_mB]
    exact T_ss_S

def UltrafilterInBasis.map_basis {β : Type _}
  (empty_notin_B : ∅ ∉ B)
  (map : OrderIsoOn (Set α) (Set β) B)
  (empty_notin_mB : ∅ ∉ map.toFun '' B)
  (U : UltrafilterInBasis B) :
  UltrafilterInBasis (map.toFun '' B)
where
  filter := Filter.InBasis.map_basis U.filter B map.toFun
  in_basis := U.in_basis.map_basis_inBasis' map
  ne_bot := by
    have β_nonempty : Nonempty β := by
      by_contra β_trivial
      rw [not_nonempty_iff] at β_trivial
      apply empty_notin_mB
      rw [Subsingleton.mem_iff_nonempty]
      simp
      let ⟨T, _, T_in_B, _⟩ := U.in_basis _ (Filter.univ_mem)
      use T

    apply Filter.InBasis.map_basis_neBot_of_neBot U.in_basis _ map.toFun_doubleMonotone.monotoneOn
    intro S S_in_B _
    by_contra empty
    rw [Set.not_nonempty_iff_eq_empty] at empty
    apply empty_notin_mB
    use S
  ultra := U.map_basis_ultra empty_notin_B map

@[simp]
theorem UltrafilterInBasis.mem_map_basis {β : Type _}
  (empty_notin_B : ∅ ∉ B)
  (map : OrderIsoOn (Set α) (Set β) B)
  (empty_notin_mB : ∅ ∉ map.toFun '' B)
  (U : UltrafilterInBasis B)
  (S : Set β):
  S ∈ U.map_basis empty_notin_B map empty_notin_mB ↔ S ∈ Filter.InBasis.map_basis U.filter B map.toFun :=
by
  rw [map_basis]
  rfl

@[simp]
theorem UltrafilterInBasis.map_basis_filter {β : Type _}
  (empty_notin_B : ∅ ∉ B)
  (map : OrderIsoOn (Set α) (Set β) B)
  (empty_notin_mB : ∅ ∉ map.toFun '' B)
  (U : UltrafilterInBasis B):
  (U.map_basis empty_notin_B map empty_notin_mB).filter = Filter.InBasis.map_basis U.filter B map.toFun :=
by
  rw [map_basis]

/-
theorem compl_not_mem_iff : sᶜ ∉ f ↔ s ∈ f :=
  ⟨fun hsc =>
    le_principal_iff.1 <|
      f.le_of_inf_neBot ⟨fun h => hsc <| mem_of_eq_bot <| by rwa [compl_compl]⟩,
    compl_not_mem⟩
-/

theorem UltrafilterInBasis.unique (U : UltrafilterInBasis B) {F : Filter α} [Filter.NeBot F] (F_in_basis : F.InBasis B) :
  F ≤ U.filter → U.filter = F :=
by
  intro F_le_U
  apply le_antisymm
  apply U.ultra
  all_goals assumption

theorem UltrafilterInBasis.eq_of_le (U U' : UltrafilterInBasis B) :
  U.filter ≤ U'.filter → U = U' :=
by
  intro U_le_U'
  symm
  rw [mk.injEq]
  exact unique _ U.in_basis U_le_U'

theorem UltrafilterInBasis.le_of_basis_sets (U U' : UltrafilterInBasis B) :
  (∀ S : Set α, S ∈ B → S ∈ U' → S ∈ U) → U.filter ≤ U'.filter :=
by
  intro h
  intro S S_in_U'
  let ⟨T, T_in_B, T_in_U', T_ss_S⟩ := U'.in_basis _ S_in_U'
  apply Filter.mem_of_superset _ T_ss_S
  apply h <;> assumption

theorem UltrafilterInBasis.le_of_inf_neBot (U : UltrafilterInBasis B)
  (B_closed : ∀ (b1 b2 : Set α), b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  {F : Filter α} (F_in_basis : F.InBasis B)
  (inf_neBot : Filter.NeBot (U.filter ⊓ F)) : U.filter ≤ F :=
by
  apply le_of_inf_eq
  symm
  apply U.unique
  · exact Filter.InBasis.inf B_closed U.in_basis F_in_basis inf_neBot
  · exact inf_le_left

theorem UltrafilterInBasis.mem_of_compl_not_mem (U : UltrafilterInBasis B)
  (B_closed : ∀ (b1 b2 : Set α), b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  {S : Set α} (S_in_B : S ∈ B):
  Sᶜ ∉ U → S ∈ U :=
by
  intro sc_notin_U
  rw [<-mem_coe, <-Filter.le_principal_iff]
  apply le_of_inf_neBot U B_closed
  · exact Filter.InBasis.principal S_in_B
  · constructor
    intro eq_bot
    apply sc_notin_U
    apply Filter.mem_of_eq_bot
    rwa [compl_compl]

theorem UltrafilterInBasis.mem_or_compl_mem (U : UltrafilterInBasis B)
  (B_closed : ∀ (b1 b2 : Set α), b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  {S : Set α} (S_in_B : S ∈ B):
  Sᶜ ∈ U ∨ S ∈ U :=
by
  by_cases S_in_U? : S ∈ U
  right; exact S_in_U?
  left
  by_contra Sc_notin_U
  apply (U.mem_of_compl_not_mem B_closed S_in_B) at Sc_notin_U
  exact S_in_U? Sc_notin_U

theorem UltrafilterInBasis.clusterPt_iff_le_nhds [TopologicalSpace α]
  (U : UltrafilterInBasis B)
  (B_basis : TopologicalSpace.IsTopologicalBasis B)
  (B_closed : ∀ (b1 b2 : Set α), b1 ∈ B → b2 ∈ B → Set.Nonempty (b1 ∩ b2) → b1 ∩ b2 ∈ B)
  (p : α) :
  ClusterPt p U.filter ↔ U.filter ≤ nhds p :=
by
  constructor
  swap
  exact fun h => ClusterPt.of_le_nhds h
  intro p_clusterPt
  intro S S_in_nhds
  let ⟨T, T_in_B, p_in_T, T_ss_S⟩ := B_basis.mem_nhds_iff.mp S_in_nhds
  have T_in_nhds : T ∈ nhds p := by
    rw [B_basis.mem_nhds_iff]
    use T
  apply Filter.mem_of_superset _ T_ss_S

  cases U.mem_or_compl_mem B_closed T_in_B with
  | inr res => exact res
  | inl Tc_in_U =>
    exfalso
    rw [clusterPt_iff] at p_clusterPt
    specialize p_clusterPt T_in_nhds Tc_in_U
    rw [Set.inter_compl_self] at p_clusterPt
    exact Set.not_nonempty_empty p_clusterPt

/--
Allows substituting the expression for the basis in the type.
--/
def UltrafilterInBasis.cast (U : UltrafilterInBasis B) {C : Set (Set α)} (B_eq_C : B = C) :
  UltrafilterInBasis C where
  filter := U.filter
  ne_bot := U.ne_bot
  in_basis := U.in_basis.mono (subset_of_eq B_eq_C)
  ultra := by
    nth_rw 1 [<-B_eq_C]
    exact U.ultra

@[simp]
theorem UltrafilterInBasis.mem_cast (U : UltrafilterInBasis B) {C : Set (Set α)} (B_eq_C : B = C) (S : Set α):
  S ∈ U.cast B_eq_C ↔ S ∈ U := by rw [cast]; rfl

@[simp]
theorem UltrafilterInBasis.le_cast (U : UltrafilterInBasis B) {C : Set (Set α)} (B_eq_C : B = C) (F : Filter α):
  F ≤ U.cast B_eq_C ↔ F ≤ U := by rw [cast]

@[simp]
theorem UltrafilterInBasis.cast_le (U : UltrafilterInBasis B) {C : Set (Set α)} (B_eq_C : B = C) (F : Filter α):
  U.cast B_eq_C ≤ F ↔ U ≤ F := by rw [cast]

@[simp]
theorem UltrafilterInBasis.cast_filter (U : UltrafilterInBasis B) {C : Set (Set α)} (B_eq_C : B = C):
  (U.cast B_eq_C).filter = U.filter := by rw [cast]
