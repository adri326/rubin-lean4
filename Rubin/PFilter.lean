import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Bases
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.PFilter
import Mathlib.Order.ZornAtoms

import Mathlib.Topology.Basic
import Mathlib.Topology.Bases

open Order

universe u
variable {α : Type u}

section Defs


structure BFilter (α : Type u) [LE α] extends UpperSet α :=
  directed : DirectedOn (· ≥ ·) carrier
  nonempty : carrier.Nonempty

instance [LE α] : Membership α (BFilter α) where
  mem := fun a f => a ∈ f.carrier

variable [LE α]

@[simp]
theorem BFilter.mem_iff {f : BFilter α} {a : α} : a ∈ f.carrier ↔ a ∈ f := Iff.rfl

@[simp]
theorem BFilter.mem_iff' {f : BFilter α} {a : α} : a ∈ f.toUpperSet ↔ a ∈ f := Iff.rfl

theorem BFilter.mem_of_le {f : BFilter α} {a b : α} (a_in_f : a ∈ f) (a_le_b : a ≤ b) : b ∈ f :=
  f.upper' a_le_b a_in_f

theorem BFilter.exists_le {f : BFilter α} {a b : α} (a_in_f : a ∈ f) (b_in_f : b ∈ f) :
    ∃ c ∈ f, c ≤ a ∧ c ≤ b := by exact f.directed a a_in_f b b_in_f

@[simp]
theorem BFilter.eq_iff {f₁ f₂ : BFilter α} : f₁.carrier = f₂.carrier ↔ f₁ = f₂ := by
  rw [mk.injEq, UpperSet.mk.injEq]

instance : SetLike (BFilter α) α where
  coe := fun f => f.carrier
  coe_injective' := by
    intro f₁ f₂
    simp only
    rw [BFilter.eq_iff]
    tauto

instance : PartialOrder (BFilter α) where
  le := fun f₁ f₂ => f₂.carrier ⊆ f₁.carrier
  lt := fun f₁ f₂ => f₂.carrier ⊂ f₁.carrier
  le_refl := fun f => subset_refl f.carrier
  le_trans := fun f₁ f₂ f₃ h12 h23 => subset_trans h23 h12
  le_antisymm := fun f₁ f₂ h h' => by
    rw [← BFilter.eq_iff]
    exact subset_antisymm h' h

@[simp]
theorem BFilter.le_iff {f₁ f₂ : BFilter α} : f₂.carrier ⊆ f₁.carrier ↔ f₁ ≤ f₂ := Iff.rfl

end Defs

section Bot

theorem BFilter.inf_mem {α : Type u} [SemilatticeInf α] {f : BFilter α} {a b : α}
    (a_in_f : a ∈ f) (b_in_f : b ∈ f) : a ⊓ b ∈ f :=
  let ⟨_, c_in_f, c_le_a, c_le_b⟩ := exists_le a_in_f b_in_f
  mem_of_le c_in_f (le_inf c_le_a c_le_b)

instance [SemilatticeInf α] [Nonempty α]: OrderBot (BFilter α) where
  bot := {
    carrier := Set.univ
    upper' := isUpperSet_univ
    nonempty := Set.univ_nonempty
    directed := fun a _ b _ => ⟨a ⊓ b, Set.mem_univ _, inf_le_left, inf_le_right⟩
  }
  bot_le := by tauto

theorem BFilter.eq_bot_iff [SemilatticeInf α] [Nonempty α] {f : BFilter α} : f = ⊥ ↔ f.carrier = Set.univ := by
  rw [← eq_iff]
  rfl

theorem BFilter.eq_bot_iff_bot_mem [SemilatticeInf α] [OrderBot α] {f : BFilter α} : f = ⊥ ↔ ⊥ ∈ f := by
  refine ⟨fun eq => eq ▸ Set.mem_univ ⊥, fun bot_mem => ?rest⟩
  rw [eq_bot_iff]
  ext a
  simp only [SetLike.mem_coe, Set.mem_univ, iff_true]
  exact mem_of_le bot_mem bot_le

end Bot

section Top

@[simp]
theorem BFilter.top_mem [PartialOrder α] [OrderTop α] {f : BFilter α}: ⊤ ∈ f :=
  BFilter.mem_of_le f.nonempty.choose_spec le_top

instance [PartialOrder α] [OrderTop α]: OrderTop (BFilter α) where
  top := {
    carrier := {⊤}
    nonempty := Set.singleton_nonempty ⊤
    upper' := by
      intro _ x le_top eq_top
      rw [eq_top, top_le_iff] at le_top
      rw [le_top]
      rfl
    directed := by
      apply directedOn_singleton
      exact fun x => le_refl x
  }
  le_top := by
    intro f _ eq_top
    rw [eq_top]
    exact BFilter.top_mem

end Top

section Lattice

instance [SemilatticeInf α] [OrderTop α] : SemilatticeSup (BFilter α) where
  sup := fun f g => {
    carrier := f.carrier ∩ g.carrier
    upper' := IsUpperSet.inter f.upper' g.upper'
    nonempty := by
      use ⊤
      simp
    directed := by
      simp
      intro a ⟨a_in_f, a_in_g⟩ b ⟨b_in_f, b_in_g⟩
      exact ⟨a ⊓ b,
        ⟨BFilter.inf_mem a_in_f b_in_f, BFilter.inf_mem a_in_g b_in_g⟩,
        inf_le_left,
        inf_le_right⟩
  }
  le_sup_left := fun a b => Set.inter_subset_left a.carrier b.carrier
  le_sup_right := fun a b => Set.inter_subset_right a.carrier b.carrier
  sup_le := fun a b c a_le_c b_le_c => Set.subset_inter a_le_c b_le_c

instance [SemilatticeInf α]: SemilatticeInf (BFilter α) where
  inf := fun f g => {
    carrier := { x | ∃ a ∈ f, ∃ b ∈ g, a ⊓ b ≤ x }
    upper' := by
      intro a b a_le_b ⟨c, c_in_f, d, d_in_g, a_le_cd⟩
      exact ⟨c, c_in_f, d, d_in_g, le_trans a_le_cd a_le_b⟩
    nonempty := by
      let ⟨a, a_in_f⟩ := f.nonempty
      let ⟨b, b_in_g⟩ := g.nonempty
      exact ⟨a ⊓ b, a, a_in_f, b, b_in_g, le_refl _⟩
    directed := by
      simp
      intro a ⟨x, x_in_f, y, y_in_g, xy_le_a⟩ b ⟨z, z_in_f, w, w_in_g, zw_le_b⟩
      refine ⟨a ⊓ b, ⟨
        x ⊓ z,
        BFilter.inf_mem x_in_f z_in_f,
        y ⊓ w,
        BFilter.inf_mem y_in_g w_in_g,
        ?inf_le_inf
      ⟩, inf_le_left, inf_le_right⟩
      apply le_inf
      · calc
          x ⊓ z ⊓ (y ⊓ w) ≤ x ⊓ z ⊓ y := by gcongr; exact inf_le_left
          _ ≤ x ⊓ y := by gcongr; exact inf_le_left
          _ ≤ a := xy_le_a
      · calc
          x ⊓ z ⊓ (y ⊓ w) ≤ x ⊓ z ⊓ w := by gcongr; exact inf_le_right
          _ ≤ z ⊓ w := by gcongr; exact inf_le_right
          _ ≤ b := zw_le_b
  }
  inf_le_left := by
    intro f g x x_in_f
    let ⟨y, y_in_g⟩ := g.nonempty
    exact ⟨x, x_in_f, y, y_in_g, inf_le_left⟩
  inf_le_right := by
    intro f g x x_in_g
    let ⟨y, y_in_f⟩ := f.nonempty
    exact ⟨y, y_in_f, x, x_in_g, inf_le_right⟩
  le_inf := by
    intro f g h f_le_g f_le_h
    intro x ⟨a, a_in_g, b, b_in_h, ab_le_x⟩
    apply BFilter.mem_of_le _ ab_le_x
    apply BFilter.inf_mem
    · exact f_le_g a_in_g
    · exact f_le_h b_in_h

theorem BFilter.mem_inf_iff [SemilatticeInf α] (f g : BFilter α) (a : α) :
    a ∈ f ⊓ g ↔ ∃ b ∈ f, ∃ c ∈ g, b ⊓ c ≤ a := Iff.rfl

instance [SemilatticeInf α] [OrderTop α] : Lattice (BFilter α) where
  inf_le_left := fun _ _ => inf_le_left
  inf_le_right := fun _ _ => inf_le_right
  le_inf := fun _ _ _ => le_inf

end Lattice

section Principal

def BFilter.principal [SemilatticeInf α] (a : α) : BFilter α where
  carrier := { b | a ≤ b }
  upper' := fun b c b_le_c a_le_b => le_trans a_le_b b_le_c
  directed := by
    simp [DirectedOn]
    intro b a_le_b c a_le_c
    exact ⟨b ⊓ c, le_inf a_le_b a_le_c, inf_le_left, inf_le_right⟩
  nonempty := ⟨a, le_refl a⟩

@[simp]
theorem BFilter.mem_principal [SemilatticeInf α] {a b : α} : b ∈ BFilter.principal a ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem BFilter.le_principal_iff [SemilatticeInf α] (a : α) (f : BFilter α):
    f ≤ BFilter.principal a ↔ a ∈ f := ⟨
  fun f_le_pa => f_le_pa (le_of_eq rfl),
  fun a_in_f _ b_le_a => mem_of_le a_in_f b_le_a⟩

end Principal

section sSup

variable [SemilatticeInf α] [OrderTop α]

lemma IsUpperSet.iInter {α ι : Type*} [LE α] {p : ι → Set α} (uppers : ∀ i : ι, IsUpperSet (p i)) :
    IsUpperSet (⋂ i, p i) := by
  intro a b a_le_b a_in_iInter
  rw [Set.mem_iInter]
  rw [Set.mem_iInter] at a_in_iInter
  intro i
  exact uppers i a_le_b (a_in_iInter i)

lemma IsUpperSet.biInter {α ι: Type*} [LE α] {s : Set ι} {p : ι → Set α} (uppers : ∀ f ∈ s, IsUpperSet (p f)) :
    IsUpperSet (⋂ f ∈ s, p f) := by
  intro a b a_le_b a_in_iInter
  rw [Set.mem_iInter₂] at a_in_iInter
  apply Set.mem_biInter
  intro t t_in_s
  exact uppers t t_in_s a_le_b (a_in_iInter t t_in_s)

instance : SupSet (BFilter α) where
  sSup := fun s => {
    carrier := ⋂ (f ∈ s), f.carrier
    nonempty := by
      use ⊤
      simp only [UpperSet.carrier_eq_coe, Set.mem_iInter, SetLike.mem_coe, BFilter.mem_iff',
        BFilter.top_mem, implies_true, forall_const]
    upper' := by
      apply IsUpperSet.biInter
      intro f _
      exact f.upper'
    directed := by
      simp only [DirectedOn, UpperSet.carrier_eq_coe, Set.mem_iInter, SetLike.mem_coe,
        BFilter.mem_iff', ge_iff_le]
      intro a h₁ b h₂
      refine ⟨a ⊓ b, fun f f_in_S => ?z_in_inf, inf_le_left, inf_le_right⟩
      specialize h₁ f f_in_S
      specialize h₂ f f_in_S
      apply BFilter.inf_mem <;> assumption
  }

theorem BFilter.mem_sSup {s : Set (BFilter α)} {a : α} : a ∈ sSup s ↔ ∀ f ∈ s, a ∈ f := by
  show a ∈ ⋂ (f ∈ s), f.carrier ↔ ∀ f ∈ s, a ∈ f
  rw [Set.mem_iInter₂]
  rfl

end sSup

section CompleteLattice

variable [SemilatticeInf α] [OrderTop α]
variable {ι : Type*} [ne : Nonempty ι]

instance : CompleteLattice (BFilter α) := {
  (inferInstance : OrderTop (BFilter α)),
  (inferInstance : OrderBot (BFilter α)),
  (inferInstance : Lattice (BFilter α)),
  (inferInstance : SupSet (BFilter α)),
  completeLatticeOfSup (BFilter α) (fun s => by
    constructor
    · intro f f_in_s a a_in_sSup
      rw [BFilter.mem_iff, BFilter.mem_sSup] at a_in_sSup
      exact a_in_sSup f f_in_s
    · intro f h₁ a a_in_f
      rw [BFilter.mem_iff, BFilter.mem_sSup]
      intro g g_in_s
      exact h₁ g_in_s a_in_f
  ) with
}

-- Heavily inspired by the proof for the atomicity of Filter:

theorem BFilter.eq_sInf_of_mem_iff_exists_mem {s : Set (BFilter α)} {f : BFilter α}
    (mem_iff_exists_mem : ∀ a, a ∈ f ↔ ∃ g ∈ s, a ∈ g) : f = sInf s := by
  apply le_antisymm
  · apply le_sInf
    intro g g_in_s a a_in_g
    rw [mem_iff, mem_iff_exists_mem]
    exact ⟨g, g_in_s, a_in_g⟩
  · intro a a_in_f
    rw [mem_iff, mem_iff_exists_mem] at a_in_f
    rw [mem_iff]
    let ⟨g, g_in_s, a_in_g⟩ := a_in_f
    exact sInf_le g_in_s a_in_g

theorem BFilter.sInf_carrier_eq {s : Set (BFilter α)} (s_nonempty : s.Nonempty)
    (h : DirectedOn (· ≥ ·) s) : (sInf s).carrier = ⋃ f ∈ s, f.carrier := by
  let ⟨i, i_in_s⟩ := s_nonempty
  let union : BFilter α := {
    carrier := ⋃ f ∈ s, f.carrier,
    nonempty := by
      simp only [Set.nonempty_iUnion, ne_eq]
      exact ⟨i, i_in_s, i.nonempty⟩
    upper' := by
      intro a b a_le_b a_in_iUnion
      rw [Set.mem_iUnion₂]
      rw [Set.mem_iUnion₂] at a_in_iUnion
      let ⟨f, f_in_s, a_in_f⟩ := a_in_iUnion
      exact ⟨f, f_in_s, BFilter.mem_of_le a_in_f a_le_b⟩
    directed := by
      simp only [DirectedOn, UpperSet.carrier_eq_coe, Set.mem_iUnion, SetLike.mem_coe, mem_iff',
        ge_iff_le, forall_exists_index]
      intro a f₁ f₁_in_s a_in_f₁ b f₂ f₂_in_s b_in_f₂
      refine ⟨a ⊓ b, ?directed, inf_le_left, inf_le_right⟩
      let ⟨f₃, f₃_in_s, f₁_le_f₃, f₂_le_f₃⟩ := h f₁ f₁_in_s f₂ f₂_in_s
      exact ⟨f₃, f₃_in_s, BFilter.inf_mem (f₁_le_f₃ a_in_f₁) (f₂_le_f₃ b_in_f₂)⟩
  }
  have union_eq : union = sInf s := by
    apply eq_sInf_of_mem_iff_exists_mem
    intro a
    rw [← mem_iff]
    simp only [UpperSet.carrier_eq_coe, Set.mem_iUnion, SetLike.mem_coe, mem_iff', exists_prop]
  rw [← union_eq]


theorem BFilter.mem_sInf_of_directed {s : Set (BFilter α)} (s_nonempty : s.Nonempty)
    (h : DirectedOn (· ≥ ·) s) (a : α) : a ∈ sInf s ↔ ∃ f ∈ s , a ∈ f := by
  simp only [← BFilter.mem_iff, sInf_carrier_eq s_nonempty h, Set.mem_iUnion]
  simp only [UpperSet.carrier_eq_coe, SetLike.mem_coe, mem_iff', exists_prop]

end CompleteLattice

section IsAtomic

variable [SemilatticeInf α] [OrderTop α] [OrderBot α]

instance BFilter.is_atomic : IsAtomic (BFilter α) := by
  apply IsAtomic.of_isChain_bounded
  intro ch ch_chain ch_nonempty bot_notin_ch
  have directed : DirectedOn (· ≥ ·) ch := IsChain.directedOn (IsChain.symm ch_chain)

  refine ⟨sInf ch, fun eq_bot => bot_notin_ch ?ne_bot, (isGLB_sInf ch).left⟩

  -- Note: it might be possible to prove this without OrderBot
  rw [BFilter.eq_bot_iff_bot_mem] at eq_bot
  rw [BFilter.mem_sInf_of_directed ch_nonempty directed] at eq_bot
  let ⟨f, f_in_ch, f_eq_bot⟩ := eq_bot
  rw [← BFilter.eq_bot_iff_bot_mem] at f_eq_bot
  rwa [← f_eq_bot]

end IsAtomic

section Ultra

variable [SemilatticeInf α] [OrderTop α] [OrderBot α]

def BFilter.IsUltra (f: BFilter α) : Prop :=
  f ≠ ⊥ ∧ ∀ f': BFilter α, f' ≠ ⊥ → f' ≤ f → f ≤ f'

theorem BFilter.isUltra_iff_isAtom (f : BFilter α) : f.IsUltra ↔ IsAtom f := by
  unfold IsAtom IsUltra
  constructor
  · intro ⟨f_ne_bot, f_ultra⟩
    refine ⟨f_ne_bot, fun g g_lt_f => ?g_eq_bot⟩
    by_contra g_ne_bot
    specialize f_ultra g g_ne_bot g_lt_f.le
    exact (le_not_le_of_lt g_lt_f).right f_ultra
  · intro ⟨f_ne_bot, f_atom⟩
    refine ⟨f_ne_bot, fun g g_ne_bot g_le_f => ?f_le_g⟩
    by_cases f = g
    case pos f_eq_g => exact le_of_eq f_eq_g
    case neg _f_ne_g =>
      by_contra g_lt_f
      apply lt_of_le_not_le g_le_f at g_lt_f
      exact g_ne_bot (f_atom _ g_lt_f)

theorem BFilter.exists_ultra_of_ne_bot {f: BFilter α} (f_ne_bot : f ≠ ⊥) :
    ∃ u: BFilter α, u.IsUltra ∧ u ≤ f := by
  have res := (BFilter.is_atomic.eq_bot_or_exists_atom_le f).resolve_left f_ne_bot
  convert res using 3
  exact BFilter.isUltra_iff_isAtom _

variable (α) in
/--
Bundled ultrafilters.
-/
structure UltraBFilter :=
  filter: BFilter α
  ultra: filter.IsUltra

instance : Coe (UltraBFilter α) (BFilter α) := ⟨UltraBFilter.filter⟩

@[simp]
theorem UltraBFilter.ne_bot (u: UltraBFilter α) : (u : BFilter α) ≠ ⊥ := u.ultra.left

theorem UltraBFilter.le_of_le {u: UltraBFilter α} {f: BFilter α} (f_ne_bot : f ≠ ⊥)
    (f_le_u : f ≤ u) : u ≤ f := u.ultra.right _ f_ne_bot f_le_u

theorem UltraBFilter.eq_of_le {u: UltraBFilter α} {f: BFilter α} (f_ne_bot : f ≠ ⊥)
    (f_le_u : f ≤ u) : f = u := le_antisymm f_le_u (u.le_of_le f_ne_bot f_le_u)

noncomputable def UltraBFilter.of (f: BFilter α) (f_ne_bot : f ≠ ⊥) : UltraBFilter α :=
  let ex_ultra := BFilter.exists_ultra_of_ne_bot f_ne_bot
  ⟨
    ex_ultra.choose,
    ex_ultra.choose_spec.left
  ⟩

theorem UltraBFilter.of_le {f: BFilter α} (f_ne_bot : f ≠ ⊥) :
    (UltraBFilter.of f f_ne_bot : BFilter α) ≤ f :=
  (BFilter.exists_ultra_of_ne_bot f_ne_bot).choose_spec.right

theorem UltraBFilter.le_of_inf_ne_bot {u : UltraBFilter α} {f : BFilter α}
    (uf_ne_bot : (u : BFilter α) ⊓ f ≠ ⊥) : u ≤ f := by
  apply le_of_inf_eq
  apply eq_of_le uf_ne_bot
  exact inf_le_left

end Ultra

section DirectedOn

theorem directedOn_of_relHom {α β : Type*} (r : α → α → Prop) (r' : β → β → Prop) (s : Set α)
    (f : r →r r') (dir : DirectedOn r s) : DirectedOn r' (f '' s) := by
  intro a' ⟨a, as, a_eq⟩ b' ⟨b, bs, b_eq⟩
  let ⟨c, cs, rac, rbc⟩ := dir a as b bs
  refine ⟨f c, ⟨c, cs, rfl⟩, ?ra_fc, ?rb_fc⟩
  · rw [← a_eq]
    exact f.map_rel rac
  · rw [← b_eq]
    exact f.map_rel rbc

theorem directedOn_relIso {α β : Type*} (r : α → α → Prop) (r' : β → β → Prop) (s : Set α)
    (f : r ≃r r') : DirectedOn r s ↔ DirectedOn r' (f '' s) := by
  constructor
  · exact directedOn_of_relHom r r' s f
  · have s_eq : s = f.symm '' (f '' s) := by
      simp only [Set.image_image, RelIso.symm_apply_apply, Set.image_id']
    nth_rw 2 [s_eq]
    exact directedOn_of_relHom r' r (f '' s) f.symm

@[simp]
theorem OrderIso.orderPreimage_le {α β: Type*} [LE α] [LE β] (f : α ≃o β) :
    f ⁻¹'o (· ≤ ·) = (· ≤ ·) := by
  ext a b
  simp only [Preimage, map_le_map_iff]

@[simp]
theorem OrderIso.orderPreimage_ge {α β: Type*} [LE α] [LE β] (f : α ≃o β) :
    f ⁻¹'o (· ≥ ·) = (· ≥ ·) := by
  ext a b
  simp only [Preimage, map_le_map_iff]

theorem directedOn_orderIso_le {α β : Type*} [LE α] [LE β] (s : Set α) (f : α ≃o β) :
    DirectedOn (· ≤ ·) s ↔ DirectedOn (· ≤ ·) (f '' s) := directedOn_relIso _ _ s f

theorem directedOn_orderIso_ge {α β : Type*} [LE α] [LE β] (s : Set α) (f : α ≃o β) :
    DirectedOn (· ≥ ·) s ↔ DirectedOn (· ≥ ·) (f '' s) := by
  rw [directedOn_image, OrderIso.orderPreimage_ge]

end DirectedOn

section BFilter.map

variable {β : Type*}
variable [Preorder α] [Preorder β]

def BFilter.map (f : BFilter α) (m : α ≃o β) : BFilter β where
  carrier := m '' f
  upper' := IsUpperSet.image f.upper' m
  nonempty := by
    let ⟨x, x_in_f⟩ := f.nonempty
    exact ⟨m x, ⟨x, x_in_f, rfl⟩⟩
  directed := by
    rw [← directedOn_orderIso_ge _ m]
    exact f.directed

@[simp]
theorem BFilter.map_carrier (f : BFilter α) (m : α ≃o β) : (f.map m).carrier = m '' f := rfl

@[simp]
theorem BFilter.map_carrier_preimage (f : BFilter α) (m : α ≃o β) :
    (f.map m).carrier = (Equiv.symm m) ⁻¹' (f : Set α) := by
  rw [BFilter.map_carrier, ← Equiv.image_eq_preimage]
  rfl

@[simp]
theorem BFilter.mem_map (f : BFilter α) (m : α ≃o β) (b : β) : b ∈ f.map m ↔ m.symm b ∈ f := by
  rw [← BFilter.mem_iff (f := f), ← Set.mem_preimage]
  show b ∈f.map m ↔ b ∈ (Equiv.symm m) ⁻¹' f.carrier
  rw [← Equiv.image_eq_preimage]
  rfl

theorem BFilter.map_map {γ : Type*} [Preorder γ] (f : BFilter α) (m₁ : α ≃o β) (m₂ : β ≃o γ) :
    (f.map m₁).map m₂ = f.map (m₁.trans m₂) := by
  rw [← BFilter.eq_iff]
  show m₂ '' (m₁ '' f.carrier) = (m₁.trans m₂) '' f.carrier
  rw [Set.image_image]
  rfl

@[simp]
theorem BFilter.map_symm (f : BFilter α) (m : α ≃o β) : (f.map m).map m.symm = f := by
  rw [map_map]
  refine le_antisymm (fun a => ?h₁) (fun a => ?h₂)
  all_goals simp only [UpperSet.carrier_eq_coe, SetLike.mem_coe, mem_iff', mem_map,
    OrderIso.symm_trans_apply, OrderIso.symm_symm, OrderIso.symm_apply_apply]
  all_goals tauto

theorem BFilter.map_le_of_le (f g : BFilter α) (m : α ≃o β) (f_le_g : f ≤ g) :
    f.map m ≤ g.map m := fun _ ⟨a, a_in_g, a_eq⟩ => ⟨a, f_le_g a_in_g, a_eq⟩

@[simp]
theorem BFilter.map_le_iff (f g : BFilter α) (m : α ≃o β) : f.map m ≤ g.map m ↔ f ≤ g := ⟨
    fun map_le => by
      have res := BFilter.map_le_of_le _ _ m.symm map_le
      simp at res
      exact res,
    BFilter.map_le_of_le f g m⟩

def BFilter.map' (m : α ≃o β) : (BFilter α) ≃o (BFilter β) where
  toFun := fun a => a.map m
  invFun := fun b => b.map m.symm
  left_inv := by
    intro f
    simp only [map_symm]
  right_inv := by
    intro f
    simp only
    nth_rw 2 [← OrderIso.symm_symm m]
    rw [map_symm]
  map_rel_iff' := by
    simp only [Equiv.coe_fn_mk, map_le_iff, implies_true]

@[simp]
theorem BFilter.map'_apply (f : BFilter α) (m : α ≃o β) : BFilter.map' m f = f.map m := rfl

end BFilter.map

section MapUltra

variable {β : Type*} [SemilatticeInf α] [OrderTop α] [SemilatticeInf β] [OrderTop β]

@[simp]
theorem BFilter.map_bot (m : α ≃o β) : (⊥ : BFilter α).map m = ⊥ := by
  rw [← map'_apply]
  exact OrderIso.map_bot _

theorem BFilter.map_ne_bot {f: BFilter α} (f_ne_bot : f ≠ ⊥) (m : α ≃o β) : f.map m ≠ ⊥ := by
  intro map_eq_bot
  apply f_ne_bot
  apply (map' m).injective
  rw [map'_apply, map_eq_bot, OrderIso.map_bot]

theorem BFilter.map_ultra {f : BFilter α} (f_ultra : f.IsUltra) (m : α ≃o β) :
    (f.map m).IsUltra := by
  constructor
  · exact map_ne_bot f_ultra.left m
  · intro g g_ne_bot g_le_map
    rw [← map_le_iff _ _ m.symm, map_symm] at g_le_map
    rw [← map_le_iff _ _ m.symm, map_symm]
    exact f_ultra.right _ (map_ne_bot g_ne_bot m.symm) g_le_map

def UltraBFilter.map (f : UltraBFilter α) (m : α ≃o β) : UltraBFilter β := ⟨
  f.filter.map m,
  BFilter.map_ultra f.ultra m⟩

@[simp]
theorem UltraBFilter.map_filter (f : UltraBFilter α) (m : α ≃o β) :
    (f.map m).filter = f.filter.map m := rfl

end MapUltra

section ToFilter

variable {β : Type*} {M : Type*}
variable [LE α] [OrderHomClass M α (Set β)]

theorem BFilter.is_basis (f : BFilter α) (m : M) :
    Filter.IsBasis (fun t => t ∈ f) (fun t => m t) := by
  constructor
  · exact f.nonempty
  · intro i j i_in_f j_in_f
    simp only [Set.subset_inter_iff]
    have ⟨k, k_in_f, k_ss_i, k_ss_j⟩ := f.directed i i_in_f j j_in_f
    refine ⟨k, k_in_f, ?k_ss_i, ?k_ss_j⟩
    all_goals apply RelHomClass.map_rel m
    all_goals assumption

def BFilter.to_filter (m : M) (f : BFilter α) : Filter β := (f.is_basis m).filter

theorem BFilter.mem_to_filter (f : BFilter α) (m : M) (s : Set β) :
    s ∈ f.to_filter m ↔ ∃ a ∈ f, m a ⊆ s := Filter.IsBasis.mem_filter_iff _

theorem BFilter.to_filter_monotone (m : M) : Monotone (BFilter.to_filter m) := by
  intro f g f_le_g s s_in_mg
  rw [mem_to_filter]
  let ⟨a, a_in_f, ma_ss_s⟩ := (mem_to_filter _ _ _).mp s_in_mg
  exact ⟨a, f_le_g a_in_f, ma_ss_s⟩

variable {α : Type*} [Preorder α]

theorem BFilter.mem_to_filter' (f : BFilter α) (m : α ↪o Set β) (a : α) :
    m a ∈ f.to_filter m ↔ a ∈ f := by
  constructor
  · intro ma_in_mf
    rw [mem_to_filter] at ma_in_mf
    let ⟨b, b_in_f, mb_ss_ma⟩ := ma_in_mf
    apply mem_of_le b_in_f
    rwa [← Set.le_iff_subset, m.le_iff_le] at mb_ss_ma
  · intro a_in_f
    rw [mem_to_filter]
    use a

theorem BFilter.to_filter_le_iff_le (f g : BFilter α) (m : α ↪o Set β) :
    f.to_filter m ≤ g.to_filter m ↔ f ≤ g := by
  refine ⟨fun mf_le_mg => ?f_le_g, fun f_le_g => BFilter.to_filter_monotone m f_le_g⟩
  intro a a_in_g
  rw [mem_iff, ← mem_to_filter' f m a]
  apply mf_le_mg
  rw [mem_to_filter]
  exact ⟨a, a_in_g, subset_refl _⟩

theorem BFilter.to_filter_injective (m : α ↪o Set β) : Function.Injective (BFilter.to_filter m) := by
  intro f g to_filter_eq
  apply le_antisymm <;> rw [← to_filter_le_iff_le _ _ m] <;> apply le_of_eq
  · exact to_filter_eq
  · exact to_filter_eq.symm

@[simp]
theorem BFilter.to_filter_eq_iff (f g : BFilter α) (m : α ↪o Set β) :
    f.to_filter m = g.to_filter m ↔ f = g := ⟨
      fun eq => BFilter.to_filter_injective m eq,
      fun eq => by rw [eq]⟩

variable {α : Type*} [SemilatticeInf α]

theorem BFilter.principal_to_filter (a : α) (m : α ↪o Set β) :
    (BFilter.principal a).to_filter m = Filter.principal (m a) := by
  ext s
  simp only [mem_to_filter, mem_principal, Set.le_eq_subset, Filter.mem_principal]
  refine ⟨
    fun ⟨b, a_le_b, mb_ss_s⟩ => subset_trans ?ma_ss_s mb_ss_s,
    fun ma_ss_s => ⟨a, le_refl a, ma_ss_s⟩
  ⟩
  exact RelHomClass.map_rel m a_le_b

end ToFilter

section InfHom

variable [SemilatticeInf α] [OrderTop α] [OrderBot α]
variable {β : Type*}

theorem BFilter.to_filter_inf_le (f g : BFilter α) {m : α ↪o (Set β)}
    (m_inf : ∀ a b, m a ∩ m b ⊆ m (a ⊓ b)) :
    f.to_filter m ⊓ g.to_filter m = (f ⊓ g).to_filter m := by
  apply le_antisymm
  · intro s s_in_minf
    rw [mem_to_filter] at s_in_minf
    let ⟨a, ⟨b, b_in_f, c, c_in_g, bc_le_a⟩, ma_ss_s⟩ := s_in_minf

    have h₁ : m b ∩ m c ∈ f.to_filter m ⊓ g.to_filter m := by
      rw [Filter.mem_inf_iff]
      refine ⟨
        m b,
        (mem_to_filter' _ _ _).mpr b_in_f,
        m c,
        (mem_to_filter' _ _ _).mpr c_in_g,
        rfl
      ⟩

    apply Filter.mem_of_superset h₁
    apply le_trans _ ma_ss_s
    rw [Set.le_iff_subset]
    apply subset_trans (m_inf b c)
    rwa [← Set.le_iff_subset, m.le_iff_le]
  · intro s s_in_inf
    rw [Filter.mem_inf_iff] at s_in_inf
    simp only [mem_to_filter] at s_in_inf
    simp only [mem_to_filter, mem_inf_iff]

    let ⟨t₁, ⟨a, a_in_f, ma_ss_t₁⟩, t₂, ⟨b, b_in_g, mb_ss_t₂⟩, s_eq⟩ := s_in_inf
    rw [s_eq]

    refine ⟨a ⊓ b, ⟨a, a_in_f, b, b_in_g, le_refl _⟩, ?minf_ss⟩

    refine Set.subset_inter (subset_trans ?minf_ss_ma ma_ss_t₁) (subset_trans ?minf_ss_mb mb_ss_t₂)
    all_goals rw [← Set.le_iff_subset, m.le_iff_le]
    · exact inf_le_left
    · exact inf_le_right

@[simp]
theorem BFilter.to_filter_bot {m : α ↪o (Set β)} (m_bot : m ⊥ = ⊥) :
    (⊥ : BFilter α).to_filter m = ⊥ := by
  rw [← le_bot_iff]
  intro a h
  rw [mem_to_filter]
  exact ⟨⊥, h, m_bot ▸ bot_le⟩

def UltraBFilter.to_filter (m : α ↪o Set β) (u : UltraBFilter α) : Filter β := u.filter.to_filter m

theorem UltraBFilter.to_filter_eq (m : α ↪o Set β) (u : UltraBFilter α) :
    u.to_filter m = u.filter.to_filter m := rfl

theorem UltraBFilter.mem_to_filter (m : α ↪o Set β) (u : UltraBFilter α) (s : Set β) :
    s ∈ u.to_filter m ↔ ∃ a ∈ u.filter, m a ⊆ s := by
  unfold to_filter
  rw [BFilter.mem_to_filter]

theorem UltraBFilter.to_filter_ne_bot (u : UltraBFilter α) {m : α ↪o Set β} (m_bot : m ⊥ = ⊥) :
    u.to_filter m ≠ ⊥ := by
  intro eq_bot
  rw [← BFilter.to_filter_bot m_bot] at eq_bot
  rw [to_filter_eq, BFilter.to_filter_eq_iff] at eq_bot
  exact u.ne_bot eq_bot

theorem UltraBFilter.to_filter_ne_bot' (u : UltraBFilter α) {m : α ↪o Set β} (m_bot : m ⊥ = ⊥) :
    Filter.NeBot (u.to_filter m) := ⟨to_filter_ne_bot u m_bot⟩

theorem UltraBFilter.to_filter.mem_of_compl_not_mem (u : UltraBFilter α) {m : α ↪o (Set β)}
    (m_inf : ∀ a b, m a ∩ m b ⊆ m (a ⊓ b)) (m_bot : m ⊥ = ⊥) {a : α}
    (compl_notin_u : (m a)ᶜ ∉ u.to_filter m) : m a ∈ u.to_filter m := by
  rw [mem_to_filter]
  refine ⟨a, ?a_in_f, le_refl _⟩

  simp only [← BFilter.le_principal_iff]
  apply le_of_inf_ne_bot
  intro eq_bot
  apply compl_notin_u
  apply Filter.mem_of_eq_bot
  rwa [to_filter_eq, compl_compl, ← BFilter.principal_to_filter, BFilter.to_filter_inf_le _ _ m_inf,
    ← BFilter.to_filter_bot m_bot, BFilter.to_filter_eq_iff]


theorem UltraBFilter.to_filter.mem_or_compl_mem (u : UltraBFilter α) {m : α ↪o (Set β)}
    (m_inf : ∀ a b, m a ∩ m b ⊆ m (a ⊓ b)) (m_bot : m ⊥ = ⊥) (a : α) :
    m a ∈ u.to_filter m ∨ (m a)ᶜ ∈ u.to_filter m := by
  by_cases (m a)ᶜ ∈ u.to_filter m
  case pos res => right; exact res
  case neg compl_not_mem =>
    left
    exact UltraBFilter.to_filter.mem_of_compl_not_mem u m_inf m_bot compl_not_mem

variable [TopologicalSpace β] in
theorem UltraBFilter.to_filter.clusterPt_iff_nhds (u : UltraBFilter α) {m : α ↪o (Set β)}
    (m_inf : ∀ a b, m a ∩ m b ⊆ m (a ⊓ b)) (m_bot : m ⊥ = ⊥)
    (m_basis : TopologicalSpace.IsTopologicalBasis (Set.range m)) (b : β) :
    ClusterPt b (u.to_filter m) ↔ u.to_filter m ≤ nhds b := by
  constructor
  · intro clusterPt s s_in_nhds
    let ⟨t, ⟨a, ma_eq_t⟩, b_in_t, t_ss_s⟩ := m_basis.mem_nhds_iff.mp s_in_nhds
    have t_in_nhds : t ∈ nhds b := by
      rw [m_basis.mem_nhds_iff]
      exact ⟨m a, ⟨a, rfl⟩, ma_eq_t ▸ b_in_t, subset_of_eq ma_eq_t⟩

    cases UltraBFilter.to_filter.mem_or_compl_mem u m_inf m_bot a with
    | inl h => exact Filter.mem_of_superset h (ma_eq_t ▸ t_ss_s)
    | inr h =>
      rw [clusterPt_iff] at clusterPt
      specialize clusterPt t_in_nhds h
      rw [ma_eq_t, Set.inter_compl_self] at clusterPt
      exfalso
      exact Set.not_nonempty_empty clusterPt
  · intro le_nhds
    exact ClusterPt.of_le_nhds' le_nhds (UltraBFilter.to_filter_ne_bot' u m_bot)

end InfHom
