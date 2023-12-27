import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation

def Filter.InBasis {α : Type _} (F : Filter α) (B : Set (Set α)) : Prop :=
  ∀ (S : Set α), S ∈ F → ∃ T ∈ F, T ∈ B ∧ T ⊆ S

/--
This is a formulation for prefilters in a basis that are ultra.
It is a weaker statement than regular ultrafilters,
but it allows for some nice properties, like the equivalence of cluster points and neighborhoods.
--/
structure UltrafilterInBasis {α : Type} (F : Filter α) (B : Set (Set α)) :=
  in_basis : Filter.InBasis F B

  ultra : ∀ (F' : Filter α), F'.InBasis B → F'.NeBot → F' ≤ F → F ≤ F'

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

--  (map_mono : ∀ A B : Set α, A ⊆ B ↔ map A ⊆ map B) (F_basis : F.InBasis B)
def Filter.InBasis.map_basis {α β : Type _} (F : Filter α) (B : Set (Set α))
  (map : Set α → Set β): Filter β :=
  ⨅ (S : Filter.InBasis.basis F B), Filter.principal (map S)

lemma Filter.InBasis.map_directed {β : Type _} (F_basis : F.InBasis B)
  (map : Set α → Set β) (map_mono : Monotone map) :
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
  (map : Set α → Set β) (map_mono : Monotone map) (map_nonempty : ∀ S ∈ B, Set.Nonempty (map S)) :
  Filter.NeBot (Filter.InBasis.map_basis F B map) :=
by
  apply Filter.iInf_neBot_of_directed
  · exact Filter.InBasis.map_directed F_basis map map_mono
  · intro ⟨S, S_in_F, S_in_B⟩
    simp
    exact map_nonempty _ S_in_B

theorem Filter.InBasis.map_basis_hasBasis {β : Type _} [Nonempty β] (F_basis : F.InBasis B)
  (map : Set α → Set β) (map_mono : Monotone map):
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
  (map : Set α → Set β) (map_mono : Monotone map) (map_nonempty : ∀ S ∈ B, Set.Nonempty (map S)) :
  (Filter.InBasis.map_basis F B map).InBasis (map '' B) :=
by
  intro S S_in_map

  have β_nonempty : Nonempty β := by
    let ⟨T, _, T_in_B⟩ := Filter.InBasis.basis_nonempty' F_basis
    let ⟨x, _⟩ := map_nonempty T T_in_B
    use x

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

theorem nhds_in_basis [TopologicalSpace α] (p : α) (B_basis : TopologicalSpace.IsTopologicalBasis B):
  (nhds p).InBasis B :=
  Filter.InBasis.from_hasBasis B_basis.nhds_hasBasis (fun _ ⟨in_B, _⟩ => in_B)

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
  : IsAtomic { F : Filter α // F.InBasis B ∨ F = ⊥ } := by
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

-- TODO: define UltrafilterInBasis.of :)
