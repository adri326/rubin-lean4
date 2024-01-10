import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Data.Set.Basic

import Rubin.MulActionExt

namespace Rubin

-- TODO: coe to / extend MulActionHom

/--
maps from `α` to `β` which preserve both the topology (they are homeomorphisms)
and the group structure (they intertwine the actions of `G` on `α` and `β`)
-/
structure EquivariantHomeomorph (G α β : Type _) [Group G] [TopologicalSpace α]
    [TopologicalSpace β] [MulAction G α] [MulAction G β] extends Homeomorph α β where
  equivariant : is_equivariant G toFun
#align equivariant_homeomorph Rubin.EquivariantHomeomorph

@[inherit_doc]
notation:25 α " ≃ₜ[" G "] " β => EquivariantHomeomorph G α β

variable {G : Type u} [Group G]
variable {α : Type v} [TopologicalSpace α] [MulAction G α]
variable {β : Type w} [TopologicalSpace β] [MulAction G β]

theorem equivariant_fun (h : EquivariantHomeomorph G α β) :
    is_equivariant G h.toFun :=
  h.equivariant
#align equivariant_fun Rubin.equivariant_fun

theorem equivariant_inv (h : EquivariantHomeomorph G α β) :
    is_equivariant G h.invFun :=
  by
  intro g x
  symm
  let e := congr_arg h.invFun (h.equivariant g (h.invFun x))
  rw [h.left_inv _, h.right_inv _] at e
  exact e
#align equivariant_inv Rubin.equivariant_inv

protected def symm (h : α ≃ₜ[G] β) : β ≃ₜ[G] α where
  toHomeomorph := h.toHomeomorph.symm
  equivariant := equivariant_inv h

protected def refl : α ≃ₜ[G] α where
  toHomeomorph := Homeomorph.refl α
  equivariant := is_equivariant_refl

/-- Composition of two homeomorphisms. -/
protected def trans {γ  : Type _} [TopologicalSpace γ] [MulAction G γ]
  (h₁ : α ≃ₜ[G] β) (h₂ : β ≃ₜ[G] γ) : α ≃ₜ[G] γ where
  continuous_toFun := h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv
  equivariant := is_equivariant_trans h₁.toFun h₂.toFun h₁.equivariant h₂.equivariant

open Topology

-- Note: this sounds like a general enough theorem that it should already be in mathlib
lemma inter_of_open_subset_of_closure {α : Type _} [TopologicalSpace α] {U V : Set α}
  (U_open : IsOpen U) (U_nonempty : Set.Nonempty U) (V_nonempty : Set.Nonempty V)
  (U_ss_clV : U ⊆ closure V) : Set.Nonempty (U ∩ V) :=
by
  by_contra empty
  rw [Set.not_nonempty_iff_eq_empty] at empty
  rw [Set.nonempty_iff_ne_empty] at U_nonempty
  apply U_nonempty

  have clV_diff_U_ss_V : V ⊆ closure V \ U := by
    rw [Set.subset_diff]
    constructor
    exact subset_closure
    symm
    rw [Set.disjoint_iff_inter_eq_empty]
    exact empty
  have clV_diff_U_closed : IsClosed (closure V \ U) := by
    apply IsClosed.sdiff
    exact isClosed_closure
    assumption
  unfold closure at U_ss_clV
  simp at U_ss_clV
  specialize U_ss_clV (closure V \ U) clV_diff_U_closed clV_diff_U_ss_V

  rw [Set.subset_diff] at U_ss_clV
  rw [Set.disjoint_iff_inter_eq_empty] at U_ss_clV
  simp at U_ss_clV
  exact U_ss_clV.right

/--
Note: `𝓝[≠] x` is notation for `nhdsWithin x {[x]}ᶜ`, ie. the neighborhood of x not containing itself.
--/
class HasNoIsolatedPoints (α : Type _) [TopologicalSpace α] :=
  -- TODO: rename to nhdsWithin_ne_bot
  nhbd_ne_bot : ∀ x : α, 𝓝[≠] x ≠ ⊥
#align has_no_isolated_points Rubin.HasNoIsolatedPoints

instance has_no_isolated_points_neBot₁ {α : Type _} [TopologicalSpace α] [h_nip: HasNoIsolatedPoints α]
  (x: α) : Filter.NeBot (𝓝[≠] x) where
  ne' := h_nip.nhbd_ne_bot x

theorem Filter.NeBot.choose {α : Type _} (F : Filter α) [Filter.NeBot F] :
  ∃ S : Set α, S ∈ F :=
by
  have res := (Filter.inhabitedMem (α := α) (f := F)).default
  exact ⟨res.val, res.prop⟩


theorem TopologicalSpace.IsTopologicalBasis.contains_point {α : Type _} [TopologicalSpace α]
  {B : Set (Set α)} (B_basis : TopologicalSpace.IsTopologicalBasis B) (p : α) :
  ∃ S : Set α, S ∈ B ∧ p ∈ S :=
by
  have nhds_basis := B_basis.nhds_hasBasis (a := p)

  rw [Filter.hasBasis_iff] at nhds_basis
  let ⟨S₁, S₁_in_nhds⟩ := Filter.NeBot.choose (𝓝 p)
  let ⟨S, ⟨⟨S_in_B, p_in_S⟩, _⟩⟩ := (nhds_basis S₁).mp S₁_in_nhds
  exact ⟨S, S_in_B, p_in_S⟩

-- The collection of all the sets in `B` (a topological basis of `α`), such that `p` is in them.
def TopologicalBasisContaining {α : Type _} [TopologicalSpace α]
  {B : Set (Set α)} (B_basis : TopologicalSpace.IsTopologicalBasis B) (p : α) : FilterBasis α
where
  sets := {b ∈ B | p ∈ b}
  nonempty := by
    let ⟨S, S_in_B, p_in_S⟩ := TopologicalSpace.IsTopologicalBasis.contains_point B_basis p
    use S
    simp
    tauto
  inter_sets := by
    intro S T ⟨S_in_B, p_in_S⟩ ⟨T_in_B, p_in_T⟩

    have S_in_nhds := B_basis.mem_nhds_iff.mpr ⟨S, S_in_B, ⟨p_in_S, Eq.subset rfl⟩⟩
    have T_in_nhds := B_basis.mem_nhds_iff.mpr ⟨T, T_in_B, ⟨p_in_T, Eq.subset rfl⟩⟩

    have ST_in_nhds : S ∩ T ∈ 𝓝 p := Filter.inter_mem S_in_nhds T_in_nhds
    rw [B_basis.mem_nhds_iff] at ST_in_nhds
    let ⟨U, props⟩ := ST_in_nhds
    use U
    simp
    simp at props
    tauto

theorem TopologicalBasisContaining.mem_iff {α : Type _} [TopologicalSpace α]
  {B : Set (Set α)} (B_basis : TopologicalSpace.IsTopologicalBasis B) (p : α) (S : Set α) :
  S ∈ TopologicalBasisContaining B_basis p ↔ S ∈ B ∧ p ∈ S :=
by
  rw [<-FilterBasis.mem_sets]
  rfl

theorem TopologicalBasisContaining.mem_nhds {α : Type _} [TopologicalSpace α]
  {B : Set (Set α)} (B_basis : TopologicalSpace.IsTopologicalBasis B) (p : α) (S : Set α) :
  S ∈ TopologicalBasisContaining B_basis p → S ∈ 𝓝 p :=
by
  rw [TopologicalBasisContaining.mem_iff]
  rw [B_basis.mem_nhds_iff]
  intro ⟨S_in_B, p_in_S⟩
  use S

instance TopologicalBasisContaining.neBot {α : Type _} [TopologicalSpace α]
  {B : Set (Set α)} (B_basis : TopologicalSpace.IsTopologicalBasis B) (p : α) :
  Filter.NeBot (TopologicalBasisContaining B_basis p).filter where
  ne' := by
    intro empty_in
    rw [<-Filter.empty_mem_iff_bot, FilterBasis.mem_filter_iff] at empty_in
    let ⟨S, ⟨S_in_basis, S_ss_empty⟩⟩ := empty_in
    rw [TopologicalBasisContaining.mem_iff] at S_in_basis
    exact S_ss_empty S_in_basis.right

-- Note: the definition of "convergence" in the article doesn't quite match with the definition of ClusterPt
-- Instead, `F ≤ nhds p` should be used.

-- Note: Filter.HasBasis is a stronger statement than just FilterBasis - it defines a two-way relationship between a filter and a property; if the property is true for a set, then any superset of it is part of the filter, and vice-versa.
-- With this, it's impossible for there to be a finer filter satisfying the property,
-- as is evidenced by `filter_eq`: stripping away the `Filter` allows us to uniquely reconstruct it from the property itself.

-- Proposition 3.3.1 trivially follows from `TopologicalSpace.IsTopologicalBasis.nhds_hasBasis` and `disjoint_nhds_nhds`: if `F.HasBasis (S → S ∈ B ∧ p ∈ S)` and `F.HasBasis (S → S ∈ B ∧ q ∈ S)`,
-- then one can prove that `F ≤ nhds x` and `F ≤ nhds y` ~> `F = ⊥`
-- Proposition 3.3.2 becomes simply `TopologicalSpace.IsTopologicalBasis.nhds_hasBasis`
-- Proposition 3.3.3 is a consequence of the structure of `HasBasis`

-- Proposition 3.4.1 can maybe be proven with `TopologicalSpace.IsTopologicalBasis.mem_closure_iff`?

-- The tricky part here though is that "F is an ultra(pre)filter on B" can't easily be expressed.
-- I should maybe define a Prop for it, and show that "F is an ultrafilter on B" + "F tends to a point p"
-- is equivalent to `TopologicalSpace.IsTopologicalBasis.nhds_hasBasis`.

-- The alternative is to only work with `Filter`, and state conditions with `Filter.HasBasis`,
-- since that will force the filter to be an ultraprefilter on B.

end Rubin
