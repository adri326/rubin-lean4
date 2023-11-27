import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Data.Set.Basic

import Rubin.RigidStabilizer
import Rubin.MulActionExt
import Rubin.SmulImage
import Rubin.Support

namespace Rubin

section Continuity

-- TODO: don't have this extend MulAction
class ContinuousMulAction (G α : Type _) [Group G] [TopologicalSpace α] extends
    MulAction G α where
  continuous : ∀ g : G, Continuous (fun x: α => g • x)
#align continuous_mul_action Rubin.ContinuousMulAction

-- TODO: give this a notation?
structure EquivariantHomeomorph (G α β : Type _) [Group G] [TopologicalSpace α]
    [TopologicalSpace β] [MulAction G α] [MulAction G β] extends Homeomorph α β where
  equivariant : is_equivariant G toFun
#align equivariant_homeomorph Rubin.EquivariantHomeomorph

variable {G α β : Type _}
variable [Group G]
variable [TopologicalSpace α] [TopologicalSpace β]

theorem equivariant_fun [MulAction G α] [MulAction G β]
    (h : EquivariantHomeomorph G α β) :
    is_equivariant G h.toFun :=
  h.equivariant
#align equivariant_fun Rubin.equivariant_fun

theorem equivariant_inv [MulAction G α] [MulAction G β]
    (h : EquivariantHomeomorph G α β) :
    is_equivariant G h.invFun :=
  by
  intro g x
  symm
  let e := congr_arg h.invFun (h.equivariant g (h.invFun x))
  rw [h.left_inv _, h.right_inv _] at e
  exact e
#align equivariant_inv Rubin.equivariant_inv

variable [Rubin.ContinuousMulAction G α]

theorem img_open_open (g : G) (U : Set α) (h : IsOpen U): IsOpen (g •'' U) :=
  by
  rw [Rubin.smulImage_eq_inv_preimage]
  exact Continuous.isOpen_preimage (Rubin.ContinuousMulAction.continuous g⁻¹) U h

#align img_open_open Rubin.img_open_open

theorem support_open (g : G) [TopologicalSpace α] [T2Space α]
    [Rubin.ContinuousMulAction G α] : IsOpen (Support α g) :=
  by
  apply isOpen_iff_forall_mem_open.mpr
  intro x xmoved
  rcases T2Space.t2 (g • x) x xmoved with ⟨U, V, open_U, open_V, gx_in_U, x_in_V, disjoint_U_V⟩
  exact
    ⟨V ∩ (g⁻¹ •'' U), fun y yW =>
      Disjoint.ne_of_mem
        disjoint_U_V
        (mem_inv_smulImage.mp (Set.mem_of_mem_inter_right yW))
        (Set.mem_of_mem_inter_left yW),
        IsOpen.inter open_V (Rubin.img_open_open g⁻¹ U open_U),
        ⟨x_in_V, mem_inv_smulImage.mpr gx_in_U⟩
    ⟩
#align support_open Rubin.support_open

end Continuity

-- TODO: come up with a name
section Other
open Topology

-- Note: `𝓝[≠] x` is notation for `nhdsWithin x {[x]}ᶜ`, ie. the neighborhood of x not containing itself
-- TODO: make this a class?
def has_no_isolated_points (α : Type _) [TopologicalSpace α] :=
  ∀ x : α, 𝓝[≠] x ≠ ⊥
#align has_no_isolated_points Rubin.has_no_isolated_points

instance has_no_isolated_points_neBot {α : Type _} [TopologicalSpace α] (h_nip: has_no_isolated_points α) (x: α): Filter.NeBot (𝓝[≠] x) where
  ne' := h_nip x

class LocallyDense (G α : Type _) [Group G] [TopologicalSpace α] extends MulAction G α :=
  isLocallyDense:
    ∀ U : Set α,
    ∀ p ∈ U,
    p ∈ interior (closure (MulAction.orbit (RigidStabilizer G U) p))
#align is_locally_dense Rubin.LocallyDense

lemma LocallyDense.nonEmpty {G α : Type _} [Group G] [TopologicalSpace α] [LocallyDense G α]:
  ∀ {U : Set α},
  Set.Nonempty U →
  ∃ p ∈ U, p ∈ interior (closure (MulAction.orbit (RigidStabilizer G U) p)) := by
  intros U H_ne
  exact ⟨H_ne.some, H_ne.some_mem, LocallyDense.isLocallyDense U H_ne.some H_ne.some_mem⟩

-- Should be put into mathlib — it doesn't use constructive logic only,
-- unlike (I assume) the inter_compl_nonempty_iff counterpart
lemma Set.inter_compl_empty_iff {α : Type _} (s t : Set α) :
  s ∩ tᶜ = ∅ ↔ s ⊆ t :=
by
  constructor
  {
    intro h₁
    by_contra h₂
    rw [<-Set.inter_compl_nonempty_iff] at h₂
    rw [Set.nonempty_iff_ne_empty] at h₂
    exact h₂ h₁
  }
  {
    intro h₁
    by_contra h₂
    rw [<-ne_eq, <-Set.nonempty_iff_ne_empty] at h₂
    rw [Set.inter_compl_nonempty_iff] at h₂
    exact h₂ h₁
  }

theorem subset_of_diff_closure_regular_empty {α : Type _} [TopologicalSpace α] {U V : Set α}
  (U_regular : interior (closure U) = U) (V_open : IsOpen V) (V_diff_cl_empty : V \ closure U = ∅) :
  V ⊆ U :=
by
  have V_eq_interior : interior V = V := IsOpen.interior_eq V_open
  -- rw [<-V_eq_interior]
  have V_subset_closure_U : V ⊆ closure U := by
    rw [Set.diff_eq_compl_inter] at V_diff_cl_empty
    rw [Set.inter_comm] at V_diff_cl_empty
    rw [Set.inter_compl_empty_iff] at V_diff_cl_empty
    exact V_diff_cl_empty
  have res : interior V ⊆ interior (closure U) := interior_mono V_subset_closure_U
  rw [U_regular] at res
  rw [V_eq_interior] at res
  exact res


end Other

end Rubin
