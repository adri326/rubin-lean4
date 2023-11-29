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

variable [ContinuousMulAction G α]

theorem img_open_open (g : G) (U : Set α) (h : IsOpen U): IsOpen (g •'' U) :=
  by
  rw [Rubin.smulImage_eq_inv_preimage]
  exact Continuous.isOpen_preimage (Rubin.ContinuousMulAction.continuous g⁻¹) U h

#align img_open_open Rubin.img_open_open

theorem support_open (g : G) [TopologicalSpace α] [T2Space α]
    [ContinuousMulAction G α] : IsOpen (Support α g) :=
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
section LocallyDense
open Topology

/--
Note: `𝓝[≠] x` is notation for `nhdsWithin x {[x]}ᶜ`, ie. the neighborhood of x not containing itself.

--/
class HasNoIsolatedPoints (α : Type _) [TopologicalSpace α] :=
  nhbd_ne_bot : ∀ x : α, 𝓝[≠] x ≠ ⊥
#align has_no_isolated_points Rubin.HasNoIsolatedPoints

instance has_no_isolated_points_neBot {α : Type _} [TopologicalSpace α] [h_nip: HasNoIsolatedPoints α] (x: α): Filter.NeBot (𝓝[≠] x) where
  ne' := h_nip.nhbd_ne_bot x

class LocallyDense (G α : Type _) [Group G] [TopologicalSpace α] extends MulAction G α :=
  isLocallyDense:
    ∀ U : Set α,
    ∀ p ∈ U,
    p ∈ interior (closure (MulAction.orbit (RigidStabilizer G U) p))
#align is_locally_dense Rubin.LocallyDense

lemma LocallyDense.nonEmpty {G α : Type _} [Group G] [TopologicalSpace α] [LocallyDense G α]:
  ∀ {U : Set α},
  Set.Nonempty U →
  ∃ p ∈ U, p ∈ interior (closure (MulAction.orbit (RigidStabilizer G U) p)) :=
by
  intros U H_ne
  exact ⟨H_ne.some, H_ne.some_mem, LocallyDense.isLocallyDense U H_ne.some H_ne.some_mem⟩

end LocallyDense


end Rubin
