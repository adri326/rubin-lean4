import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Data.Set.Basic

import Rubin.MulActionExt

namespace Rubin

class ContinuousMulAction (G α : Type _) [Group G] [TopologicalSpace α] [MulAction G α] where
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

open Topology

/--
Note: `𝓝[≠] x` is notation for `nhdsWithin x {[x]}ᶜ`, ie. the neighborhood of x not containing itself.
--/
class HasNoIsolatedPoints (α : Type _) [TopologicalSpace α] :=
  nhbd_ne_bot : ∀ x : α, 𝓝[≠] x ≠ ⊥
#align has_no_isolated_points Rubin.HasNoIsolatedPoints

instance has_no_isolated_points_neBot {α : Type _} [TopologicalSpace α] [h_nip: HasNoIsolatedPoints α] (x: α): Filter.NeBot (𝓝[≠] x) where
  ne' := h_nip.nhbd_ne_bot x

end Rubin
