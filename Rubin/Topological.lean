import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph

import Rubin.MulActionExt
import Rubin.SmulImage
import Rubin.Support

namespace Rubin.Topological


class ContinuousMulAction (G α : Type _) [Group G] [TopologicalSpace α] extends
    MulAction G α where
  continuous : ∀ g : G, Continuous (fun x: α => g • x)
#align continuous_mul_action Rubin.Topological.ContinuousMulAction

-- TODO: give this a notation?
structure EquivariantHomeomorph (G α β : Type _) [Group G] [TopologicalSpace α]
    [TopologicalSpace β] [MulAction G α] [MulAction G β] extends Homeomorph α β where
  equivariant : is_equivariant G toFun
#align equivariant_homeomorph Rubin.Topological.EquivariantHomeomorph

variable {G α β : Type _}
variable [Group G]
variable [TopologicalSpace α] [TopologicalSpace β]

theorem equivariant_fun [MulAction G α] [MulAction G β]
    (h : EquivariantHomeomorph G α β) :
    is_equivariant G h.toFun :=
  h.equivariant
#align equivariant_fun Rubin.Topological.equivariant_fun

theorem equivariant_inv [MulAction G α] [MulAction G β]
    (h : EquivariantHomeomorph G α β) :
    is_equivariant G h.invFun :=
  by
  intro g x
  symm
  let e := congr_arg h.invFun (h.equivariant g (h.invFun x))
  rw [h.left_inv _, h.right_inv _] at e
  exact e
#align equivariant_inv Rubin.Topological.equivariant_inv

variable [Rubin.Topological.ContinuousMulAction G α]

theorem img_open_open (g : G) (U : Set α) (h : IsOpen U): IsOpen (g •'' U) :=
  by
  rw [Rubin.smulImage_eq_inv_preimage]
  exact Continuous.isOpen_preimage (Rubin.Topological.ContinuousMulAction.continuous g⁻¹) U h

#align img_open_open Rubin.Topological.img_open_open

theorem support_open (g : G) [TopologicalSpace α] [T2Space α]
    [Rubin.Topological.ContinuousMulAction G α] : IsOpen (Support α g) :=
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
        IsOpen.inter open_V (Rubin.Topological.img_open_open g⁻¹ U open_U),
        ⟨x_in_V, mem_inv_smulImage.mpr gx_in_U⟩
    ⟩
#align support_open Rubin.Topological.support_open

end Rubin.Topological
