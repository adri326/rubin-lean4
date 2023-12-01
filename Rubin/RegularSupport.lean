import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation

import Rubin.Tactic
import Rubin.Support
import Rubin.Topology
import Rubin.InteriorClosure
import Rubin.RigidStabilizer

namespace Rubin

section RegularSupport_def

variable {G : Type _}
variable (α : Type _)
variable [Group G]
variable [MulAction G α]
variable [TopologicalSpace α]

-- The "regular support" is the `Support` of `g : G` in `α` (aka the elements in `α` which are moved by `g`),
-- transformed with the interior closure.
def RegularSupport (g: G) : Set α :=
  InteriorClosure (Support α g)
#align regular_support Rubin.RegularSupport

theorem RegularSupport.def {G : Type _} (α : Type _)
  [Group G] [MulAction G α] [TopologicalSpace α]
  (g: G) : RegularSupport α g = interior (closure (Support α g)) :=
by
  simp [RegularSupport]

theorem regularSupport_open [MulAction G α] (g : G) : IsOpen (RegularSupport α g) := by
  unfold RegularSupport
  simp

theorem regularSupport_regular [MulAction G α] (g : G) : Regular (RegularSupport α g) := by
  apply interiorClosure_regular
#align regular_regular_support Rubin.regularSupport_regular

end RegularSupport_def

section RegularSupport_continuous

variable {G α : Type _}
variable [Group G]
variable [TopologicalSpace α]
variable [MulAction G α]
variable [ContinuousMulAction G α]

theorem support_subset_regularSupport [T2Space α] {g : G} :
  Support α g ⊆ RegularSupport α g :=
by
  apply interiorClosure_subset
  apply support_open (α := α) (g := g)
#align support_in_regular_support Rubin.support_subset_regularSupport

theorem regularSupport_subset {g : G} {U : Set α} :
  Regular U → Support α g ⊆ U → RegularSupport α g ⊆ U :=
by
  intro U_reg h
  rw [<-U_reg]
  apply interiorClosure_mono
  exact h

theorem regularSupport_subset_closure_support {g : G} :
  RegularSupport α g ⊆ closure (Support α g) :=
by
  unfold RegularSupport
  simp
  exact interior_subset

theorem regularSupport_subset_of_rigidStabilizer {g : G} {U : Set α} (U_reg : Regular U) :
  g ∈ RigidStabilizer G U → RegularSupport α g ⊆ U :=
by
  intro g_in_rist
  apply regularSupport_subset
  · assumption
  · apply rigidStabilizer_support.mp
    assumption

theorem regularSupport_subset_iff_rigidStabilizer [T2Space α] {g : G} {U : Set α} (U_reg : Regular U) :
  g ∈ RigidStabilizer G U ↔ RegularSupport α g ⊆ U :=
by
  constructor
  · apply regularSupport_subset_of_rigidStabilizer U_reg
  · intro rs_subset
    rw [rigidStabilizer_support]
    apply subset_trans
    apply support_subset_regularSupport
    exact rs_subset
#align mem_regular_support Rubin.regularSupport_subset_of_rigidStabilizer

theorem regularSupport_smulImage {f g : G} :
  f •'' (RegularSupport α g) = RegularSupport α (f * g * f⁻¹) :=
by
  unfold RegularSupport
  rw [support_conjugate]
  rw [interiorClosure_smulImage _ _ (continuousMulAction_elem_continuous α f)]

end RegularSupport_continuous

end Rubin
