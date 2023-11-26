import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation

import Rubin.Tactic
import Rubin.Support
import Rubin.Topological

namespace Rubin

section InteriorClosure

variable {α : Type _}
variable [TopologicalSpace α]

-- Defines a kind of "regularization" transformation made to sets,
-- by calling `closure` followed by `interior` on it.
--
-- A set is then said to be regular if the InteriorClosure does not modify it.
def InteriorClosure (U : Set α) : Set α :=
  interior (closure U)
#align interior_closure Rubin.InteriorClosure

@[simp]
theorem InteriorClosure.def (U : Set α) : InteriorClosure U = interior (closure U) :=
  by simp [InteriorClosure]

@[simp]
theorem InteriorClosure.fdef : InteriorClosure = (interior ∘ (closure (α := α))) := by ext; simp

def Regular (U : Set α) : Prop :=
  InteriorClosure U = U

@[simp]
theorem Regular.def (U : Set α) : Regular U ↔ interior (closure U) = U :=
  by simp [Regular]
#align set.is_regular_def Rubin.Regular.def

theorem interiorClosure_open (U : Set α) : IsOpen (InteriorClosure U) := by simp
#align is_open_interior_closure Rubin.interiorClosure_open

theorem interiorClosure_subset {U : Set α} :
  IsOpen U → U ⊆ InteriorClosure U :=
by
  intro h
  apply subset_trans
  exact subset_interior_iff_isOpen.mpr h
  apply interior_mono
  exact subset_closure
#align is_open.interior_closure_subset Rubin.interiorClosure_subset

theorem interiorClosure_regular (U : Set α) : Regular (InteriorClosure U) :=
by
  apply Set.eq_of_subset_of_subset <;> unfold InteriorClosure
  {
    apply interior_mono
    nth_rw 2 [<-closure_closure (s := U)]
    apply closure_mono
    exact interior_subset
  }
  {
    nth_rw 1 [<-interior_interior]
    apply interior_mono
    exact subset_closure
  }
#align regular_interior_closure Rubin.interiorClosure_regular

theorem interiorClosure_mono (U V : Set α) :
  U ⊆ V → InteriorClosure U ⊆ InteriorClosure V
:= interior_mono ∘ closure_mono
#align interior_closure_mono Rubin.interiorClosure_mono

theorem monotone_interior_closure : Monotone (InteriorClosure (α := α))
:= fun a b =>
  interiorClosure_mono a b

theorem regular_open (U : Set α) : Regular U → IsOpen U :=
by
  intro h_reg
  rw [<-h_reg]
  simp

theorem regular_interior (U : Set α) : Regular U → interior U = U :=
by
  intro h_reg
  rw [<-h_reg]
  simp

end InteriorClosure

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

@[simp]
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

end RegularSupport_continuous

end Rubin
