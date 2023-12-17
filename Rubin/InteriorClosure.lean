import Mathlib.Topology.Basic
import Mathlib.Topology.Separation

import Rubin.SmulImage

namespace Rubin

variable {α : Type _}
variable [TopologicalSpace α]

/--
Defines a kind of "regularization" transformation made to sets,
by calling `closure` followed by `interior` on those sets.

A set is then said to be [`Regular`] if the InteriorClosure does not modify it.
--/
def InteriorClosure (U : Set α) : Set α :=
  interior (closure U)
#align interior_closure Rubin.InteriorClosure

@[simp]
theorem InteriorClosure.def (U : Set α) : InteriorClosure U = interior (closure U) :=
  by simp [InteriorClosure]

@[simp]
theorem InteriorClosure.fdef : InteriorClosure = (interior ∘ (closure (α := α))) := by ext; simp

/--
A set `U` is said to be regular if the interior of the closure of `U` is equal to `U`.
Notably, a regular set is also open, and the interior of a regular set is equal to itself.
--/
def Regular (U : Set α) : Prop :=
  InteriorClosure U = U

@[simp]
theorem Regular.def (U : Set α) : Regular U ↔ interior (closure U) = U :=
  by simp [Regular]
#align set.is_regular_def Rubin.Regular.def

@[simp]
theorem Regular.eq {U : Set α} (U_reg : Regular U) : interior (closure U) = U :=
  (Regular.def U).mp U_reg

instance Regular.instCoe {U : Set α} : Coe (Regular U) (interior (closure U) = U) where
  coe := Regular.eq

/-- From this, the set of regular sets is the set of regular *open* sets. --/
theorem regular_open (U : Set α) : Regular U → IsOpen U :=
by
  intro h_reg
  rw [<-h_reg]
  simp

theorem Regular.isOpen {U : Set α} (U_regular : Regular U): IsOpen U := regular_open _ U_regular

theorem regular_interior {U : Set α} : Regular U → interior U = U :=
by
  intro h_reg
  rw [<-h_reg]
  simp

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

theorem monotone_interiorClosure : Monotone (InteriorClosure (α := α))
:= fun a b =>
  interiorClosure_mono a b

theorem interiorClosure_subset_of_regular {U V : Set α} (U_ss_V : U ⊆ V) (V_regular : Regular V) :
  InteriorClosure U ⊆ V :=
by
  rw [<-V_regular]
  apply interiorClosure_mono
  assumption

theorem compl_closure_regular_of_open {S : Set α} (S_open : IsOpen S) : Regular (closure S)ᶜ := by
  apply Set.eq_of_subset_of_subset
  · simp
    apply closure_mono
    rw [IsOpen.subset_interior_iff S_open]
    exact subset_closure
  · apply interiorClosure_subset
    simp

@[simp]
theorem interiorClosure_closure {S : Set α} (S_open : IsOpen S) : closure (InteriorClosure S) = closure S :=
by
  apply Set.eq_of_subset_of_subset
  · simp
    rw [<-Set.compl_subset_compl]
    rw [<-(compl_closure_regular_of_open S_open)]
    simp
    rfl
  · apply closure_mono
    exact interiorClosure_subset S_open

@[simp]
theorem interiorClosure_interior {S : Set α} : interior (InteriorClosure S) = (InteriorClosure S) :=
regular_interior (interiorClosure_regular S)

theorem disjoint_interiorClosure_left {U V : Set α} (V_open : IsOpen V) :
  Disjoint U V → Disjoint (InteriorClosure U) V :=
by
  intro disj
  apply Set.disjoint_of_subset_left interior_subset
  exact Disjoint.closure_left disj V_open

theorem disjoint_interiorClosure_right {U V : Set α} (U_open : IsOpen U)
  (disj : Disjoint U V) : Disjoint U (InteriorClosure V) :=
  (disjoint_interiorClosure_left U_open (Disjoint.symm disj)).symm

theorem disjoint_interiorClosure_left_iff {U V : Set α} (U_open : IsOpen U) (V_open : IsOpen V) :
  Disjoint U V ↔ Disjoint (InteriorClosure U) V :=
by
  constructor
  exact disjoint_interiorClosure_left V_open

  intro disj
  apply Set.disjoint_of_subset_left
  · exact subset_closure
  · rw [<-interiorClosure_closure U_open]
    exact Disjoint.closure_left disj V_open

theorem disjoint_interiorClosure_iff {U V : Set α} (U_open : IsOpen U) (V_open : IsOpen V) :
  Disjoint U V ↔ Disjoint (InteriorClosure U) (InteriorClosure V) :=
by
  constructor
  {
    intro disj
    apply disjoint_interiorClosure_left (interiorClosure_regular V).isOpen
    apply disjoint_interiorClosure_right U_open
    exact disj
  }
  {
    intro disj
    rw [disjoint_interiorClosure_left_iff U_open V_open]
    symm
    rw [disjoint_interiorClosure_left_iff V_open (interiorClosure_open _)]
    symm
    exact disj
  }

theorem subset_from_diff_closure_eq_empty {U V : Set α}
  (U_regular : Regular U) (V_open : IsOpen V) (V_diff_cl_empty : V \ closure U = ∅) :
  V ⊆ U :=
by
  have V_eq_interior : interior V = V := IsOpen.interior_eq V_open
  rw [<-V_eq_interior]
  rw [<-U_regular]
  apply interior_mono
  rw [<-Set.diff_eq_empty]
  exact V_diff_cl_empty

theorem regular_nbhd [T2Space α] {u v : α} (u_ne_v : u ≠ v):
  ∃ (U V : Set α), Regular U ∧ Regular V ∧ Disjoint U V ∧ u ∈ U ∧ v ∈ V :=
by
  let ⟨U', V', U'_open, V'_open, u_in_U', v_in_V', disj⟩ := t2_separation u_ne_v
  let U := InteriorClosure U'
  let V := InteriorClosure V'
  use U, V
  repeat' apply And.intro
  · apply interiorClosure_regular
  · apply interiorClosure_regular
  · apply disjoint_interiorClosure_left (interiorClosure_regular V').isOpen
    apply disjoint_interiorClosure_right U'_open
    exact disj
  · exact (interiorClosure_subset U'_open) u_in_U'
  · exact (interiorClosure_subset V'_open) v_in_V'

theorem regular_inter {U V : Set α} : Regular U → Regular V → Regular (U ∩ V) :=
by
  intro U_reg V_reg
  simp
  have UV_open : IsOpen (U ∩ V) := IsOpen.inter U_reg.isOpen V_reg.isOpen

  apply Set.eq_of_subset_of_subset
  · simp
    constructor
    · nth_rw 2 [<-U_reg]
      apply interiorClosure_mono
      simp
    · nth_rw 2 [<-V_reg]
      apply interiorClosure_mono
      simp
  · apply interiorClosure_subset
    exact UV_open

theorem regular_sInter {S : Set (Set α)} (S_finite : Set.Finite S) (all_reg : ∀ U ∈ S, Regular U):
  Regular (⋂₀ S) :=
Set.Finite.induction_on' S_finite (by simp) (by
  intro U S' U_in_S _ _ IH
  rw [Set.sInter_insert]
  apply regular_inter
  · exact all_reg _ U_in_S
  · exact IH
)

theorem interiorClosure_smulImage' {G : Type _} [Group G] [MulAction G α]
  (g : G) (U : Set α)
  (g_continuous : ∀ S : Set α, IsOpen S → IsOpen (g •'' S) ∧ IsOpen (g⁻¹ •'' S)) :
  InteriorClosure (g •'' U) = g •'' InteriorClosure U :=
by
  simp
  rw [<-smulImage_interior' _ _ g_continuous]
  rw [<-smulImage_closure' _ _ g_continuous]

theorem interiorClosure_smulImage {G : Type _} [Group G] [MulAction G α] [ContinuousMulAction G α]
  (g : G) (U : Set α) :
  InteriorClosure (g •'' U) = g •'' InteriorClosure U :=
  interiorClosure_smulImage' g U (continuousMulAction_elem_continuous α g)

end Rubin
