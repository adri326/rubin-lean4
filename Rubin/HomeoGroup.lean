import Mathlib.Logic.Equiv.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph

import Rubin.LocallyDense
import Rubin.Topology
import Rubin.Support
import Rubin.RegularSupport

structure HomeoGroup (α : Type _) [TopologicalSpace α] extends Homeomorph α α

variable {α : Type _}
variable [TopologicalSpace α]

def HomeoGroup.coe : HomeoGroup α -> Homeomorph α α := HomeoGroup.toHomeomorph

def HomeoGroup.from : Homeomorph α α -> HomeoGroup α := HomeoGroup.mk

instance homeoGroup_coe : Coe (HomeoGroup α) (Homeomorph α α) where
  coe := HomeoGroup.coe

instance homeoGroup_coe₂ : Coe (Homeomorph α α) (HomeoGroup α) where
  coe := HomeoGroup.from

def HomeoGroup.toPerm : HomeoGroup α → Equiv.Perm α := fun g => g.coe.toEquiv

instance homeoGroup_coe_perm : Coe (HomeoGroup α) (Equiv.Perm α) where
  coe := HomeoGroup.toPerm

@[simp]
theorem HomeoGroup.toPerm_def (g : HomeoGroup α) : g.coe.toEquiv = (g : Equiv.Perm α) := rfl

@[simp]
theorem HomeoGroup.mk_coe (g : HomeoGroup α) : HomeoGroup.mk (g.coe) = g := rfl

@[simp]
theorem HomeoGroup.eq_iff_coe_eq {f g : HomeoGroup α} : f.coe = g.coe ↔ f = g := by
  constructor
  {
    intro f_eq_g
    rw [<-HomeoGroup.mk_coe f]
    rw [f_eq_g]
    simp
  }
  {
    intro f_eq_g
    unfold HomeoGroup.coe
    rw [f_eq_g]
  }

@[simp]
theorem HomeoGroup.from_toHomeomorph (m : Homeomorph α α) : (HomeoGroup.from m).toHomeomorph = m := rfl

instance homeoGroup_one : One (HomeoGroup α) where
  one := HomeoGroup.from (Homeomorph.refl α)

theorem HomeoGroup.one_def : (1 : HomeoGroup α) = (Homeomorph.refl α : HomeoGroup α) := rfl

instance homeoGroup_inv : Inv (HomeoGroup α) where
  inv := fun g => HomeoGroup.from (g.coe.symm)

@[simp]
theorem HomeoGroup.inv_def (g : HomeoGroup α) : (Homeomorph.symm g.coe : HomeoGroup α) = g⁻¹ := rfl

theorem HomeoGroup.coe_inv {g : HomeoGroup α} : HomeoGroup.coe (g⁻¹) = (HomeoGroup.coe g).symm := rfl

instance homeoGroup_mul : Mul (HomeoGroup α) where
  mul := fun a b => ⟨b.toHomeomorph.trans a.toHomeomorph⟩

theorem HomeoGroup.coe_mul {f g : HomeoGroup α} : HomeoGroup.coe (f * g) = (HomeoGroup.coe g).trans (HomeoGroup.coe f) := rfl

@[simp]
theorem HomeoGroup.mul_def (f g : HomeoGroup α) : HomeoGroup.from ((HomeoGroup.coe g).trans (HomeoGroup.coe f)) = f * g := rfl

instance homeoGroup_group : Group (HomeoGroup α) where
  mul_assoc := by
    intro a b c
    rw [<-HomeoGroup.eq_iff_coe_eq]
    repeat rw [HomeoGroup_coe_mul]
    rfl
  mul_one := by
    intro a
    rw [<-HomeoGroup.eq_iff_coe_eq]
    rw [HomeoGroup.coe_mul]
    rfl
  one_mul := by
    intro a
    rw [<-HomeoGroup.eq_iff_coe_eq]
    rw [HomeoGroup.coe_mul]
    rfl
  mul_left_inv := by
    intro a
    rw [<-HomeoGroup.eq_iff_coe_eq]
    rw [HomeoGroup.coe_mul]
    rw [HomeoGroup.coe_inv]
    simp
    rfl

/--
The HomeoGroup trivially has a continuous and faithful `MulAction` on the underlying topology `α`.
--/
instance homeoGroup_smul₁ : SMul (HomeoGroup α) α where
  smul := fun g x => g.toFun x

@[simp]
theorem HomeoGroup.smul₁_def (f : HomeoGroup α) (x : α) : f.toFun x = f • x := rfl

@[simp]
theorem HomeoGroup.smul₁_def' (f : HomeoGroup α) (x : α) : f.toHomeomorph x = f • x := rfl

@[simp]
theorem HomeoGroup.coe_toFun_eq_smul₁ (f : HomeoGroup α) (x : α) : FunLike.coe (HomeoGroup.coe f) x = f • x := rfl

instance homeoGroup_mulAction₁ : MulAction (HomeoGroup α) α where
  one_smul := by
    intro x
    rfl
  mul_smul := by
    intro f g x
    rfl

instance homeoGroup_mulAction₁_continuous : Rubin.ContinuousMulAction (HomeoGroup α) α where
  continuous := by
    intro h
    constructor
    intro S S_open
    conv => {
      congr; ext
      congr; ext
      rw [<-HomeoGroup.smul₁_def']
    }
    simp only [Homeomorph.isOpen_preimage]
    exact S_open

instance homeoGroup_mulAction₁_faithful : FaithfulSMul (HomeoGroup α) α where
  eq_of_smul_eq_smul := by
    intro f g hyp
    rw [<-HomeoGroup.eq_iff_coe_eq]
    ext x
    simp
    exact hyp x

theorem homeoGroup_support_eq_support_toHomeomorph {G : Type _}
  [Group G] [MulAction G α] [Rubin.ContinuousMulAction G α] (g : G) :
  Rubin.Support α g = Rubin.Support α (HomeoGroup.from (Rubin.ContinuousMulAction.toHomeomorph α g)) :=
by
  ext x
  repeat rw [Rubin.mem_support]
  rw [<-HomeoGroup.smul₁_def]
  rw [HomeoGroup.from_toHomeomorph]
  rw [Rubin.ContinuousMulAction.toHomeomorph_toFun]

theorem HomeoGroup.smulImage_eq_image (g : HomeoGroup α) (S : Set α) :
  g •'' S = ⇑g.toHomeomorph '' S := rfl

namespace Rubin

section Other

/--
## Proposition 3.1
--/
theorem homeoGroup_rigidStabilizer_subset_iff {α : Type _} [TopologicalSpace α]
  [h_lm : LocallyMoving (HomeoGroup α) α]
  {U V : Set α} (U_reg : Regular U) (V_reg : Regular V):
  U ⊆ V ↔ RigidStabilizer (HomeoGroup α) U ≤ RigidStabilizer (HomeoGroup α) V :=
by
  constructor
  exact rigidStabilizer_mono
  intro rist_ss

  by_contra U_not_ss_V

  let W := U \ closure V
  have W_nonempty : Set.Nonempty W := by
    by_contra W_empty
    apply U_not_ss_V
    apply subset_from_diff_closure_eq_empty
    · assumption
    · exact U_reg.isOpen
    · rw [Set.not_nonempty_iff_eq_empty] at W_empty
      exact W_empty
  have W_ss_U : W ⊆ U := by
    simp
    exact Set.diff_subset _ _
  have W_open : IsOpen W := by
    unfold_let
    rw [Set.diff_eq_compl_inter]
    apply IsOpen.inter
    simp
    exact U_reg.isOpen

  have ⟨f, f_in_ristW, f_ne_one⟩ := h_lm.get_nontrivial_rist_elem W_open W_nonempty

  have f_in_ristU : f ∈ RigidStabilizer (HomeoGroup α) U := by
    exact rigidStabilizer_mono W_ss_U f_in_ristW

  have f_notin_ristV : f ∉ RigidStabilizer (HomeoGroup α) V := by
    apply rigidStabilizer_compl f_ne_one
    apply rigidStabilizer_mono _ f_in_ristW
    calc
      W = U ∩ (closure V)ᶜ := by unfold_let; rw [Set.diff_eq_compl_inter, Set.inter_comm]
      _ ⊆ (closure V)ᶜ := Set.inter_subset_right _ _
      _ ⊆ Vᶜ := by
        rw [Set.compl_subset_compl]
        exact subset_closure

  exact f_notin_ristV (rist_ss f_in_ristU)

theorem homeoGroup_rigidStabilizer_eq_iff {α : Type _} [TopologicalSpace α]
  [LocallyMoving (HomeoGroup α) α]
  {U V : Set α} (U_reg : Regular U) (V_reg : Regular V):
  RigidStabilizer (HomeoGroup α) U = RigidStabilizer (HomeoGroup α) V ↔ U = V :=
by
  constructor
  · intro rist_eq
    apply le_antisymm <;> simp only [Set.le_eq_subset]
    all_goals {
      rw [homeoGroup_rigidStabilizer_subset_iff] <;> try assumption
      rewrite [rist_eq]
      rfl
    }
  · intro H_eq
    rw [H_eq]

theorem homeoGroup_rigidStabilizer_injective {α : Type _} [TopologicalSpace α] [LocallyMoving (HomeoGroup α) α]
  : Function.Injective (fun U : { S : Set α // Regular S } => RigidStabilizer (HomeoGroup α) U.val) :=
by
  intro ⟨U, U_reg⟩
  intro ⟨V, V_reg⟩
  simp
  exact (homeoGroup_rigidStabilizer_eq_iff U_reg V_reg).mp

end Other

end Rubin
