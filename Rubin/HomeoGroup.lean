import Mathlib.Logic.Equiv.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Algebra.ConstMulAction

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

instance homeoGroup_mulAction₁_continuous : ContinuousConstSMul (HomeoGroup α) α where
  continuous_const_smul := by
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

theorem HomeoGroup.smulImage_eq_image (g : HomeoGroup α) (S : Set α) :
  g •'' S = ⇑g.toHomeomorph '' S := rfl

section FromContinuousConstSMul

variable {G : Type _} [Group G]
variable [MulAction G α] [ContinuousConstSMul G α]

/--
`fromContinuous` is a structure-preserving transformation from a continuous `MulAction` to a `HomeoGroup`
--/
def HomeoGroup.fromContinuous (α : Type _) [TopologicalSpace α] [MulAction G α] [ContinuousConstSMul G α]
  (g : G) : HomeoGroup α :=
  HomeoGroup.from (Homeomorph.smul g)

@[simp]
theorem HomeoGroup.fromContinuous_def (g : G) :
  HomeoGroup.from (Homeomorph.smul g) = HomeoGroup.fromContinuous α g := rfl

@[simp]
theorem HomeoGroup.fromContinuous_smul (g : G) :
  ∀ x : α, (HomeoGroup.fromContinuous α g) • x = g • x :=
by
  intro x
  unfold fromContinuous
  rw [<-HomeoGroup.smul₁_def', HomeoGroup.from_toHomeomorph]
  unfold Homeomorph.smul
  simp

theorem HomeoGroup.fromContinuous_one :
  HomeoGroup.fromContinuous α (1 : G) = (1 : HomeoGroup α) :=
by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
  simp

theorem HomeoGroup.fromContinuous_mul (g h : G):
  (HomeoGroup.fromContinuous α g) * (HomeoGroup.fromContinuous α h) = (HomeoGroup.fromContinuous α (g * h)) :=
by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
  intro x
  rw [mul_smul]
  simp
  rw [mul_smul]

theorem HomeoGroup.fromContinuous_inv (g : G):
  HomeoGroup.fromContinuous α g⁻¹ = (HomeoGroup.fromContinuous α g)⁻¹ :=
by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
  intro x
  group_action
  rw [mul_smul]
  simp

theorem HomeoGroup.fromContinuous_eq_iff [FaithfulSMul G α] (g h : G):
  (HomeoGroup.fromContinuous α g) = (HomeoGroup.fromContinuous α h) ↔ g = h :=
by
  constructor
  · intro cont_eq
    apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
    intro x
    rw [<-HomeoGroup.fromContinuous_smul g]
    rw [cont_eq]
    simp
  · tauto

@[simp]
theorem HomeoGroup.fromContinuous_support (g : G) :
  Rubin.Support α (HomeoGroup.fromContinuous α g) = Rubin.Support α g :=
by
  ext x
  repeat rw [Rubin.mem_support]
  rw [<-HomeoGroup.smul₁_def, <-HomeoGroup.fromContinuous_def]
  rw [HomeoGroup.from_toHomeomorph]
  rw [Homeomorph.smul]
  simp only [Equiv.toFun_as_coe, MulAction.toPerm_apply]

@[simp]
theorem HomeoGroup.fromContinuous_regularSupport (g : G) :
  Rubin.RegularSupport α (HomeoGroup.fromContinuous α g) = Rubin.RegularSupport α g :=
by
  unfold Rubin.RegularSupport
  rw [HomeoGroup.fromContinuous_support]

@[simp]
theorem HomeoGroup.fromContinuous_smulImage (g : G) (V : Set α) :
  (HomeoGroup.fromContinuous α g) •'' V = g •'' V :=
by
  repeat rw [Rubin.smulImage_def]
  simp

def HomeoGroup.fromContinuous_embedding (α : Type _) [TopologicalSpace α] [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α]: G ↪ (HomeoGroup α) where
  toFun := fun (g : G) => HomeoGroup.fromContinuous α g
  inj' := by
    intro g h fromCont_eq
    simp at fromCont_eq
    apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
    intro x
    rw [<-fromContinuous_smul, fromCont_eq, fromContinuous_smul]

@[simp]
theorem HomeoGroup.fromContinuous_embedding_toFun [FaithfulSMul G α] (g : G):
  HomeoGroup.fromContinuous_embedding α g = HomeoGroup.fromContinuous α g := rfl

def HomeoGroup.fromContinuous_monoidHom (α : Type _) [TopologicalSpace α] [MulAction G α] [ContinuousConstSMul G α] [FaithfulSMul G α]: G →* (HomeoGroup α) where
  toFun := fun (g : G) => HomeoGroup.fromContinuous α g
  map_one' := by
    simp
    rw [fromContinuous_one]
  map_mul' := by
    simp
    intros
    rw [fromContinuous_mul]

end FromContinuousConstSMul
