import Mathlib.Logic.Equiv.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph

-- TODO: extract ContinuousMulAction into its own file, or into MulActionExt?
import Rubin.Topological
import Rubin.RegularSupport

structure HomeoGroup (α : Type _) [TopologicalSpace α] extends
  Homeomorph α α

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

namespace Rubin

variable {α : Type _}
variable [TopologicalSpace α]

-- Note that the condition that the resulting set is non-empty is introduced later in `RegularInter`
-- TODO: rename!!!
def RegularInterElem (S : Finset (HomeoGroup α)): Set α :=
  ⋂₀ ((fun (g : HomeoGroup α) => RegularSupport α g) '' S)

def RegularInter (α : Type _) [TopologicalSpace α]: Type* :=
  { S : Set α //
    Set.Nonempty S
    ∧ ∃ (seed : Finset (HomeoGroup α)), S = RegularInterElem seed
  }

@[simp]
theorem regularInter_open (S : RegularInter α) : Set.Nonempty S.val := S.prop.left

@[simp]
theorem regularInter_regular (S : RegularInter α) : Regular S.val := by
  have ⟨seed, S_from_seed⟩ := S.prop.right
  rw [S_from_seed]
  unfold RegularInterElem

  apply regular_sInter
  · have set_decidable : DecidableEq (Set α) := Classical.typeDecidableEq (Set α)
    let fin : Finset (Set α) := seed.image ((fun g => RegularSupport α g))

    apply Set.Finite.ofFinset fin
    simp
  · intro S S_in_set
    simp at S_in_set
    let ⟨g, ⟨_, Heq⟩⟩ := S_in_set
    rw [<-Heq]
    exact regularSupport_regular α g

-- TODO:
-- def RegularInter.smul : HomeoGroup α → RegularInter α -> RegularInter α

-- instance homeoGroup_smul₂ : SMul (HomeoGroup α) (RegularInter α) where
--   smul := fun g x =>

end Rubin
