import Mathlib.Logic.Equiv.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph

import Rubin.Topology
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
variable [DecidableEq α]

/--
Maps a "seed" of homeorphisms in α to the intersection of their regular support in α.

Note that the condition that the resulting set is non-empty is introduced later in `AssociatedPosetSeed`
--/
def AssociatedPosetElem (S : Finset (HomeoGroup α)): Set α :=
  ⋂₀ ((fun (g : HomeoGroup α) => RegularSupport α g) '' S)

/--
This is a predecessor type to `AssociatedPoset`, where equality is defined on the `seed` used, rather than the `val`.
--/
structure AssociatedPosetSeed (α : Type _) [TopologicalSpace α] where
  seed : Finset (HomeoGroup α)
  val_nonempty : Set.Nonempty (AssociatedPosetElem seed)

theorem AssociatedPosetSeed.eq_iff_seed_eq (S T : AssociatedPosetSeed α) : S = T ↔ S.seed = T.seed := by
  -- Spooky :3c
  rw [mk.injEq]

def AssociatedPosetSeed.val (S : AssociatedPosetSeed α) : Set α := AssociatedPosetElem S.seed

theorem AssociatedPosetSeed.val_def (S : AssociatedPosetSeed α) : S.val = AssociatedPosetElem S.seed := rfl

/--
A partially-ordered set, associated to Rubin's proof.
Any element in that set is made up of a `seed`,
such that `val = AssociatedPosetElem seed` and `Set.Nonempty val`.

Actions on this set are first defined in terms of `AssociatedPosetSeed`,
as the proofs otherwise get hairy with `Exists.choose`.
--/
structure AssociatedPoset (α : Type _) [TopologicalSpace α] where
  val : Set α
  val_has_seed : ∃ po_seed : AssociatedPosetSeed α, po_seed.val = val

theorem AssociatedPoset.eq_iff_val_eq (S T : AssociatedPoset α) : S = T ↔ S.val = T.val := by
  rw [mk.injEq]

def AssociatedPoset.fromSeed (seed : AssociatedPosetSeed α) : AssociatedPoset α := ⟨
  seed.val,
  ⟨seed, seed.val_def⟩
⟩

noncomputable def AssociatedPoset.full_seed (S : AssociatedPoset α) : AssociatedPosetSeed α :=
  (Exists.choose S.val_has_seed)

noncomputable def AssociatedPoset.seed (S : AssociatedPoset α) : Finset (HomeoGroup α) :=
  S.full_seed.seed

@[simp]
theorem AssociatedPoset.full_seed_seed (S : AssociatedPoset α) : S.full_seed.seed = S.seed := rfl

@[simp]
theorem AssociatedPoset.fromSeed_val (seed : AssociatedPosetSeed α) :
  (AssociatedPoset.fromSeed seed).val = seed.val :=
by
  unfold fromSeed
  simp

@[simp]
theorem AssociatedPoset.val_from_seed (S : AssociatedPoset α) : AssociatedPosetElem S.seed = S.val := by
  unfold seed full_seed
  rw [<-AssociatedPosetSeed.val_def]
  rw [Exists.choose_spec S.val_has_seed]

@[simp]
theorem AssociatedPoset.val_from_seed₂ (S : AssociatedPoset α) : S.full_seed.val = S.val := by
  unfold full_seed
  rw [AssociatedPosetSeed.val_def]
  nth_rw 2 [<-AssociatedPoset.val_from_seed]
  unfold seed full_seed
  rfl

-- Allows one to prove properties of AssociatedPoset without jumping through `Exists.choose`-shaped hoops
theorem AssociatedPoset.prop_from_val {p : Set α → Prop}
  (any_seed : ∀ po_seed : AssociatedPosetSeed α, p po_seed.val) :
  ∀ (S : AssociatedPoset α), p S.val :=
by
  intro S
  rw [<-AssociatedPoset.val_from_seed]
  have res := any_seed S.full_seed
  rw [AssociatedPoset.val_from_seed₂] at res
  rw [AssociatedPoset.val_from_seed]
  exact res

@[simp]
theorem AssociatedPosetSeed.nonempty (S : AssociatedPosetSeed α) : Set.Nonempty S.val := S.val_nonempty

@[simp]
theorem AssociatedPoset.nonempty : ∀ (S : AssociatedPoset α), Set.Nonempty S.val :=
  AssociatedPoset.prop_from_val AssociatedPosetSeed.nonempty

@[simp]
theorem AssociatedPosetSeed.regular (S : AssociatedPosetSeed α) : Regular S.val := by
  rw [S.val_def]
  unfold AssociatedPosetElem

  apply regular_sInter
  · have set_decidable : DecidableEq (Set α) := Classical.typeDecidableEq (Set α)
    let fin : Finset (Set α) := S.seed.image ((fun g => RegularSupport α g))

    apply Set.Finite.ofFinset fin
    simp
  · intro S S_in_set
    simp at S_in_set
    let ⟨g, ⟨_, Heq⟩⟩ := S_in_set
    rw [<-Heq]
    exact regularSupport_regular α g

@[simp]
theorem AssociatedPoset.regular : ∀ (S : AssociatedPoset α), Regular S.val :=
  AssociatedPoset.prop_from_val AssociatedPosetSeed.regular

lemma AssociatedPosetElem.mul_seed (seed : Finset (HomeoGroup α)) [DecidableEq (HomeoGroup α)] (f : HomeoGroup α):
  AssociatedPosetElem (Finset.image (fun g => f * g * f⁻¹) seed) = f •'' AssociatedPosetElem seed :=
by
  unfold AssociatedPosetElem
  simp
  conv => {
    rhs
    ext; lhs; ext x; ext; lhs
    ext
    rw [regularSupport_smulImage]
  }

variable [DecidableEq (HomeoGroup α)]

/--
A `HomeoGroup α` group element `f` acts on an `AssociatedPosetSeed α` set `S`,
by mapping each element `g` of `S.seed` to `f * g * f⁻¹`
--/
instance homeoGroup_smul₂ : SMul (HomeoGroup α) (AssociatedPosetSeed α) where
  smul := fun f S => ⟨
    (Finset.image (fun g => f * g * f⁻¹) S.seed),
    by
      rw [AssociatedPosetElem.mul_seed]
      simp
      exact S.val_nonempty
  ⟩

theorem AssociatedPosetSeed.smul_seed (f : HomeoGroup α) (S : AssociatedPosetSeed α) :
  (f • S).seed = (Finset.image (fun g => f * g * f⁻¹) S.seed) := rfl

theorem AssociatedPosetSeed.smul_val (f : HomeoGroup α) (S : AssociatedPosetSeed α) :
  (f • S).val = AssociatedPosetElem (Finset.image (fun g => f * g * f⁻¹) S.seed) := rfl

theorem AssociatedPosetSeed.smul_val' (f : HomeoGroup α) (S : AssociatedPosetSeed α) :
  (f • S).val = f •'' S.val :=
by
  unfold val
  rw [<-AssociatedPosetElem.mul_seed]
  rw [AssociatedPosetSeed.smul_seed]

instance homeoGroup_mulAction₂ : MulAction (HomeoGroup α) (AssociatedPosetSeed α) where
  one_smul := by
    intro S
    rw [AssociatedPosetSeed.eq_iff_seed_eq]
    rw [AssociatedPosetSeed.smul_seed]
    simp
  mul_smul := by
    intro f g S
    rw [AssociatedPosetSeed.eq_iff_seed_eq]
    repeat rw [AssociatedPosetSeed.smul_seed]
    rw [Finset.image_image]
    ext x
    simp
    group

def AssociatedPoset.smul_from_seed (f : HomeoGroup α) (S : AssociatedPoset α) : AssociatedPoset α :=
  AssociatedPoset.fromSeed (f • S.full_seed)

-- TODO: use smulImage instead?
instance homeoGroup_smul₃ : SMul (HomeoGroup α) (AssociatedPoset α) where
  smul := AssociatedPoset.smul_from_seed

theorem AssociatedPoset.smul_fromSeed (f : HomeoGroup α) (S : AssociatedPoset α) :
  f • S = AssociatedPoset.fromSeed (f • S.full_seed) := rfl

theorem AssociatedPoset.smul_seed' (f : HomeoGroup α) (S : AssociatedPoset α) (seed : Finset (HomeoGroup α)) :
  S.val = AssociatedPosetElem seed →
  (f • S).val = AssociatedPosetElem (Finset.image (fun g => f * g * f⁻¹) seed) :=
by
  intro S_val_eq

  rw [AssociatedPoset.smul_fromSeed]
  rw [AssociatedPoset.fromSeed_val]
  rw [AssociatedPosetSeed.smul_val]
  repeat rw [AssociatedPosetElem.mul_seed]
  rw [<-S_val_eq]
  rw [AssociatedPoset.full_seed_seed]
  rw [<-AssociatedPoset.val_from_seed]

theorem AssociatedPoset.smul_seed (f : HomeoGroup α) (S : AssociatedPoset α) :
  (f • S).val = AssociatedPosetElem (Finset.image (fun g => f * g * f⁻¹) S.seed) :=
by
  apply AssociatedPoset.smul_seed'
  symm
  exact AssociatedPoset.val_from_seed S

theorem AssociatedPoset.smul_val (f : HomeoGroup α) (S : AssociatedPoset α) :
  (f • S).val = f •'' S.val :=
by
  rw [AssociatedPoset.smul_fromSeed]
  rw [AssociatedPoset.fromSeed_val]
  rw [<-AssociatedPoset.val_from_seed₂]
  exact AssociatedPosetSeed.smul_val' _ _

instance homeoGroup_mulAction₃ : MulAction (HomeoGroup α) (AssociatedPoset α) where
  one_smul := by
    intro S
    rw [AssociatedPoset.eq_iff_val_eq]
    repeat rw [AssociatedPoset.smul_val]
    rw [one_smulImage]
  mul_smul := by
    intro S f g
    rw [AssociatedPoset.eq_iff_val_eq]
    repeat rw [AssociatedPoset.smul_val]
    rw [smulImage_mul]



end Rubin
