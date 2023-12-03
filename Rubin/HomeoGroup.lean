import Mathlib.Logic.Equiv.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph

import Rubin.LocallyDense
import Rubin.Topology
import Rubin.Support
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

section AssociatedPoset.Prelude

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

@[simp]
theorem AssociatedPosetSeed.nonempty (S : AssociatedPosetSeed α) : Set.Nonempty S.val := S.val_nonempty

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

-- We define a "preliminary" group action from `HomeoGroup α` to `AssociatedPosetSeed`
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

end AssociatedPoset.Prelude


/--
A partially-ordered set, associated to Rubin's proof.
Any element in that set is made up of a `seed`,
such that `val = AssociatedPosetElem seed` and `Set.Nonempty val`.

Actions on this set are first defined in terms of `AssociatedPosetSeed`,
as the proofs otherwise get hairy with a bunch of `Exists.choose` appearing.
--/
structure AssociatedPoset (α : Type _) [TopologicalSpace α] where
  val : Set α
  val_has_seed : ∃ po_seed : AssociatedPosetSeed α, po_seed.val = val

namespace AssociatedPoset

variable {α : Type _}
variable [TopologicalSpace α]
variable [DecidableEq α]

theorem eq_iff_val_eq (S T : AssociatedPoset α) : S = T ↔ S.val = T.val := by
  rw [mk.injEq]

def fromSeed (seed : AssociatedPosetSeed α) : AssociatedPoset α := ⟨
  seed.val,
  ⟨seed, seed.val_def⟩
⟩

noncomputable def full_seed (S : AssociatedPoset α) : AssociatedPosetSeed α :=
  (Exists.choose S.val_has_seed)

noncomputable def seed (S : AssociatedPoset α) : Finset (HomeoGroup α) :=
  S.full_seed.seed

@[simp]
theorem full_seed_seed (S : AssociatedPoset α) : S.full_seed.seed = S.seed := rfl

@[simp]
theorem fromSeed_val (seed : AssociatedPosetSeed α) :
  (fromSeed seed).val = seed.val :=
by
  unfold fromSeed
  simp

@[simp]
theorem val_from_seed (S : AssociatedPoset α) : AssociatedPosetElem S.seed = S.val := by
  unfold seed full_seed
  rw [<-AssociatedPosetSeed.val_def]
  rw [Exists.choose_spec S.val_has_seed]

@[simp]
theorem val_from_seed₂ (S : AssociatedPoset α) : S.full_seed.val = S.val := by
  unfold full_seed
  rw [AssociatedPosetSeed.val_def]
  nth_rw 2 [<-val_from_seed]
  unfold seed full_seed
  rfl

-- Allows one to prove properties of AssociatedPoset without jumping through `Exists.choose`-shaped hoops
theorem prop_from_val {p : Set α → Prop}
  (any_seed : ∀ po_seed : AssociatedPosetSeed α, p po_seed.val) :
  ∀ (S : AssociatedPoset α), p S.val :=
by
  intro S
  rw [<-val_from_seed]
  have res := any_seed S.full_seed
  rw [val_from_seed₂] at res
  rw [val_from_seed]
  exact res

@[simp]
theorem nonempty : ∀ (S : AssociatedPoset α), Set.Nonempty S.val :=
  prop_from_val AssociatedPosetSeed.nonempty

@[simp]
theorem regular : ∀ (S : AssociatedPoset α), Regular S.val :=
  prop_from_val AssociatedPosetSeed.regular

variable [DecidableEq (HomeoGroup α)]

instance homeoGroup_smul₃ : SMul (HomeoGroup α) (AssociatedPoset α) where
  smul := fun f S => ⟨
    f •'' S.val,
    by
      use f • S.full_seed
      rw [AssociatedPosetSeed.smul_val']
      simp
  ⟩

theorem smul_val (f : HomeoGroup α) (S : AssociatedPoset α) :
  (f • S).val = f •'' S.val := rfl

theorem smul_seed' (f : HomeoGroup α) (S : AssociatedPoset α) (seed : Finset (HomeoGroup α)) :
  S.val = AssociatedPosetElem seed →
  (f • S).val = AssociatedPosetElem (Finset.image (fun g => f * g * f⁻¹) seed) :=
by
  intro S_val_eq
  rw [smul_val]
  rw [AssociatedPosetElem.mul_seed]
  rw [S_val_eq]

theorem smul_seed (f : HomeoGroup α) (S : AssociatedPoset α) :
  (f • S).val = AssociatedPosetElem (Finset.image (fun g => f * g * f⁻¹) S.seed) :=
by
  apply smul_seed'
  symm
  exact val_from_seed S

-- Note: we could potentially implement MulActionHom
instance homeoGroup_mulAction₃ : MulAction (HomeoGroup α) (AssociatedPoset α) where
  one_smul := by
    intro S
    rw [eq_iff_val_eq]
    repeat rw [smul_val]
    rw [one_smulImage]
  mul_smul := by
    intro S f g
    rw [eq_iff_val_eq]
    repeat rw [smul_val]
    rw [smulImage_mul]

instance associatedPoset_le : LE (AssociatedPoset α) where
  le := fun S T => S.val ⊆ T.val

theorem le_def (S T : AssociatedPoset α) : S ≤ T ↔ S.val ⊆ T.val := by
  rw [iff_eq_eq]
  rfl

instance associatedPoset_partialOrder : PartialOrder (AssociatedPoset α) where
  le_refl := fun S => (le_def S S).mpr (le_refl S.val)
  le_trans := fun S T U S_le_T S_le_U => (le_def S U).mpr (le_trans
    ((le_def _ _).mp S_le_T)
    ((le_def _ _).mp S_le_U)
  )
  le_antisymm := by
    intro S T S_le_T T_le_S
    rw [le_def] at S_le_T
    rw [le_def] at T_le_S
    rw [eq_iff_val_eq]
    apply le_antisymm <;> assumption

theorem smul_mono {S T : AssociatedPoset α} (f : HomeoGroup α) (S_le_T : S ≤ T) :
  f • S ≤ f • T :=
by
  rw [le_def]
  repeat rw [smul_val]
  apply smulImage_mono
  assumption

instance associatedPoset_coeSet : Coe (AssociatedPoset α) (Set α) where
  coe := AssociatedPoset.val

def asSet (α : Type _) [TopologicalSpace α]: Set (Set α) :=
  { S : Set α | ∃ T : AssociatedPoset α, T.val = S }

theorem asSet_def :
  AssociatedPoset.asSet α = { S : Set α | ∃ T : AssociatedPoset α, T.val = S } := rfl

theorem mem_asSet (S : Set α) :
  S ∈ AssociatedPoset.asSet α ↔ ∃ T : AssociatedPoset α, T.val = S :=
by
  rw [asSet_def]
  simp

theorem mem_asSet' (S : Set α) :
  S ∈ AssociatedPoset.asSet α ↔ Set.Nonempty S ∧ ∃ seed : Finset (HomeoGroup α), S = AssociatedPosetElem seed :=
by
  rw [asSet_def]
  simp
  constructor
  · intro ⟨T, T_eq⟩
    rw [<-T_eq]
    constructor
    simp

    let ⟨⟨seed, _⟩, eq⟩ := T.val_has_seed
    rw [AssociatedPosetSeed.val_def] at eq
    simp at eq
    use seed
    exact eq.symm
  · intro ⟨S_nonempty, ⟨seed, val_from_seed⟩⟩
    rw [val_from_seed] at S_nonempty
    use fromSeed ⟨seed, S_nonempty⟩
    rw [val_from_seed]
    simp
    rw [AssociatedPosetSeed.val_def]

end AssociatedPoset

section Other

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

end Other

end Rubin
