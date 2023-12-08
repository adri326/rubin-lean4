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

section RegularSupportBasis.Prelude

variable {α : Type _}
variable [TopologicalSpace α]
variable [DecidableEq α]

/--
Maps a "seed" of homeorphisms in α to the intersection of their regular support in α.

Note that the condition that the resulting set is non-empty is introduced later in `RegularSupportBasis₀`
--/
def RegularSupportInter₀ (S : Finset (HomeoGroup α)): Set α :=
  ⋂ (g ∈ S), RegularSupport α g

theorem RegularSupportInter₀.eq_sInter (S : Finset (HomeoGroup α)) :
  RegularSupportInter₀ S = ⋂₀ ((fun (g : HomeoGroup α) => RegularSupport α g) '' S) :=
by
  rw [Set.sInter_image]
  rfl

/--
This is a predecessor type to `RegularSupportBasis`, where equality is defined on the `seed` used, rather than the `val`.
--/
structure RegularSupportBasis₀ (α : Type _) [TopologicalSpace α] where
  seed : Finset (HomeoGroup α)
  val_nonempty : Set.Nonempty (RegularSupportInter₀ seed)

theorem RegularSupportBasis₀.eq_iff_seed_eq (S T : RegularSupportBasis₀ α) : S = T ↔ S.seed = T.seed := by
  -- Spooky :3c
  rw [mk.injEq]

def RegularSupportBasis₀.val (S : RegularSupportBasis₀ α) : Set α := RegularSupportInter₀ S.seed

theorem RegularSupportBasis₀.val_def (S : RegularSupportBasis₀ α) : S.val = RegularSupportInter₀ S.seed := rfl

@[simp]
theorem RegularSupportBasis₀.nonempty (S : RegularSupportBasis₀ α) : Set.Nonempty S.val := S.val_nonempty

@[simp]
theorem RegularSupportBasis₀.regular (S : RegularSupportBasis₀ α) : Regular S.val := by
  rw [S.val_def]
  rw [RegularSupportInter₀.eq_sInter]

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

lemma RegularSupportInter₀.mul_seed (seed : Finset (HomeoGroup α)) [DecidableEq (HomeoGroup α)] (f : HomeoGroup α):
  RegularSupportInter₀ (Finset.image (fun g => f * g * f⁻¹) seed) = f •'' RegularSupportInter₀ seed :=
by
  unfold RegularSupportInter₀
  simp
  conv => {
    rhs
    ext; lhs; ext x; ext; lhs
    ext
    rw [regularSupport_smulImage]
  }

variable [DecidableEq (HomeoGroup α)]

/--
A `HomeoGroup α` group element `f` acts on an `RegularSupportBasis₀ α` set `S`,
by mapping each element `g` of `S.seed` to `f * g * f⁻¹`
--/
instance homeoGroup_smul₂ : SMul (HomeoGroup α) (RegularSupportBasis₀ α) where
  smul := fun f S => ⟨
    (Finset.image (fun g => f * g * f⁻¹) S.seed),
    by
      rw [RegularSupportInter₀.mul_seed]
      simp
      exact S.val_nonempty
  ⟩

theorem RegularSupportBasis₀.smul_seed (f : HomeoGroup α) (S : RegularSupportBasis₀ α) :
  (f • S).seed = (Finset.image (fun g => f * g * f⁻¹) S.seed) := rfl

theorem RegularSupportBasis₀.smul_val (f : HomeoGroup α) (S : RegularSupportBasis₀ α) :
  (f • S).val = RegularSupportInter₀ (Finset.image (fun g => f * g * f⁻¹) S.seed) := rfl

theorem RegularSupportBasis₀.smul_val' (f : HomeoGroup α) (S : RegularSupportBasis₀ α) :
  (f • S).val = f •'' S.val :=
by
  unfold val
  rw [<-RegularSupportInter₀.mul_seed]
  rw [RegularSupportBasis₀.smul_seed]

-- We define a "preliminary" group action from `HomeoGroup α` to `RegularSupportBasis₀`
instance homeoGroup_mulAction₂ : MulAction (HomeoGroup α) (RegularSupportBasis₀ α) where
  one_smul := by
    intro S
    rw [RegularSupportBasis₀.eq_iff_seed_eq]
    rw [RegularSupportBasis₀.smul_seed]
    simp
  mul_smul := by
    intro f g S
    rw [RegularSupportBasis₀.eq_iff_seed_eq]
    repeat rw [RegularSupportBasis₀.smul_seed]
    rw [Finset.image_image]
    ext x
    simp
    group

end RegularSupportBasis.Prelude


/--
A partially-ordered set, associated to Rubin's proof.
Any element in that set is made up of a `seed`,
such that `val = RegularSupportInter₀ seed` and `Set.Nonempty val`.

Actions on this set are first defined in terms of `RegularSupportBasis₀`,
as the proofs otherwise get hairy with a bunch of `Exists.choose` appearing.
--/
structure RegularSupportBasis (α : Type _) [TopologicalSpace α] where
  val : Set α
  val_has_seed : ∃ po_seed : RegularSupportBasis₀ α, po_seed.val = val

namespace RegularSupportBasis

variable {α : Type _}
variable [TopologicalSpace α]
variable [DecidableEq α]

theorem eq_iff_val_eq (S T : RegularSupportBasis α) : S = T ↔ S.val = T.val := by
  rw [mk.injEq]

def fromSeed (seed : RegularSupportBasis₀ α) : RegularSupportBasis α := ⟨
  seed.val,
  ⟨seed, seed.val_def⟩
⟩

noncomputable def full_seed (S : RegularSupportBasis α) : RegularSupportBasis₀ α :=
  (Exists.choose S.val_has_seed)

noncomputable def seed (S : RegularSupportBasis α) : Finset (HomeoGroup α) :=
  S.full_seed.seed

@[simp]
theorem full_seed_seed (S : RegularSupportBasis α) : S.full_seed.seed = S.seed := rfl

@[simp]
theorem fromSeed_val (seed : RegularSupportBasis₀ α) :
  (fromSeed seed).val = seed.val :=
by
  unfold fromSeed
  simp

@[simp]
theorem val_from_seed (S : RegularSupportBasis α) : RegularSupportInter₀ S.seed = S.val := by
  unfold seed full_seed
  rw [<-RegularSupportBasis₀.val_def]
  rw [Exists.choose_spec S.val_has_seed]

@[simp]
theorem val_from_seed₂ (S : RegularSupportBasis α) : S.full_seed.val = S.val := by
  unfold full_seed
  rw [RegularSupportBasis₀.val_def]
  nth_rw 2 [<-val_from_seed]
  unfold seed full_seed
  rfl

-- Allows one to prove properties of RegularSupportBasis without jumping through `Exists.choose`-shaped hoops
theorem prop_from_val {p : Set α → Prop}
  (any_seed : ∀ po_seed : RegularSupportBasis₀ α, p po_seed.val) :
  ∀ (S : RegularSupportBasis α), p S.val :=
by
  intro S
  rw [<-val_from_seed]
  have res := any_seed S.full_seed
  rw [val_from_seed₂] at res
  rw [val_from_seed]
  exact res

@[simp]
theorem nonempty : ∀ (S : RegularSupportBasis α), Set.Nonempty S.val :=
  prop_from_val RegularSupportBasis₀.nonempty

@[simp]
theorem regular : ∀ (S : RegularSupportBasis α), Regular S.val :=
  prop_from_val RegularSupportBasis₀.regular

variable [DecidableEq (HomeoGroup α)]

instance homeoGroup_smul₃ : SMul (HomeoGroup α) (RegularSupportBasis α) where
  smul := fun f S => ⟨
    f •'' S.val,
    by
      use f • S.full_seed
      rw [RegularSupportBasis₀.smul_val']
      simp
  ⟩

theorem smul_val (f : HomeoGroup α) (S : RegularSupportBasis α) :
  (f • S).val = f •'' S.val := rfl

theorem smul_seed' (f : HomeoGroup α) (S : RegularSupportBasis α) (seed : Finset (HomeoGroup α)) :
  S.val = RegularSupportInter₀ seed →
  (f • S).val = RegularSupportInter₀ (Finset.image (fun g => f * g * f⁻¹) seed) :=
by
  intro S_val_eq
  rw [smul_val]
  rw [RegularSupportInter₀.mul_seed]
  rw [S_val_eq]

theorem smul_seed (f : HomeoGroup α) (S : RegularSupportBasis α) :
  (f • S).val = RegularSupportInter₀ (Finset.image (fun g => f * g * f⁻¹) S.seed) :=
by
  apply smul_seed'
  symm
  exact val_from_seed S

-- Note: we could potentially implement MulActionHom
instance homeoGroup_mulAction₃ : MulAction (HomeoGroup α) (RegularSupportBasis α) where
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

instance associatedPoset_le : LE (RegularSupportBasis α) where
  le := fun S T => S.val ⊆ T.val

theorem le_def (S T : RegularSupportBasis α) : S ≤ T ↔ S.val ⊆ T.val := by
  rw [iff_eq_eq]
  rfl

instance associatedPoset_partialOrder : PartialOrder (RegularSupportBasis α) where
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

theorem smul_mono {S T : RegularSupportBasis α} (f : HomeoGroup α) (S_le_T : S ≤ T) :
  f • S ≤ f • T :=
by
  rw [le_def]
  repeat rw [smul_val]
  apply smulImage_mono
  assumption

instance associatedPoset_coeSet : Coe (RegularSupportBasis α) (Set α) where
  coe := RegularSupportBasis.val

def asSet (α : Type _) [TopologicalSpace α]: Set (Set α) :=
  { S : Set α | ∃ T : RegularSupportBasis α, T.val = S }

theorem asSet_def :
  RegularSupportBasis.asSet α = { S : Set α | ∃ T : RegularSupportBasis α, T.val = S } := rfl

theorem mem_asSet (S : Set α) :
  S ∈ RegularSupportBasis.asSet α ↔ ∃ T : RegularSupportBasis α, T.val = S :=
by
  rw [asSet_def]
  simp

theorem mem_asSet' (S : Set α) :
  S ∈ RegularSupportBasis.asSet α ↔ Set.Nonempty S ∧ ∃ seed : Finset (HomeoGroup α), S = RegularSupportInter₀ seed :=
by
  rw [asSet_def]
  simp
  constructor
  · intro ⟨T, T_eq⟩
    rw [<-T_eq]
    constructor
    simp

    let ⟨⟨seed, _⟩, eq⟩ := T.val_has_seed
    rw [RegularSupportBasis₀.val_def] at eq
    simp at eq
    use seed
    exact eq.symm
  · intro ⟨S_nonempty, ⟨seed, val_from_seed⟩⟩
    rw [val_from_seed] at S_nonempty
    use fromSeed ⟨seed, S_nonempty⟩
    rw [val_from_seed]
    simp
    rw [RegularSupportBasis₀.val_def]

instance membership : Membership α (RegularSupportBasis α) where
  mem := fun x S => x ∈ S.val

theorem mem_iff (x : α) (S : RegularSupportBasis α) : x ∈ S ↔ x ∈ (S : Set α) := iff_eq_eq ▸ rfl

section Basis
open Topology

-- TODO: clean this lemma to not mention W anymore?
lemma proposition_3_2_subset (G : Type _) {α : Type _} [Group G] [TopologicalSpace α] [MulAction G α]
  [T2Space α] [LocallyCompactSpace α] [h_ld : LocallyDense G α] [HasNoIsolatedPoints α]
  [ContinuousMulAction G α]
  {U : Set α} (U_open : IsOpen U) {p : α} (p_in_U : p ∈ U) :
  ∃ (W : Set α), W ∈ 𝓝 p ∧ closure W ⊆ U ∧
  ∃ (g : G), g ∈ RigidStabilizer G W ∧ p ∈ RegularSupport α g ∧ RegularSupport α g ⊆ closure W :=
by
  have U_in_nhds : U ∈ 𝓝 p := by
    rw [mem_nhds_iff]
    use U

  let ⟨W', W'_in_nhds, W'_ss_U, W'_compact⟩ := local_compact_nhds U_in_nhds

  -- This feels like black magic, but okay
  let ⟨W, _W_compact, W_closed, W'_ss_int_W, W_ss_U⟩ := exists_compact_closed_between W'_compact U_open W'_ss_U
  have W_cl_eq_W : closure W = W := IsClosed.closure_eq W_closed

  have W_in_nhds : W ∈ 𝓝 p := by
    rw [mem_nhds_iff]
    use interior W
    repeat' apply And.intro
    · exact interior_subset
    · simp
    · exact W'_ss_int_W (mem_of_mem_nhds W'_in_nhds)

  use W

  repeat' apply And.intro
  exact W_in_nhds
  {
    rw [W_cl_eq_W]
    exact W_ss_U
  }

  have p_in_int_W : p ∈ interior W := W'_ss_int_W (mem_of_mem_nhds W'_in_nhds)

  let ⟨g, g_in_rist, g_moves_p⟩ := get_moving_elem_in_rigidStabilizer G isOpen_interior p_in_int_W

  use g
  repeat' apply And.intro
  · apply rigidStabilizer_mono interior_subset
    simp
    exact g_in_rist
  · rw [<-mem_support] at g_moves_p
    apply support_subset_regularSupport
    exact g_moves_p
  · rw [rigidStabilizer_support] at g_in_rist
    apply subset_trans
    exact regularSupport_subset_closure_support
    apply closure_mono
    apply subset_trans
    exact g_in_rist
    exact interior_subset

/--
## Proposition 3.2 : RegularSupportBasis is a topological basis of `α`
-/
theorem isBasis (G α : Type _) [Group G] [TopologicalSpace α] [MulAction G α]
  [T2Space α] [LocallyCompactSpace α] [h_ld : LocallyDense G α] [HasNoIsolatedPoints α]
  [hc : ContinuousMulAction G α] :
  TopologicalSpace.IsTopologicalBasis (RegularSupportBasis.asSet α) :=
by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  {
    intro U U_in_poset
    rw [RegularSupportBasis.mem_asSet] at U_in_poset
    let ⟨T, T_val⟩ := U_in_poset
    rw [<-T_val]
    exact T.regular.isOpen
  }
  intro p U p_in_U U_open

  let ⟨W, _, clW_ss_U, ⟨g, _, p_in_rsupp, rsupp_ss_clW⟩⟩ := proposition_3_2_subset G U_open p_in_U
  use RegularSupport α g
  repeat' apply And.intro
  · rw [RegularSupportBasis.mem_asSet']
    constructor
    exact ⟨p, p_in_rsupp⟩
    use {(ContinuousMulAction.toHomeomorph α g : HomeoGroup α)}
    unfold RegularSupportInter₀
    simp
    unfold RegularSupport
    rw [<-homeoGroup_support_eq_support_toHomeomorph g]
  · exact p_in_rsupp
  · apply subset_trans
    exact rsupp_ss_clW
    exact clW_ss_U

end Basis
end RegularSupportBasis

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

end Other

end Rubin
