/-
This file describes [`RigidStabilizerBasis`], which are all non-trivial subgroups of `G` constructed
by finite intersections of `RigidStabilizer G (RegularSupport α g)`.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph

import Rubin.RegularSupport
import Rubin.RigidStabilizer

namespace Rubin

variable {G α : Type _}
variable [Group G]
variable [MulAction G α]
variable [TopologicalSpace α]

/--
Finite intersections of rigid stabilizers of regular supports
(which are equivalent to the rigid stabilizers of finite intersections of regular supports).
-/
def RigidStabilizerInter₀ {G: Type _} (α : Type _) [Group G] [MulAction G α] [TopologicalSpace α]
  (S : Finset G) : Subgroup G :=
  ⨅ (g ∈ S), RigidStabilizer G (RegularSupport α g)

theorem RigidStabilizerInter₀.eq_sInter (S : Finset G) :
  RigidStabilizerInter₀ α S = RigidStabilizer G (⋂ g ∈ S, (RegularSupport α g)) :=
by
  have img_eq : ⋂ g ∈ S, RegularSupport α g = ⋂₀ ((fun g : G => RegularSupport α g) '' S) :=
    by simp only [Set.sInter_image, Finset.mem_coe]

  rw [img_eq]
  rw [rigidStabilizer_sInter]
  unfold RigidStabilizerInter₀

  ext x
  repeat rw [Subgroup.mem_iInf]
  constructor
  · intro H T
    rw [Subgroup.mem_iInf]
    intro T_in_img
    simp at T_in_img
    let ⟨g, ⟨g_in_S, T_eq⟩⟩ := T_in_img
    specialize H g
    rw [Subgroup.mem_iInf] at H
    rw [<-T_eq]
    apply H; assumption
  · intro H g
    rw [Subgroup.mem_iInf]
    intro g_in_S
    specialize H (RegularSupport α g)
    rw [Subgroup.mem_iInf] at H
    simp at H
    apply H g <;> tauto

/--
A predecessor structure to [`RigidStabilizerBasis`], where equality is defined on the choice of
group elements who regular support's rigid stabilizer get intersected upon.
--/
structure RigidStabilizerBasis₀ (G α : Type _) [Group G] [MulAction G α] [TopologicalSpace α] where
  seed : Finset G
  val_ne_bot : RigidStabilizerInter₀ α seed ≠ ⊥

def RigidStabilizerBasis₀.val (B : RigidStabilizerBasis₀ G α) : Subgroup G :=
  RigidStabilizerInter₀ α B.seed

theorem RigidStabilizerBasis₀.val_def (B : RigidStabilizerBasis₀ G α) : B.val = RigidStabilizerInter₀ α B.seed := rfl

/--
The set of all non-trivial subgroups of `G` constructed
by finite intersections of `RigidStabilizer G (RegularSupport α g)`.
--/
def RigidStabilizerBasis (G α : Type _) [Group G] [MulAction G α] [TopologicalSpace α] : Set (Subgroup G) :=
  { H.val | H : RigidStabilizerBasis₀ G α }

theorem RigidStabilizerBasis.mem_iff (H : Subgroup G) :
  H ∈ RigidStabilizerBasis G α ↔ ∃ B : RigidStabilizerBasis₀ G α, B.val = H := by rfl

theorem RigidStabilizerBasis.mem_iff' (H : Subgroup G)
  (H_ne_bot : H ≠ ⊥) :
  H ∈ RigidStabilizerBasis G α ↔ ∃ seed : Finset G, RigidStabilizerInter₀ α seed = H :=
by
  rw [mem_iff]
  constructor
  · intro ⟨B, B_eq⟩
    use B.seed
    rw [RigidStabilizerBasis₀.val_def] at B_eq
    exact B_eq
  · intro ⟨seed, seed_eq⟩
    let B := RigidStabilizerInter₀ α seed
    have val_ne_bot : B ≠ ⊥ := by
      unfold_let
      rw [seed_eq]
      exact H_ne_bot
    use ⟨seed, val_ne_bot⟩
    rw [<-seed_eq]
    rfl

def RigidStabilizerBasis.asSets (G α : Type _) [Group G] [MulAction G α] [TopologicalSpace α] : Set (Set G) :=
  { (H.val : Set G) | H : RigidStabilizerBasis₀ G α }

theorem RigidStabilizerBasis.mem_asSets_iff (S : Set G) :
  S ∈ RigidStabilizerBasis.asSets G α ↔ ∃ H ∈ RigidStabilizerBasis G α, H.carrier = S :=
by
  unfold asSets RigidStabilizerBasis
  simp
  rfl

theorem RigidStabilizerBasis.mem_iff_asSets (H : Subgroup G) :
  H ∈ RigidStabilizerBasis G α ↔ (H : Set G) ∈ RigidStabilizerBasis.asSets G α :=
by
  unfold asSets RigidStabilizerBasis
  simp

variable [ContinuousMulAction G α]

lemma RigidStabilizerBasis.smulImage_mem₀ {H : Subgroup G} (H_in_ristBasis : H ∈ RigidStabilizerBasis G α)
  (f : G) : ((fun g => f * g * f⁻¹) '' H.carrier) ∈ RigidStabilizerBasis.asSets G α :=
by
  have G_decidable : DecidableEq G := Classical.decEq _
  rw [mem_iff] at H_in_ristBasis
  let ⟨seed, H_eq⟩ := H_in_ristBasis
  rw [mem_asSets_iff]

  let new_seed := Finset.image (fun g => f * g * f⁻¹) seed.seed
  have new_seed_ne_bot : RigidStabilizerInter₀ α new_seed ≠ ⊥ := by
    rw [RigidStabilizerInter₀.eq_sInter]
    unfold_let
    simp [<-regularSupport_smulImage]
    rw [<-ne_eq]
    rw [<-smulImage_iInter_fin]

    have val_ne_bot := seed.val_ne_bot
    rw [Subgroup.ne_bot_iff_exists_ne_one] at val_ne_bot
    let ⟨⟨g, g_in_ristInter⟩, g_ne_one⟩ := val_ne_bot
    simp at g_ne_one

    have fgf_in_ristInter₂ : f * g * f⁻¹ ∈ RigidStabilizer G (f •'' ⋂ x ∈ seed.seed, RegularSupport α x) := by
      rw [rigidStabilizer_smulImage]
      group
      rw [RigidStabilizerInter₀.eq_sInter] at g_in_ristInter
      exact g_in_ristInter

    have fgf_ne_one : f * g * f⁻¹ ≠ 1 := by
      intro h₁
      have h₂ := congr_arg (fun x => x * f) h₁
      group at h₂
      have h₃ := congr_arg (fun x => f⁻¹ * x) h₂
      group at h₃
      exact g_ne_one h₃


    rw [Subgroup.ne_bot_iff_exists_ne_one]
    use ⟨f * g * f⁻¹, fgf_in_ristInter₂⟩
    simp
    rw [<-ne_eq]
    exact fgf_ne_one

  use RigidStabilizerInter₀ α new_seed
  apply And.intro
  exact ⟨⟨new_seed, new_seed_ne_bot⟩, rfl⟩
  rw [RigidStabilizerInter₀.eq_sInter]
  unfold_let
  simp [<-regularSupport_smulImage]
  rw [<-smulImage_iInter_fin]

  ext x
  simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
    Subgroup.mem_toSubmonoid, Set.mem_image]
  rw [rigidStabilizer_smulImage]
  rw [<-H_eq, RigidStabilizerBasis₀.val_def, RigidStabilizerInter₀.eq_sInter]

  constructor
  · intro fxf_mem
    use f⁻¹ * x * f
    constructor
    · exact fxf_mem
    · group
  · intro ⟨y, ⟨y_in_H, y_conj⟩⟩
    rw [<-y_conj]
    group
    exact y_in_H

def RigidStabilizerBasisMul (G α : Type _) [Group G] [MulAction G α] [TopologicalSpace α]
  [ContinuousMulAction G α] (f : G) (H : Subgroup G)
  : Subgroup G
where
  carrier := (fun g => f * g * f⁻¹) '' H.carrier
  mul_mem' := by
    intro a b a_mem b_mem
    simp at a_mem
    simp at b_mem
    let ⟨a', a'_in_H, a'_eq⟩ := a_mem
    let ⟨b', b'_in_H, b'_eq⟩ := b_mem
    use a' * b'
    constructor
    · apply Subsemigroup.mul_mem' <;> simp <;> assumption
    · simp
      rw [<-a'_eq, <-b'_eq]
      group
  one_mem' := by
    simp
    use 1
    constructor
    exact Subgroup.one_mem H
    group
  inv_mem' := by
    simp
    intro g g_in_H
    use g⁻¹
    constructor
    exact Subgroup.inv_mem H g_in_H
    rw [mul_assoc]

theorem RigidStabilizerBasisMul_mem (f : G) {H : Subgroup G} (H_in_basis : H ∈ RigidStabilizerBasis G α)
  : RigidStabilizerBasisMul G α f H ∈ RigidStabilizerBasis G α :=
by
  rw [RigidStabilizerBasis.mem_iff_asSets]
  unfold RigidStabilizerBasisMul
  simp

  apply RigidStabilizerBasis.smulImage_mem₀
  assumption

instance rigidStabilizerBasis_smul : SMul G (RigidStabilizerBasis G α) where
  smul := fun g H => ⟨
    RigidStabilizerBasisMul G α g H.val,
    RigidStabilizerBasisMul_mem g H.prop
  ⟩

theorem RigidStabilizerBasis.smul_eq (g : G) {H: Subgroup G} (H_in_basis : H ∈ RigidStabilizerBasis G α) :
  g • (⟨H, H_in_basis⟩ : RigidStabilizerBasis G α) = ⟨
    RigidStabilizerBasisMul G α g H,
    RigidStabilizerBasisMul_mem g H_in_basis
  ⟩ := rfl

theorem RigidStabilizerBasis.mem_smul (f g : G) {H: Subgroup G} (H_in_basis : H ∈ RigidStabilizerBasis G α):
  f ∈ (g • (⟨H, H_in_basis⟩ : RigidStabilizerBasis G α)).val ↔ g⁻¹ * f * g ∈ H :=
by
  rw [RigidStabilizerBasis.smul_eq]
  simp
  rw [<-Subgroup.mem_carrier]
  unfold RigidStabilizerBasisMul
  simp
  constructor
  · intro ⟨x, x_in_H, f_eq⟩
    rw [<-f_eq]
    group
    exact x_in_H
  · intro gfg_in_H
    use g⁻¹ * f * g
    constructor
    assumption
    group

instance rigidStabilizerBasis_mulAction : MulAction G (RigidStabilizerBasis G α) where
  one_smul := by
    intro ⟨H, H_in_ristBasis⟩
    ext x
    rw [RigidStabilizerBasis.mem_smul]
    group
  mul_smul := by
    intro f g ⟨B, B_in_ristBasis⟩
    ext x
    repeat rw [RigidStabilizerBasis.mem_smul]
    group

end Rubin
