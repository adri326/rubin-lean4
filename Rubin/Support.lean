import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic

import Rubin.MulActionExt
import Rubin.SmulImage
import Rubin.Tactic

namespace Rubin

/--
The support of a group action of `g: G` on `α` (here generalized to `SMul G α`)
is the set of values `x` in `α` for which `g • x ≠ x`.

This can also be thought of as the complement of the fixpoints of `(g •)`,
which [`support_eq_not_fixed_by`] provides.
--/
def Support {G : Type _} (α : Type _) [SMul G α] (g : G) :=
  {x : α | g • x ≠ x}
#align support Rubin.Support

theorem SmulSupport_def {G : Type _} (α : Type _) [SMul G α] {g : G} :
  Support α g = {x : α | g • x ≠ x} := by tauto

variable {G α: Type _}
variable [Group G]
variable [MulAction G α]
variable {f g : G}
variable {x : α}

theorem support_eq_not_fixed_by : Support α g = (MulAction.fixedBy α g)ᶜ := by tauto
#align support_eq_not_fixed_by Rubin.support_eq_not_fixed_by

theorem support_compl_eq_fixed_by : (Support α g)ᶜ = MulAction.fixedBy α g := by
  rw [<-compl_compl (MulAction.fixedBy _ _)]
  exact congr_arg (·ᶜ) support_eq_not_fixed_by

theorem mem_support :
    x ∈ Support α g ↔ g • x ≠ x := by tauto
#align mem_support Rubin.mem_support

theorem not_mem_support :
    x ∉ Support α g ↔ g • x = x := by
  rw [Rubin.mem_support, Classical.not_not]
#align mem_not_support Rubin.not_mem_support

theorem smul_mem_support :
    x ∈ Support α g → g • x ∈ Support α g := fun h =>
  h ∘ smul_left_cancel g
#align smul_in_support Rubin.smul_mem_support

theorem inv_smul_mem_support :
    x ∈ Support α g → g⁻¹ • x ∈ Support α g := fun h k =>
  h (smul_inv_smul g x ▸ smul_congr g k)
#align inv_smul_in_support Rubin.inv_smul_mem_support

theorem fixed_of_disjoint {U : Set α} :
    x ∈ U → Disjoint U (Support α g) → g • x = x :=
  fun x_in_U disjoint_U_support =>
  not_mem_support.mp (Set.disjoint_left.mp disjoint_U_support x_in_U)
#align fixed_of_disjoint Rubin.fixed_of_disjoint

theorem fixed_smulImage_in_support (g : G) {U : Set α} :
    Support α g ⊆ U → g •'' U = U :=
  by
  intro support_in_U
  ext x
  cases' @or_not (x ∈ Support α g) with xmoved xfixed
  exact
    ⟨fun _ => support_in_U xmoved, fun _ =>
      mem_smulImage.mpr (support_in_U (Rubin.inv_smul_mem_support xmoved))⟩
  rw [Rubin.mem_smulImage, smul_eq_iff_inv_smul_eq.mp (not_mem_support.mp xfixed)]
#align fixes_subset_within_support Rubin.fixed_smulImage_in_support

theorem smulImage_subset_in_support (g : G) (U V : Set α) :
    U ⊆ V → Support α g ⊆ V → g •'' U ⊆ V := fun U_in_V support_in_V =>
  Rubin.fixed_smulImage_in_support g support_in_V ▸
    Rubin.smulImage_subset g U_in_V
#align moves_subset_within_support Rubin.smulImage_subset_in_support

theorem support_mul (g h : G) (α : Type _) [MulAction G α] :
    Support α (g * h) ⊆
      Support α g ∪ Support α h :=
  by
  intro x x_in_support
  by_contra h_support

  let res := not_or.mp h_support
  exact
    x_in_support
      ((mul_smul g h x).trans
        ((congr_arg (g • ·) (not_mem_support.mp res.2)).trans <| not_mem_support.mp res.1))
#align support_mul Rubin.support_mul

theorem support_conjugate (α : Type _) [MulAction G α] (g h : G) :
    Support α (h * g * h⁻¹) = h •'' Support α g :=
  by
  ext x
  rw [Rubin.mem_support, Rubin.mem_smulImage, Rubin.mem_support,
    mul_smul, mul_smul]
  constructor
  · intro h1; by_contra h2; exact h1 ((congr_arg (h • ·) h2).trans (smul_inv_smul _ _))
  · intro h1; by_contra h2; exact h1 (inv_smul_smul h (g • h⁻¹ • x) ▸ congr_arg (h⁻¹ • ·) h2)
#align support_conjugate Rubin.support_conjugate

theorem support_inv (α : Type _) [MulAction G α] (g : G) :
    Support α g⁻¹ = Support α g :=
  by
  ext x
  rw [Rubin.mem_support, Rubin.mem_support]
  constructor
  · intro h1; by_contra h2; exact h1 (smul_eq_iff_inv_smul_eq.mp h2)
  · intro h1; by_contra h2; exact h1 (smul_eq_iff_inv_smul_eq.mpr h2)
#align support_inv Rubin.support_inv

theorem support_pow (α : Type _) [MulAction G α] (g : G) (j : ℕ) :
    Support α (g ^ j) ⊆ Support α g :=
  by
  intro x xmoved
  by_contra xfixed
  rw [Rubin.mem_support] at xmoved
  induction j with
  | zero => apply xmoved; rw [pow_zero g, one_smul]
  | succ j j_ih =>
    apply xmoved
    let j_ih := (congr_arg (g • ·) (not_not.mp j_ih)).trans (not_mem_support.mp xfixed)
    simp at j_ih
    group_action at j_ih
    rw [<-Nat.one_add, <-zpow_ofNat, Int.ofNat_add]
    exact j_ih
    -- TODO: address this pain point
    -- Alternatively:
    -- rw [Int.add_comm, Int.ofNat_add_one_out, zpow_ofNat] at j_ih
    -- exact j_ih
#align support_pow Rubin.support_pow

theorem support_comm (α : Type _) [MulAction G α] (g h : G) :
    Support α ⁅g, h⁆ ⊆
      Support α h ∪ (g •'' Support α h) :=
  by
  intro x x_in_support
  by_contra all_fixed
  rw [Set.mem_union] at all_fixed
  cases' @or_not (h • x = x) with xfixed xmoved
  · rw [Rubin.mem_support, commutatorElement_def, mul_smul,
      smul_eq_iff_inv_smul_eq.mp xfixed, ← Rubin.mem_support] at x_in_support
    exact
      ((Rubin.support_conjugate α h g).symm ▸ (not_or.mp all_fixed).2)
        x_in_support
  · exact all_fixed (Or.inl xmoved)
#align support_comm Rubin.support_comm

theorem disjoint_support_comm (f g : G) {U : Set α} :
    Support α f ⊆ U → Disjoint U (g •'' U) → ∀ x ∈ U, ⁅f, g⁆ • x = f • x :=
  by
  intro support_in_U disjoint_U x x_in_U
  have support_conj : Support α (g * f⁻¹ * g⁻¹) ⊆ g •'' U :=
    ((Rubin.support_conjugate α f⁻¹ g).trans
          (Rubin.SmulImage.congr g (Rubin.support_inv α f))).symm ▸
      Rubin.smulImage_subset g support_in_U
  have goal :=
    (congr_arg (f • ·)
        (Rubin.fixed_of_disjoint x_in_U
          (Set.disjoint_of_subset_right support_conj disjoint_U))).symm
  simp at goal

  -- NOTE: the nth_rewrite must happen on the second occurence, or else group_action yields an incorrect f⁻²
  nth_rewrite 2 [goal]
  group_action
#align disjoint_support_comm Rubin.disjoint_support_comm


end Rubin
