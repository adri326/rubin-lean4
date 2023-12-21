import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Basic

import Rubin.MulActionExt
import Rubin.SmulImage
import Rubin.Tactic

namespace Rubin

/--
The support of a group action of `g: G` on `α` (here generalized to `SMul G α`)
is the set of values `x` in `α` for which `g • x ≠ x`.

This can also be thought of as the complement of the fixpoints of `(g •)`,
which [`support_eq_compl_fixedBy`] provides.
--/
-- TODO: rename to MulAction.support
def Support {G : Type _} (α : Type _) [SMul G α] (g : G) :=
  {x : α | g • x ≠ x}
#align support Rubin.Support

variable {G α: Type _}
variable [Group G]
variable [MulAction G α]
variable {f g : G}
variable {x : α}

theorem support_eq_compl_fixedBy : Support α g = (MulAction.fixedBy α g)ᶜ := by tauto
#align support_eq_not_fixed_by Rubin.support_eq_compl_fixedBy

theorem fixedBy_eq_compl_support : MulAction.fixedBy α g = (Support α g)ᶜ := by
  rw [<-compl_compl (MulAction.fixedBy _ _)]
  exact congr_arg (·ᶜ) support_eq_compl_fixedBy

theorem mem_support :
    x ∈ Support α g ↔ g • x ≠ x := by tauto
#align mem_support Rubin.mem_support

theorem not_mem_support :
    x ∉ Support α g ↔ g • x = x := by
  rw [Rubin.mem_support, Classical.not_not]
#align mem_not_support Rubin.not_mem_support

theorem support_one : Support α (1 : G) = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x
  rw [not_mem_support]
  simp

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

theorem support_zpow (α : Type _) [MulAction G α] (g : G) (j : ℤ) :
    Support α (g ^ j) ⊆ Support α g :=
by
  cases j with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zpow_coe_nat]
    exact support_pow α g n
  | negSucc n =>
    rw [Int.negSucc_eq, zpow_neg, support_inv, zpow_add, zpow_coe_nat, zpow_one]
    nth_rw 2 [<-pow_one g]
    rw [<-pow_add]
    exact support_pow α g (n+1)

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
  have support_conj : Support α (g * f⁻¹ * g⁻¹) ⊆ g •'' U := by
    rw [support_conjugate]
    apply smulImage_mono
    rw [support_inv]
    exact support_in_U
  have goal :=
    (congr_arg (f • ·)
        (Rubin.fixed_of_disjoint x_in_U
          (Set.disjoint_of_subset_right support_conj disjoint_U))).symm
  simp at goal

  -- NOTE: the nth_rewrite must happen on the second occurence, or else group_action yields an incorrect f⁻²
  nth_rewrite 2 [goal]
  group_action
#align disjoint_support_comm Rubin.disjoint_support_comm

lemma empty_of_subset_disjoint {α : Type _} {U V : Set α} :
  Disjoint U V → U ⊆ V → U = ∅ :=
by
  intro disj subset
  apply Set.eq_of_subset_of_subset <;> try simp
  intro x x_in_U
  simp
  apply disjoint_not_mem disj
  exact x_in_U
  exact subset x_in_U

theorem not_commute_of_disj_support_smulImage {G α : Type _}
  [Group G] [MulAction G α] [FaithfulSMul G α]
  {f g : G} {U : Set α} (f_ne_one : f ≠ 1)
  (subset : Support α f ⊆ U)
  (disj : Disjoint (Support α f) (g •'' U)) :
  ¬Commute f g :=
by
  intro h_comm
  have h₀ : ∀ x ∈ U, x ∉ Support α f := by
    intro x x_in_U
    unfold Commute SemiconjBy at h_comm
    have gx_in_img := (mem_smulImage' g).mpr x_in_U
    have h₁ : g • f • x = g • x := by
      have res := disjoint_not_mem₂ disj gx_in_img
      rw [not_mem_support] at res
      rw [<-mul_smul] at res
      rw [h_comm] at res
      rw [mul_smul] at res
      exact res
    have h₂ : f • x = x := by
      rw [<-one_smul G (f • x)]
      nth_rw 2 [<-one_smul G x]
      rw [<-mul_left_inv g]
      rw [mul_smul]
      rw [mul_smul]
      nth_rw 1 [h₁]
    rw [<-not_mem_support] at h₂
    exact h₂

  have h₀' : Disjoint (Support α f) U := by
    intro T; simp
    intro T_ss_supp T_ss_U
    intro x x_in_T
    apply h₀
    exact T_ss_U x_in_T
    exact T_ss_supp x_in_T

  have support_empty : Support α f = ∅ := empty_of_subset_disjoint h₀' subset

  apply f_ne_one
  apply smul_left_injective' (α := α)
  ext x
  simp
  by_contra h
  rw [<-ne_eq, <-mem_support] at h
  apply Set.eq_empty_iff_forall_not_mem.mp support_empty
  exact h

theorem support_eq: Support α f = Support α g ↔ ∀ (x : α), (f • x = x ∧ g • x = x) ∨ (f • x ≠ x ∧ g • x ≠ x) := by
  constructor
  · intro h
    intro x
    by_cases x_in? : x ∈ Support α f
    · right
      have gx_ne_x := by rw [h] at x_in?; exact x_in?
      exact ⟨x_in?, gx_ne_x⟩
    · left
      have fx_eq_x : f • x = x := by rw [<-not_mem_support]; exact x_in?
      have gx_eq_x : g • x = x := by rw [<-not_mem_support, <-h]; exact x_in?
      exact ⟨fx_eq_x, gx_eq_x⟩
  · intro h
    ext x
    constructor
    · intro fx_ne_x
      rw [mem_support] at fx_ne_x
      rw [mem_support]
      cases h x with
      | inl h₁ => exfalso; exact fx_ne_x h₁.left
      | inr h₁ => exact h₁.right
    · intro gx_ne_x
      rw [mem_support] at gx_ne_x
      rw [mem_support]
      cases h x with
      | inl h₁ => exfalso; exact gx_ne_x h₁.right
      | inr h₁ => exact h₁.left

theorem support_empty_iff (g : G) [h_f : FaithfulSMul G α] :
  Support α g = ∅ ↔ g = 1 :=
by
  constructor
  · intro supp_empty
    rw [Set.eq_empty_iff_forall_not_mem] at supp_empty
    apply h_f.eq_of_smul_eq_smul
    intro x
    specialize supp_empty x
    rw [not_mem_support] at supp_empty
    simp
    exact supp_empty
  · intro g_eq_1
    rw [g_eq_1]
    exact support_one

theorem support_nonempty_iff (g : G) [h_f : FaithfulSMul G α] :
  Set.Nonempty (Support α g) ↔ g ≠ 1 :=
by
  constructor
  · intro ⟨x, x_in_supp⟩
    by_contra g_eq_1
    rw [g_eq_1, support_one] at x_in_supp
    exact x_in_supp
  · intro g_ne_one
    by_contra supp_empty
    rw [Set.not_nonempty_iff_eq_empty] at supp_empty
    exact g_ne_one ((support_empty_iff _).mp supp_empty)

theorem elem_moved_in_support (g : G) (p : α) :
  p ∈ Support α g ↔ g • p ∈ Support α g :=
by
  suffices ∀ (g : G) (p : α), p ∈ Support α g → g • p ∈ Support α g by
    constructor
    exact this g p
    rw [<-support_inv]
    intro H
    rw [<-one_smul G p, <-mul_left_inv g, mul_smul]
    exact this _ _ H
  intro g p p_in_supp
  by_contra gp_notin_supp
  rw [<-support_inv, not_mem_support] at gp_notin_supp
  rw [mem_support] at p_in_supp
  apply p_in_supp
  symm at gp_notin_supp
  group_action at gp_notin_supp
  exact gp_notin_supp

theorem elem_moved_in_support' {g : G} (p : α) {U : Set α} (support_in_U : Support α g ⊆ U):
  p ∈ U ↔ g • p ∈ U :=
by
  by_cases p_in_supp? : p ∈ Support α g
  · constructor
    rw [elem_moved_in_support] at p_in_supp?
    all_goals intro; exact support_in_U p_in_supp?
  · rw [not_mem_support] at p_in_supp?
    rw [p_in_supp?]

theorem elem_moved_in_support_zpow {g : G} (p : α) (j : ℤ) {U : Set α} (support_in_U : Support α g ⊆ U):
  p ∈ U ↔ g^j • p ∈ U :=
by
  by_cases p_in_supp? : p ∈ Support α g
  · constructor
    all_goals intro; apply support_in_U
    swap; exact p_in_supp?
    rw [<-elem_moved_in_support' p (support_zpow α g j)]
    assumption
  · rw [not_mem_support] at p_in_supp?
    rw [smul_zpow_eq_of_smul_eq j p_in_supp?]

theorem orbit_subset_support (g : G) (p : α) :
  MulAction.orbit (Subgroup.closure {g}) p ⊆ Support α g ∪ {p} :=
by
  intro q q_in_orbit
  rw [MulAction.mem_orbit_iff] at q_in_orbit
  let ⟨⟨h, h_in_closure⟩, hp_eq_q⟩ := q_in_orbit
  simp at hp_eq_q
  rw [Subgroup.mem_closure_singleton] at h_in_closure
  let ⟨n, g_pow_n_eq_h⟩ := h_in_closure
  rw [<-hp_eq_q, <-g_pow_n_eq_h]
  clear hp_eq_q g_pow_n_eq_h h_in_closure

  have union_superset : Support α g ⊆ Support α g ∪ {p} := by
    simp only [Set.union_singleton, Set.subset_insert]
  rw [<-elem_moved_in_support_zpow _ _ union_superset]
  simp only [Set.union_singleton, Set.mem_insert_iff, true_or]

theorem orbit_subset_of_support_subset (g : G) {p : α} {U : Set α} (p_in_U : p ∈ U)
  (supp_ss_U : Support α g ⊆ U) :
  MulAction.orbit (Subgroup.closure {g}) p ⊆ U :=
by
  apply subset_trans
  exact orbit_subset_support g p
  apply Set.union_subset
  assumption
  rw [Set.singleton_subset_iff]
  assumption

theorem fixed_smulImage_in_support (g : G) {U : Set α} :
  Support α g ⊆ U → g •'' U = U :=
by
  intro support_in_U
  ext x
  rw [mem_smulImage]
  symm
  apply elem_moved_in_support'
  rw [support_inv]
  assumption
#align fixes_subset_within_support Rubin.fixed_smulImage_in_support

theorem smulImage_subset_in_support (g : G) (U V : Set α) :
    U ⊆ V → Support α g ⊆ V → g •'' U ⊆ V := fun U_in_V support_in_V =>
  Rubin.fixed_smulImage_in_support g support_in_V ▸
    smulImage_mono g U_in_V
#align moves_subset_within_support Rubin.smulImage_subset_in_support


section Continuous

variable {G α : Type _}
variable [Group G]
variable [TopologicalSpace α]
variable [MulAction G α]
variable [ContinuousMulAction G α]

theorem img_open_open (g : G) (U : Set α) (h : IsOpen U): IsOpen (g •'' U) :=
  by
  rw [Rubin.smulImage_eq_inv_preimage]
  exact Continuous.isOpen_preimage (Rubin.ContinuousMulAction.continuous g⁻¹) U h

#align img_open_open Rubin.img_open_open

theorem support_open (g : G) [T2Space α]: IsOpen (Support α g) :=
  by
  apply isOpen_iff_forall_mem_open.mpr
  intro x xmoved
  rcases T2Space.t2 (g • x) x xmoved with ⟨U, V, open_U, open_V, gx_in_U, x_in_V, disjoint_U_V⟩
  exact
    ⟨V ∩ (g⁻¹ •'' U), fun y yW =>
      Disjoint.ne_of_mem
        disjoint_U_V
        (mem_inv_smulImage.mp (Set.mem_of_mem_inter_right yW))
        (Set.mem_of_mem_inter_left yW),
        IsOpen.inter open_V (Rubin.img_open_open g⁻¹ U open_U),
        ⟨x_in_V, mem_inv_smulImage.mpr gx_in_U⟩
    ⟩
#align support_open Rubin.support_open

end Continuous

end Rubin
