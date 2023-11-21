import Mathlib.GroupTheory.Subgroup.Basic
-- import Mathlib.GroupTheory.Commutator
-- import Mathlib.GroupTheory.GroupAction.Basic
-- import Mathlib.GroupTheory.Exponent
-- import Mathlib.GroupTheory.Perm.Basic

import Lean.Meta.Tactic.Util
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Simp.Main
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Group

namespace Rubin.Tactic

open Lean.Parser.Tactic

--@[simp]
theorem smul_eq_smul_inv {G α : Type _} [Group G] [MulAction G α] {g h : G}
    {x y : α} : g • x = h • y ↔ (h⁻¹ * g) • x = y :=
  by
  constructor
  · intro hyp
    let res := congr_arg ((· • ·) h⁻¹) hyp
    simp at res
    rw [← mul_smul] at res
    exact res
  · intro hyp
    rw [<-hyp, mul_smul]
    simp
#align smul_eq_smul Rubin.Tactic.smul_eq_smul_inv

theorem smul_succ {G α : Type _} (n : ℕ) [Group G] [MulAction G α] {g : G}
    {x : α} : g ^ n.succ • x = g • g ^ n • x :=
  by
  rw [pow_succ, mul_smul]
#align smul_succ Rubin.Tactic.smul_succ

-- Note: calling "group" after "group_action₁" might not be a good idea, as they can end up running in a loop
syntax (name := group_action₁) "group_action₁" (location)?: tactic
macro_rules
  | `(tactic| group_action₁ $[at $location]?) => `(tactic| simp only [
    smul_smul,
    Rubin.Tactic.smul_eq_smul_inv,
    Rubin.Tactic.smul_succ,

    one_smul,
    mul_one,
    one_mul,
    sub_self,
    add_neg_self,
    neg_add_self,
    neg_neg,
    tsub_self,
    <-mul_assoc,

    one_pow,
    one_zpow,
    <-mul_zpow_neg_one,
    zpow_zero,
    mul_zpow,
    zpow_sub,
    zpow_ofNat,
    <-zpow_neg_one,
    <-zpow_mul,
    <-zpow_add_one,
    <-zpow_one_add,
    <-zpow_add,

    Int.ofNat_add,
    Int.ofNat_mul,
    Int.ofNat_zero,
    Int.ofNat_one,
    Int.mul_neg_eq_neg_mul_symm,
    Int.neg_mul_eq_neg_mul_symm,

    Mathlib.Tactic.Group.zpow_trick,
    Mathlib.Tactic.Group.zpow_trick_one,
    Mathlib.Tactic.Group.zpow_trick_one',

    commutatorElement_def
  ] $[at $location]?
)

/-- Tactic for normalizing expressions in group actions, without assuming
commutativity, using only the group axioms without any information about
which group is manipulated.
Example:
```lean
example {G α : Type} [Group G] [MulAction G α] (a b : G) (x y : α) (h : a • b • x = a • y) : b⁻¹ • y = x := by
  group_action at h -- normalizes `h` which becomes `h : c = d`
  rw [←h]           -- the goal is now `a*d*d⁻¹ = a`
  group_action      -- which then normalized and closed
```
-/
syntax (name := group_action) "group_action" (location)?: tactic
macro_rules
  | `(tactic| group_action $[at $location]?) => `(tactic|
    repeat (fail_if_no_progress (group_action₁ $[at $location]? <;> group $[at $location]?))
  )

example {G α: Type _} [Group G] [MulAction G α] (g h: G) (x: α): g • h • x = (g * h) • x := by
  group_action

example {G α : Type} [Group G] [MulAction G α] (a b : G) (x y : α) (h : a • b • x = a • y) : b⁻¹ • y = x := by
  group_action at h  -- normalizes `h` which becomes `h : c = d`
  rw [←h]            -- the goal is now `a*d*d⁻¹ = a`
  group_action       -- which then normalized and closed

example (G α : Type _) [Group G] (a b c : G) [MulAction G α] (x : α) :
    ⁅a * b, c⁆ • x = (a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆) • x := by
  group_action

section PotentialLoops

variable {G α : Type _}
variable [Group G]
variable [MulAction G α]
variable (g f : G)
variable (x : α)

example: x = g • f⁻¹ • g⁻¹ • x ↔ g⁻¹ • x = f • g⁻¹ • x := by
  group_action
  constructor <;> intro h <;> exact h.symm

example: x = g • f⁻¹ • g⁻¹ • x ↔ g⁻¹ • x = f • g⁻¹ • x := by
  constructor
  · intro h
    group_action at h
    nth_rewrite 2 [h]
    group_action
  · intro h
    group_action at h
    nth_rewrite 1 [<-h]
    group_action

example: x = g • f⁻¹ • g⁻¹ • x ↔ g⁻¹ • x = f⁻¹ • g⁻¹ • x := by
  constructor
  · intro h
    nth_rewrite 1 [h]
    group_action
  · intro h
    group_action at h
    nth_rewrite 2 [<-h]
    group_action

example (h: (g * f ^ (-2 : ℤ) * g ^ (-1 : ℤ)) • x = x):
  g⁻¹ • (g * f ^ (-1 : ℤ) * g ^ (-1 : ℤ)) • x = f • g⁻¹ • x :=
by
  group_action
  exact h

example (h: x = g • f⁻¹ • g⁻¹ • x): True := by
  group_action at h
  exact True.intro

example (j: ℕ) (h: g • g ^ j • x = x): True := by
  group_action at h
  exact True.intro

end PotentialLoops

end Rubin.Tactic
