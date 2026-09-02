/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.Data.Nat.Choose.Basic

/-!
# Binomial coefficients with lower argument two

This file records elementary identities for consecutive binomial coefficients with lower argument
two.
-/

namespace Nat

/-- The difference between consecutive binomial coefficients with lower argument two. -/
theorem choose_two_sub_choose_two_pred (n : ℕ) :
    n.choose 2 - (n - 1).choose 2 = n - 1 := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one]
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    simp

end Nat
