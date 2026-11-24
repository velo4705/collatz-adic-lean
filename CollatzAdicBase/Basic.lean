import Mathlib.Logic.Function.Iterate

universe u

namespace Nat

-- `Nat.iterate` is provided by Mathlib (`Mathlib.Logic.Function.Iterate`) with
-- exactly this definition.  Importing it here (rather than redefining it)
-- keeps the module compatible with `RationalDescent`, which imports Mathlib.

/-- The other recursion equation: applying `f` once before `n` iterations is
    the same as applying it once after. -/
theorem iterate_succ' {α : Sort u} (op : α → α) (n : Nat) (a : α) :
    iterate op (n + 1) a = op (iterate op n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      change iterate op n (op (op a)) = op (iterate op n (op a))
      exact ih (op a)

/-- Apply `op` before or after `n` iterations: the "other" successor rule. -/
theorem iterate_succ_apply {α : Sort u} (op : α → α) (n : Nat) (a : α) :
    iterate op n (op a) = op (iterate op n a) := by
  change iterate op (n + 1) a = op (iterate op n a)
  exact iterate_succ' op n a

/-- Iteration is additive in the number of steps. -/
theorem iterate_add {α : Sort u} (op : α → α) (m n : Nat) (a : α) :
    iterate op (m + n) a = iterate op m (iterate op n a) := by
  induction m generalizing a with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [iterate]
      rw [ih]
      rw [iterate_succ_apply op n a]

end Nat

/-- The standard (integer) Collatz map on natural numbers. -/
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The odd shortcut: combine the odd step and the following even step. -/
def shortcut (m : Nat) : Nat := (3 * m + 1) / 2

/-- `G(n) ≥ m`: no positive number of steps up to `m` brings `n` back down
    to (or below) its starting value. -/
def GlideAtLeast (n m : Nat) : Prop :=
  ∀ t, 1 ≤ t → t ≤ m → Nat.iterate collatz t n > n

/-- `G(n) = m`: the orbit stays strictly above `n` for steps `1 .. m-1` and
    drops strictly below `n` at step `m`. -/
def GlideEq (n m : Nat) : Prop :=
  (∀ t, 1 ≤ t → t < m → Nat.iterate collatz t n > n) ∧
  Nat.iterate collatz m n < n
