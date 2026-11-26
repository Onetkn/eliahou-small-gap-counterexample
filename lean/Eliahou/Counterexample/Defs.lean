import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace Eliahou.Counterexample

abbrev Coeff := Fin 7 → ℕ

def weight (u : Coeff) : ℕ :=
  4 * (u 0 + u 1) + 5 * (u 2 + u 3 + u 4 + u 5 + u 6)

def offset (u : Coeff) : ℕ :=
  u 1 + 10 * u 2 + 100 * u 3 + 1000 * u 4 + 10000 * u 5 + 100000 * u 6

def value (M : ℕ) (u : Coeff) : ℕ := M * weight u + offset u

def degree (u : Coeff) : ℕ := u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 6

def unitCoeff (i : Fin 7) : Coeff := fun j => if j = i then 1 else 0

def generator (M : ℕ) (i : Fin 7) : ℕ := value M (unitCoeff i)

def Generated (M n : ℕ) : Prop := ∃ u : Coeff, value M u = n

def Semigroup (M : ℕ) : Set ℕ := {n | Generated M n ∨ 32 * M ≤ n}

def Decomposable (M n : ℕ) : Prop :=
  ∃ x ∈ Semigroup M, ∃ y ∈ Semigroup M, 0 < x ∧ 0 < y ∧ x + y = n

def Primitive (M n : ℕ) : Prop :=
  n ∈ Semigroup M ∧ 0 < n ∧ ¬ Decomposable M n

noncomputable section
open Classical

def left (M : ℕ) : Finset ℕ := (Finset.range (32 * M)).filter (· ∈ Semigroup M)

def leftPrims (M : ℕ) : Finset ℕ :=
  (Finset.range (32 * M)).filter (Primitive M)

def rightDecomp (M : ℕ) : Finset ℕ :=
  (Finset.Ico (32 * M) (36 * M)).filter (Decomposable M)

def eliahou (M : ℕ) : ℤ :=
  ((leftPrims M).card : ℤ) * ((left M).card : ℤ) - 8 * ((rightDecomp M).card : ℤ)

end
end Eliahou.Counterexample
