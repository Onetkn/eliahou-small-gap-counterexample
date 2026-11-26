import Eliahou.Counterexample.Main

/-! The conjecture is stated for arbitrary numerical semigroups and the
ordinary conductor-relative Eliahou invariant.  This module identifies
the constructed family's concrete counts with that general invariant. -/

namespace Eliahou.Counterexample

def IsNumericalSemigroup (S : Set ℕ) : Prop :=
  0 ∈ S ∧ (∀ x y, x ∈ S → y ∈ S → x + y ∈ S) ∧
    ∃ c, ∀ n, c ≤ n → n ∈ S

def IsMultiplicity (S : Set ℕ) (m : ℕ) : Prop :=
  0 < m ∧ m ∈ S ∧ ∀ n, n ∈ S → 0 < n → m ≤ n

/-- The conductor is the least starting point of a full infinite tail. -/
def IsConductor (S : Set ℕ) (c : ℕ) : Prop :=
  (∀ n, c ≤ n → n ∈ S) ∧
    ∀ b, (∀ n, b ≤ n → n ∈ S) → c ≤ b

def genericDecomposable (S : Set ℕ) (n : ℕ) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, 0 < x ∧ 0 < y ∧ x + y = n

def genericPrimitive (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ 0 < n ∧ ¬ genericDecomposable S n

/-- `m` and `a` are the first two primitive elements, and both are left. -/
def FirstTwoLeftPrimitives (S : Set ℕ) (m c a : ℕ) : Prop :=
  genericPrimitive S m ∧ genericPrimitive S a ∧ m < a ∧ a < c ∧
    ∀ p, genericPrimitive S p → m < p → a ≤ p

/-- Natural-number ceiling division, for positive multiplicity. -/
def genericDepth (m c : ℕ) : ℕ := (c + m - 1) / m

noncomputable section
open Classical

def genericLeft (S : Set ℕ) (c : ℕ) : Finset ℕ :=
  (Finset.range c).filter (· ∈ S)

def genericLeftPrims (S : Set ℕ) (c : ℕ) : Finset ℕ :=
  (Finset.range c).filter (genericPrimitive S)

def genericRightDecomp (S : Set ℕ) (m c : ℕ) : Finset ℕ :=
  (Finset.Ico c (c + m)).filter (genericDecomposable S)

/-- The usual Eliahou expression `ell*k - q*s + (q*m-c)`.
All subtractions take place in the integers. -/
def genericEliahou (S : Set ℕ) (m c : ℕ) : ℤ :=
  let q : ℤ := genericDepth m c
  ((genericLeftPrims S c).card : ℤ) * ((genericLeft S c).card : ℤ) -
    q * ((genericRightDecomp S m c).card : ℤ) + (q * (m : ℤ) - (c : ℤ))

/-- Bacher's small-gap assertion for arbitrary full-tail cutoffs, as in the
source's convention permitting both canonical and noncanonical presentations.
The counterexample below additionally has the least possible cutoff. -/
def genericSmallGapConjecture : Prop :=
  ∀ (S : Set ℕ) (m c a : ℕ), IsNumericalSemigroup S →
    IsMultiplicity S m → (∀ n, c ≤ n → n ∈ S) → FirstTwoLeftPrimitives S m c a →
    a ≤ m + 6 → 0 ≤ genericEliahou S m c

theorem family_isNumericalSemigroup (M : ℕ) :
    IsNumericalSemigroup (Semigroup M) := by
  refine ⟨semigroup_zero M, ?_, 32 * M, ?_⟩
  · intro x y hx hy
    exact semigroup_add hx hy
  · intro n hn
    exact Or.inr hn

theorem family_isMultiplicity {M : ℕ} (hM : 1000000 ≤ M) :
    IsMultiplicity (Semigroup M) (4 * M) := by
  refine ⟨by omega, ?_, ?_⟩
  · simpa only [generator_zero] using generator_mem M 0
  · intro n hn hp
    exact semigroup_lower hM hn hp

theorem family_isConductor {M : ℕ} (hM : 1000000 ≤ M) :
    IsConductor (Semigroup M) (32 * M) := by
  refine ⟨fun n hn => Or.inr hn, ?_⟩
  intro b hb
  by_contra hc
  exact conductor_gap hM (hb (32 * M - 1) (by omega))

theorem family_firstTwoLeftPrimitives {M : ℕ} (hM : 1000000 ≤ M) :
    FirstTwoLeftPrimitives (Semigroup M) (4 * M) (32 * M) (4 * M + 1) := by
  have hp0 : genericPrimitive (Semigroup M) (4 * M) := by
    change Primitive M (4 * M)
    simpa only [generator_zero] using generator_primitive hM 0
  have hp1 : genericPrimitive (Semigroup M) (4 * M + 1) := by
    change Primitive M (4 * M + 1)
    simpa only [generator_one] using generator_primitive hM 1
  refine ⟨hp0, hp1, by omega, by omega, ?_⟩
  intro p _ hp
  omega

theorem family_depth {M : ℕ} (hM : 1000000 ≤ M) :
    genericDepth (4 * M) (32 * M) = 8 := by
  unfold genericDepth
  apply Nat.div_eq_of_lt_le <;> omega

theorem genericEliahou_family {M : ℕ} (hM : 1000000 ≤ M) :
    genericEliahou (Semigroup M) (4 * M) (32 * M) = eliahou M := by
  have hl : genericLeft (Semigroup M) (32 * M) = left M := rfl
  have hp : genericLeftPrims (Semigroup M) (32 * M) = leftPrims M := rfl
  have hd : genericRightDecomp (Semigroup M) (4 * M) (32 * M) = rightDecomp M := by
    have he : 32 * M + 4 * M = 36 * M := by omega
    simp only [genericRightDecomp, rightDecomp, he]
    rfl
  unfold genericEliahou
  rw [family_depth hM, hl, hp, hd]
  simp only [Nat.cast_ofNat, Nat.cast_mul]
  unfold eliahou
  omega

/-- A genuine family of counterexamples, including actual multiplicity,
least conductor, consecutive first primitives, and the general invariant. -/
theorem counterexample_family {M : ℕ} (hM : 1000000 ≤ M) :
    IsNumericalSemigroup (Semigroup M) ∧
    IsMultiplicity (Semigroup M) (4 * M) ∧
    IsConductor (Semigroup M) (32 * M) ∧
    FirstTwoLeftPrimitives (Semigroup M) (4 * M) (32 * M) (4 * M + 1) ∧
    genericEliahou (Semigroup M) (4 * M) (32 * M) = -8 := by
  refine ⟨family_isNumericalSemigroup M, family_isMultiplicity hM,
    family_isConductor hM, family_firstTwoLeftPrimitives hM, ?_⟩
  rw [genericEliahou_family hM, eliahou_eq_neg_eight hM]

/-- Explicit refutation of the universally quantified small-gap conjecture.
The witness uses `M = 1000000`, hence multiplicity `4000000`, actual
conductor `32000000`, and second primitive `4000001`. -/
theorem not_smallGapConjecture : ¬ genericSmallGapConjecture := by
  intro hc
  obtain ⟨hs, hm, hcond, hp, he⟩ := counterexample_family (M := 1000000) (by decide)
  have hnonneg := hc (Semigroup 1000000) (4 * 1000000) (32 * 1000000)
    (4 * 1000000 + 1) hs hm hcond.1 hp (by omega)
  rw [he] at hnonneg
  omega

end
end Eliahou.Counterexample
