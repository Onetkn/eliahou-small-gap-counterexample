import Eliahou.Counterexample.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite weighted simplices and their cardinalities. The recurrence counts
coefficient tuples; it does not enumerate semigroup elements or assume unique
factorization. The semantic use of the counts is separate. -/

namespace Eliahou.Counterexample

open Finset
open scoped BigOperators

noncomputable section
open Classical

def tupleWeight : (n : ℕ) → (Fin n → ℕ) → (Fin n → ℕ) → ℕ
  | 0, _, _ => 0
  | n + 1, w, u => w 0 * u 0 + tupleWeight n (Fin.tail w) (Fin.tail u)

def simplex : (n : ℕ) → (Fin n → ℕ) → ℕ → Finset (Fin n → ℕ)
  | 0, _, _ => {fun i => Fin.elim0 i}
  | n + 1, w, B => (range (B / w 0 + 1)).biUnion fun a =>
      (simplex n (Fin.tail w) (B - w 0 * a)).image (Fin.cons a)

def simplexCount : (n : ℕ) → (Fin n → ℕ) → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, w, B => ∑ a ∈ range (B / w 0 + 1),
      simplexCount n (Fin.tail w) (B - w 0 * a)

theorem mem_simplex (n : ℕ) (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (B : ℕ) (u : Fin n → ℕ) :
    u ∈ simplex n w B ↔ tupleWeight n w u ≤ B := by
  induction n generalizing B with
  | zero =>
      simp only [simplex, mem_singleton, tupleWeight, Nat.zero_le, iff_true]
      exact Subsingleton.elim _ _
  | succ n ih =>
      simp only [simplex, mem_biUnion, mem_image]
      constructor
      · rintro ⟨a, ha, v, hv, rfl⟩
        have hprod : w 0 * a ≤ B := by
          have := (Nat.le_div_iff_mul_le (hw 0)).mp (Nat.lt_succ_iff.mp (mem_range.mp ha))
          simpa [Nat.mul_comm] using this
        have htail := (ih (Fin.tail w) (fun i => hw i.succ) (B - w 0 * a) v).mp hv
        simp only [tupleWeight, Fin.cons_zero, Fin.tail_cons]
        omega
      · intro hu
        change w 0 * u 0 + tupleWeight n (Fin.tail w) (Fin.tail u) ≤ B at hu
        have hprod : w 0 * u 0 ≤ B := by omega
        have hrange : u 0 ∈ range (B / w 0 + 1) := by
          apply mem_range.mpr
          apply Nat.lt_succ_iff.mpr
          apply (Nat.le_div_iff_mul_le (hw 0)).mpr
          simpa [Nat.mul_comm] using hprod
        refine ⟨u 0, hrange, Fin.tail u, ?_, Fin.cons_self_tail u⟩
        apply (ih (Fin.tail w) (fun i => hw i.succ) (B - w 0 * u 0) (Fin.tail u)).mpr
        omega

theorem card_simplex (n : ℕ) (w : Fin n → ℕ) (B : ℕ) :
    (simplex n w B).card = simplexCount n w B := by
  induction n generalizing B with
  | zero => simp [simplex, simplexCount]
  | succ n ih =>
      rw [simplex, card_biUnion]
      · simp only [card_image_of_injective _ (Fin.cons_right_injective _), ih]
        rfl
      · intro a ha b hb hab
        apply disjoint_left.mpr
        intro u hua hub
        obtain ⟨v, hv, huv⟩ := mem_image.mp hua
        obtain ⟨z, hz, huz⟩ := mem_image.mp hub
        have heq : a = b := by
          have := congrFun (huv.trans huz.symm) 0
          simpa using this
        exact hab heq

def coefficientWeights : Fin 7 → ℕ := fun i => if i.val < 2 then 4 else 5

theorem coefficientWeights_pos (i : Fin 7) : 0 < coefficientWeights i := by
  simp only [coefficientWeights]
  split <;> omega

theorem tupleWeight_eq_weight (u : Coeff) :
    tupleWeight 7 coefficientWeights u = weight u := by
  simp [tupleWeight, coefficientWeights, Fin.tail, weight]
  omega

def coeffsLt (n : ℕ) : Finset Coeff :=
  if n = 0 then ∅ else simplex 7 coefficientWeights (n - 1)

@[simp] theorem mem_coeffsLt_iff (n : ℕ) (u : Coeff) :
    u ∈ coeffsLt n ↔ weight u < n := by
  by_cases hn : n = 0
  · simp [coeffsLt, hn]
  · rw [coeffsLt, ite_eq_right hn, mem_simplex _ _ coefficientWeights_pos,
      tupleWeight_eq_weight]
    omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem card_coeffsLt_32 : (coeffsLt 32).card = 2024 := by
  rw [coeffsLt, ite_eq_right (by decide), card_simplex]
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem card_coeffsLt_36 : (coeffsLt 36).card = 3796 := by
  rw [coeffsLt, ite_eq_right (by decide), card_simplex]
  decide

theorem card_coeffsBand_32_36 :
    ((coeffsLt 36).filter (fun u => 32 ≤ weight u)).card = 1772 := by
  have hsub : coeffsLt 32 ⊆ coeffsLt 36 := by
    intro u hu
    simp only [mem_coeffsLt_iff] at hu ⊢
    omega
  have heq : (coeffsLt 36).filter (fun u => 32 ≤ weight u) =
      coeffsLt 36 \ coeffsLt 32 := by
    ext u
    simp only [mem_filter, mem_coeffsLt_iff, mem_sdiff]
    omega
  rw [heq, card_sdiff_of_subset hsub, card_coeffsLt_36, card_coeffsLt_32]

end
end Eliahou.Counterexample
