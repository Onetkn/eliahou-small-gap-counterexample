import Eliahou.Counterexample.Semantics
import Eliahou.Counterexample.Counts

namespace Eliahou.Counterexample

open Finset
noncomputable section
open Classical

theorem left_eq_image {M : ℕ} (hM : 1000000 ≤ M) :
    left M = (coeffsLt 32).image (value M) := by
  ext n
  simp only [left, mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hn, hs⟩
    rcases hs with ⟨u, rfl⟩ | ht
    · exact ⟨u, (mem_coeffsLt_iff 32 u).2 ((value_lt_iff hM (by decide) u).1 hn), rfl⟩
    · omega
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(value_lt_iff hM (by decide) u).2 ((mem_coeffsLt_iff 32 u).1 hu),
      Or.inl ⟨u, rfl⟩⟩

theorem leftPrims_eq_image {M : ℕ} (hM : 1000000 ≤ M) :
    leftPrims M = univ.image (generator M) := by
  ext n
  simp only [leftPrims, mem_filter, mem_range, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨hn, hp⟩
    exact (primitive_left_iff hM hn).1 hp
  · rintro ⟨i, rfl⟩
    exact ⟨by have := (generator_bounds hM i).2; omega, generator_primitive hM i⟩

theorem rightDecomp_eq_image {M : ℕ} (hM : 1000000 ≤ M) :
    rightDecomp M = ((coeffsLt 36).filter (fun u => 32 ≤ weight u)).image (value M) := by
  ext n
  simp only [rightDecomp, mem_filter, mem_Ico, mem_image]
  constructor
  · rintro ⟨⟨hl, hu⟩, hd⟩
    obtain ⟨u, rfl⟩ := (decomposable_right_iff hM hl hu).1 hd
    refine ⟨u, ⟨(mem_coeffsLt_iff 36 u).2 ((value_lt_iff hM (by decide) u).1 hu), ?_⟩, rfl⟩
    by_contra hc
    have hv := (value_lt_iff hM (by decide : 32 ≤ 36) u).2 (by omega)
    omega
  · rintro ⟨u, ⟨hu, hl⟩, rfl⟩
    have hupper : value M u < 36 * M :=
      (value_lt_iff hM (by decide) u).2 ((mem_coeffsLt_iff 36 u).1 hu)
    have hlower : 32 * M ≤ value M u := by
      by_contra hc
      have hw := (value_lt_iff hM (by decide : 32 ≤ 36) u).1 (by omega)
      omega
    exact ⟨⟨hlower, hupper⟩, (decomposable_right_iff hM hlower hupper).2 ⟨u, rfl⟩⟩

theorem card_left {M : ℕ} (hM : 1000000 ≤ M) : (left M).card = 2024 := by
  rw [left_eq_image hM, card_image_of_injOn, card_coeffsLt_32]
  intro u hu v hv he
  have hu' := (mem_coeffsLt_iff 32 u).1 hu
  have hv' := (mem_coeffsLt_iff 32 v).1 hv
  exact value_injective_below hM (by omega) (by omega) he

theorem card_leftPrims {M : ℕ} (hM : 1000000 ≤ M) : (leftPrims M).card = 7 := by
  rw [leftPrims_eq_image hM, card_image_of_injective _ (generator_injective hM)]
  simp

theorem card_rightDecomp {M : ℕ} (hM : 1000000 ≤ M) : (rightDecomp M).card = 1772 := by
  rw [rightDecomp_eq_image hM, card_image_of_injOn, card_coeffsBand_32_36]
  intro u hu v hv he
  exact value_injective_below hM
    ((mem_coeffsLt_iff 36 u).1 (mem_filter.1 hu).1)
    ((mem_coeffsLt_iff 36 v).1 (mem_filter.1 hv).1) he

theorem eliahou_eq_neg_eight {M : ℕ} (hM : 1000000 ≤ M) : eliahou M = -8 := by
  rw [eliahou, card_leftPrims hM, card_left hM, card_rightDecomp hM]
  norm_num

end
end Eliahou.Counterexample
