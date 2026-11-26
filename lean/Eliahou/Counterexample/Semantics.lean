import Eliahou.Counterexample.Defs

namespace Eliahou.Counterexample

theorem value_zero (M : ℕ) : value M (fun _ => 0) = 0 := by
  simp [value, weight, offset]

theorem value_add (M : ℕ) (u v : Coeff) :
    value M (u + v) = value M u + value M v := by
  simp only [value, weight, offset, Pi.add_apply, Nat.mul_add]
  omega

theorem generated_add {M x y : ℕ} (hx : Generated M x) (hy : Generated M y) :
    Generated M (x + y) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact ⟨u + v, value_add M u v⟩

theorem semigroup_zero (M : ℕ) : 0 ∈ Semigroup M :=
  Or.inl ⟨fun _ => 0, value_zero M⟩

theorem semigroup_add {M x y : ℕ} (hx : x ∈ Semigroup M) (hy : y ∈ Semigroup M) :
    x + y ∈ Semigroup M := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (generated_add hx hy)
  all_goals exact Or.inr (by omega)

theorem four_degree_le_weight (u : Coeff) : 4 * degree u ≤ weight u := by
  simp only [degree, weight]
  omega

theorem coord_le_degree (u : Coeff) (i : Fin 7) : u i ≤ degree u := by
  fin_cases i <;> norm_num [degree] <;> omega

theorem offset_le_degree (u : Coeff) : offset u ≤ 100000 * degree u := by
  simp only [degree, offset]
  omega

theorem bounds_of_weight_lt {u : Coeff} (hu : weight u < 36) :
    (∀ i, u i ≤ 8) ∧ offset u ≤ 800000 := by
  have hdeg : degree u ≤ 8 := by have := four_degree_le_weight u; omega
  exact ⟨fun i => (coord_le_degree u i).trans hdeg,
    (offset_le_degree u).trans (Nat.mul_le_mul_left 100000 hdeg)⟩

theorem offset_lt_of_weight_lt {M : ℕ} (hM : 1000000 ≤ M)
    {u : Coeff} (hu : weight u < 36) : offset u < M := by
  have := (bounds_of_weight_lt hu).2
  omega

theorem weight_lt_of_value_lt {M B : ℕ} (hM : 0 < M) {u : Coeff}
    (hu : value M u < B * M) : weight u < B := by
  by_contra hc
  have hp := Nat.mul_le_mul_left M (show B ≤ weight u by omega)
  unfold value at hu
  nlinarith

theorem value_lt_iff {M B : ℕ} (hM : 1000000 ≤ M) (hB : B ≤ 36) (u : Coeff) :
    value M u < B * M ↔ weight u < B := by
  constructor
  · exact weight_lt_of_value_lt (by omega)
  · intro hu
    have ho := offset_lt_of_weight_lt hM (show weight u < 36 by omega)
    have hp := Nat.mul_le_mul_left M (show weight u + 1 ≤ B by omega)
    unfold value
    nlinarith

private theorem decimal_digit {a b x y : ℕ} (ha : a ≤ 8) (hb : b ≤ 8)
    (he : a + 10 * x = b + 10 * y) : a = b ∧ x = y := by omega

set_option maxHeartbeats 2000000 in
theorem value_injective_below {M : ℕ} (hM : 1000000 ≤ M)
    {u v : Coeff} (hu : weight u < 36) (hv : weight v < 36)
    (he : value M u = value M v) : u = v := by
  have hou := offset_lt_of_weight_lt hM hu
  have hov := offset_lt_of_weight_lt hM hv
  have hw : weight u = weight v := by
    by_contra hc
    rcases lt_or_gt_of_ne hc with hc | hc
    · have hp := Nat.mul_le_mul_left M (show weight u + 1 ≤ weight v by omega)
      unfold value at he
      nlinarith
    · have hp := Nat.mul_le_mul_left M (show weight v + 1 ≤ weight u by omega)
      unfold value at he
      nlinarith
  have ho : offset u = offset v := by unfold value at he; rw [hw] at he; omega
  have bu := (bounds_of_weight_lt hu).1
  have bv := (bounds_of_weight_lt hv).1
  have bu0 := bu 0; have bu1 := bu 1; have bu2 := bu 2; have bu3 := bu 3
  have bu4 := bu 4; have bu5 := bu 5; have bu6 := bu 6
  have bv0 := bv 0; have bv1 := bv 1; have bv2 := bv 2; have bv3 := bv 3
  have bv4 := bv 4; have bv5 := bv 5; have bv6 := bv 6
  simp only [offset] at ho
  have ⟨h1, e2⟩ := decimal_digit bu1 bv1
    (x := u 2 + 10 * u 3 + 100 * u 4 + 1000 * u 5 + 10000 * u 6)
    (y := v 2 + 10 * v 3 + 100 * v 4 + 1000 * v 5 + 10000 * v 6) (by omega)
  have ⟨h2, e3⟩ := decimal_digit bu2 bv2
    (x := u 3 + 10 * u 4 + 100 * u 5 + 1000 * u 6)
    (y := v 3 + 10 * v 4 + 100 * v 5 + 1000 * v 6) (by omega)
  have ⟨h3, e4⟩ := decimal_digit bu3 bv3
    (x := u 4 + 10 * u 5 + 100 * u 6)
    (y := v 4 + 10 * v 5 + 100 * v 6) (by omega)
  have ⟨h4, e5⟩ := decimal_digit bu4 bv4
    (x := u 5 + 10 * u 6) (y := v 5 + 10 * v 6) (by omega)
  have ⟨h5, h6⟩ := decimal_digit bu5 bv5 (x := u 6) (y := v 6) (by omega)
  have h0 : u 0 = v 0 := by simp only [weight] at hw; omega
  funext i
  fin_cases i <;> assumption

theorem generator_bounds {M : ℕ} (hM : 1000000 ≤ M) (i : Fin 7) :
    4 * M ≤ generator M i ∧ generator M i < 8 * M := by
  fin_cases i <;> simp [generator, value, weight, offset, unitCoeff] <;> omega

@[simp] theorem generator_zero (M : ℕ) : generator M 0 = 4 * M := by
  simp [generator, value, weight, offset, unitCoeff, Nat.mul_comm]

@[simp] theorem generator_one (M : ℕ) : generator M 1 = 4 * M + 1 := by
  simp [generator, value, weight, offset, unitCoeff, Nat.mul_comm]

theorem generator_mem (M : ℕ) (i : Fin 7) : generator M i ∈ Semigroup M :=
  Or.inl ⟨unitCoeff i, rfl⟩

theorem generated_positive_split {M n : ℕ} (hM : 1000000 ≤ M)
    (hn : Generated M n) (hp : 0 < n) :
    (∃ i, generator M i = n) ∨ Decomposable M n := by
  obtain ⟨u, rfl⟩ := hn
  have hpos : ∃ i, 0 < u i := by
    by_contra hc
    have hz : u = fun _ => 0 := by
      funext i
      have hi : ¬ 0 < u i := fun hi => hc ⟨i, hi⟩
      omega
    rw [hz, value_zero] at hp
    omega
  obtain ⟨i, hi⟩ := hpos
  let v : Coeff := fun j => u j - unitCoeff i j
  have hu : u = unitCoeff i + v := by
    funext j
    by_cases he : j = i
    · subst j; simp [Pi.add_apply, v, unitCoeff]; omega
    · simp [Pi.add_apply, v, unitCoeff, he]
  have he : generator M i + value M v = value M u := by
    rw [hu, value_add]
    rfl
  by_cases hv : value M v = 0
  · exact Or.inl ⟨i, by omega⟩
  · exact Or.inr ⟨generator M i, generator_mem M i, value M v,
      Or.inl ⟨v, rfl⟩, by have := (generator_bounds hM i).1; omega, by omega, he⟩

theorem semigroup_lower {M n : ℕ} (hM : 1000000 ≤ M)
    (hn : n ∈ Semigroup M) (hp : 0 < n) : 4 * M ≤ n := by
  rcases hn with hn | hn
  · obtain ⟨u, rfl⟩ := hn
    have hdeg : 0 < degree u := by
      by_contra hc
      have hz : u = fun _ => 0 := by
        funext i
        have := coord_le_degree u i
        omega
      rw [hz, value_zero] at hp
      omega
    have hw : 4 ≤ weight u := by have := four_degree_le_weight u; omega
    have hmul := Nat.mul_le_mul_left M hw
    unfold value
    nlinarith
  · omega

theorem generator_primitive {M : ℕ} (hM : 1000000 ≤ M) (i : Fin 7) :
    Primitive M (generator M i) := by
  have hb := generator_bounds hM i
  refine ⟨generator_mem M i, by omega, ?_⟩
  rintro ⟨x, hx, y, hy, hxp, hyp, he⟩
  have := semigroup_lower hM hx hxp
  have := semigroup_lower hM hy hyp
  omega

theorem primitive_left_iff {M n : ℕ} (hM : 1000000 ≤ M) (hn : n < 32 * M) :
    Primitive M n ↔ ∃ i, generator M i = n := by
  constructor
  · rintro ⟨hs, hp, hnd⟩
    have hg : Generated M n := by rcases hs with hs | hs; exact hs; omega
    rcases generated_positive_split hM hg hp with hg | hd
    · exact hg
    · exact False.elim (hnd hd)
  · rintro ⟨i, rfl⟩
    exact generator_primitive hM i

theorem decomposable_right_iff {M n : ℕ} (hM : 1000000 ≤ M)
    (hl : 32 * M ≤ n) (hu : n < 36 * M) :
    Decomposable M n ↔ Generated M n := by
  constructor
  · rintro ⟨x, hx, y, hy, hxp, hyp, he⟩
    have hxm := semigroup_lower hM hx hxp
    have hym := semigroup_lower hM hy hyp
    have hxg : Generated M x := by rcases hx with hx | hx; exact hx; omega
    have hyg : Generated M y := by rcases hy with hy | hy; exact hy; omega
    exact he ▸ generated_add hxg hyg
  · intro hg
    rcases generated_positive_split hM hg (by omega) with ⟨i, he⟩ | hd
    · have := (generator_bounds hM i).2
      omega
    · exact hd

theorem conductor_gap {M : ℕ} (hM : 1000000 ≤ M) :
    32 * M - 1 ∉ Semigroup M := by
  intro hn
  rcases hn with ⟨u, he⟩ | ht
  · have hpos : 0 < M := by omega
    have hu : weight u < 32 := weight_lt_of_value_lt hpos (by omega : value M u < 32 * M)
    have ho := (bounds_of_weight_lt (show weight u < 36 by omega)).2
    have hp := Nat.mul_le_mul_left M (show weight u ≤ 31 by omega)
    have hsub : 32 * M - 1 + 1 = 32 * M := by omega
    unfold value at he
    nlinarith
  · omega

theorem unit_weight_lt (i : Fin 7) : weight (unitCoeff i) < 36 := by
  fin_cases i <;> decide

theorem generator_injective {M : ℕ} (hM : 1000000 ≤ M) :
    Function.Injective (generator M) := by
  intro i j he
  have hu := value_injective_below hM (unit_weight_lt i) (unit_weight_lt j) he
  by_contra hne
  have hc := congrFun hu i
  simp [unitCoeff, hne] at hc

end Eliahou.Counterexample
