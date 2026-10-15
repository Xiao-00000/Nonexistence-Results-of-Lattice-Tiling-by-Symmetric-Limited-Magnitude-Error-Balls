module

public import RequestProject.DSeries

/-!
# Closed forms of `d_2`, `d_4`, `d_6`

The explicit expressions for `d_2(q,k)`, `d_4(q,k)`, `d_6(q,k)` stated in `paper.tex` right after
Theorem `thm:main`. They are stated with denominators cleared, as identities in `ℚ⟦q⟧`
(the variable `q` is `PowerSeries.X`), and also in the form `d = N · D⁻¹` with the inverse of
a power series with nonzero constant term.

The proof uses the coefficientwise form of the differential equation `g' = g f'`
(`LatticeTiling.derivativeFun_gSeries`) together with Faulhaber's formulas for
`∑_{b=1}^k b^2`, `∑_{b=1}^k b^4`, `∑_{b=1}^k b^6`.
-/

@[expose] public section

open Finset PowerSeries

namespace LatticeTiling

/-- The formal variable `q` of `ℚ⟦q⟧`. -/
local notation "q" => (PowerSeries.X : PowerSeries ℚ)

/-- Faulhaber: `6 ∑_{b=1}^k b^2 = k(k+1)(2k+1)`. -/
lemma sum_Icc_pow_two (k : ℕ) :
    6 * ∑ b ∈ Icc 1 k, (b : ℚ) ^ 2 = k * (k + 1) * (2 * k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; push_cast; ring

/-- Faulhaber: `30 ∑_{b=1}^k b^4 = k(k+1)(2k+1)(3k²+3k-1)`. -/
lemma sum_Icc_pow_four (k : ℕ) :
    30 * ∑ b ∈ Icc 1 k, (b : ℚ) ^ 4 = k * (k + 1) * (2 * k + 1) * (3 * k ^ 2 + 3 * k - 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; push_cast; ring

/-- Faulhaber: `42 ∑_{b=1}^k b^6 = k(k+1)(2k+1)(3k⁴+6k³-3k+1)`. -/
lemma sum_Icc_pow_six (k : ℕ) :
    42 * ∑ b ∈ Icc 1 k, (b : ℚ) ^ 6 =
      k * (k + 1) * (2 * k + 1) * (3 * k ^ 4 + 6 * k ^ 3 - 3 * k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; push_cast; ring

lemma coeff_hSeries_even (k j : ℕ) :
    coeff (2 * j) (hSeries k) = 2 * (∑ b ∈ Icc 1 k, (b : ℚ) ^ (2 * j)) / ((2 * j).factorial : ℚ) := by
  simp only [hSeries, map_sum, coeff_twoCosh, Even.neg_pow ⟨j, two_mul j⟩]
  rw [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun b _ => by ring

lemma coeff_hSeries_odd (k m : ℕ) (hm : Odd m) : coeff m (hSeries k) = 0 := by
  simpa using coeff_hSeries_pow_odd k 1 m hm

lemma coeff_gSeries (k m : ℕ) :
    coeff m (gSeries k) = (if m = 0 then 1 else 0) + X * C (coeff m (hSeries k)) := by
  simp [gSeries, coeff_one, coeff_C_mul, coeff_map]

lemma cancel_natCast_mul (c : ℕ) (hc : c ≠ 0) {x y : PowerSeries ℚ}
    (h : (c : PowerSeries ℚ) * x = c * y) : x = y :=
  mul_left_cancel₀ (fun h0 => hc (by simpa using congrArg constantCoeff h0)) h

/-- The coefficientwise form of `g' = g f'`: for every `m`,
`(m+1) g_{m+1} = ∑_{i+j=m} g_i (j+1) d_{j+1}`. -/
lemma ode_coeff (k m : ℕ) :
    coeff (m + 1) (gSeries k) * ((m : PowerSeries ℚ) + 1) =
      ∑ p ∈ antidiagonal m, coeff p.1 (gSeries k) * (dSeries k (p.2 + 1) * ((p.2 : PowerSeries ℚ) + 1)) := by
  have h := congrArg (coeff m) (derivativeFun_gSeries k)
  rw [coeff_derivativeFun, coeff_mul] at h
  simpa [coeff_derivativeFun, fSeries] using h

/-- The three relations obtained from `g' = g f'` at orders `x^1, x^3, x^5`, together with the
values of the coefficients of `g`. -/
lemma dSeries_relations (k : ℕ) :
    (1 + 2 * (k : PowerSeries ℚ) * X) * dSeries k 2 = X * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 2) ∧
    12 * ((1 + 2 * (k : PowerSeries ℚ) * X) * dSeries k 4) =
      X * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 4) - 6 * X * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 2) * dSeries k 2 ∧
    360 * ((1 + 2 * (k : PowerSeries ℚ) * X) * dSeries k 6) =
      X * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 6) - 240 * X * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 2) * dSeries k 4
        - 10 * X * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 4) * dSeries k 2 := by
  have g0 : coeff 0 (gSeries k) = 1 + 2 * (k : PowerSeries ℚ) * X := by
    rw [coeff_gSeries, coeff_zero_eq_constantCoeff_apply, constantCoeff_hSeries]
    simp [map_ofNat]; ring
  have godd : ∀ m, Odd m → coeff m (gSeries k) = 0 := by
    intro m hm
    rw [coeff_gSeries, coeff_hSeries_odd k m hm, if_neg (by rintro rfl; simp at hm)]; simp
  have dodd : ∀ m, Odd m → dSeries k m = 0 := dSeries_odd k
  have g2 : coeff 2 (gSeries k) = X * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 2) := by
    rw [coeff_gSeries, show (2 : ℕ) = 2 * 1 from rfl, coeff_hSeries_even]
    simp [Nat.factorial]
  have g4 : 12 * coeff 4 (gSeries k) = X * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 4) := by
    rw [coeff_gSeries, show (4 : ℕ) = 2 * 2 from rfl, coeff_hSeries_even, if_neg (by norm_num),
      zero_add, ← map_ofNat (C (R := ℚ)) 12, mul_left_comm, ← map_mul]
    congr 2
    simp [Nat.factorial]; ring
  have g6 : 360 * coeff 6 (gSeries k) = X * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 6) := by
    rw [coeff_gSeries, show (6 : ℕ) = 2 * 3 from rfl, coeff_hSeries_even, if_neg (by norm_num),
      zero_add, ← map_ofNat (C (R := ℚ)) 360, mul_left_comm, ← map_mul]
    congr 2
    simp [Nat.factorial]; ring
  have e1 := ode_coeff k 1
  have e3 := ode_coeff k 3
  have e5 := ode_coeff k 5
  simp only [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, sum_singleton] at e1 e3 e5
  simp only [zero_add, Nat.reduceAdd, g0, godd 1 (by decide), godd 3 (by decide),
    godd 5 (by decide), dodd 1 (by decide), dodd 3 (by decide), dodd 5 (by decide),
    zero_mul, mul_zero, add_zero] at e1 e3 e5
  push_cast at e1 e3 e5
  refine ⟨cancel_natCast_mul 2 (by norm_num) ?_, cancel_natCast_mul 4 (by norm_num) ?_,
    cancel_natCast_mul 6 (by norm_num) ?_⟩
  · push_cast; linear_combination -e1 + 2 * g2
  · push_cast; linear_combination -12 * e3 + 4 * g4 - 24 * dSeries k 2 * g2
  · push_cast
    linear_combination -360 * e5 + 6 * g6 - 1440 * dSeries k 4 * g2 - 60 * dSeries k 2 * g4


lemma faulhaber_powerSeries (k : ℕ) :
    6 * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 2) = (k : PowerSeries ℚ) * (k + 1) * (2 * k + 1) ∧
    30 * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 4) =
      (k : PowerSeries ℚ) * (k + 1) * (2 * k + 1) * (3 * k ^ 2 + 3 * k - 1) ∧
    42 * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 6) =
      (k : PowerSeries ℚ) * (k + 1) * (2 * k + 1) * (3 * k ^ 4 + 6 * k ^ 3 - 3 * k + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [map_ofNat] using congrArg (C (R := ℚ)) (sum_Icc_pow_two k)
  · simpa [map_ofNat] using congrArg (C (R := ℚ)) (sum_Icc_pow_four k)
  · simpa [map_ofNat] using congrArg (C (R := ℚ)) (sum_Icc_pow_six k)

/-- **Closed form of `d_2(q,k)`** (`paper.tex`, display after Theorem `thm:main`):
`d_2(q,k) = q k (2k²+3k+1) / (12 q k + 6)`, stated with the denominator cleared. -/
theorem dSeries_two (k : ℕ) :
    (12 * k * q + 6) * dSeries k 2 = k * (2 * k ^ 2 + 3 * k + 1) * q := by
  obtain ⟨R1, -, -⟩ := dSeries_relations k
  obtain ⟨P2, -, -⟩ := faulhaber_powerSeries k
  linear_combination 6 * R1 + X * P2

/-- **Closed form of `d_4(q,k)`** (`paper.tex`, display after Theorem `thm:main`):
`d_4(q,k) = -(4k³q+9k²q-3k²+7qk-3k+1)(k+1)(2k+1)qk / (360 (2qk+1)²)`, stated with the
denominator cleared. -/
theorem dSeries_four (k : ℕ) :
    360 * (2 * q * k + 1) ^ 2 * dSeries k 4 =
      -((4 * k ^ 3 * q + 9 * k ^ 2 * q - 3 * k ^ 2 + 7 * q * k - 3 * k + 1) *
        (k + 1) * (2 * k + 1) * q * k) := by
  obtain ⟨R1, R3, -⟩ := dSeries_relations k
  obtain ⟨P2, P4, -⟩ := faulhaber_powerSeries k
  set u : PowerSeries ℚ := 1 + 2 * (k : PowerSeries ℚ) * X
  set S2 := C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 2)
  linear_combination 30 * u * R3 - 180 * X * S2 * R1 + u * X * P4 -
    5 * X ^ 2 * (6 * S2 + (k : PowerSeries ℚ) * (k + 1) * (2 * k + 1)) * P2

/-- **Closed form of `d_6(q,k)`** (`paper.tex`, display after Theorem `thm:main`):
`d_6(q,k) = (k+1)(2k+1)(64q²k⁶ + 282q²k⁵ - 90k⁵q + 490q²k⁴ - 243k⁴q + 384q²k³ + 9k⁴ - 210k³q
  + 124q²k² + 18k³ - 36k²q + 33qk - 9k + 3) qk / (45360 (2qk+1)³)`, stated with the
denominator cleared. -/
theorem dSeries_six (k : ℕ) :
    45360 * (2 * q * k + 1) ^ 3 * dSeries k 6 =
      (k + 1) * (2 * k + 1) *
        (64 * q ^ 2 * k ^ 6 + 282 * q ^ 2 * k ^ 5 - 90 * k ^ 5 * q + 490 * q ^ 2 * k ^ 4 -
          243 * k ^ 4 * q + 384 * q ^ 2 * k ^ 3 + 9 * k ^ 4 - 210 * k ^ 3 * q +
          124 * q ^ 2 * k ^ 2 + 18 * k ^ 3 - 36 * k ^ 2 * q + 33 * q * k - 9 * k + 3) * q * k := by
  obtain ⟨R1, R3, R5⟩ := dSeries_relations k
  obtain ⟨P2, P4, P6⟩ := faulhaber_powerSeries k
  set u : PowerSeries ℚ := 1 + 2 * (k : PowerSeries ℚ) * X
  set S2 := C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 2)
  set S4 := C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 4)
  set A2 : PowerSeries ℚ := (k : PowerSeries ℚ) * (k + 1) * (2 * k + 1)
  set A4 : PowerSeries ℚ := (k : PowerSeries ℚ) * (k + 1) * (2 * k + 1) * (3 * k ^ 2 + 3 * k - 1)
  have T : 45360 * u ^ 3 * dSeries k 6 = 126 * u ^ 2 * X * C (∑ b ∈ Icc 1 k, (b : ℚ) ^ 6) -
      3780 * u * X ^ 2 * S2 * S4 + 15120 * X ^ 3 * S2 ^ 3 := by
    linear_combination 126 * u ^ 2 * R5 - 2520 * u * X * S2 * R3 - 1260 * u * X * S4 * R1 +
      15120 * X ^ 2 * S2 ^ 2 * R1
  linear_combination T + 3 * u ^ 2 * X * P6 - 21 * u * X ^ 2 * (6 * S2 * P4 + A4 * P2) +
    70 * X ^ 3 * ((6 * S2) ^ 2 + 6 * S2 * A2 + A2 ^ 2) * P2

/-- **`d_2(q,k)` as a quotient** (`paper.tex`, display after Theorem `thm:main`):
`d_2(q,k) = q k (2k²+3k+1) · (12qk+6)⁻¹` in `ℚ⟦q⟧`. -/
theorem dSeries_two_eq_mul_inv (k : ℕ) :
    dSeries k 2 = k * (2 * k ^ 2 + 3 * k + 1) * q * (12 * k * q + 6)⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp; rw [map_ofNat]; norm_num), mul_comm, dSeries_two]

/-- **`d_4(q,k)` as a quotient** (`paper.tex`, display after Theorem `thm:main`). -/
theorem dSeries_four_eq_mul_inv (k : ℕ) :
    dSeries k 4 = -((4 * k ^ 3 * q + 9 * k ^ 2 * q - 3 * k ^ 2 + 7 * q * k - 3 * k + 1) *
        (k + 1) * (2 * k + 1) * q * k) * (360 * (2 * q * k + 1) ^ 2)⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp; rw [map_ofNat]; norm_num), mul_comm, dSeries_four]

/-- **`d_6(q,k)` as a quotient** (`paper.tex`, display after Theorem `thm:main`). -/
theorem dSeries_six_eq_mul_inv (k : ℕ) :
    dSeries k 6 = (k + 1) * (2 * k + 1) *
        (64 * q ^ 2 * k ^ 6 + 282 * q ^ 2 * k ^ 5 - 90 * k ^ 5 * q + 490 * q ^ 2 * k ^ 4 -
          243 * k ^ 4 * q + 384 * q ^ 2 * k ^ 3 + 9 * k ^ 4 - 210 * k ^ 3 * q +
          124 * q ^ 2 * k ^ 2 + 18 * k ^ 3 - 36 * k ^ 2 * q + 33 * q * k - 9 * k + 3) * q * k *
        (45360 * (2 * q * k + 1) ^ 3)⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp; rw [map_ofNat]; norm_num), mul_comm, dSeries_six]

end LatticeTiling
