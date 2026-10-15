module

public import RequestProject.Bell

/-!
# The series `d_{2j}(q,k)`

Formalization of the series `d_{2j}(q,k)` of `paper.tex`, Theorem `thm:main`:
`f(x) := ln(1 + 2q ∑_{b=1}^k cosh(bx)) = ∑_{j ≥ 0} d_{2j}(q,k) x^{2j}`,
the explicit expressions of `d_0, d_2, d_4, d_6` stated after Theorem `thm:main`, the
differential equation `g' = g f'` (with `g = 1 + 2q∑ cosh(bx)`) used in the proof, the vanishing of
the odd coefficients, and the integrality of `(2j)! d_{2j}(q,k)`.

Formal power series in `q` are elements of `PowerSeries ℚ`; formal power series in `x` with
coefficients that are power series in `q` are elements of `PowerSeries (PowerSeries ℚ)`.
-/

@[expose] public section

open Finset PowerSeries

namespace LatticeTiling

/-- The formal power series `2 cosh(bx) = e^{bx} + e^{-bx} ∈ ℚ⟦x⟧`. -/
noncomputable def twoCosh (b : ℚ) : PowerSeries ℚ :=
  rescale b (exp ℚ) + rescale (-b) (exp ℚ)

/-- The formal power series `h(x) = 2 ∑_{b=1}^{k} cosh(bx) ∈ ℚ⟦x⟧`. -/
noncomputable def hSeries (k : ℕ) : PowerSeries ℚ :=
  ∑ b ∈ Icc 1 k, twoCosh b

/-- **The series `d_m(q,k)`** (`paper.tex`, Theorem `thm:main`): the coefficient of `x^m` in
`f(x) = ln(1 + 2q ∑_{b=1}^k cosh(bx)) = ln(1 + q h(x))`, a formal power series in `q`.
Expanding `ln(1 + u) = ∑_{i ≥ 1} (-1)^{i+1} u^i / i` with `u = q h(x)` (which is legitimate in
`ℚ⟦q, x⟧` since `u` has no constant term), the coefficient of `q^i x^m` is
`(-1)^{i+1}/i · [x^m] h(x)^i` for `i ≥ 1`, and `0` for `i = 0`.
The paper's `d_{2j}(q,k)` is `dSeries k (2 * j)`; odd coefficients vanish
(`dSeries_odd`). -/
noncomputable def dSeries (k m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun i => if i = 0 then 0 else (-1) ^ (i + 1) / (i : ℚ) * coeff m (hSeries k ^ i)

/-- The series `f(x) = ln(1 + 2q ∑_{b=1}^k cosh(bx)) = ∑_m d_m(q,k) x^m`, as a power series in
`x` whose coefficients are power series in `q` (`paper.tex`, Theorem `thm:main`). -/
noncomputable def fSeries (k : ℕ) : PowerSeries (PowerSeries ℚ) :=
  PowerSeries.mk (dSeries k)

/-- The series `g(x) = 1 + 2q ∑_{b=1}^k cosh(bx) = 1 + q h(x)`, as a power series in `x` whose
coefficients are power series in `q`. -/
noncomputable def gSeries (k : ℕ) : PowerSeries (PowerSeries ℚ) :=
  1 + C (X : PowerSeries ℚ) * PowerSeries.map (C : ℚ →+* PowerSeries ℚ) (hSeries k)

/-- The formal logarithm `ln(1 + a q) = ∑_{i ≥ 1} (-1)^{i+1} a^i q^i / i ∈ ℚ⟦q⟧`. -/
noncomputable def logOneAdd (a : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun i => if i = 0 then 0 else (-1) ^ (i + 1) / (i : ℚ) * a ^ i

lemma coeff_twoCosh (b : ℚ) (m : ℕ) :
    coeff m (twoCosh b) = (b ^ m + (-b) ^ m) / (m.factorial : ℚ) := by
  simp [twoCosh, coeff_rescale, coeff_exp]
  ring

lemma constantCoeff_hSeries (k : ℕ) : constantCoeff (hSeries k) = 2 * k := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [hSeries, coeff_twoCosh, map_sum]
  ring

/-- `h` is an even power series. -/
lemma rescale_neg_one_hSeries (k : ℕ) : rescale (-1 : ℚ) (hSeries k) = hSeries k := by
  ext m
  simp only [hSeries, map_sum, coeff_rescale, coeff_twoCosh]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases Nat.even_or_odd m with hm | hm
  · rw [hm.neg_one_pow, one_mul]
  · rw [hm.neg_one_pow, hm.neg_pow]; ring

/-- The odd coefficients of `h^i` vanish. -/
lemma coeff_hSeries_pow_odd (k i m : ℕ) (hm : Odd m) : coeff m (hSeries k ^ i) = 0 := by
  have h := congrArg (coeff m) (congrArg (· ^ i) (rescale_neg_one_hSeries k))
  simp only [← map_pow, coeff_rescale, hm.neg_one_pow] at h
  linarith

/-- **The odd coefficients `d_{2j+1}(q,k)` vanish**, so `f(x) = ∑_j d_{2j}(q,k) x^{2j}`
(`paper.tex`, Theorem `thm:main`). -/
theorem dSeries_odd (k m : ℕ) (hm : Odd m) : dSeries k m = 0 := by
  ext i
  simp [dSeries, coeff_hSeries_pow_odd k i m hm]

/-- **`d_0(q,k) = ln(2qk + 1)`** (`paper.tex`, display after Theorem `thm:main`). -/
theorem dSeries_zero (k : ℕ) : dSeries k 0 = logOneAdd (2 * k) := by
  ext i
  simp [dSeries, logOneAdd, coeff_zero_eq_constantCoeff, constantCoeff_hSeries]

/-- Derivative of a power: `D(F^{n+1}) = (n+1) F^n DF`. -/
lemma derivativeFun_pow_succ' (F : PowerSeries ℚ) (n : ℕ) :
    derivativeFun (F ^ (n + 1)) = C ((n : ℚ) + 1) * (F ^ n * derivativeFun F) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, derivativeFun_mul, ih, smul_eq_mul, smul_eq_mul]
    simp only [map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
    ring

/-- **The differential equation `g'(x) = g(x) f'(x)`** satisfied by
`f = ln g`, `g = 1 + 2q ∑_{b=1}^k cosh(bx)` (`paper.tex`, Section 3, proof of
Theorem `thm:main`); derivatives are taken with respect to `x`. -/
theorem derivativeFun_gSeries (k : ℕ) :
    derivativeFun (gSeries k) = gSeries k * derivativeFun (fSeries k) := by
  set h := hSeries k with hh
  have hcg : ∀ m, coeff m (gSeries k) = (if m = 0 then 1 else 0) + X * C (coeff m h) := by
    intro m
    simp [gSeries, coeff_one, coeff_C_mul, coeff_map, h]
  have hnat : ∀ (x : PowerSeries ℚ) (m : ℕ), x * ((m : PowerSeries ℚ) + 1) =
      C ((m : ℚ) + 1) * x := by
    intro x m; rw [mul_comm]; simp [map_add, map_natCast]
  have hDcoeff : ∀ (F G : PowerSeries ℚ) (m : ℕ),
      ∑ p ∈ antidiagonal m, coeff p.1 F * (coeff (p.2 + 1) G * ((p.2 : ℚ) + 1)) =
        coeff m (F * derivativeFun G) := by
    intro F G m
    rw [coeff_mul]
    exact Finset.sum_congr rfl fun p _ => by rw [coeff_derivativeFun]
  ext m : 1
  have L : coeff m (derivativeFun (gSeries k)) = X * C (coeff (m + 1) h * ((m : ℚ) + 1)) := by
    rw [coeff_derivativeFun, hcg, if_neg (Nat.succ_ne_zero m), zero_add, hnat, map_mul]; ring
  have Rr : coeff m (gSeries k * derivativeFun (fSeries k)) =
      C ((m : ℚ) + 1) * dSeries k (m + 1) +
        X * ∑ p ∈ antidiagonal m, C (coeff p.1 h * ((p.2 : ℚ) + 1)) * dSeries k (p.2 + 1) := by
    rw [PowerSeries.coeff_mul (φ := gSeries k)]
    simp only [hcg, coeff_derivativeFun, fSeries, coeff_mk, add_mul, Finset.sum_add_distrib,
      ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (0, m), if_pos rfl, Finset.mul_sum]
    · congr 1
      · rw [hnat]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [hnat, map_mul]; ring
    · intro b hb hne
      rw [if_neg]
      intro h0; apply hne
      have := mem_antidiagonal.1 hb
      ext <;> simp_all
    · intro hn; exact absurd (mem_antidiagonal.2 (by simp)) hn
  rw [L, Rr]
  ext a
  rcases a with _ | a
  · simp [dSeries]
  rw [coeff_succ_X_mul, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_C, map_sum]
  simp only [coeff_C_mul, dSeries, coeff_mk, if_neg (Nat.succ_ne_zero a)]
  have P1 : coeff (m + 1) (h ^ (a + 1)) * ((m : ℚ) + 1) =
      ((a : ℚ) + 1) * coeff m (h ^ a * derivativeFun h) := by
    rw [← coeff_derivativeFun, derivativeFun_pow_succ', coeff_C_mul]
  rcases a with _ | a
  · simp only [pow_zero, if_true, mul_zero, Finset.sum_const_zero, add_zero]
    rw [← coeff_derivativeFun]
    simp at P1 ⊢
    rw [← P1, ← hh]; ring
  · simp only [← hh, if_neg (Nat.succ_ne_zero a)]
    have P2 : ∑ p ∈ antidiagonal m, coeff p.1 h * ((p.2 : ℚ) + 1) *
        ((-1) ^ (a + 1 + 1) / ((a + 1 : ℕ) : ℚ) * coeff (p.2 + 1) (h ^ (a + 1))) =
        (-1) ^ (a + 1 + 1) * coeff m (h ^ (a + 1) * derivativeFun h) := by
      rw [show (∑ p ∈ antidiagonal m, coeff p.1 h * ((p.2 : ℚ) + 1) *
          ((-1) ^ (a + 1 + 1) / ((a + 1 : ℕ) : ℚ) * coeff (p.2 + 1) (h ^ (a + 1)))) =
          (-1) ^ (a + 1 + 1) / ((a + 1 : ℕ) : ℚ) *
            ∑ p ∈ antidiagonal m, coeff p.1 h * (coeff (p.2 + 1) (h ^ (a + 1)) * ((p.2 : ℚ) + 1))
          by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring]
      rw [hDcoeff, derivativeFun_pow_succ', mul_left_comm, coeff_C_mul, ← mul_assoc h, ← pow_succ']
      field_simp
      push_cast; ring
    rw [P2]
    have e : ((m : ℚ) + 1) * ((-1) ^ (a + 1 + 1 + 1) / ((a + 1 + 1 : ℕ) : ℚ) *
        coeff (m + 1) (h ^ (a + 1 + 1))) =
        (-1) ^ (a + 1 + 1 + 1) * coeff m (h ^ (a + 1) * derivativeFun h) := by
      rw [show ((m : ℚ) + 1) * ((-1) ^ (a + 1 + 1 + 1) / ((a + 1 + 1 : ℕ) : ℚ) *
        coeff (m + 1) (h ^ (a + 1 + 1))) = (-1) ^ (a + 1 + 1 + 1) / ((a + 1 + 1 : ℕ) : ℚ) *
        (coeff (m + 1) (h ^ (a + 1 + 1)) * ((m : ℚ) + 1)) by ring, P1]
      push_cast
      field_simp
    rw [e, pow_succ _ (a + 1 + 1)]
    ring

end LatticeTiling
