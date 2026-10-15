import RequestProject.Ex4_3_6_Examples

/-!
# Explicit data of Examples `ex:t6k1p5`, `ex:t3k2p5`, `ex:t4k3p11`

`paper.tex`, Section 4. For each example we verify the closed form of `|𝓑(n,t,k,k)|` and the
closed forms `A(n), B(n), C(n)` (resp. `A_λ(n)`) of the coefficients `c_λ` of the expansion
`Q^r_{𝓑(n,t,k,k)}(X) = ∑_{λ ⊢ r} c_λ ∏_i s_{2λ_i}(X)` (equation `eq:defclambda`), as identities
valid for every `n`. The partition `λ` is written `partOf r [λ_1, …, λ_ℓ] _ _`.

The finitely many weights `w_j(λ)` (with `c_λ = ∑_j w_j(λ) |𝓑(n,t-j,k,k)|`) are evaluated with
`native_decide`; this file is not a `module`, so that the evaluation can use compiled code.
-/

open Finset Polynomial

namespace LatticeTiling

set_option linter.style.nativeDecide false

/-! ### Example `ex:t6k1p5` -/

/-- **Example `ex:t6k1p5`** (`paper.tex`, Section 4): the size of the ball is
`|𝓑(n,6,1,1)| = ∑_{i=0}^{6} 2^i \binom{n}{i} = 4/45n^6 - 16/15n^5 + 50/9n^4 - 40/3n^3 + 736/45n^2 - 28/5n + 1`. -/
theorem card_ball_t6k1 (n : ℕ) :
    ((ball n 6 1 1).card : ℚ) = (4/45) * (n : ℚ) ^ 6 - (16/15) * (n : ℚ) ^ 5 + (50/9) * (n : ℚ) ^ 4 - (40/3) * (n : ℚ) ^ 3 + (736/45) * (n : ℚ) ^ 2 - (28/5) * (n : ℚ) + 1 := by
  rw [card_ball_eq_bsize]
  simp only [bsize_cast, sum_range_succ, sum_range_zero, descPochhammer_succ_right,
    descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast, eval_one, Nat.factorial]
  push_cast
  ring

/-- **Example `ex:t6k1p5`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^1_{𝓑(n,6,1,1)}(X)` (equation `eq:defclambda`) for `λ = (1)` is
`A(n) = 8/15n^5 - 20/3n^4 + 104/3n^3 - 256/3n^2 + 504/5n - 42`. -/
theorem cLambda_t6k1_A (n : ℕ) :
    (cLambda n 6 1 1 (partOf 1 [1] (by decide) (by decide)) : ℚ) = (8/15) * (n : ℚ) ^ 5 - (20/3) * (n : ℚ) ^ 4 + (104/3) * (n : ℚ) ^ 3 - (256/3) * (n : ℚ) ^ 2 + (504/5) * (n : ℚ) - 42 := by
  have hw : cWeightP 1 1 (partOf 1 [1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 1 1 (partOf 1 [1] (by decide) (by decide)) 1 = 2 ∧
      cWeightP 1 1 (partOf 1 [1] (by decide) (by decide)) 2 = -4 ∧
      cWeightP 1 1 (partOf 1 [1] (by decide) (by decide)) 3 = 8 ∧
      cWeightP 1 1 (partOf 1 [1] (by decide) (by decide)) 4 = -16 ∧
      cWeightP 1 1 (partOf 1 [1] (by decide) (by decide)) 5 = 32 ∧
      cWeightP 1 1 (partOf 1 [1] (by decide) (by decide)) 6 = -64 := by native_decide
  rw [cLambda_cast_eq_sum]
  simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
    descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
    eval_one, Nat.factorial]
  push_cast
  ring

/-- **Example `ex:t6k1p5`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^2_{𝓑(n,6,1,1)}(X)` (equation `eq:defclambda`) for `λ = (2)` is
`B(n) = 8/15n^5 - 44/3n^4 + 392/3n^3 - 1600/3n^2 + 5064/5n - 726`. -/
theorem cLambda_t6k1_B (n : ℕ) :
    (cLambda n 6 1 2 (partOf 2 [2] (by decide) (by decide)) : ℚ) = (8/15) * (n : ℚ) ^ 5 - (44/3) * (n : ℚ) ^ 4 + (392/3) * (n : ℚ) ^ 3 - (1600/3) * (n : ℚ) ^ 2 + (5064/5) * (n : ℚ) - 726 := by
  have hw : cWeightP 1 2 (partOf 2 [2] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 1 2 (partOf 2 [2] (by decide) (by decide)) 1 = 2 ∧
      cWeightP 1 2 (partOf 2 [2] (by decide) (by decide)) 2 = -16 ∧
      cWeightP 1 2 (partOf 2 [2] (by decide) (by decide)) 3 = 56 ∧
      cWeightP 1 2 (partOf 2 [2] (by decide) (by decide)) 4 = -160 ∧
      cWeightP 1 2 (partOf 2 [2] (by decide) (by decide)) 5 = 416 ∧
      cWeightP 1 2 (partOf 2 [2] (by decide) (by decide)) 6 = -1024 := by native_decide
  rw [cLambda_cast_eq_sum]
  simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
    descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
    eval_one, Nat.factorial]
  push_cast
  ring

/-- **Example `ex:t6k1p5`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^2_{𝓑(n,6,1,1)}(X)` (equation `eq:defclambda`) for `λ = (1,1)` is
`C(n) = 8n^4 - 96n^3 + 448n^2 - 912n + 684`. -/
theorem cLambda_t6k1_C (n : ℕ) :
    cLambda n 6 1 2 (partOf 2 [1, 1] (by decide) (by decide)) = 8 * (n : ℤ) ^ 4 - 96 * (n : ℤ) ^ 3 + 448 * (n : ℤ) ^ 2 - 912 * (n : ℤ) + 684 := by
  have hw : cWeightP 1 2 (partOf 2 [1, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 1 2 (partOf 2 [1, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 1 2 (partOf 2 [1, 1] (by decide) (by decide)) 2 = 12 ∧
      cWeightP 1 2 (partOf 2 [1, 1] (by decide) (by decide)) 3 = -48 ∧
      cWeightP 1 2 (partOf 2 [1, 1] (by decide) (by decide)) 4 = 144 ∧
      cWeightP 1 2 (partOf 2 [1, 1] (by decide) (by decide)) 5 = -384 ∧
      cWeightP 1 2 (partOf 2 [1, 1] (by decide) (by decide)) 6 = 960 := by native_decide
  have h : (cLambda n 6 1 2 (partOf 2 [1, 1] (by decide) (by decide)) : ℚ) = 8 * (n : ℚ) ^ 4 - 96 * (n : ℚ) ^ 3 + 448 * (n : ℚ) ^ 2 - 912 * (n : ℚ) + 684 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-! ### Example `ex:t3k2p5` -/

/-- **Example `ex:t3k2p5`** (`paper.tex`, Section 4): the size of the ball is
`|𝓑(n,3,2,2)| = ∑_{i=0}^{3} 4^i \binom{n}{i} = 32/3n^3 - 24n^2 + 52/3n + 1`. -/
theorem card_ball_t3k2 (n : ℕ) :
    ((ball n 3 2 2).card : ℚ) = (32/3) * (n : ℚ) ^ 3 - 24 * (n : ℚ) ^ 2 + (52/3) * (n : ℚ) + 1 := by
  rw [card_ball_eq_bsize]
  simp only [bsize_cast, sum_range_succ, sum_range_zero, descPochhammer_succ_right,
    descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast, eval_one, Nat.factorial]
  push_cast
  ring

/-- **Example `ex:t3k2p5`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^1_{𝓑(n,3,2,2)}(X)` (equation `eq:defclambda`) for `λ = (1)` is
`A(n) = 80n^2 - 200n + 130`. -/
theorem cLambda_t3k2_A (n : ℕ) :
    cLambda n 3 2 1 (partOf 1 [1] (by decide) (by decide)) = 80 * (n : ℤ) ^ 2 - 200 * (n : ℤ) + 130 := by
  have hw : cWeightP 2 1 (partOf 1 [1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 2 1 (partOf 1 [1] (by decide) (by decide)) 1 = 10 ∧
      cWeightP 2 1 (partOf 1 [1] (by decide) (by decide)) 2 = -40 ∧
      cWeightP 2 1 (partOf 1 [1] (by decide) (by decide)) 3 = 160 := by native_decide
  have h : (cLambda n 3 2 1 (partOf 1 [1] (by decide) (by decide)) : ℚ) = 80 * (n : ℚ) ^ 2 - 200 * (n : ℚ) + 130 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t3k2p5`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^2_{𝓑(n,3,2,2)}(X)` (equation `eq:defclambda`) for `λ = (2)` is
`B(n) = 272n^2 - 1880n + 2542`. -/
theorem cLambda_t3k2_B (n : ℕ) :
    cLambda n 3 2 2 (partOf 2 [2] (by decide) (by decide)) = 272 * (n : ℤ) ^ 2 - 1880 * (n : ℤ) + 2542 := by
  have hw : cWeightP 2 2 (partOf 2 [2] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 2 2 (partOf 2 [2] (by decide) (by decide)) 1 = 34 ∧
      cWeightP 2 2 (partOf 2 [2] (by decide) (by decide)) 2 = -436 ∧
      cWeightP 2 2 (partOf 2 [2] (by decide) (by decide)) 3 = 2944 := by native_decide
  have h : (cLambda n 3 2 2 (partOf 2 [2] (by decide) (by decide)) : ℚ) = 272 * (n : ℚ) ^ 2 - 1880 * (n : ℚ) + 2542 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t3k2p5`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^2_{𝓑(n,3,2,2)}(X)` (equation `eq:defclambda`) for `λ = (1,1)` is
`C(n) = 1200n - 2100`. -/
theorem cLambda_t3k2_C (n : ℕ) :
    cLambda n 3 2 2 (partOf 2 [1, 1] (by decide) (by decide)) = 1200 * (n : ℤ) - 2100 := by
  have hw : cWeightP 2 2 (partOf 2 [1, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 2 2 (partOf 2 [1, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 2 2 (partOf 2 [1, 1] (by decide) (by decide)) 2 = 300 ∧
      cWeightP 2 2 (partOf 2 [1, 1] (by decide) (by decide)) 3 = -2400 := by native_decide
  have h : (cLambda n 3 2 2 (partOf 2 [1, 1] (by decide) (by decide)) : ℚ) = 1200 * (n : ℚ) - 2100 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-! ### Example `ex:t4k3p11` -/

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the size of the ball is
`|𝓑(n,4,3,3)| = ∑_{i=0}^{4} 6^i \binom{n}{i} = 54n^4 - 288n^3 + 504n^2 - 264n + 1`. -/
theorem card_ball_t4k3 (n : ℕ) :
    ((ball n 4 3 3).card : ℚ) = 54 * (n : ℚ) ^ 4 - 288 * (n : ℚ) ^ 3 + 504 * (n : ℚ) ^ 2 - 264 * (n : ℚ) + 1 := by
  rw [card_ball_eq_bsize]
  simp only [bsize_cast, sum_range_succ, sum_range_zero, descPochhammer_succ_right,
    descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast, eval_one, Nat.factorial]
  push_cast
  ring

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^1_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (1)` is
`A_{1}(n) = 1008n^3 - 5544n^2 + 9744n - 5180`. -/
theorem cLambda_t4k3_A_1 (n : ℕ) :
    cLambda n 4 3 1 (partOf 1 [1] (by decide) (by decide)) = 1008 * (n : ℤ) ^ 3 - 5544 * (n : ℤ) ^ 2 + 9744 * (n : ℤ) - 5180 := by
  have hw : cWeightP 3 1 (partOf 1 [1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 1 (partOf 1 [1] (by decide) (by decide)) 1 = 28 ∧
      cWeightP 3 1 (partOf 1 [1] (by decide) (by decide)) 2 = -168 ∧
      cWeightP 3 1 (partOf 1 [1] (by decide) (by decide)) 3 = 1008 ∧
      cWeightP 3 1 (partOf 1 [1] (by decide) (by decide)) 4 = -6048 := by native_decide
  have h : (cLambda n 4 3 1 (partOf 1 [1] (by decide) (by decide)) : ℚ) = 1008 * (n : ℚ) ^ 3 - 5544 * (n : ℚ) ^ 2 + 9744 * (n : ℚ) - 5180 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^2_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (2)` is
`A_{2}(n) = 7056n^3 - 81144n^2 + 265776n - 264404`. -/
theorem cLambda_t4k3_A_2 (n : ℕ) :
    cLambda n 4 3 2 (partOf 2 [2] (by decide) (by decide)) = 7056 * (n : ℤ) ^ 3 - 81144 * (n : ℤ) ^ 2 + 265776 * (n : ℤ) - 264404 := by
  have hw : cWeightP 3 2 (partOf 2 [2] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 2 (partOf 2 [2] (by decide) (by decide)) 1 = 196 ∧
      cWeightP 3 2 (partOf 2 [2] (by decide) (by decide)) 2 = -3528 ∧
      cWeightP 3 2 (partOf 2 [2] (by decide) (by decide)) 3 = 35280 ∧
      cWeightP 3 2 (partOf 2 [2] (by decide) (by decide)) 4 = -296352 := by native_decide
  have h : (cLambda n 4 3 2 (partOf 2 [2] (by decide) (by decide)) : ℚ) = 7056 * (n : ℚ) ^ 3 - 81144 * (n : ℚ) ^ 2 + 265776 * (n : ℚ) - 264404 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^2_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (1,1)` is
`A_{1,1}(n) = 42336n^2 - 197568n + 228144`. -/
theorem cLambda_t4k3_A_1_1 (n : ℕ) :
    cLambda n 4 3 2 (partOf 2 [1, 1] (by decide) (by decide)) = 42336 * (n : ℤ) ^ 2 - 197568 * (n : ℤ) + 228144 := by
  have hw : cWeightP 3 2 (partOf 2 [1, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 2 (partOf 2 [1, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 2 (partOf 2 [1, 1] (by decide) (by decide)) 2 = 2352 ∧
      cWeightP 3 2 (partOf 2 [1, 1] (by decide) (by decide)) 3 = -28224 ∧
      cWeightP 3 2 (partOf 2 [1, 1] (by decide) (by decide)) 4 = 254016 := by native_decide
  have h : (cLambda n 4 3 2 (partOf 2 [1, 1] (by decide) (by decide)) : ℚ) = 42336 * (n : ℚ) ^ 2 - 197568 * (n : ℚ) + 228144 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^3_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (3)` is
`A_{3}(n) = 57168n^3 - 1796184n^2 + 11418864n - 19474340`. -/
theorem cLambda_t4k3_A_3 (n : ℕ) :
    cLambda n 4 3 3 (partOf 3 [3] (by decide) (by decide)) = 57168 * (n : ℤ) ^ 3 - 1796184 * (n : ℤ) ^ 2 + 11418864 * (n : ℤ) - 19474340 := by
  have hw : cWeightP 3 3 (partOf 3 [3] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 3 (partOf 3 [3] (by decide) (by decide)) 1 = 1588 ∧
      cWeightP 3 3 (partOf 3 [3] (by decide) (by decide)) 2 = -91848 ∧
      cWeightP 3 3 (partOf 3 [3] (by decide) (by decide)) 3 = 1703568 ∧
      cWeightP 3 3 (partOf 3 [3] (by decide) (by decide)) 4 = -21087648 := by native_decide
  have h : (cLambda n 4 3 3 (partOf 3 [3] (by decide) (by decide)) : ℚ) = 57168 * (n : ℚ) ^ 3 - 1796184 * (n : ℚ) ^ 2 + 11418864 * (n : ℚ) - 19474340 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^3_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (2,1)` is
`A_{2,1}(n) = 1481760n^2 - 12841920n + 24778320`. -/
theorem cLambda_t4k3_A_2_1 (n : ℕ) :
    cLambda n 4 3 3 (partOf 3 [2, 1] (by decide) (by decide)) = 1481760 * (n : ℤ) ^ 2 - 12841920 * (n : ℤ) + 24778320 := by
  have hw : cWeightP 3 3 (partOf 3 [2, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 3 (partOf 3 [2, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 3 (partOf 3 [2, 1] (by decide) (by decide)) 2 = 82320 ∧
      cWeightP 3 3 (partOf 3 [2, 1] (by decide) (by decide)) 3 = -1975680 ∧
      cWeightP 3 3 (partOf 3 [2, 1] (by decide) (by decide)) 4 = 26671680 := by native_decide
  have h : (cLambda n 4 3 3 (partOf 3 [2, 1] (by decide) (by decide)) : ℚ) = 1481760 * (n : ℚ) ^ 2 - 12841920 * (n : ℚ) + 24778320 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^3_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (1,1,1)` is
`A_{1,1,1}(n) = 1975680n - 5597760`. -/
theorem cLambda_t4k3_A_1_1_1 (n : ℕ) :
    cLambda n 4 3 3 (partOf 3 [1, 1, 1] (by decide) (by decide)) = 1975680 * (n : ℤ) - 5597760 := by
  have hw : cWeightP 3 3 (partOf 3 [1, 1, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 3 (partOf 3 [1, 1, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 3 (partOf 3 [1, 1, 1] (by decide) (by decide)) 2 = 0 ∧
      cWeightP 3 3 (partOf 3 [1, 1, 1] (by decide) (by decide)) 3 = 329280 ∧
      cWeightP 3 3 (partOf 3 [1, 1, 1] (by decide) (by decide)) 4 = -5927040 := by native_decide
  have h : (cLambda n 4 3 3 (partOf 3 [1, 1, 1] (by decide) (by decide)) : ℚ) = 1975680 * (n : ℚ) - 5597760 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^4_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (4)` is
`A_{4}(n) = 490896n^3 - 49311864n^2 + 609500976n - 1738103444`. -/
theorem cLambda_t4k3_A_4 (n : ℕ) :
    cLambda n 4 3 4 (partOf 4 [4] (by decide) (by decide)) = 490896 * (n : ℤ) ^ 3 - 49311864 * (n : ℤ) ^ 2 + 609500976 * (n : ℤ) - 1738103444 := by
  have hw : cWeightP 3 4 (partOf 4 [4] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 4 (partOf 4 [4] (by decide) (by decide)) 1 = 13636 ∧
      cWeightP 3 4 (partOf 4 [4] (by decide) (by decide)) 2 = -2671368 ∧
      cWeightP 3 4 (partOf 4 [4] (by decide) (by decide)) 3 = 96104400 ∧
      cWeightP 3 4 (partOf 4 [4] (by decide) (by decide)) 4 = -1831550112 := by native_decide
  have h : (cLambda n 4 3 4 (partOf 4 [4] (by decide) (by decide)) : ℚ) = 490896 * (n : ℚ) ^ 3 - 49311864 * (n : ℚ) ^ 2 + 609500976 * (n : ℚ) - 1738103444 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^4_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (3,1)` is
`A_{3,1}(n) = 22409856n^2 - 491812608n + 1734236224`. -/
theorem cLambda_t4k3_A_3_1 (n : ℕ) :
    cLambda n 4 3 4 (partOf 4 [3, 1] (by decide) (by decide)) = 22409856 * (n : ℤ) ^ 2 - 491812608 * (n : ℤ) + 1734236224 := by
  have hw : cWeightP 3 4 (partOf 4 [3, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 4 (partOf 4 [3, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 4 (partOf 4 [3, 1] (by decide) (by decide)) 2 = 1244992 ∧
      cWeightP 3 4 (partOf 4 [3, 1] (by decide) (by decide)) 3 = -79478784 ∧
      cWeightP 3 4 (partOf 4 [3, 1] (by decide) (by decide)) 4 = 1812470016 := by native_decide
  have h : (cLambda n 4 3 4 (partOf 4 [3, 1] (by decide) (by decide)) : ℚ) = 22409856 * (n : ℚ) ^ 2 - 491812608 * (n : ℚ) + 1734236224 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^4_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (2,2)` is
`A_{2,2}(n) = 24202080n^2 - 306559680n + 872619440`. -/
theorem cLambda_t4k3_A_2_2 (n : ℕ) :
    cLambda n 4 3 4 (partOf 4 [2, 2] (by decide) (by decide)) = 24202080 * (n : ℤ) ^ 2 - 306559680 * (n : ℤ) + 872619440 := by
  have hw : cWeightP 3 4 (partOf 4 [2, 2] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 4 (partOf 4 [2, 2] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 4 (partOf 4 [2, 2] (by decide) (by decide)) 2 = 1344560 ∧
      cWeightP 3 4 (partOf 4 [2, 2] (by decide) (by decide)) 3 = -48404160 ∧
      cWeightP 3 4 (partOf 4 [2, 2] (by decide) (by decide)) 4 = 919679040 := by native_decide
  have h : (cLambda n 4 3 4 (partOf 4 [2, 2] (by decide) (by decide)) : ℚ) = 24202080 * (n : ℚ) ^ 2 - 306559680 * (n : ℚ) + 872619440 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^4_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (2,1,1)` is
`A_{2,1,1}(n) = 193616640n - 935813760`. -/
theorem cLambda_t4k3_A_2_1_1 (n : ℕ) :
    cLambda n 4 3 4 (partOf 4 [2, 1, 1] (by decide) (by decide)) = 193616640 * (n : ℤ) - 935813760 := by
  have hw : cWeightP 3 4 (partOf 4 [2, 1, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 4 (partOf 4 [2, 1, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 4 (partOf 4 [2, 1, 1] (by decide) (by decide)) 2 = 0 ∧
      cWeightP 3 4 (partOf 4 [2, 1, 1] (by decide) (by decide)) 3 = 32269440 ∧
      cWeightP 3 4 (partOf 4 [2, 1, 1] (by decide) (by decide)) 4 = -968083200 := by native_decide
  have h : (cLambda n 4 3 4 (partOf 4 [2, 1, 1] (by decide) (by decide)) : ℚ) = 193616640 * (n : ℚ) - 935813760 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^4_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (1,1,1,1)` is
`A_{1,1,1,1}(n) = 64538880`. -/
theorem cLambda_t4k3_A_1_1_1_1 (n : ℕ) :
    cLambda n 4 3 4 (partOf 4 [1, 1, 1, 1] (by decide) (by decide)) = 64538880 := by
  have hw : cWeightP 3 4 (partOf 4 [1, 1, 1, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 4 (partOf 4 [1, 1, 1, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 4 (partOf 4 [1, 1, 1, 1] (by decide) (by decide)) 2 = 0 ∧
      cWeightP 3 4 (partOf 4 [1, 1, 1, 1] (by decide) (by decide)) 3 = 0 ∧
      cWeightP 3 4 (partOf 4 [1, 1, 1, 1] (by decide) (by decide)) 4 = 64538880 := by native_decide
  have h : (cLambda n 4 3 4 (partOf 4 [1, 1, 1, 1] (by decide) (by decide)) : ℚ) = 64538880 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^5_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (5)` is
`A_{5}(n) = 4325328n^3 - 1509571224n^2 + 36717347184n - 173616608900`. -/
theorem cLambda_t4k3_A_5 (n : ℕ) :
    cLambda n 4 3 5 (partOf 5 [5] (by decide) (by decide)) = 4325328 * (n : ℤ) ^ 3 - 1509571224 * (n : ℤ) ^ 2 + 36717347184 * (n : ℤ) - 173616608900 := by
  have hw : cWeightP 3 5 (partOf 5 [5] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 5 (partOf 5 [5] (by decide) (by decide)) 1 = 120148 ∧
      cWeightP 3 5 (partOf 5 [5] (by decide) (by decide)) 2 = -83264328 ∧
      cWeightP 3 5 (partOf 5 [5] (by decide) (by decide)) 3 = 5951827728 ∧
      cWeightP 3 5 (partOf 5 [5] (by decide) (by decide)) 4 = -179485292448 := by native_decide
  have h : (cLambda n 4 3 5 (partOf 5 [5] (by decide) (by decide)) : ℚ) = 4325328 * (n : ℚ) ^ 3 - 1509571224 * (n : ℚ) ^ 2 + 36717347184 * (n : ℚ) - 173616608900 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^5_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (4,1)` is
`A_{4,1}(n) = 309264480n^2 - 21020247360n + 138453784560`. -/
theorem cLambda_t4k3_A_4_1 (n : ℕ) :
    cLambda n 4 3 5 (partOf 5 [4, 1] (by decide) (by decide)) = 309264480 * (n : ℤ) ^ 2 - 21020247360 * (n : ℤ) + 138453784560 := by
  have hw : cWeightP 3 5 (partOf 5 [4, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 5 (partOf 5 [4, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 5 (partOf 5 [4, 1] (by decide) (by decide)) 2 = 17181360 ∧
      cWeightP 3 5 (partOf 5 [4, 1] (by decide) (by decide)) 3 = -3469011840 ∧
      cWeightP 3 5 (partOf 5 [4, 1] (by decide) (by decide)) 4 = 141905615040 := by native_decide
  have h : (cLambda n 4 3 5 (partOf 5 [4, 1] (by decide) (by decide)) : ℚ) = 309264480 * (n : ℚ) ^ 2 - 21020247360 * (n : ℚ) + 138453784560 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^5_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (3,2)` is
`A_{3,2}(n) = 1176517440n^2 - 30526231680n + 145040760480`. -/
theorem cLambda_t4k3_A_3_2 (n : ℕ) :
    cLambda n 4 3 5 (partOf 5 [3, 2] (by decide) (by decide)) = 1176517440 * (n : ℤ) ^ 2 - 30526231680 * (n : ℤ) + 145040760480 := by
  have hw : cWeightP 3 5 (partOf 5 [3, 2] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 5 (partOf 5 [3, 2] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 5 (partOf 5 [3, 2] (by decide) (by decide)) 2 = 65362080 ∧
      cWeightP 3 5 (partOf 5 [3, 2] (by decide) (by decide)) 3 = -4956981120 ∧
      cWeightP 3 5 (partOf 5 [3, 2] (by decide) (by decide)) 4 = 149932379520 := by native_decide
  have h : (cLambda n 4 3 5 (partOf 5 [3, 2] (by decide) (by decide)) : ℚ) = 1176517440 * (n : ℚ) ^ 2 - 30526231680 * (n : ℚ) + 145040760480 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^5_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (3,1,1)` is
`A_{3,1,1}(n) = 4706069760n - 53993358720`. -/
theorem cLambda_t4k3_A_3_1_1 (n : ℕ) :
    cLambda n 4 3 5 (partOf 5 [3, 1, 1] (by decide) (by decide)) = 4706069760 * (n : ℤ) - 53993358720 := by
  have hw : cWeightP 3 5 (partOf 5 [3, 1, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 5 (partOf 5 [3, 1, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 5 (partOf 5 [3, 1, 1] (by decide) (by decide)) 2 = 0 ∧
      cWeightP 3 5 (partOf 5 [3, 1, 1] (by decide) (by decide)) 3 = 784344960 ∧
      cWeightP 3 5 (partOf 5 [3, 1, 1] (by decide) (by decide)) 4 = -54777703680 := by native_decide
  have h : (cLambda n 4 3 5 (partOf 5 [3, 1, 1] (by decide) (by decide)) : ℚ) = 4706069760 * (n : ℚ) - 53993358720 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^5_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (2,2,1)` is
`A_{2,2,1}(n) = 10164873600n - 69459969600`. -/
theorem cLambda_t4k3_A_2_2_1 (n : ℕ) :
    cLambda n 4 3 5 (partOf 5 [2, 2, 1] (by decide) (by decide)) = 10164873600 * (n : ℤ) - 69459969600 := by
  have hw : cWeightP 3 5 (partOf 5 [2, 2, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 5 (partOf 5 [2, 2, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 5 (partOf 5 [2, 2, 1] (by decide) (by decide)) 2 = 0 ∧
      cWeightP 3 5 (partOf 5 [2, 2, 1] (by decide) (by decide)) 3 = 1694145600 ∧
      cWeightP 3 5 (partOf 5 [2, 2, 1] (by decide) (by decide)) 4 = -71154115200 := by native_decide
  have h : (cLambda n 4 3 5 (partOf 5 [2, 2, 1] (by decide) (by decide)) : ℚ) = 10164873600 * (n : ℚ) - 69459969600 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^5_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (2,1,1,1)` is
`A_{2,1,1,1}(n) = 13553164800`. -/
theorem cLambda_t4k3_A_2_1_1_1 (n : ℕ) :
    cLambda n 4 3 5 (partOf 5 [2, 1, 1, 1] (by decide) (by decide)) = 13553164800 := by
  have hw : cWeightP 3 5 (partOf 5 [2, 1, 1, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 5 (partOf 5 [2, 1, 1, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 5 (partOf 5 [2, 1, 1, 1] (by decide) (by decide)) 2 = 0 ∧
      cWeightP 3 5 (partOf 5 [2, 1, 1, 1] (by decide) (by decide)) 3 = 0 ∧
      cWeightP 3 5 (partOf 5 [2, 1, 1, 1] (by decide) (by decide)) 4 = 13553164800 := by native_decide
  have h : (cLambda n 4 3 5 (partOf 5 [2, 1, 1, 1] (by decide) (by decide)) : ℚ) = 13553164800 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

/-- **Example `ex:t4k3p11`** (`paper.tex`, Section 4): the coefficient `c_λ` of
`∏_i s_{2λ_i}(X)` in `Q^5_{𝓑(n,4,3,3)}(X)` (equation `eq:defclambda`) for `λ = (1,1,1,1,1)` is
`A_{1,1,1,1,1}(n) = 0`. -/
theorem cLambda_t4k3_A_1_1_1_1_1 (n : ℕ) :
    cLambda n 4 3 5 (partOf 5 [1, 1, 1, 1, 1] (by decide) (by decide)) = 0 := by
  have hw : cWeightP 3 5 (partOf 5 [1, 1, 1, 1, 1] (by decide) (by decide)) 0 = 0 ∧
      cWeightP 3 5 (partOf 5 [1, 1, 1, 1, 1] (by decide) (by decide)) 1 = 0 ∧
      cWeightP 3 5 (partOf 5 [1, 1, 1, 1, 1] (by decide) (by decide)) 2 = 0 ∧
      cWeightP 3 5 (partOf 5 [1, 1, 1, 1, 1] (by decide) (by decide)) 3 = 0 ∧
      cWeightP 3 5 (partOf 5 [1, 1, 1, 1, 1] (by decide) (by decide)) 4 = 0 := by native_decide
  have h : (cLambda n 4 3 5 (partOf 5 [1, 1, 1, 1, 1] (by decide) (by decide)) : ℚ) = 0 := by
    rw [cLambda_cast_eq_sum]
    simp only [sum_range_succ, sum_range_zero, hw, bsize_cast, Nat.reduceSub, Nat.reduceAdd,
      descPochhammer_succ_right, descPochhammer_zero, eval_mul, eval_sub, eval_X, eval_natCast,
      eval_one, Nat.factorial]
    push_cast
    ring
  exact_mod_cast h

end LatticeTiling
