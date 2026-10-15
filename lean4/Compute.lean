module

public import RequestProject.CLambda

/-!
# Computing the coefficients `c_λ`

Explicit, computable expressions for the coefficients of `d_m(q,k)` and for the coefficients
`c_λ` of `eq:defclambda` (`paper.tex`, Theorem `thm:main` "together with the Bell polynomial
expansion"), used to carry out the computations of Examples `ex:t6k1p5`, `ex:t3k2p5`,
`ex:t4k3p11`.
-/

@[expose] public section

open Finset PowerSeries

namespace LatticeTiling

/-- The set `{-k, …, -1, 1, …, k} ⊆ ℤ`. -/
def symSet (k : ℕ) : Finset ℤ := (Icc (-(k : ℤ)) k).erase 0

lemma hSeries_eq_sum_symSet (k : ℕ) :
    hSeries k = ∑ β ∈ symSet k, rescale (β : ℚ) (exp ℚ) := by
  have h := sum_Icc_neg_eq (fun β : ℤ => rescale (β : ℚ) (exp ℚ)) k
  rw [← Finset.add_sum_erase _ _ (by simp : (0 : ℤ) ∈ Icc (-(k : ℤ)) k)] at h
  have h2 := add_left_cancel h
  rw [symSet, h2, hSeries]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [twoCosh]

/-- An explicit formula for the coefficients of `h(x)^i`:
`[x^m] h(x)^i = ∑_{β ∈ ({±1,…,±k})^i} (β_1 + ⋯ + β_i)^m / m!`. -/
lemma coeff_hSeries_pow (k i m : ℕ) :
    coeff m (hSeries k ^ i) = (∑ β ∈ Fintype.piFinset (fun _ : Fin i => symSet k),
      ((∑ j, β j : ℤ) : ℚ) ^ m) / (m.factorial : ℚ) := by
  rw [hSeries_eq_sum_symSet, ← Fin.prod_const, Finset.prod_univ_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [prod_rescale_exp, coeff_rescale, coeff_exp]
  simp [div_eq_mul_inv]

/-- The coefficient of `q^i` in `d_m(q,k)`, as an explicit (computable) rational number. -/
def dCoeff (k m i : ℕ) : ℚ :=
  if i = 0 then 0 else (-1) ^ (i + 1) / (i : ℚ) *
    ((∑ β ∈ Fintype.piFinset (fun _ : Fin i => symSet k), ((∑ j, β j : ℤ) : ℚ) ^ m) /
      (m.factorial : ℚ))

lemma coeff_dSeries (k m i : ℕ) : coeff i (dSeries k m) = dCoeff k m i := by
  rw [dSeries, coeff_mk, dCoeff, coeff_hSeries_pow]

/-- `[x^m] h(x)^i`, computed by the recursion `h^{i+1} = h · h^i` (an efficient implementation
of `dCoeff`, see `dCoeff_eq_dCoeffFast`). -/
def hCoeffFast (k : ℕ) : ℕ → ℕ → ℚ
  | 0, m => if m = 0 then 1 else 0
  | i + 1, m => ∑ a ∈ range (m + 1),
      (∑ β ∈ symSet k, (β : ℚ) ^ a) / (a.factorial : ℚ) * hCoeffFast k i (m - a)

lemma coeff_hSeries (k a : ℕ) :
    coeff a (hSeries k) = (∑ β ∈ symSet k, (β : ℚ) ^ a) / (a.factorial : ℚ) := by
  rw [hSeries_eq_sum_symSet, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [coeff_rescale, coeff_exp]
  simp [div_eq_mul_inv]

lemma hCoeffFast_eq (k i m : ℕ) : hCoeffFast k i m = coeff m (hSeries k ^ i) := by
  induction i generalizing m with
  | zero => simp [hCoeffFast, coeff_one]
  | succ i ih =>
    rw [hCoeffFast, pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ih, coeff_hSeries]

/-- Efficient implementation of `dCoeff`. -/
def dCoeffFast (k m i : ℕ) : ℚ :=
  if i = 0 then 0 else (-1) ^ (i + 1) / (i : ℚ) * hCoeffFast k i m

@[csimp] theorem dCoeff_eq_dCoeffFast : @dCoeff = @dCoeffFast := by
  funext k m i
  rw [dCoeff, dCoeffFast, hCoeffFast_eq, coeff_hSeries_pow]

/-- Coefficients of a product of power series given by the lists of their coefficient
functions (truncated convolution). -/
def convCoeff : List (ℕ → ℚ) → ℕ → ℚ
  | [], j => if j = 0 then 1 else 0
  | f :: L, j => ∑ l ∈ range (j + 1), f l * convCoeff L (j - l)

lemma coeff_list_prod (L : List (PowerSeries ℚ)) (j : ℕ) :
    coeff j L.prod = convCoeff (L.map fun F l => coeff l F) j := by
  induction L generalizing j with
  | nil => simp [convCoeff, coeff_one]
  | cons F L ih =>
    rw [List.prod_cons, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      List.map_cons, convCoeff]
    exact Finset.sum_congr rfl fun l _ => by rw [ih]

/-- The size `|𝓑(n,t,k,k)| = ∑_{i=0}^t (2k)^i \binom{n}{i}` as a computable function. -/
def bsize (n t k : ℕ) : ℕ := ∑ i ∈ range (t + 1), (2 * k) ^ i * n.choose i

lemma card_ball_eq_bsize (n t k : ℕ) : (ball n t k k).card = bsize n t k := card_ball n t k

lemma coeff_ball_genFun (n s k : ℕ) :
    coeff s ((1 + C (2 * k : ℚ) * X) ^ n * PowerSeries.mk 1) = (bsize n s k : ℚ) := by
  rw [← card_ball_eq_bsize, card_ball_eq_coeff]

/-- The integer weights `w_j(λ)` such that
`c_λ = ∑_{j=0}^{t} w_j(λ) |𝓑(n, t-j, k, k)|`: `w_j(λ) = (2r)!/∏m_j(λ)! · [q^j] ∏_i d_{2λ_i}(q,k)`.
They are given for a list `L` of the parts of `λ`. -/
def cWeight (k r : ℕ) (L : List ℕ) (mfp : ℕ) (j : ℕ) : ℚ :=
  ((2 * r).factorial : ℚ) / (mfp : ℚ) * convCoeff (L.map fun i l => dCoeff k (2 * i) l) j

/-- The coefficient `c_λ` (Theorem `thm:main`) as an explicit finite sum:
`c_λ = ∑_{j=0}^{t} w_j(λ) |𝓑(n, t-j, k, k)|`. -/
lemma cLambdaQ_eq_sum (n t k r : ℕ) (μ : r.Partition) (L : List ℕ) (hL : μ.parts = (L : Multiset ℕ)) :
    cLambdaQ n t k r μ = ∑ j ∈ range (t + 1),
      cWeight k r L (multFactorialProd μ) j * (bsize n (t - j) k : ℚ) := by
  rw [cLambdaQ, hL, Multiset.map_coe, Multiset.prod_coe, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ t := Nat.lt_succ_iff.1 (mem_range.1 hj)
  rw [show t + 1 - 1 - j = t - j by omega, show t - (t - j) = j by omega, coeff_ball_genFun,
    coeff_list_prod, List.map_map, cWeight]
  simp only [Function.comp_def, coeff_dSeries]
  ring

end LatticeTiling
