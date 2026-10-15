module

public import RequestProject.Thm1_1_QFormula
public import RequestProject.DClosed
public import RequestProject.Thm1_2_Ideal

/-!
# The coefficients `c_λ` are integers

`paper.tex`, Section 1, equation `eq:defclambda`: the Q-polynomial `Q^r_{𝓑(n,t,k,k)}(X)` is a
linear combination `∑_{λ ⊢ r} c_λ ∏_i s_{2λ_i}(X)` of products of power sums, and the `c_λ` are
integers. Theorem `thm:main` gives the explicit value
`c_λ = (2r)!/∏_j m_j(λ)! · [q^t] ( (1+2qk)^n/(1-q) ∏_i d_{2λ_i}(q,k) )`.

We prove integrality via
* the integrality of `m! d_m(q,k) ∈ ℤ⟦q⟧` for `m ≥ 1` (from `g' = g f'`), and
* the divisibility `∏_i (2λ_i)! · ∏_j m_j(λ)! ∣ (2r)!`.
-/

@[expose] public section

open Finset PowerSeries

namespace LatticeTiling

/-! ### Factorial divisibility -/

/-- `(a!)^m · m! ∣ (a m)!` for `a ≥ 1`. -/
lemma factorial_pow_mul_factorial_dvd (a m : ℕ) (ha : 0 < a) :
    a.factorial ^ m * m.factorial ∣ (a * m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    set N := a * (m + 1)
    have hN : N = (N - 1) + 1 := by have : 0 < N := Nat.mul_pos ha (Nat.succ_pos m); omega
    have hch : N.choose a = (m + 1) * (N - 1).choose (a - 1) := by
      have h1 := Nat.add_one_mul_choose_eq (N - 1) (a - 1)
      rw [← hN, Nat.sub_add_cancel ha] at h1
      have h2 : N * (N - 1).choose (a - 1) = a * ((m + 1) * (N - 1).choose (a - 1)) := by
        simp only [N]; ring
      rw [h2, mul_comm (N.choose a)] at h1
      exact (Nat.eq_of_mul_eq_mul_left ha h1).symm
    have hfac : N.factorial = N.choose a * a.factorial * (a * m).factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial (show a ≤ N from Nat.le_mul_of_pos_right a
        (Nat.succ_pos m))]
      congr 2
      simp only [N]; rw [Nat.mul_succ]; omega
    rw [hfac, hch, pow_succ, Nat.factorial_succ]
    obtain ⟨c, hc⟩ := ih
    exact ⟨(N - 1).choose (a - 1) * c, by rw [hc]; ring⟩

/-- `∏_i (2λ_i)! · ∏_j m_j(λ)! ∣ (2r)!` for a partition `λ ⊢ r`. -/
lemma prod_factorial_mul_multFactorialProd_dvd {r : ℕ} (μ : r.Partition) :
    (μ.parts.map fun i => (2 * i).factorial).prod * multFactorialProd μ ∣ (2 * r).factorial := by
  classical
  rw [multFactorialProd, Finset.prod_multiset_map_count, ← Finset.prod_mul_distrib]
  have hsum : 2 * r = ∑ j ∈ μ.parts.toFinset, 2 * j * μ.parts.count j := by
    conv_lhs => rw [← μ.parts_sum]
    rw [Finset.sum_multiset_count, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul]; ring
  rw [hsum]
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun j hj => ?_)
    (Nat.prod_factorial_dvd_factorial_sum _ _)
  exact factorial_pow_mul_factorial_dvd (2 * j) _ (by
    have := μ.parts_pos (Multiset.mem_toFinset.1 hj); omega)

/-! ### Integrality of `m! d_m(q,k)` -/

/-- The subring `ℤ⟦q⟧ ⊆ ℚ⟦q⟧` of power series with integer coefficients. -/
noncomputable def intPS : Subring (PowerSeries ℚ) := (PowerSeries.map (Int.castRingHom ℚ)).range

lemma X_mem_intPS : (X : PowerSeries ℚ) ∈ intPS := ⟨X, by simp⟩

lemma C_intCast_mem_intPS (z : ℤ) : C (z : ℚ) ∈ intPS := ⟨C z, by simp⟩

lemma mk_one_mem_intPS : PowerSeries.mk (1 : ℕ → ℚ) ∈ intPS :=
  ⟨PowerSeries.mk 1, by ext; simp⟩

lemma one_add_mul_X_mul_mk {S : Type*} [CommRing S] (a : S) :
    (1 + C a * X) * PowerSeries.mk (fun i => (-a) ^ i) = 1 := by
  ext m
  rcases m with _ | m
  · simp
  · rw [add_mul, one_mul, mul_assoc, map_add, coeff_C_mul, coeff_succ_X_mul]
    simp [coeff_one, pow_succ]
    ring

lemma factorial_mul_coeff_gSeries_mem (k i : ℕ) :
    (i.factorial : PowerSeries ℚ) * coeff i (gSeries k) ∈ intPS := by
  rw [coeff_gSeries, mul_add]
  refine add_mem (by split_ifs <;> simp [natCast_mem]) ?_
  have e : (i.factorial : ℚ) * coeff i (hSeries k) =
      ((∑ b ∈ Icc 1 k, ((b : ℤ) ^ i + (-(b : ℤ)) ^ i) : ℤ) : ℚ) := by
    simp only [hSeries, map_sum, coeff_twoCosh, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp
  rw [mul_left_comm, show (i.factorial : PowerSeries ℚ) = C (i.factorial : ℚ) by simp, ← map_mul, e]
  exact mul_mem X_mem_intPS (C_intCast_mem_intPS _)

/-- **Integrality of `m! d_m(q,k)`**: for every `m ≥ 1`, `m! · d_m(q,k) ∈ ℤ⟦q⟧`. (This is the
integrality underlying the statement "the `c_λ` are integers" after equation `eq:defclambda` of
`paper.tex`.) -/
theorem factorial_mul_dSeries_mem (k m : ℕ) :
    ((m + 1).factorial : PowerSeries ℚ) * dSeries k (m + 1) ∈ intPS := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  set D : ℕ → PowerSeries ℚ := fun j => (j.factorial : PowerSeries ℚ) * dSeries k j
  set G : ℕ → PowerSeries ℚ := fun i => (i.factorial : PowerSeries ℚ) * coeff i (gSeries k)
  have hode := ode_coeff k m
  have key : G (m + 1) = ∑ i ∈ range (m + 1), ((m.choose i : ℕ) : PowerSeries ℚ) * G i *
      D (m - i + 1) := by
    have := congrArg (fun z => (m.factorial : PowerSeries ℚ) * z) hode
    simp only [Finset.mul_sum] at this
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (m.factorial : PowerSeries ℚ) *
        (coeff i (gSeries k) * (dSeries k (j + 1) * ((j : PowerSeries ℚ) + 1))))] at this
    simp only [G, D]
    rw [Nat.factorial_succ]
    push_cast
    convert this using 1
    · ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hi)
      have hfac := Nat.choose_mul_factorial_mul_factorial hi'
      rw [Nat.factorial_succ]
      have hfac' : ((m.choose i : ℕ) : PowerSeries ℚ) * (i.factorial : PowerSeries ℚ) *
          ((m - i).factorial : PowerSeries ℚ) = (m.factorial : PowerSeries ℚ) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul, hfac]
      rw [← hfac']
      push_cast
      ring
  rw [Finset.sum_range_succ'] at key
  have hg0 : G 0 = 1 + C (2 * k : ℚ) * X := by
    simp only [G, Nat.factorial_zero, Nat.cast_one, one_mul]
    rw [coeff_gSeries, coeff_zero_eq_constantCoeff_apply, constantCoeff_hSeries]
    simp; ring
  have hrest : ∑ i ∈ range m, ((m.choose (i + 1) : ℕ) : PowerSeries ℚ) * G (i + 1) *
      D (m - (i + 1) + 1) ∈ intPS := by
    refine sum_mem fun i hi => mul_mem (mul_mem (natCast_mem _ _)
      (factorial_mul_coeff_gSeries_mem k _)) ?_
    have hi' := mem_range.1 hi
    have := ih (m - (i + 1)) (by omega)
    exact this
  have h0 : (1 + C (2 * k : ℚ) * X) * D (m + 1) ∈ intPS := by
    have e : (1 + C (2 * k : ℚ) * X) * D (m + 1) = G (m + 1) -
        ∑ i ∈ range m, ((m.choose (i + 1) : ℕ) : PowerSeries ℚ) * G (i + 1) *
          D (m - (i + 1) + 1) := by
      rw [key, ← hg0]; simp
    rw [e]
    exact sub_mem (factorial_mul_coeff_gSeries_mem k _) hrest
  have hw : PowerSeries.mk (fun i => (-(2 * k : ℚ)) ^ i) ∈ intPS :=
    ⟨PowerSeries.mk (fun i => (-(2 * k : ℤ)) ^ i), by ext; simp⟩
  have := mul_mem hw h0
  rwa [← mul_assoc, mul_comm (PowerSeries.mk _), one_add_mul_X_mul_mk, one_mul] at this


/-! ### The canonical coefficients `c_λ` -/

/-- **The coefficient `c_λ`** of `eq:defclambda`, as given by Theorem `thm:main`
(`paper.tex`, Section 1): for `λ ⊢ r`,
`c_λ = (2r)!/∏_j m_j(λ)! · [q^t] ( (1+2qk)^n/(1-q) · ∏_{i=1}^{ℓ(λ)} d_{2λ_i}(q,k) )`,
a priori a rational number. -/
noncomputable def cLambdaQ (n t k r : ℕ) (μ : r.Partition) : ℚ :=
  ((2 * r).factorial : ℚ) / (multFactorialProd μ : ℚ) *
    coeff t ((1 + C (2 * k : ℚ) * X) ^ n * PowerSeries.mk 1 *
      (μ.parts.map fun i => dSeries k (2 * i)).prod)

/-- **Equation `eq:defclambda` with the explicit coefficients of Theorem `thm:main`**:
`Q^r_{𝓑(n,t,k,k)}(X) = ∑_{λ ⊢ r} c_λ ∏_{i=1}^{ℓ(λ)} s_{2λ_i}(X)` in `ℚ[X₁,…,Xₙ]`, with
`c_λ = cLambdaQ n t k r λ`. -/
theorem QPoly_ball_eq_sum_cLambdaQ (n t k r : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (QPoly (ball n t k k) r) =
      ∑ μ : r.Partition, MvPolynomial.C (cLambdaQ n t k r μ) *
        (μ.parts.map fun i => powerSum ℚ n (2 * i)).prod := by
  rw [QPoly_ball_formula]
  set Φ := PowerSeries.map (algebraMap ℚ (MvPolynomial (Fin n) ℚ))
  have hprod : ∀ μ : r.Partition, (μ.parts.map fun i => Φ (dSeries k (2 * i)) *
      C (powerSum ℚ n (2 * i))).prod = Φ ((μ.parts.map fun i => dSeries k (2 * i)).prod) *
        C ((μ.parts.map fun i => powerSum ℚ n (2 * i)).prod) := by
    intro μ
    rw [Multiset.prod_map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map,
      Multiset.map_map]
    rfl
  have hU : (1 + C (2 * k : MvPolynomial (Fin n) ℚ) * X) ^ n * PowerSeries.mk 1 =
      Φ ((1 + C (2 * k : ℚ) * X) ^ n * PowerSeries.mk 1) := by
    simp only [Φ, map_mul, map_pow, map_add, map_one, PowerSeries.map_C, PowerSeries.map_X]
    congr 2
  simp_rw [hprod]
  rw [hU, Finset.mul_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [mul_smul_comm, ← mul_assoc, ← map_mul, coeff_smul, PowerSeries.coeff_mul_C, coeff_map,
    MvPolynomial.algebraMap_eq, smul_smul, MvPolynomial.smul_eq_C_mul, ← mul_assoc,
    ← map_mul, cLambdaQ]
  congr 2
  rw [mul_assoc]
  field_simp


lemma factorial_mul_dSeries_two_mul_mem (k i : ℕ) (hi : 1 ≤ i) :
    ((2 * i).factorial : PowerSeries ℚ) * dSeries k (2 * i) ∈ intPS := by
  have := factorial_mul_dSeries_mem k (2 * i - 1)
  rwa [show 2 * i - 1 + 1 = 2 * i by omega] at this

/-- **The `c_λ` are integers** (`paper.tex`, Section 1, sentence after equation
`eq:defclambda`): the coefficient `c_λ = cLambdaQ n t k r λ` given by Theorem `thm:main` is an
integer. -/
theorem cLambdaQ_isInt (n t k r : ℕ) (μ : r.Partition) : ∃ z : ℤ, cLambdaQ n t k r μ = z := by
  obtain ⟨N, hN⟩ := prod_factorial_mul_multFactorialProd_dvd μ
  set P := (μ.parts.map fun i => (2 * i).factorial).prod
  set F : PowerSeries ℚ := (1 + C (2 * k : ℚ) * X) ^ n * PowerSeries.mk 1
  have hF : F ∈ intPS := by
    refine mul_mem (pow_mem (add_mem (one_mem _) (mul_mem ?_ X_mem_intPS)) _) mk_one_mem_intPS
    exact_mod_cast C_intCast_mem_intPS (2 * k)
  have hD : (P : PowerSeries ℚ) * (μ.parts.map fun i => dSeries k (2 * i)).prod =
      (μ.parts.map fun i => ((2 * i).factorial : PowerSeries ℚ) * dSeries k (2 * i)).prod := by
    rw [Multiset.prod_map_mul, Nat.cast_multiset_prod, Multiset.map_map]
    rfl
  have hmem : F * (μ.parts.map fun i => ((2 * i).factorial : PowerSeries ℚ) *
      dSeries k (2 * i)).prod ∈ intPS := by
    refine mul_mem hF (multiset_prod_mem _ fun x hx => ?_)
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hx
    exact factorial_mul_dSeries_two_mul_mem k i (μ.parts_pos hi)
  obtain ⟨Z, hZ⟩ := hmem
  refine ⟨N * coeff (R := ℤ) t Z, ?_⟩
  have hc : coeff t (F * (μ.parts.map fun i => ((2 * i).factorial : PowerSeries ℚ) *
      dSeries k (2 * i)).prod) = (coeff (R := ℤ) t Z : ℚ) := by
    rw [← hZ, coeff_map]; rfl
  rw [← hD, mul_left_comm, show (P : PowerSeries ℚ) = C (P : ℚ) by simp, coeff_C_mul] at hc
  rw [cLambdaQ, hN]
  push_cast
  rw [← hc]
  have hm : (multFactorialProd μ : ℚ) ≠ 0 := by exact_mod_cast (multFactorialProd_pos μ).ne'
  field_simp
  rfl

/-- The integer value of `c_λ` (`paper.tex`, equation `eq:defclambda`). -/
noncomputable def cLambda (n t k r : ℕ) (μ : r.Partition) : ℤ :=
  (cLambdaQ_isInt n t k r μ).choose

lemma cLambda_cast (n t k r : ℕ) (μ : r.Partition) :
    (cLambda n t k r μ : ℚ) = cLambdaQ n t k r μ :=
  (cLambdaQ_isInt n t k r μ).choose_spec.symm

/-- **Equation `eq:defclambda`** (`paper.tex`, Section 1): `Q^r_{𝓑(n,t,k,k)}(X)` is an integer
linear combination of products of power sums,
`Q^r_{𝓑(n,t,k,k)}(X) = ∑_{λ ∈ 𝓟(r)} c_λ ∏_{i=1}^{ℓ(λ)} s_{2λ_i}(X)` in `ℤ[X₁,…,Xₙ]`, with
`c_λ = cLambda n t k r λ ∈ ℤ` (whose rational value is given by Theorem `thm:main`,
`cLambda_cast`). -/
theorem QPoly_ball_eq_sum_cLambda (n t k r : ℕ) :
    QPoly (ball n t k k) r = ∑ μ : r.Partition, MvPolynomial.C (cLambda n t k r μ) *
      (μ.parts.map fun i => powerSum ℤ n (2 * i)).prod := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [QPoly_ball_eq_sum_cLambdaQ, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_mul, MvPolynomial.map_C, map_multiset_prod, Multiset.map_map]
  simp [cLambda_cast, powerSum, MvPolynomial.psum, map_sum]

/-- The canonical coefficients satisfy the hypothesis `IsCLambdaExpansion` of
Theorems `thm:conditionY` and `thm:ideal`. -/
theorem isCLambdaExpansion_cLambda (n t k R : ℕ) :
    IsCLambdaExpansion n t k R (cLambda n t k) :=
  fun r _ _ => QPoly_ball_eq_sum_cLambda n t k r

/-- **Theorem `thm:ideal`** (`paper.tex`, Section 1), with the coefficients `c_λ` of
`eq:defclambda` given explicitly by Theorem `thm:main`: let `p > 2` be a prime, assume
`|𝓑(n,t,k,k)| = pM` with `p ∤ M`, and let `f_r = ∑_{λ ⊢ r} c_λ ∏_i Y_{λ_i} ∈ 𝔽_p[Y_1,…,Y_{(p-1)/2}]`.
If `f_{(p-1)/2} ∈ (f_1, …, f_{(p-1)/2-1})`, then no lattice tiling of `ℤⁿ` by `𝓑(n,t,k,k)`
exists. -/
theorem no_lattice_tiling_of_mem_ideal' (n t k p M : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hcard : (ball n t k k).card = p * M) (hM : ¬ p ∣ M)
    (hmem : fPoly p (cLambda n t k) ((p - 1) / 2) ∈
      Ideal.span (fPoly p (cLambda n t k) '' Set.Ico 1 ((p - 1) / 2))) :
    ¬ HasLatticeTiling (ball n t k k : Set (Fin n → ℤ)) :=
  no_lattice_tiling_of_mem_ideal t k p M hp2 hcard hM _ (isCLambdaExpansion_cLambda n t k _) hmem

end LatticeTiling
