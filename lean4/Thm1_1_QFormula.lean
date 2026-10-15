module

public import RequestProject.DSeries

/-!
# Q-polynomials of symmetric limited magnitude error balls

Formalization of `paper.tex`, Theorem `thm:main` and its proof (Section 3).

Throughout, `A = ℚ[X₁, …, Xₙ]` (`MvPolynomial (Fin n) ℚ`), formal power series in `q` with
coefficients in `A` are elements of `PowerSeries A`, and the generating function `F_n(X,z,q)` is a
power series in `z` with coefficients in `PowerSeries A`.
-/

@[expose] public section

open Finset PowerSeries

namespace LatticeTiling

variable (n : ℕ)

/-- The coefficient map `ℚ⟦q⟧ → A⟦q⟧`. -/
noncomputable abbrev qMap : PowerSeries ℚ →+* PowerSeries (MvPolynomial (Fin n) ℚ) :=
  PowerSeries.map (algebraMap ℚ (MvPolynomial (Fin n) ℚ))

/-- The coefficient map `ℚ⟦q⟧⟦x⟧ → A⟦q⟧⟦z⟧`. -/
noncomputable abbrev zMap :
    PowerSeries (PowerSeries ℚ) →+* PowerSeries (PowerSeries (MvPolynomial (Fin n) ℚ)) :=
  PowerSeries.map (qMap n)

lemma derivativeFun_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (F : PowerSeries R) : derivativeFun (PowerSeries.map φ F) = PowerSeries.map φ (derivativeFun F) := by
  ext m
  simp [coeff_derivativeFun, map_add, map_natCast]

lemma derivativeFun_rescale {R : Type*} [CommSemiring R] (a : R) (F : PowerSeries R) :
    derivativeFun (rescale a F) = C a * rescale a (derivativeFun F) := by
  ext m
  simp only [coeff_derivativeFun, coeff_rescale, coeff_C_mul]
  ring

variable (k : ℕ)

/-- The factor `g(zXᵢ) = 1 + 2q ∑_{b=1}^k cosh(zXᵢb)` of the generating function. -/
noncomputable def gFactor (i : Fin n) : PowerSeries (PowerSeries (MvPolynomial (Fin n) ℚ)) :=
  rescale (C (MvPolynomial.X i)) (zMap n (gSeries k))

/-- The generating function `F_n(X, z, q) (1 - q) = ∏_{i=1}^n g(zXᵢ)` (`paper.tex`, Section 3). -/
noncomputable def genProd : PowerSeries (PowerSeries (MvPolynomial (Fin n) ℚ)) :=
  ∏ i, gFactor n k i

/-- The coefficients `c_j = d_j(q,k) s_j(X)` of the exponent `∑_j d_j(q,k) s_j(X) z^j`. -/
noncomputable def cCoeff (j : ℕ) : PowerSeries (MvPolynomial (Fin n) ℚ) :=
  qMap n (dSeries k j) * C (powerSum ℚ n j)

/-- `(1 + 2qk)^n · exp(∑_{j ≥ 1} d_j(q,k) s_j(X) z^j)`. -/
noncomputable def expSide : PowerSeries (PowerSeries (MvPolynomial (Fin n) ℚ)) :=
  C ((1 + C (2 * k : MvPolynomial (Fin n) ℚ) * X) ^ n) * Nat.Partition.genFun (expChar (cCoeff n k))

/-- The logarithmic derivative `∑_i Xᵢ f'(zXᵢ)`. -/
noncomputable def logDeriv : PowerSeries (PowerSeries (MvPolynomial (Fin n) ℚ)) :=
  ∑ i, C (C (MvPolynomial.X i)) * rescale (C (MvPolynomial.X i)) (zMap n (derivativeFun (fSeries k)))

lemma derivativeFun_genProd : derivativeFun (genProd n k) = genProd n k * logDeriv n k := by
  unfold genProd logDeriv
  apply derivativeFun_prod
  intro i _
  rw [gFactor, derivativeFun_rescale, derivativeFun_map, derivativeFun_gSeries, map_mul, map_mul]
  ring

lemma logDeriv_eq : logDeriv n k = PowerSeries.mk fun j => (j + 1 : PowerSeries (MvPolynomial (Fin n) ℚ)) * cCoeff n k (j + 1) := by
  ext1 j
  simp only [logDeriv, map_sum, coeff_C_mul, coeff_rescale, coeff_map, coeff_derivativeFun,
    fSeries, coeff_mk, cCoeff, powerSum, MvPolynomial.psum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_add, map_natCast, map_one, map_pow]
  ring

lemma derivativeFun_expSide : derivativeFun (expSide n k) = expSide n k * logDeriv n k := by
  rw [expSide, derivativeFun_mul, derivativeFun_C, smul_zero, add_zero, smul_eq_mul,
    derivativeFun_genFun_expChar, logDeriv_eq, mul_assoc]

lemma constantCoeff_genProd :
    constantCoeff (genProd n k) = (1 + C (2 * k : MvPolynomial (Fin n) ℚ) * X) ^ n := by
  have h1 : ∀ i, constantCoeff (gFactor n k i) = 1 + C (2 * k : MvPolynomial (Fin n) ℚ) * X := by
    intro i
    rw [gFactor, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_map, coeff_zero_eq_constantCoeff_apply]
    have hm : constantCoeff (PowerSeries.map (C : ℚ →+* PowerSeries ℚ) (hSeries k)) =
        C (2 * k : ℚ) := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_hSeries]
    simp only [gSeries, map_add, map_one, map_mul, constantCoeff_C, hm]
    ext m
    simp [coeff_one, mul_comm, map_ofNat]
  rw [genProd, map_prod, Finset.prod_congr rfl (fun i _ => h1 i), prod_const, card_univ,
    Fintype.card_fin]

/-- The key identity of the proof of Theorem `thm:main`:
`∏_{i=1}^n (1 + 2q ∑_{b=1}^k cosh(zXᵢb)) = (1+2qk)^n exp(∑_{j ≥ 1} d_j(q,k) s_j(X) z^j)`. -/
theorem genProd_eq_expSide : genProd n k = expSide n k := by
  apply eq_of_derivativeFun_eq_mul (derivativeFun_genProd n k) (derivativeFun_expSide n k)
  rw [constantCoeff_genProd, expSide, constantCoeff.map_mul, constantCoeff_C,
    constantCoeff_genFun_expChar, mul_one]

/-- Splitting a sum over the symmetric integer interval `[-k, k]`. -/
lemma sum_Icc_neg_eq {M : Type*} [AddCommMonoid M] (f : ℤ → M) (k : ℕ) :
    ∑ β ∈ Icc (-(k : ℤ)) k, f β = f 0 + ∑ b ∈ Icc 1 k, (f b + f (-b)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
        insert ((k + 1 : ℕ) : ℤ) (insert (-((k + 1 : ℕ) : ℤ)) (Icc (-(k : ℤ)) k)) := by
      ext x; simp only [mem_Icc, mem_insert]; push_cast; omega
    have e2 : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [e1, sum_insert (by simp; omega), sum_insert (by simp), ih, e2,
      sum_insert (by simp)]
    push_cast
    abel_nf

/-- `2 cosh` expressed through the interval `[-k,k]`: the image of `g(x)` in `A⟦q⟧⟦z⟧` is
`∑_{β = -k}^{k} q^{[β ≠ 0]} e^{β z}` (`paper.tex`, Section 3, proof of Theorem `thm:main`). -/
lemma zMap_gSeries :
    zMap n (gSeries k) = ∑ β ∈ Icc (-(k : ℤ)) k,
      C (if β ≠ 0 then (X : PowerSeries (MvPolynomial (Fin n) ℚ)) else 1) *
        rescale (β : PowerSeries (MvPolynomial (Fin n) ℚ)) (exp _) := by
  rw [sum_Icc_neg_eq]
  simp only [ne_eq, not_true_eq_false, if_false, Int.cast_zero, map_one, one_mul,
    rescale_zero, RingHom.coe_comp, Function.comp_apply, constantCoeff_exp, Int.cast_natCast,
    Int.cast_neg]
  ext m : 1
  have hcg : coeff m (gSeries k) = (if m = 0 then 1 else 0) + X * C (coeff m (hSeries k)) := by
    simp [gSeries, coeff_one, coeff_C_mul, coeff_map]
  have hb : ∀ b ∈ Icc 1 k, ¬ ((b : ℤ) = 0) ∧ ¬ (-(b : ℤ) = 0) := by
    intro b hb; simp at hb; omega
  rw [coeff_map, hcg, map_add, map_add, coeff_one, map_sum]
  simp only [apply_ite, map_one, map_zero]
  congr 1
  rw [Finset.sum_congr rfl fun b h => by rw [if_pos (hb b h).1, if_pos (hb b h).2]]
  simp only [hSeries, map_sum, coeff_twoCosh, map_mul, map_X]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_add, coeff_C_mul, coeff_C_mul, coeff_rescale, coeff_rescale, coeff_exp, ← mul_add]
  congr 1
  have e : ∀ x : ℚ, qMap n (C x) = algebraMap ℚ (PowerSeries (MvPolynomial (Fin n) ℚ)) x := by
    intro x; ext j : 1; simp [coeff_C, PowerSeries.algebraMap_apply]
  rw [e, ← add_mul, div_eq_mul_one_div, map_mul]
  simp

lemma prod_rescale_exp {S ι : Type*} [CommRing S] [Algebra ℚ S] (s : Finset ι) (a : ι → S) :
    ∏ i ∈ s, rescale (a i) (exp S) = rescale (∑ i ∈ s, a i) (exp S) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rescale_zero]
  | insert j s hj ih => rw [prod_insert hj, sum_insert hj, ih, exp_mul_exp_eq_exp_add]

lemma rescale_C {S : Type*} [CommSemiring S] (a w : S) : rescale a (C w) = C w := by
  ext m : 1
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

/-- Expansion of the generating function as a sum over the box `[-k,k]ⁿ`:
`∏_{i=1}^n g(zXᵢ) = ∑_{b ∈ ([-k,k] ∩ ℤ)ⁿ} q^{wt(b)} e^{z⟨X,b⟩}`
(`paper.tex`, Section 3, proof of Theorem `thm:main`). -/
lemma genProd_eq_sum : genProd n k = ∑ b ∈ box n k k,
    C ((X : PowerSeries (MvPolynomial (Fin n) ℚ)) ^ wt b) *
      rescale (C (innerX ℚ b)) (exp (PowerSeries (MvPolynomial (Fin n) ℚ))) := by
  unfold genProd gFactor
  simp only [zMap_gSeries, map_sum, map_mul, rescale_C, rescale_rescale]
  rw [Finset.prod_univ_sum, box]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, prod_rescale_exp]
  congr 2
  · rw [Finset.prod_ite, prod_const_one, mul_one, prod_const]; rfl
  · simp [innerX, map_sum, map_mul, map_intCast]

lemma coeff_mk_one_mul {S : Type*} [Semiring S] (F : PowerSeries S) (t : ℕ) :
    coeff t (PowerSeries.mk 1 * F) = ∑ j ∈ range (t + 1), coeff j F := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (PowerSeries.mk 1) * coeff j F)]
  simp only [coeff_mk, Pi.one_apply, one_mul]
  rw [← Finset.sum_range_reflect (fun j => coeff j F)]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1

lemma map_innerX (b : Fin n → ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ) (innerX ℤ b) = innerX ℚ b := by
  simp [innerX, map_sum]

/-- The Q-polynomial as a coefficient of the generating function (`paper.tex`, Section 3,
equation `eq:dFdz1`): `Q^r_{𝓑(n,t,k,k)}(X) = (2r)! [q^t][z^{2r}] F_n(X,z,q)`, where
`F_n = (1-q)^{-1} ∏_i g(zXᵢ)`. -/
lemma QPoly_eq_coeff_genProd (t r : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (QPoly (ball n t k k) r) =
      ((2 * r).factorial : ℚ) • coeff t (PowerSeries.mk 1 * coeff (2 * r) (genProd n k)) := by
  rw [genProd_eq_sum, map_sum, coeff_mk_one_mul]
  simp only [map_sum]
  rw [Finset.sum_comm, Finset.smul_sum]
  unfold QPoly ball
  rw [map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_pow, map_innerX]
  simp only [coeff_C_mul, coeff_rescale, coeff_exp]
  have e : (C (innerX ℚ b) : PowerSeries (MvPolynomial (Fin n) ℚ)) ^ (2 * r) *
      algebraMap ℚ (PowerSeries (MvPolynomial (Fin n) ℚ)) (1 / ((2 * r).factorial : ℚ)) =
      C (innerX ℚ b ^ (2 * r) * algebraMap ℚ _ (1 / ((2 * r).factorial : ℚ))) := by
    rw [map_mul, map_pow]; congr 1; ext j : 1; simp [coeff_C, PowerSeries.algebraMap_apply]
  simp_rw [e, mul_comm (X ^ wt b), coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq']
  simp only [mem_range]
  split_ifs with h1 h2 h2
  · rw [Algebra.smul_def, ← mul_assoc, mul_comm (algebraMap ℚ _ _), mul_assoc, ← map_mul,
      mul_one_div_cancel (by exact_mod_cast (Nat.factorial_pos _).ne'), map_one, mul_one]
  · omega
  · omega
  · simp

omit n k in
/-- **Theorem `thm:main`** (`paper.tex`, Section 1, equation `eq:Q-main`; proved in Section 3).
For `k ≥ 1`, `n ≥ t ≥ 1` and `r ≥ 1`, the `r`-th Q-polynomial of `𝓑(n,t,k,k)` is
`Q^r_{𝓑(n,t,k,k)}(X) = (2r)! · [q^t] ( (1+2qk)^n/(1-q) · ∑_{μ ⊢ r} 1/(∏_j m_j(μ)!) ·
  ∏_{i=1}^{ℓ(μ)} d_{2μ_i}(q,k) s_{2μ_i}(X) )`,
where `d_{2j}(q,k)` are the coefficients of
`ln(1 + 2q ∑_{b=1}^k cosh(bx)) = ∑_j d_{2j}(q,k) x^{2j}` (`LatticeTiling.dSeries`).

Here `Q^r` is computed over `ℤ` and mapped to `ℚ[X₁,…,Xₙ]`; the right-hand side is the
coefficient of `q^t` of a power series in `q` with coefficients in `ℚ[X₁,…,Xₙ]`, `1/(1-q)` is
`PowerSeries.mk 1 = ∑_i q^i`, and `s_j(X)` is the power sum `powerSum ℚ n j`. The hypotheses
`k ≥ 1`, `n ≥ t ≥ 1`, `r ≥ 1` of the paper are not needed: the identity holds for all
`n t k r : ℕ`. -/
theorem QPoly_ball_formula (n t k r : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (QPoly (ball n t k k) r) =
      ((2 * r).factorial : ℚ) • coeff t
        ((1 + C (2 * k : MvPolynomial (Fin n) ℚ) * X) ^ n * PowerSeries.mk 1 *
          ∑ μ : r.Partition, (1 / (multFactorialProd μ : ℚ)) •
            (μ.parts.map fun i => PowerSeries.map (algebraMap ℚ (MvPolynomial (Fin n) ℚ))
              (dSeries k (2 * i)) * C (powerSum ℚ n (2 * i))).prod) := by
  rw [QPoly_eq_coeff_genProd, genProd_eq_expSide, expSide, coeff_C_mul,
    coeff_genFun_expChar_even _ (fun i hi => by simp [cCoeff, dSeries_odd k i hi]),
    coeff_genFun_expChar]
  simp only [cCoeff, Algebra.smul_def]
  congr 2
  ring

omit n k in
/-- **Theorem `thm:main`, Bell polynomial form** (`paper.tex`, Section 3, proof of
Theorem `thm:main`): with `a_j = j! · d_j(q,k) s_j(X)` (so that `a_{2j-1} = 0` and
`a_{2j} = (2j)! d_{2j}(q,k) s_{2j}(X)`),
`Q^r_{𝓑(n,t,k,k)}(X) = [q^t] ( (1+2qk)^n/(1-q) · B_{2r}(a_1, …, a_{2r}) )`. -/
theorem QPoly_ball_formula_bell (n t k r : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (QPoly (ball n t k k) r) =
      coeff t ((1 + C (2 * k : MvPolynomial (Fin n) ℚ) * X) ^ n * PowerSeries.mk 1 *
        completeBell (2 * r) (fun j => (j.factorial : ℚ) •
          (PowerSeries.map (algebraMap ℚ (MvPolynomial (Fin n) ℚ)) (dSeries k j) *
            C (powerSum ℚ n j)))) := by
  rw [QPoly_eq_coeff_genProd, genProd_eq_expSide, expSide, coeff_C_mul, completeBell_eq_coeff]
  have hc : (fun i : ℕ => algebraMap ℚ (PowerSeries (MvPolynomial (Fin n) ℚ))
      (1 / (i.factorial : ℚ)) * ((i.factorial : ℚ) •
        (PowerSeries.map (algebraMap ℚ (MvPolynomial (Fin n) ℚ)) (dSeries k i) *
          C (powerSum ℚ n i)))) = cCoeff n k := by
    funext i
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul,
      one_div_mul_cancel (by exact_mod_cast (Nat.factorial_pos i).ne'), map_one, one_mul]
    rfl
  rw [hc, Algebra.smul_def]
  set Γ := coeff (2 * r) (Nat.Partition.genFun (expChar (cCoeff n k)))
  have e : ((1 + C (2 * k : MvPolynomial (Fin n) ℚ) * X) ^ n * PowerSeries.mk 1 *
      (algebraMap ℚ (PowerSeries (MvPolynomial (Fin n) ℚ)) ((2 * r).factorial : ℚ) * Γ)) =
      C (algebraMap ℚ (MvPolynomial (Fin n) ℚ) ((2 * r).factorial : ℚ)) *
        (PowerSeries.mk 1 * ((1 + C (2 * k : MvPolynomial (Fin n) ℚ) * X) ^ n * Γ)) := by
    rw [PowerSeries.algebraMap_apply]; ring
  rw [e, coeff_C_mul]

end LatticeTiling
