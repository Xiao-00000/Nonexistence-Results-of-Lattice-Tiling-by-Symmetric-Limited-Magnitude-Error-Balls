module

public import RequestProject.CLambda
public import RequestProject.Thm2_6_Kummer

/-!
# Two infinite families of parameters with no lattice tiling

Formalization of `paper.tex`, Section 5 (`sec:family`): Corollary `cor:p=3`, the computation
of `[q^t] (1+2qk)^n/(1-q) B_2(0, 2d_2(q,k))`, the analysis of `|𝓑(n,t,k,k)| mod 9`, and
Theorems `thm:keq4mod9` and `thm:keq8mod9`.
-/

@[expose] public section

open Finset PowerSeries

namespace LatticeTiling

/-- The sequence `(a_1, a_2, …) = (0, 2 d_2(q,k), 0, 0, …)`, so that `B_2(a_1,a_2) = B_2(0, 2d_2)`
(`paper.tex`, Corollary `cor:p=3`). -/
noncomputable def bellArgP3 (k : ℕ) : ℕ → PowerSeries ℚ :=
  fun j => if j = 2 then 2 * dSeries k 2 else 0

/-- The rational number `[q^t] (1+2qk)^n/(1-q) · B_2(0, 2d_2(q,k))` of Corollary `cor:p=3`. -/
noncomputable def p3Value (n t k : ℕ) : ℚ :=
  coeff t ((1 + C (2 * k : ℚ) * X) ^ n * PowerSeries.mk 1 * completeBell 2 (bellArgP3 k))

lemma completeBell_two_bellArgP3 (k : ℕ) : completeBell 2 (bellArgP3 k) = 2 * dSeries k 2 := by
  rw [completeBell_two]; simp [bellArgP3]

/-- For `r = 1` the coefficient `c_{(1)}` equals `[q^t] (1+2qk)^n/(1-q) · B_2(0, 2d_2(q,k))`. -/
lemma cLambdaQ_one (n t k : ℕ) (μ : (1 : ℕ).Partition) : cLambdaQ n t k 1 μ = p3Value n t k := by
  rw [cLambdaQ, p3Value, completeBell_two_bellArgP3, Nat.Partition.partition_one_parts]
  simp only [multFactorialProd, Nat.Partition.partition_one_parts, Multiset.toFinset_singleton,
    prod_singleton, Multiset.count_singleton_self, Nat.factorial_one, Multiset.map_singleton,
    Multiset.prod_singleton]
  rw [show ((1 + C (2 * k : ℚ) * X) ^ n * PowerSeries.mk 1 * (2 * dSeries k (2 * 1))) =
    C (2 : ℚ) * ((1 + C (2 * k : ℚ) * X) ^ n * PowerSeries.mk 1 * dSeries k 2) by
      rw [map_ofNat]; ring, coeff_C_mul]
  norm_num

/-- **Corollary `cor:p=3`** (`paper.tex`, Section 5): there is no lattice tiling of `ℤⁿ` by
`𝓑(n,t,k,k)` if `3 ∥ |𝓑(n,t,k,k)|` and `3 ∣ [q^t] (1+2qk)^n/(1-q) B_2(0, 2d_2(q,k))`, where `B_2`
is the complete Bell polynomial. (The divisibility of the a priori rational number
`[q^t](…)` by `3` means that it is `3` times an integer.) -/
theorem no_lattice_tiling_of_p3 (n t k : ℕ) (h3 : 3 ∣ (ball n t k k).card)
    (h9 : ¬ 9 ∣ (ball n t k k).card) (hdiv : ∃ z : ℤ, p3Value n t k = 3 * z) :
    ¬ HasLatticeTiling (ball n t k k : Set (Fin n → ℤ)) := by
  obtain ⟨M, hM⟩ := h3
  have hM3 : ¬ 3 ∣ M := by rintro ⟨j, rfl⟩; exact h9 ⟨j, by rw [hM]; ring⟩
  obtain ⟨z, hz⟩ := hdiv
  have hc : ∀ μ : (1 : ℕ).Partition, cLambda n t k 1 μ = 3 * z := by
    intro μ
    have := cLambda_cast n t k 1 μ
    rw [cLambdaQ_one, hz] at this
    exact_mod_cast this
  refine no_lattice_tiling_of_conditionY t k 3 M (by norm_num) hM (cLambda n t k)
    (isCLambdaExpansion_cLambda n t k _) ?_
  rintro ⟨Y, -, hY⟩
  have : MvPolynomial.eval Y (fPoly 3 (cLambda n t k) ((3 - 1) / 2)) = 0 := by
    simp only [fPoly, map_sum, map_mul, MvPolynomial.eval_C]
    refine Finset.sum_eq_zero fun μ _ => ?_
    have e : cLambda n t k ((3 - 1) / 2) μ = 3 * z := hc μ
    rw [e]
    push_cast
    rw [show (3 : ZMod 3) = 0 from rfl, zero_mul, zero_mul]
  rw [this, eq_comm, neg_eq_zero, ZMod.natCast_eq_zero_iff] at hY
  exact hM3 hY

/-- **Computation of the quantity of Corollary `cor:p=3`** (`paper.tex`, Section 5): since
`d_2(q,k) = q k(k+1)(2k+1) / (6(1+2qk))`, for `n ≥ 1`
`3 · [q^t] (1+2qk)^n/(1-q) B_2(0,2d_2(q,k)) = k(k+1)(2k+1) · [q^t] q(1+2qk)^{n-1}/(1-q)`. -/
theorem three_mul_p3Value (n t k : ℕ) (hn : 1 ≤ n) :
    3 * p3Value n t k = ((k : ℚ) * (k + 1) * (2 * k + 1)) *
      coeff t (X * ((1 + C (2 * k : ℚ) * X) ^ (n - 1) * PowerSeries.mk 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd := dSeries_two k
  have hu : (1 + C (2 * k : ℚ) * X) = 1 + 2 * (k : PowerSeries ℚ) * X := by
    simp [map_mul, map_natCast, map_ofNat]
  have key : C (3 : ℚ) * ((1 + C (2 * k : ℚ) * X) ^ (m + 1) * PowerSeries.mk 1 *
      completeBell 2 (bellArgP3 k)) = C ((k : ℚ) * (k + 1) * (2 * k + 1)) *
        (X * ((1 + C (2 * k : ℚ) * X) ^ (m + 1 - 1) * PowerSeries.mk 1)) := by
    rw [completeBell_two_bellArgP3, Nat.add_sub_cancel, hu, pow_succ]
    simp only [map_mul, map_add, map_natCast, map_one, map_ofNat]
    linear_combination ((1 + 2 * (k : PowerSeries ℚ) * X) ^ m * PowerSeries.mk 1) * hd
  have := congrArg (coeff t) key
  rwa [coeff_C_mul, coeff_C_mul] at this

/-- If `9 ∣ k(k+1)(2k+1)` (equivalently `3 ∣ k(k+1)(2k+1)/3`, i.e. `k ≡ 0,4,8 (mod 9)`), then the
second hypothesis of Corollary `cor:p=3` holds (`paper.tex`, Section 5, the displayed chain of
implications). -/
theorem p3Value_dvd_of_nine_dvd (n t k : ℕ) (hn : 1 ≤ n) (hk : 9 ∣ k * (k + 1) * (2 * k + 1)) :
    ∃ z : ℤ, p3Value n t k = 3 * z := by
  obtain ⟨w, hw⟩ := hk
  set F : PowerSeries ℚ := X * ((1 + C (2 * k : ℚ) * X) ^ (n - 1) * PowerSeries.mk 1)
  have hF : F ∈ intPS := by
    refine mul_mem X_mem_intPS (mul_mem (pow_mem (add_mem (one_mem _) (mul_mem ?_ X_mem_intPS))
      _) mk_one_mem_intPS)
    exact_mod_cast C_intCast_mem_intPS (2 * k)
  obtain ⟨Z, hZ⟩ := hF
  refine ⟨w * coeff (R := ℤ) t Z, ?_⟩
  have h := three_mul_p3Value n t k hn
  have hc : coeff t F = (coeff (R := ℤ) t Z : ℚ) := by rw [← hZ, coeff_map]; rfl
  have hw' : ((k : ℚ) * (k + 1) * (2 * k + 1)) = 9 * w := by exact_mod_cast hw
  rw [hc, hw'] at h
  push_cast
  linarith

/-- `k ≡ 0, 4, 8 (mod 9) ⟺ 9 ∣ k(k+1)(2k+1) ⟺ 3 ∣ k(k+1)(2k+1)/3` (`paper.tex`, Section 5,
"direct check modulo 9"). -/
theorem nine_dvd_iff (k : ℕ) :
    9 ∣ k * (k + 1) * (2 * k + 1) ↔ k % 9 = 0 ∨ k % 9 = 4 ∨ k % 9 = 8 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mul_mod k, Nat.add_mod k, Nat.add_mod (2 * k),
    Nat.mul_mod 2]
  have : k % 9 < 9 := Nat.mod_lt _ (by norm_num)
  interval_cases k % 9 <;> simp

lemma card_ball_zmod (n t k : ℕ) : ((ball n t k k).card : ZMod 9) =
    ∑ i ∈ range (t + 1), (2 * (k : ZMod 9)) ^ i * (n.choose i : ZMod 9) := by
  rw [card_ball]; push_cast; rfl

/-- **Case `k ≡ 0 (mod 9)`** (`paper.tex`, Section 5, item 1): then `|𝓑(n,t,k,k)| ≡ 1 (mod 9)`,
so the hypothesis `3 ∥ |𝓑(n,t,k,k)|` of Corollary `cor:p=3` never holds. -/
theorem card_ball_mod_nine_of_zero (n t k : ℕ) (hk : k % 9 = 0) :
    (ball n t k k).card % 9 = 1 := by
  have h : ((ball n t k k).card : ZMod 9) = 1 := by
    rw [card_ball_zmod, sum_range_succ']
    have hk' : (k : ZMod 9) = 0 := by rw [← ZMod.natCast_mod, hk]; rfl
    simp [hk']
  have := (ZMod.natCast_eq_natCast_iff' _ 1 9).1 (by simpa using h)
  simpa using this

/-- **`|𝓑(n,t,k,k)| mod 9` for `k ≡ 4 (mod 9)`** (`paper.tex`, Section 5, proof of
Theorem `thm:keq4mod9`): `|𝓑(n,t,k,k)| ≡ ∑_{i=0}^t (-1)^i \binom{n}{i} ≡ (-1)^t \binom{n-1}{t}
(mod 9)` for `n ≥ 1`. -/
theorem card_ball_modEq_of_four (n t k : ℕ) (hn : 1 ≤ n) (hk : k % 9 = 4) :
    ((ball n t k k).card : ℤ) ≡ (-1) ^ t * ((n - 1).choose t : ℤ) [ZMOD 9] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 9).1 ?_
  push_cast
  rw [card_ball_zmod]
  have hk' : 2 * (k : ZMod 9) = -1 := by rw [← ZMod.natCast_mod, hk]; rfl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := congrArg (Int.cast : ℤ → ZMod 9) (Int.alternating_sum_range_choose_eq_choose (n := m) (m := t))
  push_cast at this
  rw [hk', Nat.add_sub_cancel, ← this]

/-- **`|𝓑(n,n-1,k,k)| mod 9` for `k ≡ 8 (mod 9)`** (`paper.tex`, Section 5, proof of
Theorem `thm:keq8mod9`): `|𝓑(n,n-1,k,k)| ≡ ∑_{i=0}^{n-1} (-2)^i \binom{n}{i} ≡ (-1)^n - (-2)^n
(mod 9)` for `n ≥ 1`. -/
theorem card_ball_modEq_of_eight (n k : ℕ) (hn : 1 ≤ n) (hk : k % 9 = 8) :
    ((ball n (n - 1) k k).card : ℤ) ≡ (-1) ^ n - (-2) ^ n [ZMOD 9] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 9).1 ?_
  push_cast
  rw [card_ball_zmod]
  have hk' : 2 * (k : ZMod 9) = -2 := by rw [← ZMod.natCast_mod, hk]; rfl
  rw [hk', Nat.sub_add_cancel hn]
  have h := add_pow (-2 : ZMod 9) 1 n
  rw [sum_range_succ] at h
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one] at h
  rw [show (-2 : ZMod 9) + 1 = -1 by ring] at h
  rw [h]; ring

/-- **Theorem `thm:keq4mod9`** (`paper.tex`, Section 1, proved in Section 5): there is no lattice
tiling of `ℤⁿ` by `𝓑(n,t,k,k)` if `k ≡ 4 (mod 9)` and the addition of `t` and `n-1-t` in base `3`
produces exactly one carry. -/
theorem no_lattice_tiling_keq4mod9 (n t k : ℕ) (hk : k % 9 = 4) (hc : carries 3 t (n - 1 - t) = 1) :
    ¬ HasLatticeTiling (ball n t k k : Set (Fin n → ℤ)) := by
  have h0 : n - 1 - t ≠ 0 := by
    intro h
    rw [h, ← kummer 3 t 0, Nat.add_zero, Nat.choose_self, padicValNat.one] at hc
    exact zero_ne_one hc
  have htn : t ≤ n - 1 := by omega
  have hv : padicValNat 3 ((n - 1).choose t) = 1 := by rw [kummer' 3 htn, hc]
  have hC : (n - 1).choose t ≠ 0 := (Nat.choose_pos htn).ne'
  have h3 : 3 ∣ (n - 1).choose t := by
    have := pow_padicValNat_dvd (p := 3) (n := (n - 1).choose t); rwa [hv, pow_one] at this
  have h9 : ¬ 9 ∣ (n - 1).choose t := by
    have := pow_succ_padicValNat_not_dvd (p := 3) hC; rwa [hv] at this
  have hmod := card_ball_modEq_of_four n t k (by omega) hk
  have hpar : ((-1 : ℤ) ^ t = 1 ∨ (-1 : ℤ) ^ t = -1) := neg_one_pow_eq_or ℤ t
  set C := (n - 1).choose t
  set x := (ball n t k k).card
  have key : 3 ∣ x ∧ ¬ 9 ∣ x := by
    have hd := Int.ModEq.dvd hmod
    rcases hpar with h | h <;> rw [h] at hd <;> omega
  refine no_lattice_tiling_of_p3 n t k key.1 key.2 (p3Value_dvd_of_nine_dvd n t k (by omega)
    ((nine_dvd_iff k).2 (Or.inr (Or.inl hk))))

/-- **Theorem `thm:keq8mod9`** (`paper.tex`, Section 1, proved in Section 5): there is no lattice
tiling of `ℤⁿ` by `𝓑(n,n-1,k,k)` if `k ≡ 8 (mod 9)` and `n ≡ 2, 4 (mod 6)`. -/
theorem no_lattice_tiling_keq8mod9 (n k : ℕ) (hk : k % 9 = 8) (hn : n % 6 = 2 ∨ n % 6 = 4) :
    ¬ HasLatticeTiling (ball n (n - 1) k k : Set (Fin n → ℤ)) := by
  have hn1 : 1 ≤ n := by omega
  have hmod := card_ball_modEq_of_eight n k hn1 hk
  set x := (ball n (n - 1) k k).card
  have hval : (x : ZMod 9) = 6 ∨ (x : ZMod 9) = 3 := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ 9).2 hmod
    push_cast at h
    rw [h]
    obtain ⟨q, hq⟩ : ∃ q, n = 6 * q + n % 6 := ⟨n / 6, (Nat.div_add_mod n 6).symm⟩
    rw [hq, pow_add, pow_add, pow_mul, pow_mul]
    have e1 : ((-1 : ZMod 9) ^ 6) = 1 := by decide
    have e2 : ((-2 : ZMod 9) ^ 6) = 1 := by decide
    simp only [e1, e2, one_pow, one_mul]
    rcases hn with h | h <;> rw [h]
    · left; decide
    · right; decide
  have key : 3 ∣ x ∧ ¬ 9 ∣ x := by
    rcases hval with h | h
    · have := (ZMod.natCast_eq_natCast_iff' x 6 9).1 (by simpa using h); omega
    · have := (ZMod.natCast_eq_natCast_iff' x 3 9).1 (by simpa using h); omega
  exact no_lattice_tiling_of_p3 n (n - 1) k key.1 key.2 (p3Value_dvd_of_nine_dvd n (n - 1) k hn1
    ((nine_dvd_iff k).2 (Or.inr (Or.inr hk))))

/-- **Example in the proof of Theorem `thm:keq4mod9`** (`paper.tex`, Section 5): for every integer
`a ≥ 1` and `k ≡ 4 (mod 9)`, there is no lattice tiling of `ℤⁿ` by `𝓑(n,t,k,k)` with
`n = 3^a + 1` and `t = 3^{a-1}`. -/
theorem no_lattice_tiling_keq4mod9_pow (a k : ℕ) (ha : 1 ≤ a) (hk : k % 9 = 4) :
    ¬ HasLatticeTiling (ball (3 ^ a + 1) (3 ^ (a - 1)) k k : Set (Fin (3 ^ a + 1) → ℤ)) := by
  apply no_lattice_tiling_keq4mod9 _ _ k hk
  have h3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨h3⟩
  have hle : 3 ^ (a - 1) ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show 3 ^ a + 1 - 1 - 3 ^ (a - 1) = 3 ^ a - 3 ^ (a - 1) by omega, ← kummer,
    Nat.add_sub_cancel' hle, ← Nat.factorization_def _ h3,
    Nat.factorization_choose_prime_pow h3 hle (by positivity), Nat.factorization_pow]
  simp [h3.factorization_self]
  omega

end LatticeTiling
