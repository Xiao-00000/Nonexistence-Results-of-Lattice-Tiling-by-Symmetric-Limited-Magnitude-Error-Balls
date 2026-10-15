module

public import RequestProject.Def2_7_Defs

/-!
# Complete Bell polynomials and the exponential formula

Formalization of the combinatorial preliminaries of `paper.tex`, Section 2.1: integer partitions
and complete Bell polynomials (equation `eq:Bell-explicit`), together with the analytic tools
used in the proof of Theorem `thm:main`: the exponential formula for sums over partitions,
in the form of a first-order differential equation, and uniqueness of solutions of such
equations.
-/

@[expose] public section

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace LatticeTiling

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The power series `exp(c X^{i+1}) = ∑_{m ≥ 0} c^m X^{(i+1)m} / m!`. -/
noncomputable def expMonomial (c : R) (i : ℕ) : PowerSeries R :=
  PowerSeries.mk fun m => if (i + 1) ∣ m then
    algebraMap ℚ R (1 / ((m / (i + 1)).factorial : ℚ)) * c ^ (m / (i + 1)) else 0

/-- The character `f(i, m) = c_i^m / m!` of the exponential formula. -/
noncomputable def expChar (c : ℕ → R) : ℕ → ℕ → R :=
  fun i m => algebraMap ℚ R (1 / (m.factorial : ℚ)) * c i ^ m

/-- The `i`-th factor of the product formula of `Nat.Partition.genFun` for the character
`expChar c` is `exp(c_{i+1} X^{i+1})`. -/
lemma genFun_factor_eq [TopologicalSpace R] [T2Space R] (c : ℕ → R) (i : ℕ) :
    (1 + ∑' j, expChar c (i + 1) (j + 1) • (X : PowerSeries R) ^ ((i + 1) * (j + 1))) =
      expMonomial (c (i + 1)) i := by
  ext m
  rw [map_add, (Nat.Partition.summable_genFun_term (expChar c) i).map_tsum _
    (WithPiTopology.continuous_coeff _ _)]
  simp only [map_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero, coeff_one,
    expMonomial, coeff_mk]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm, zero_add]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      have hq : q ≠ 0 := by rintro rfl; simp at hm
      rw [tsum_eq_single (q - 1)]
      · rw [if_pos (by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hq)]),
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hq), Nat.mul_div_cancel_left _ (by omega)]
        rfl
      · intro b hb
        rw [if_neg]
        intro h
        have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < i + 1) h
        omega
    · convert tsum_zero with j
      rw [if_neg]
      rintro rfl
      exact hd (dvd_mul_right _ _)

omit [Algebra ℚ R] in
/-- If `F ≡ 1 (mod X^{d+1})`, multiplying by `F` does not change the coefficient of `X^d`. -/
lemma coeff_mul_of_X_pow_dvd_sub_one {d : ℕ} {F : PowerSeries R}
    (hF : (X : PowerSeries R) ^ (d + 1) ∣ F - 1) (G : PowerSeries R) :
    coeff d (G * F) = coeff d G := by
  obtain ⟨H, hH⟩ := hF
  rw [show F = 1 + X ^ (d + 1) * H by rw [← hH]; ring, mul_add, mul_one, map_add,
    mul_left_comm, coeff_X_pow_mul', if_neg (by omega), add_zero]

/-- Truncation: for `d ≤ N`, the coefficient of `X^d` of the partition generating function of
the exponential character agrees with that of the finite product `∏_{i<N} exp(c_{i+1}X^{i+1})`. -/
lemma coeff_genFun_eq_coeff_prod (c : ℕ → R) {d N : ℕ} (hdN : d ≤ N) :
    coeff d (Nat.Partition.genFun (expChar c)) =
      coeff d (∏ i ∈ range N, expMonomial (c (i + 1)) i) := by
  classical
  letI : TopologicalSpace R := ⊥
  haveI : DiscreteTopology R := ⟨rfl⟩
  have hp := Nat.Partition.hasProd_genFun (expChar c)
  simp only [genFun_factor_eq] at hp
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto] at hp
  have hd := hp d
  rw [nhds_discrete, Filter.tendsto_pure] at hd
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.1 hd
  have key := hs0 (range N ∪ s0) subset_union_right
  rw [← key, ← Finset.union_sdiff_self_eq_union, prod_union disjoint_sdiff,
    coeff_mul_of_X_pow_dvd_sub_one]
  apply Finset.prod_induction (p := fun F : PowerSeries R => (X : PowerSeries R) ^ (d + 1) ∣ F - 1)
  · intro a b ha hb
    have : a * b - 1 = (a - 1) * b + (b - 1) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left ha _) hb
  · simp
  · intro i hi
    have hiN : N ≤ i := by simpa using (mem_sdiff.1 hi).2
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, coeff_one, expMonomial, coeff_mk]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · rw [if_neg (Nat.not_dvd_of_pos_of_lt hm0 (by omega)), if_neg (by omega), sub_zero]

/-- Derivative of `exp(c X^{i+1})`: `D exp(cX^{i+1}) = exp(cX^{i+1}) · (i+1) c X^i`. -/
lemma derivativeFun_expMonomial (c : R) (i : ℕ) :
    derivativeFun (expMonomial c i) =
      expMonomial c i * (C ((i + 1 : R) * c) * X ^ i) := by
  ext m
  rw [coeff_derivativeFun, show expMonomial c i * (C ((i + 1 : R) * c) * X ^ i) =
    C ((i + 1 : R) * c) * (expMonomial c i * X ^ i) by ring, coeff_C_mul, coeff_mul_X_pow']
  simp only [expMonomial, coeff_mk]
  by_cases hd : (i + 1) ∣ (m + 1)
  · obtain ⟨k, hk⟩ := hd
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hk
      · omega⟩
    have him : i ≤ m := by nlinarith
    have hmi : m - i = (i + 1) * k' := by
      have : m + 1 = (i + 1) * k' + (i + 1) := by rw [hk]; ring
      omega
    rw [if_pos ⟨k' + 1, hk⟩, if_pos him, hmi, if_pos ⟨k', rfl⟩, hk,
      Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
    have hmq : ((m : ℚ) + 1) = (i + 1) * (k' + 1) := by exact_mod_cast hk
    have e1 : ((m : R) + 1) = algebraMap ℚ R ((i + 1) * (k' + 1)) := by
      rw [← hmq]; simp
    have e2 : ((i : R) + 1) = algebraMap ℚ R (i + 1) := by simp
    rw [e1, e2]
    calc algebraMap ℚ R (1 / ((k' + 1).factorial : ℚ)) * c ^ (k' + 1) *
          algebraMap ℚ R ((i + 1) * (k' + 1))
        = algebraMap ℚ R (1 / ((k' + 1).factorial : ℚ) * ((i + 1) * (k' + 1))) *
            c ^ (k' + 1) := by simp only [map_mul]; ring
      _ = algebraMap ℚ R ((i + 1) * (1 / (k'.factorial : ℚ))) * c ^ (k' + 1) := by
          congr 2
          rw [Nat.factorial_succ]; push_cast
          field_simp
      _ = algebraMap ℚ R (i + 1) * c * (algebraMap ℚ R (1 / (k'.factorial : ℚ)) * c ^ k') := by
          simp only [map_mul, pow_succ]; ring
  · rw [if_neg hd, zero_mul]
    split_ifs with h1 h2
    · exfalso; apply hd
      obtain ⟨q, hq⟩ := h2
      exact ⟨q + 1, by rw [mul_add, ← hq]; omega⟩
    · simp
    · simp

omit [Algebra ℚ R] in
/-- Logarithmic derivative of a finite product. -/
lemma derivativeFun_prod {ι : Type*} (s : Finset ι) (F G : ι → PowerSeries R)
    (h : ∀ i ∈ s, derivativeFun (F i) = F i * G i) :
    derivativeFun (∏ i ∈ s, F i) = (∏ i ∈ s, F i) * ∑ i ∈ s, G i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [derivativeFun_one]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, derivativeFun_mul, smul_eq_mul, smul_eq_mul,
      ih (fun i hi => h i (mem_insert_of_mem hi)), h a (mem_insert_self a s)]
    ring

/-- **Exponential formula (differential form).** The partition generating function
`Γ(X) = ∑_r X^r ∑_{λ ⊢ r} ∏_j c_j^{m_j(λ)}/m_j(λ)!` (which is `exp(∑_j c_j X^j)`) satisfies
`Γ' = Γ · ∑_j (j+1) c_{j+1} X^j`. -/
theorem derivativeFun_genFun_expChar (c : ℕ → R) :
    derivativeFun (Nat.Partition.genFun (expChar c)) =
      Nat.Partition.genFun (expChar c) * PowerSeries.mk fun j => (j + 1 : R) * c (j + 1) := by
  ext m
  rw [coeff_derivativeFun, coeff_genFun_eq_coeff_prod c (N := m + 2) (by omega),
    ← coeff_derivativeFun, derivativeFun_prod (range (m + 2)) _ _
      (fun i _ => derivativeFun_expMonomial _ _), coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun ab hab => ?_
  have hab' := Finset.antidiagonal.fst_le hab
  have hab'' := Finset.antidiagonal.snd_le hab
  rw [← coeff_genFun_eq_coeff_prod c (by omega), map_sum, coeff_mk]
  congr 1
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (range (m + 2)) ab.2, if_pos (mem_range.2 (by omega))]

/-- **Uniqueness for the differential equation `Y' = Y · H`** over a `ℚ`-algebra: two power
series satisfying it with the same constant coefficient are equal. -/
theorem eq_of_derivativeFun_eq_mul {P E H : PowerSeries R}
    (hP : derivativeFun P = P * H) (hE : derivativeFun E = E * H)
    (h0 : constantCoeff P = constantCoeff E) : P = E := by
  ext m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · simpa using h0
    · have h1 := congrArg (coeff m) hP
      have h2 := congrArg (coeff m) hE
      rw [coeff_derivativeFun, coeff_mul] at h1 h2
      have hsum : ∑ p ∈ antidiagonal m, coeff p.1 P * coeff p.2 H =
          ∑ p ∈ antidiagonal m, coeff p.1 E * coeff p.2 H :=
        sum_congr rfl fun p hp => by
          rw [ih p.1 (by have := antidiagonal.fst_le hp; omega)]
      have key : coeff (m + 1) P * ((m : R) + 1) = coeff (m + 1) E * ((m : R) + 1) := by
        rw [h1, h2, hsum]
      have hinv : ((m : R) + 1) * algebraMap ℚ R (1 / ((m : ℚ) + 1)) = 1 := by
        rw [show ((m : R) + 1) = algebraMap ℚ R ((m : ℚ) + 1) by simp, ← map_mul]
        rw [mul_one_div_cancel (by positivity), map_one]
      calc coeff (m + 1) P
          = coeff (m + 1) P * ((m : R) + 1) * algebraMap ℚ R (1 / ((m : ℚ) + 1)) := by
            rw [mul_assoc, hinv, mul_one]
        _ = coeff (m + 1) E * ((m : R) + 1) * algebraMap ℚ R (1 / ((m : ℚ) + 1)) := by
            rw [key]
        _ = coeff (m + 1) E := by rw [mul_assoc, hinv, mul_one]

/-- `∏_{j=1}^{r} m_j(λ)!`, the product of the factorials of the multiplicities of the parts of a
partition `λ` (`paper.tex`, Section 2.1). -/
def multFactorialProd {r : ℕ} (μ : r.Partition) : ℕ :=
  ∏ j ∈ μ.parts.toFinset, (μ.parts.count j).factorial

lemma multFactorialProd_pos {r : ℕ} (μ : r.Partition) : 0 < multFactorialProd μ :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

/-- The summand of the partition generating function of the exponential character:
`∏_j c_j^{m_j}/m_j! = (∏_i c_{λ_i}) / ∏_j m_j!`. -/
lemma toFinsupp_prod_expChar {r : ℕ} (c : ℕ → R) (μ : r.Partition) :
    μ.parts.toFinsupp.prod (expChar c) =
      algebraMap ℚ R (1 / (multFactorialProd μ : ℚ)) * (μ.parts.map c).prod := by
  classical
  rw [Finsupp.prod, Multiset.toFinsupp_support, Finset.prod_multiset_map_count, multFactorialProd]
  simp only [Multiset.toFinsupp_apply, expChar]
  rw [Finset.prod_mul_distrib, ← map_prod]
  congr 2
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one]

/-- The coefficients of the partition generating function of the exponential character:
`[X^r] exp(∑_j c_j X^j) = ∑_{λ ⊢ r} (∏_i c_{λ_i}) / ∏_j m_j(λ)!`. -/
lemma coeff_genFun_expChar (c : ℕ → R) (r : ℕ) :
    coeff r (Nat.Partition.genFun (expChar c)) =
      ∑ μ : r.Partition, algebraMap ℚ R (1 / (multFactorialProd μ : ℚ)) * (μ.parts.map c).prod := by
  rw [Nat.Partition.coeff_genFun]
  exact Finset.sum_congr rfl fun μ _ => toFinsupp_prod_expChar c μ

lemma constantCoeff_genFun_expChar (c : ℕ → R) :
    constantCoeff (Nat.Partition.genFun (expChar c)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_genFun_eq_coeff_prod c (N := 0) le_rfl]
  simp

/-- The partition of `2r` obtained by doubling every part of a partition of `r`. -/
def doublePartition {r : ℕ} (μ : r.Partition) : (2 * r).Partition where
  parts := μ.parts.map (2 * ·)
  parts_pos := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hi
    have := μ.parts_pos hj; omega
  parts_sum := by
    rw [Multiset.sum_map_mul_left, Multiset.map_id', μ.parts_sum]

/-- **Even exponential formula.** If `c_i = 0` for all odd `i`, then
`[X^{2r}] exp(∑_j c_j X^j) = [X^r] exp(∑_j c_{2j} X^j)`. This encodes the observation in the
proof of Theorem `thm:main` (`paper.tex`, Section 3) that only partitions `λ ⊢ 2r` with even
parts `λ_i = 2μ_i` contribute. -/
lemma coeff_genFun_expChar_even (c : ℕ → R) (hc : ∀ i, Odd i → c i = 0) (r : ℕ) :
    coeff (2 * r) (Nat.Partition.genFun (expChar c)) =
      coeff r (Nat.Partition.genFun (expChar fun j => c (2 * j))) := by
  classical
  rw [Nat.Partition.coeff_genFun, Nat.Partition.coeff_genFun]
  symm
  refine Finset.sum_of_injOn doublePartition ?_ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
  · intro μ _ ν _ h
    have h' : μ.parts.map (2 * ·) = ν.parts.map (2 * ·) := congrArg Nat.Partition.parts h
    exact Nat.Partition.ext (Multiset.map_injective (fun a b hab => by simpa using hab) h')
  · intro lam _ hlam
    by_cases hall : ∀ i ∈ lam.parts, Even i
    · exfalso
      apply hlam
      refine ⟨⟨lam.parts.map (· / 2), ?_, ?_⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hi
        have := lam.parts_pos hj
        obtain ⟨k, hk⟩ := hall j hj
        omega
      · have h2 : (lam.parts.map (· / 2)).map (2 * ·) = lam.parts := by
          rw [Multiset.map_map]
          conv_rhs => rw [← Multiset.map_id lam.parts]
          refine Multiset.map_congr rfl fun j hj => ?_
          obtain ⟨k, hk⟩ := hall j hj
          simp only [Function.comp, id]; omega
        have := lam.parts_sum
        rw [← h2, Multiset.sum_map_mul_left, Multiset.map_id'] at this
        omega
      · apply Nat.Partition.ext
        change (lam.parts.map (· / 2)).map (2 * ·) = lam.parts
        rw [Multiset.map_map]
        conv_rhs => rw [← Multiset.map_id lam.parts]
        refine Multiset.map_congr rfl fun j hj => ?_
        obtain ⟨k, hk⟩ := hall j hj
        simp only [Function.comp, id]; omega
    · push_neg at hall
      obtain ⟨i, hi, hodd⟩ := hall
      rw [Finsupp.prod, Multiset.toFinsupp_support]
      apply Finset.prod_eq_zero (Multiset.mem_toFinset.2 hi)
      rw [Multiset.toFinsupp_apply, expChar, hc i (Nat.not_even_iff_odd.1 hodd),
        zero_pow (Multiset.count_ne_zero.2 hi), mul_zero]
  · intro μ _
    rw [toFinsupp_prod_expChar, toFinsupp_prod_expChar]
    congr 2
    · congr 2
      unfold multFactorialProd doublePartition
      simp only
      rw [Multiset.toFinset_map, Finset.prod_image (fun a _ b _ h => by simpa using h)]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Multiset.count_map_eq_count' _ _ (fun a b h => by simpa using h)]
    · simp [doublePartition, Multiset.map_map, Function.comp]

/-- **Complete Bell polynomials** (`paper.tex`, Section 2.1, explicit formula `eq:Bell-explicit`,
cf. Stanley, *Enumerative Combinatorics*):
`B_r(a_1, …, a_r) = ∑_{λ ⊢ r} r!/(∏_i λ_i!) · 1/(∏_j m_j(λ)!) · ∏_i a_{λ_i}`.
The arguments are given as a sequence `a : ℕ → R` (only `a 1, …, a r` are used). The defining
generating-function identity `exp(∑_j a_j z^j/j!) = ∑_r B_r z^r/r!` is
`LatticeTiling.hasProd_completeBell`. -/
noncomputable def completeBell (r : ℕ) (a : ℕ → R) : R :=
  ∑ μ : r.Partition, algebraMap ℚ R ((r.factorial : ℚ) /
    ((μ.parts.map fun i => (i.factorial : ℚ)).prod * multFactorialProd μ)) * (μ.parts.map a).prod

/-- `B_r(a) = r! · [z^r] exp(∑_j a_j z^j / j!)`. -/
lemma completeBell_eq_coeff (r : ℕ) (a : ℕ → R) :
    completeBell r a = algebraMap ℚ R (r.factorial : ℚ) *
      coeff r (Nat.Partition.genFun (expChar fun i => algebraMap ℚ R (1 / (i.factorial : ℚ)) * a i)) := by
  rw [coeff_genFun_expChar, Finset.mul_sum, completeBell]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Multiset.prod_map_mul, ← mul_assoc, ← mul_assoc, ← map_mul]
  have : (μ.parts.map fun i => algebraMap ℚ R (1 / (i.factorial : ℚ))).prod =
      algebraMap ℚ R (1 / (μ.parts.map fun i => (i.factorial : ℚ)).prod) := by
    rw [show (fun i : ℕ => algebraMap ℚ R (1 / (i.factorial : ℚ))) =
      (algebraMap ℚ R) ∘ (fun i : ℕ => ((i.factorial : ℚ))⁻¹) by funext i; simp,
      ← Multiset.map_map, ← map_multiset_prod, Multiset.prod_map_inv, one_div]
  rw [this, ← map_mul]
  congr 2
  have h1 : (0 : ℚ) < (multFactorialProd μ : ℚ) := by exact_mod_cast multFactorialProd_pos μ
  have h2 : (0 : ℚ) < (μ.parts.map fun i => (i.factorial : ℚ)).prod :=
    Multiset.prod_pos fun x hx => by
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.1 hx; exact_mod_cast Nat.factorial_pos i
  field_simp

/-- **Defining identity of the complete Bell polynomials** (`paper.tex`, Section 2.1):
`exp(∑_{j ≥ 1} a_j z^j / j!) = ∑_{r ≥ 0} B_r(a_1, …, a_r) z^r / r!`, where the left-hand side
is written as the (convergent, in the coefficientwise topology) infinite product
`∏_{j ≥ 1} exp(a_j z^j / j!)`. -/
theorem hasProd_completeBell [TopologicalSpace R] [T2Space R] (a : ℕ → R) :
    HasProd (fun j => expMonomial (algebraMap ℚ R (1 / ((j + 1).factorial : ℚ)) * a (j + 1)) j)
      (PowerSeries.mk fun r => algebraMap ℚ R (1 / (r.factorial : ℚ)) * completeBell r a) := by
  have hp := Nat.Partition.hasProd_genFun
    (expChar fun i => algebraMap ℚ R (1 / (i.factorial : ℚ)) * a i)
  simp only [genFun_factor_eq] at hp
  convert hp using 1
  ext r
  rw [coeff_mk, completeBell_eq_coeff, ← mul_assoc, ← map_mul,
    one_div_mul_cancel (by exact_mod_cast (Nat.factorial_pos r).ne'), map_one, one_mul]

/-- `B_2(a_1, a_2) = a_1^2 + a_2`. -/
lemma completeBell_two (a : ℕ → R) : completeBell 2 a = a 1 ^ 2 + a 2 := by
  rw [completeBell_eq_coeff]
  set c : ℕ → R := fun i => algebraMap ℚ R (1 / (i.factorial : ℚ)) * a i with hc
  have hD := derivativeFun_genFun_expChar c
  have e0 := congrArg (coeff 0) hD
  have e1 := congrArg (coeff 1) hD
  have h0 := constantCoeff_genFun_expChar c
  rw [← coeff_zero_eq_constantCoeff_apply] at h0
  simp only [coeff_derivativeFun, coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton, coeff_mk, h0] at e0 e1
  have c1 : c 1 = a 1 := by simp [hc]
  have c2 : c 2 = algebraMap ℚ R (1 / 2) * a 2 := by simp [hc, Nat.factorial]
  have h2 : algebraMap ℚ R ((Nat.factorial 2 : ℕ) : ℚ) = 2 := by
    simp [Nat.factorial, map_ofNat]
  rw [h2]
  have hhalf : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
    rw [show (2 : R) = algebraMap ℚ R 2 by simp [map_ofNat], ← map_mul]; norm_num
  simp only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul, mul_one, one_add_one_eq_two] at e0 e1
  rw [c1] at e0
  rw [c1, c2, e0] at e1
  linear_combination e1 + a 2 * hhalf

end LatticeTiling
