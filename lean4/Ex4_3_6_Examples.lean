module

public import RequestProject.Compute
public import RequestProject.Lem2_4_5_Period

/-!
# Examples `ex:t6k1p5`, `ex:t3k2p5`, `ex:t4k3p11` and Corollaries `cor:t6k1`, `cor:t3k2`, `cor:t4k3`

`paper.tex`, Section 4. We turn Theorem `thm:ideal` into a finite, machine-checkable criterion:

* the coefficients `c_λ` of `eq:defclambda` are computed explicitly as
  `c_λ = ∑_{j=0}^{t} w_j(λ) |𝓑(n,t-j,k,k)|` with explicit rational weights `w_j(λ)`;
* `|𝓑(n,s,k,k)| mod p^e` is periodic in `n` with period dividing `p^{e + ⌊log_p t⌋}` for
  `s ≤ t` (the periodicity argument of Example `ex:t6k1p5`, via Lemma `lem:period`);
* a sufficient condition for the ideal membership `f_{(p-1)/2} ∈ (f_1, …, f_{(p-1)/2-1})` that
  only involves the residues of the `c_λ` modulo `p`.

The resulting finite checks are then carried out by evaluation.
-/

@[expose] public section

open Finset PowerSeries

namespace LatticeTiling

/-! ### Computable coefficients `c_λ` -/

lemma convCoeff_perm (k : ℕ) {L L' : List ℕ} (h : L.Perm L') (j : ℕ) :
    convCoeff (L.map fun i l => dCoeff k (2 * i) l) j =
      convCoeff (L'.map fun i l => dCoeff k (2 * i) l) j := by
  have key : ∀ L : List ℕ, convCoeff (L.map fun i l => dCoeff k (2 * i) l) j =
      coeff j ((L.map fun i => dSeries k (2 * i)).prod) := by
    intro L
    rw [coeff_list_prod, List.map_map]
    congr 2
    funext i l
    simp [coeff_dSeries]
  rw [key, key, (h.map _).prod_eq]

/-- The weight `w_j(λ) = (2r)!/∏_j m_j(λ)! · [q^j] ∏_i d_{2λ_i}(q,k)` as a computable function
of the partition `λ ⊢ r`. -/
def cWeightP (k r : ℕ) (μ : r.Partition) (j : ℕ) : ℚ :=
  ((2 * r).factorial : ℚ) / (multFactorialProd μ : ℚ) *
    Quot.lift (fun L : List ℕ => convCoeff (L.map fun i l => dCoeff k (2 * i) l) j)
      (fun _ _ h => convCoeff_perm k h j) μ.parts

lemma cWeightP_eq (k r : ℕ) (μ : r.Partition) (L : List ℕ) (hL : μ.parts = (L : Multiset ℕ))
    (j : ℕ) : cWeightP k r μ j = cWeight k r L (multFactorialProd μ) j := by
  unfold cWeightP
  rw [hL]
  rfl

/-- The integer combination `∑_{j=0}^t num(w_j(λ)) |𝓑(n,t-j,k,k)|`; it equals `c_λ` as soon as
all weights `w_j(λ)` are integers (`cLambda_eq_cIntZ`). -/
def cIntZ (n t k r : ℕ) (μ : r.Partition) : ℤ :=
  ∑ j ∈ range (t + 1), (cWeightP k r μ j).num * (bsize n (t - j) k : ℤ)

lemma cLambda_eq_cIntZ (n t k r : ℕ) (μ : r.Partition)
    (hden : ∀ j < t + 1, (cWeightP k r μ j).den = 1) :
    cLambda n t k r μ = cIntZ n t k r μ := by
  have h := cLambda_cast n t k r μ
  rw [cLambdaQ_eq_sum n t k r μ μ.parts.toList (by simp)] at h
  apply Int.cast_injective (α := ℚ)
  rw [h, cIntZ]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Rat.coe_int_num_of_den_eq_one (hden j (mem_range.1 hj)),
    cWeightP_eq k r μ μ.parts.toList (by simp)]

/-- `c_λ = ∑_{j=0}^{t} w_j(λ) |𝓑(n,t-j,k,k)|` (over `ℚ`). -/
lemma cLambda_cast_eq_sum (n t k r : ℕ) (μ : r.Partition) :
    (cLambda n t k r μ : ℚ) = ∑ j ∈ range (t + 1), cWeightP k r μ j * (bsize n (t - j) k : ℚ) := by
  rw [cLambda_cast, cLambdaQ_eq_sum n t k r μ μ.parts.toList (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cWeightP_eq k r μ μ.parts.toList (by simp)]

/-- `|𝓑(n,s,k,k)| = ∑_{i=0}^{s} (2k)^i n(n-1)⋯(n-i+1)/i!` as a polynomial expression in `n`. -/
lemma bsize_cast (n s k : ℕ) : (bsize n s k : ℚ) =
    ∑ i ∈ range (s + 1), (2 * k : ℚ) ^ i * ((descPochhammer ℚ i).eval (n : ℚ) / i.factorial) := by
  unfold bsize
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_choose_eq_descPochhammer_div]

/-- The partition of `r` with the given list of parts (used to name specific partitions such as
`(2,1,1) ⊢ 4` in the examples). -/
def partOf (r : ℕ) (L : List ℕ) (h1 : ∀ i ∈ L, 0 < i) (h2 : L.sum = r) : r.Partition :=
  ⟨(L : Multiset ℕ), fun hi => h1 _ (by simpa using hi), by simpa using h2⟩

/-! ### Periodicity -/

lemma choose_add_cast_eq {p : ℕ} (hp : p.Prime) {e h N i : ℕ} (he : 1 ≤ e)
    (hN : p ^ (e - 1 + h) ∣ N) (hi : i < p ^ h) (n : ℕ) :
    (((n + N).choose i : ℕ) : ZMod (p ^ e)) = ((n.choose i : ℕ) : ZMod (p ^ e)) := by
  rw [Nat.add_choose_eq]
  push_cast
  rw [Finset.sum_eq_single (i, 0)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    rw [mem_antidiagonal] at hab
    have hb : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · exact absurd (by simp at hab; simp [hab]) hne
      · exact hb
    have hd := prime_pow_dvd_choose hp hN hb (by omega)
    rw [Nat.sub_add_cancel he] at hd
    simp only
    rw [(ZMod.natCast_eq_zero_iff _ _).2 hd, mul_zero]
  · intro h; simp at h

lemma bsize_add_cast_eq {p : ℕ} (hp : p.Prime) {e h N : ℕ} (he : 1 ≤ e)
    (hN : p ^ (e - 1 + h) ∣ N) {s : ℕ} (hs : s < p ^ h) (n k : ℕ) :
    ((bsize (n + N) s k : ℕ) : ZMod (p ^ e)) = ((bsize n s k : ℕ) : ZMod (p ^ e)) := by
  unfold bsize
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have := choose_add_cast_eq hp he hN (lt_of_le_of_lt (Nat.lt_succ_iff.1 (mem_range.1 hi)) hs) n
  push_cast at this
  rw [this]

lemma cIntZ_add_cast_eq {p : ℕ} (hp : p.Prime) {e h N : ℕ} (he : 1 ≤ e)
    (hN : p ^ (e - 1 + h) ∣ N) {t : ℕ} (ht : t < p ^ h) (n k r : ℕ) (μ : r.Partition) :
    ((cIntZ (n + N) t k r μ : ℤ) : ZMod (p ^ e)) = ((cIntZ n t k r μ : ℤ) : ZMod (p ^ e)) := by
  unfold cIntZ
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have := bsize_add_cast_eq hp he hN (s := t - j) (by omega) n k
  push_cast at this
  rw [this]

/-! ### A sufficient condition for the ideal membership -/

lemma exists_part_lt_of_ne_indiscrete {j : ℕ} (μ : j.Partition)
    (hμ : μ ≠ Nat.Partition.indiscrete j) : ∃ i ∈ μ.parts, i < j := by
  by_contra hcon
  push_neg at hcon
  apply hμ
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact Subsingleton.elim _ _
  have hall : ∀ i ∈ μ.parts, i = j := fun i hi =>
    le_antisymm (μ.parts_sum ▸ Multiset.le_sum_of_mem hi) (hcon i hi)
  have hrep : μ.parts = Multiset.replicate μ.parts.card j := Multiset.eq_replicate.2 ⟨rfl, hall⟩
  have hsum := μ.parts_sum
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hc : μ.parts.card = 1 := by
    have : μ.parts.card * j = 1 * j := by rw [hsum, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hj this
  ext1
  rw [Nat.Partition.indiscrete_parts hj.ne', hrep, hc]
  rfl

/-- **A sufficient condition for `f_{(p-1)/2} ∈ (f_1, …, f_{(p-1)/2-1})`.** Let `J < (p-1)/2`.
If `c_{(j)} ≢ 0 (mod p)` for the one-part partitions `(j)`, `1 ≤ j ≤ J` (so that
`Y_1, …, Y_J` lie in the ideal), and every `λ ⊢ (p-1)/2` with `c_λ ≢ 0 (mod p)` has a part
`≤ J`, then `f_{(p-1)/2}` lies in the ideal generated by `f_1, …, f_{(p-1)/2-1}`. -/
theorem fPoly_mem_span_of (p : ℕ) [Fact p.Prime] (c : (r : ℕ) → r.Partition → ℤ) (J : ℕ)
    (hJ : J < (p - 1) / 2)
    (hunit : ∀ j, 1 ≤ j → j ≤ J → ((c j (Nat.Partition.indiscrete j) : ℤ) : ZMod p) ≠ 0)
    (hzero : ∀ μ : ((p - 1) / 2).Partition,
      ((c _ μ : ℤ) : ZMod p) = 0 ∨ ∃ i ∈ μ.parts, i ≤ J) :
    fPoly p c ((p - 1) / 2) ∈ Ideal.span (fPoly p c '' Set.Ico 1 ((p - 1) / 2)) := by
  set m := (p - 1) / 2 with hm
  set I := Ideal.span (fPoly p c '' Set.Ico 1 m) with hI
  have hprod : ∀ {r : ℕ} (μ : r.Partition) (a : ZMod p) (i : ℕ), i ∈ μ.parts →
      yVar p m i ∈ I → MvPolynomial.C a * (μ.parts.map fun j => yVar p m j).prod ∈ I := by
    intro r μ a i hi hYi
    obtain ⟨d, hd⟩ := Multiset.dvd_prod (Multiset.mem_map_of_mem (fun j => yVar p m j) hi)
    rw [hd]
    exact I.mul_mem_left _ (I.mul_mem_right _ hYi)
  have hY : ∀ j, 1 ≤ j → j ≤ J → yVar p m j ∈ I := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj1 hjJ
      have hf : fPoly p c j ∈ I := Ideal.subset_span ⟨j, ⟨hj1, by omega⟩, rfl⟩
      rw [fPoly, ← Finset.add_sum_erase _ _ (mem_univ (Nat.Partition.indiscrete j)),
        Nat.Partition.indiscrete_parts (by omega)] at hf
      have hrest : ∑ μ ∈ univ.erase (Nat.Partition.indiscrete j),
          MvPolynomial.C ((c j μ : ℤ) : ZMod p) * (μ.parts.map fun j => yVar p m j).prod ∈ I := by
        refine I.sum_mem fun μ hμ => ?_
        obtain ⟨i, hi, hij⟩ := exists_part_lt_of_ne_indiscrete μ (Finset.ne_of_mem_erase hμ)
        exact hprod μ _ i hi (ih i hij (μ.parts_pos hi) (by omega))
      have h1 := (I.add_mem_iff_left hrest).1 hf
      simp only [Multiset.map_singleton, Multiset.prod_singleton] at h1
      have hu := hunit j hj1 hjJ
      rw [show yVar p m j = MvPolynomial.C (((c j (Nat.Partition.indiscrete j) : ℤ) : ZMod p))⁻¹ *
          (MvPolynomial.C ((c j (Nat.Partition.indiscrete j) : ℤ) : ZMod p) * yVar p m j) by
        rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hu, MvPolynomial.C_1, one_mul]]
      exact I.mul_mem_left _ h1
  rw [fPoly]
  refine I.sum_mem fun μ _ => ?_
  rcases hzero μ with h0 | ⟨i, hi, hiJ⟩
  · rw [h0, MvPolynomial.C_0, zero_mul]; exact I.zero_mem
  · exact hprod μ _ i hi (hY i (μ.parts_pos hi) hiJ)

/-! ### The finite criterion -/

/-- **Finite criterion derived from Theorem `thm:ideal`** (`paper.tex`, Section 4, the procedure
of Example `ex:t6k1p5` and Appendix `app:maple-ideal`). Let `p > 2` be prime, `J < (p-1)/2`
and put `P = p^{2 + ⌊log_p t⌋}`. Suppose that for the residue `n₀`:
* `p ∣ |𝓑(n₀,t,k,k)|` and `p² ∤ |𝓑(n₀,t,k,k)|`;
* all weights `w_j(λ)` (`λ ⊢ r ≤ (p-1)/2`, `j ≤ t`) are integers;
* `c_{(j)}(n₀) ≢ 0 (mod p)` for `1 ≤ j ≤ J`, and every `λ ⊢ (p-1)/2` with
  `c_λ(n₀) ≢ 0 (mod p)` has a part `≤ J`.
Then for every `n ≡ n₀ (mod P)` there is no lattice tiling of `ℤⁿ` by `𝓑(n,t,k,k)`. -/
theorem no_lattice_tiling_of_residue (t k p J n₀ : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hJ : J < (p - 1) / 2)
    (hdiv : bsize n₀ t k % p = 0) (hndiv : bsize n₀ t k % p ^ 2 ≠ 0)
    (hden : ∀ r < (p - 1) / 2 + 1, ∀ μ : r.Partition, ∀ j < t + 1, (cWeightP k r μ j).den = 1)
    (hunit : ∀ j < J + 1, 1 ≤ j → cIntZ n₀ t k j (Nat.Partition.indiscrete j) % p ≠ 0)
    (hzero : ∀ μ : ((p - 1) / 2).Partition,
      cIntZ n₀ t k _ μ % p = 0 ∨ ¬ ∀ i ∈ μ.parts, J < i)
    (n : ℕ) (hn : n % p ^ (2 + Nat.log p t) = n₀) :
    ¬ HasLatticeTiling (ball n t k k : Set (Fin n → ℤ)) := by
  have hpp := hp.out
  set L := Nat.log p t
  set P := p ^ (2 + L) with hP
  have ht : t < p ^ (L + 1) := Nat.lt_pow_succ_log_self hpp.one_lt t
  have hnP : n = n₀ + P * (n / P) := by rw [← hn]; exact (Nat.mod_add_div n P).symm
  have hB : ∀ q, ((bsize (n₀ + P * q) t k : ℕ) : ZMod (p ^ 2)) = bsize n₀ t k := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, ← add_assoc, bsize_add_cast_eq hpp (e := 2) (h := L + 1) (by norm_num)
        (by rw [hP]; ring_nf; rfl) ht, ih]
  have hC : ∀ q r (μ : r.Partition),
      ((cIntZ (n₀ + P * q) t k r μ : ℤ) : ZMod p) = cIntZ n₀ t k r μ := by
    intro q r μ
    induction q with
    | zero => simp
    | succ q ih =>
      have := cIntZ_add_cast_eq hpp (e := 1) (h := L + 1) le_rfl
        (show p ^ (1 - 1 + (L + 1)) ∣ P from pow_dvd_pow p (by omega)) ht (n₀ + P * q) k r μ
      have h' := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 this
      rw [pow_one] at h'
      rw [Nat.mul_succ, ← add_assoc, ← ih]
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 h'
  have hBn : bsize n t k % p ^ 2 = bsize n₀ t k % p ^ 2 := by
    rw [← ZMod.natCast_eq_natCast_iff', hnP, hB]
  have hdvd : p ∣ bsize n t k := by
    rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_mod_of_dvd _ (dvd_pow_self p two_ne_zero), hBn,
      Nat.mod_mod_of_dvd _ (dvd_pow_self p two_ne_zero), hdiv]
  have hcard : (ball n t k k).card = p * (bsize n t k / p) := by
    rw [card_ball_eq_bsize, Nat.mul_div_cancel' hdvd]
  have hM : ¬ p ∣ bsize n t k / p := by
    rintro ⟨d, hd⟩
    apply hndiv
    rw [← hBn, Nat.dvd_iff_mod_eq_zero.mp]
    exact ⟨d, by rw [← Nat.mul_div_cancel' hdvd, hd]; ring⟩
  have hcl : ∀ r ≤ (p - 1) / 2, ∀ μ : r.Partition,
      ((cLambda n t k r μ : ℤ) : ZMod p) = cIntZ n₀ t k r μ := by
    intro r hr μ
    rw [cLambda_eq_cIntZ n t k r μ (hden r (by omega) μ), hnP, hC]
  refine no_lattice_tiling_of_mem_ideal' n t k p _ hp2 hcard hM
    (fPoly_mem_span_of p _ J hJ (fun j hj1 hjJ => ?_) (fun μ => ?_))
  · rw [hcl j (by omega), Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    exact hunit j (by omega) hj1
  · rw [hcl _ le_rfl, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    rcases hzero μ with h | h
    · exact Or.inl h
    · push_neg at h; exact Or.inr h

end LatticeTiling
