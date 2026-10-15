module

public import RequestProject.Def2_7_Defs

/-!
# `p`-adic valuation and periodicity preliminaries

Formalization of `paper.tex`, Section 2.3: Lemma `lem:cahen-chabert` (in the case `V = ℤ`
localised at `p`, i.e. with the `p`-adic valuation on `ℤ`, which is the case used in the paper)
and Lemma `lem:period`.
-/

@[expose] public section

open Finset Polynomial
open scoped fwdDiff

namespace LatticeTiling

/-- A polynomial `f ∈ ℚ[X]` is **integer-valued** if `f(ℤ) ⊆ ℤ` (`paper.tex`, Section 2.3,
the ring `Int(ℤ)` of integer-valued polynomials). -/
def IsIntValued (f : ℚ[X]) : Prop := ∀ x : ℤ, ∃ m : ℤ, f.eval (x : ℚ) = m

/-- If `p^(s+h) ∣ N` and `1 ≤ j < p^h`, then `p^(s+1) ∣ \binom{N}{j}`. -/
lemma prime_pow_dvd_choose {p : ℕ} (hp : p.Prime) {N j s h : ℕ} (hN : p ^ (s + h) ∣ N)
    (hj0 : 1 ≤ j) (hjh : j < p ^ h) : p ^ (s + 1) ∣ N.choose j := by
  have hj : j ≠ 0 := by omega
  have key : j * N.choose j = N * (N - 1).choose (j - 1) := by
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp [Nat.choose_eq_zero_of_lt (by omega : 0 < j)]
    · obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have := Nat.add_one_mul_choose_eq N' j'
      linarith [this, mul_comm (N'.choose j') (N' + 1)]
  have h1 : p ^ (s + h) ∣ j * N.choose j := key ▸ Dvd.dvd.mul_right hN _
  set v := j.factorization p with hv
  have hdecomp := Nat.ordProj_mul_ordCompl_eq_self j p
  have hcop : Nat.Coprime p (ordCompl[p] j) := Nat.coprime_ordCompl hp hj
  have hvle : p ^ v ≤ j := Nat.ordProj_le p hj
  have hvh : v < h := by
    have : p ^ v < p ^ h := lt_of_le_of_lt hvle hjh
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 this
  have h1' : p ^ v * (ordCompl[p] j * N.choose j) = j * N.choose j := by
    rw [← mul_assoc, hdecomp]
  rw [← h1'] at h1
  have h2 : p ^ (s + h - v) ∣ ordCompl[p] j * N.choose j := by
    have e : p ^ (s + h) = p ^ v * p ^ (s + h - v) := by
      rw [← pow_add]; congr 1; omega
    rw [e] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h1
  have h3 : p ^ (s + h - v) ∣ N.choose j :=
    (Nat.Coprime.pow_left _ hcop).dvd_of_dvd_mul_left h2
  exact (pow_dvd_pow p (by omega)).trans h3

/-- Iterated forward differences of an integer-valued polynomial take integer values at
integers. -/
lemma fwdDiff_iter_int {f : ℚ[X]} (hf : IsIntValued f) (j : ℕ) (a : ℤ) :
    ∃ m : ℤ, (fwdDiff (1 : ℚ))^[j] f.eval (a : ℚ) = m := by
  rw [fwdDiff_iter_eq_sum_shift]
  choose g hg using hf
  refine ⟨∑ i ∈ range (j + 1), (-1) ^ (j - i) * j.choose i * g (a + i), ?_⟩
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul, nsmul_eq_mul, mul_one, ← hg]
  push_cast; ring

/-- The forward-step version of Lemma `lem:cahen-chabert` over `ℤ`. -/
lemma cahenChabert_aux (p : ℕ) [hp : Fact p.Prime] {f : ℚ[X]} (hf : IsIntValued f)
    (s h : ℕ) (hdeg : f.natDegree < p ^ h) (a : ℤ) (N : ℕ) (hN : p ^ (s + h) ∣ N) :
    ∃ z : ℤ, f.eval ((a : ℚ) + N) - f.eval (a : ℚ) = (p : ℚ) ^ (s + 1) * z := by
  have hshift := shift_eq_sum_fwdDiff_iter (1 : ℚ) f.eval N (a : ℚ)
  rw [nsmul_eq_mul, mul_one] at hshift
  rw [hshift, Finset.sum_range_succ', Nat.choose_zero_right, one_smul,
    Function.iterate_zero_apply, add_sub_cancel_right]
  have hterm : ∀ i ∈ range N, ∃ z : ℤ,
      N.choose (i + 1) • (fwdDiff (1 : ℚ))^[i + 1] f.eval (a : ℚ) = (p : ℚ) ^ (s + 1) * z := by
    intro i _
    obtain ⟨m, hm⟩ := fwdDiff_iter_int hf (i + 1) a
    by_cases hi : i + 1 ≤ f.natDegree
    · obtain ⟨c, hc⟩ := prime_pow_dvd_choose (j := i + 1) hp.out hN (by omega) (by omega)
      refine ⟨c * m, ?_⟩
      rw [hm, hc, nsmul_eq_mul]; push_cast; ring
    · refine ⟨0, ?_⟩
      rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by omega)]
      simp
  choose z hz using hterm
  refine ⟨∑ i ∈ (range N).attach, z i.1 i.2, ?_⟩
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_attach]
  exact Finset.sum_congr rfl fun i _ => hz i.1 i.2

/-- **Lemma `lem:cahen-chabert`** (`paper.tex`, Section 2.3; Cahen–Chabert, Proposition III.3.1,
in the case `V = ℤ` with the `p`-adic valuation `v = v_p`, so that `q = p`; cf. Gilmer–Smith for
`V = ℤ`): let `h` be a nonnegative integer and `f` an integer-valued polynomial with
`deg f < p^h`. Then for every `s` and all `a, b ∈ ℤ`,
`v_p(b - a) ≥ s + h ⟹ v_p(f(b) - f(a)) ≥ s + 1`.

The valuation inequalities are expressed as divisibilities: `p^(s+h) ∣ b - a` and
`f(b) - f(a) = p^(s+1) z` with `z ∈ ℤ`. Here `s, h ∈ ℕ`; for `s < 0` the conclusion is trivial
since `f(b) - f(a) ∈ ℤ`. -/
theorem cahenChabert_int (p : ℕ) [Fact p.Prime] {f : ℚ[X]} (hf : IsIntValued f)
    (s h : ℕ) (hdeg : f.natDegree < p ^ h) (a b : ℤ) (hab : (p : ℤ) ^ (s + h) ∣ b - a) :
    ∃ z : ℤ, f.eval (b : ℚ) - f.eval (a : ℚ) = (p : ℚ) ^ (s + 1) * z := by
  rcases le_total a b with hle | hle
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, b - a = N := ⟨(b - a).toNat, by omega⟩
    have hN' : p ^ (s + h) ∣ N := by exact_mod_cast hN ▸ hab
    obtain ⟨z, hz⟩ := cahenChabert_aux p hf s h hdeg a N hN'
    refine ⟨z, ?_⟩
    rw [show (b : ℚ) = a + N by exact_mod_cast (by omega : b = a + N)]
    exact hz
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, a - b = N := ⟨(a - b).toNat, by omega⟩
    have hN' : p ^ (s + h) ∣ N := by
      have : (p : ℤ) ^ (s + h) ∣ a - b := by
        rw [show a - b = -(b - a) by ring]; exact (dvd_neg).2 hab
      exact_mod_cast hN ▸ this
    obtain ⟨z, hz⟩ := cahenChabert_aux p hf s h hdeg b N hN'
    refine ⟨-z, ?_⟩
    rw [show (a : ℚ) = b + N by exact_mod_cast (by omega : a = b + N)]
    push_cast
    linarith

/-- **Lemma `lem:period`** (`paper.tex`, Section 2.3): let `f` be an integer-valued polynomial of
degree `d` and let `p` be a prime. Then for every integer `n` and every `e ≥ 1`,
`f(n + p^(e + ⌊log_p d⌋)) ≡ f(n) (mod p^e)`.

The congruence is expressed as `f(n + p^(e + ⌊log_p d⌋)) - f(n) = p^e z` with `z ∈ ℤ`;
`⌊log_p d⌋` is `Nat.log p d`. The paper assumes `d ≥ 1` and `e ≥ 1`; neither assumption is
needed for the statement as formalized here. -/
theorem period (p : ℕ) [hp : Fact p.Prime] {f : ℚ[X]} (hf : IsIntValued f) (n : ℤ) (e : ℕ) :
    ∃ z : ℤ, f.eval ((n : ℚ) + (p : ℚ) ^ (e + Nat.log p f.natDegree)) - f.eval (n : ℚ) =
      (p : ℚ) ^ e * z := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · obtain ⟨m₁, hm₁⟩ := hf (n + (p : ℤ) ^ (0 + Nat.log p f.natDegree))
    obtain ⟨m₂, hm₂⟩ := hf n
    refine ⟨m₁ - m₂, ?_⟩
    push_cast at hm₁
    rw [hm₁, hm₂]; push_cast; ring
  · have hdeg : f.natDegree < p ^ (Nat.log p f.natDegree + 1) :=
      Nat.lt_pow_succ_log_self hp.out.one_lt _
    have hab : (p : ℤ) ^ ((e - 1) + (Nat.log p f.natDegree + 1)) ∣
        (n + (p : ℤ) ^ (e + Nat.log p f.natDegree)) - n := by
      rw [add_sub_cancel_left, show e - 1 + (Nat.log p f.natDegree + 1) =
        e + Nat.log p f.natDegree by omega]
    obtain ⟨z, hz⟩ := cahenChabert_int p hf (e - 1) _ hdeg n _ hab
    refine ⟨z, ?_⟩
    rw [show e - 1 + 1 = e by omega] at hz
    push_cast at hz
    exact hz

/-- **Lemma `lem:period`, "in particular" part** (`paper.tex`, Section 2.3): if the degree `d`
of the integer-valued polynomial `f` satisfies `d < p`, then `f(n + p^e) ≡ f(n) (mod p^e)`,
so the period of `f(n) mod p^e` divides `p^e`. -/
theorem period_of_natDegree_lt (p : ℕ) [hp : Fact p.Prime] {f : ℚ[X]} (hf : IsIntValued f)
    (hd : f.natDegree < p) (n : ℤ) (e : ℕ) :
    ∃ z : ℤ, f.eval ((n : ℚ) + (p : ℚ) ^ e) - f.eval (n : ℚ) = (p : ℚ) ^ e * z := by
  have := period p hf n e
  rwa [Nat.log_of_lt hd, add_zero] at this

end LatticeTiling
