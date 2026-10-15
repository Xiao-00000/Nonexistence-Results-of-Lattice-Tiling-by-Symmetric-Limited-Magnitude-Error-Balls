module

public import RequestProject.Thm2_6_Kummer
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Strength of the condition `v_3 \binom{n-1}{t} = 1`

Formalization of the end of `paper.tex`, Section 5: Theorem `thm:asymptotic-ratio` and its proof
(the counts `A_k`, `B_k`, `C_k = 6^k` of pairs with exactly one / no carry), and the numerical table
for `M = 100, 500, 1000`.
-/

@[expose] public section

open Finset

namespace LatticeTiling

/-! ### Carries in base 3 of numbers below `3^K` -/

/-- The number of carries among the lowest `K` digit positions of the base-`3` addition of `t`
and `s`: `#{1 ≤ i ≤ K : 3^i ≤ (t mod 3^i) + (s mod 3^i)}`. -/
def cnt3 (K t s : ℕ) : ℕ :=
  ∑ i ∈ range K, if 3 ^ (i + 1) ≤ t % 3 ^ (i + 1) + s % 3 ^ (i + 1) then 1 else 0

lemma carries_eq_cnt3 (K t s : ℕ) (ht : t < 3 ^ K) (hs : s < 3 ^ K) :
    carries 3 t s = cnt3 K t s := by
  have hc : ∀ i, carry 3 t s i = if 3 ^ i ≤ t % 3 ^ i + s % 3 ^ i then 1 else 0 :=
    carry_eq_ite 3 t s (by norm_num)
  have e1 : cnt3 K t s = ∑ i ∈ Ico 1 (K + 1), carry 3 t s i := by
    rw [Finset.sum_Ico_eq_sum_range, cnt3, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by rw [hc, add_comm 1 i]
  rw [e1, carries]
  have hsub1 : Ico 1 (t + s + 1) ⊆ Ico 1 (t + s + K + 1) := Ico_subset_Ico le_rfl (by omega)
  have hsub2 : Ico 1 (K + 1) ⊆ Ico 1 (t + s + K + 1) := Ico_subset_Ico le_rfl (by omega)
  rw [Finset.sum_subset hsub1, Finset.sum_subset hsub2]
  · intro i hi hni
    simp only [mem_Ico] at hi hni
    rw [hc, if_neg]
    have hK : 3 ^ K < 3 ^ i := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have : 3 ^ i = 3 * 3 ^ (i - 1) := by rw [← pow_succ']; congr 1; omega
    have : 3 ^ K ≤ 3 ^ (i - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro i hi hni
    simp only [mem_Ico] at hi hni
    rw [hc, if_neg]
    have h1 := Nat.mod_le t (3 ^ i)
    have h2 := Nat.mod_le s (3 ^ i)
    have h3 : i < 3 ^ i := Nat.lt_pow_self (by norm_num)
    omega

/-- Splitting a sum over `[0, mN)` according to the quotient and remainder modulo `N`. -/
lemma sum_range_mul_eq {β : Type*} [AddCommMonoid β] (m N : ℕ) (f : ℕ → β) :
    ∑ t ∈ range (m * N), f t = ∑ a ∈ range m, ∑ t ∈ range N, f (a * N + t) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma mod_pow_of_lt (K i a t : ℕ) (hi : i < K) :
    (a * 3 ^ K + t) % 3 ^ (i + 1) = t % 3 ^ (i + 1) := by
  obtain ⟨c, hc⟩ : 3 ^ (i + 1) ∣ 3 ^ K := pow_dvd_pow 3 (by omega)
  rw [hc, show a * (3 ^ (i + 1) * c) + t = t + 3 ^ (i + 1) * (a * c) by ring,
    Nat.add_mul_mod_self_left]

lemma lt_three_pow_succ (K a t : ℕ) (ha : a < 3) (ht : t < 3 ^ K) : a * 3 ^ K + t < 3 ^ (K + 1) := by
  have : a * 3 ^ K ≤ 2 * 3 ^ K := Nat.mul_le_mul_right _ (by omega)
  rw [pow_succ]; omega

lemma cnt3_succ (K a b t s : ℕ) (ht : t < 3 ^ K) (hs : s < 3 ^ K) (ha : a < 3) (hb : b < 3) :
    cnt3 (K + 1) (a * 3 ^ K + t) (b * 3 ^ K + s) =
      cnt3 K t s + if 3 ^ (K + 1) ≤ a * 3 ^ K + t + (b * 3 ^ K + s) then 1 else 0 := by
  rw [cnt3, sum_range_succ, cnt3]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => by
      rw [mod_pow_of_lt K i a t (mem_range.1 hi), mod_pow_of_lt K i b s (mem_range.1 hi)]
  · rw [Nat.mod_eq_of_lt (lt_three_pow_succ K a t ha ht),
      Nat.mod_eq_of_lt (lt_three_pow_succ K b s hb hs)]

lemma cnt3_pos (K t s : ℕ) (ht : t < 3 ^ K) (hs : s < 3 ^ K) (h : 3 ^ K ≤ t + s) :
    1 ≤ cnt3 K t s := by
  rcases K with _ | K
  · simp at ht hs; omega
  · rw [cnt3, sum_range_succ, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hs, if_pos h]
    omega

/-- Splitting a double sum over `[0, 3^{K+1})²` by the top base-`3` digits. -/
lemma sum_sum_three_pow_succ (K : ℕ) (g : ℕ → ℕ → ℕ) :
    ∑ t ∈ range (3 ^ (K + 1)), ∑ s ∈ range (3 ^ (K + 1)), g t s =
      ∑ t ∈ range (3 ^ K), ∑ s ∈ range (3 ^ K), ∑ a ∈ range 3, ∑ b ∈ range 3,
        g (a * 3 ^ K + t) (b * 3 ^ K + s) := by
  rw [pow_succ', sum_range_mul_eq]
  simp_rw [sum_range_mul_eq 3 (3 ^ K)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  calc _ = ∑ a ∈ range 3, ∑ s ∈ range (3 ^ K), ∑ b ∈ range 3,
        g (a * 3 ^ K + t) (b * 3 ^ K + s) := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma split_cond (N x j : ℕ) (hx : x < 2 * N) (hj : j ≤ 4) :
    (j * N + x < 3 * N ↔ j + (if N ≤ x then 1 else 0) ≤ 2) := by
  interval_cases j <;> split_ifs <;> omega

lemma sum_nine (h : ℕ → ℕ) :
    ∑ a ∈ range 3, ∑ b ∈ range 3, h (a + b) = h 0 + 2 * h 1 + 3 * h 2 + 2 * h 3 + h 4 := by
  simp only [sum_range_succ, sum_range_zero]; ring

/-- The number `A_K` of pairs `(t,s) ∈ [0,3^K)²` with `t + s < 3^K` and exactly one carry
(`paper.tex`, proof of Theorem `thm:asymptotic-ratio`). -/
def countA (K : ℕ) : ℕ := ∑ t ∈ range (3 ^ K), ∑ s ∈ range (3 ^ K),
  if t + s < 3 ^ K ∧ cnt3 K t s = 1 then 1 else 0

/-- The number `B_K` of pairs `(t,s) ∈ [0,3^K)²` with `t + s ≥ 3^K` and exactly one carry. -/
def countB (K : ℕ) : ℕ := ∑ t ∈ range (3 ^ K), ∑ s ∈ range (3 ^ K),
  if 3 ^ K ≤ t + s ∧ cnt3 K t s = 1 then 1 else 0

/-- The number `C_K` of pairs `(t,s) ∈ [0,3^K)²` without any carry. -/
def countC (K : ℕ) : ℕ := ∑ t ∈ range (3 ^ K), ∑ s ∈ range (3 ^ K),
  if cnt3 K t s = 0 then 1 else 0

lemma inner_rewrite (K t s : ℕ) (ht : t < 3 ^ K) (hs : s < 3 ^ K) (P : ℕ → ℕ → Prop)
    [DecidableRel P] :
    ∑ a ∈ range 3, ∑ b ∈ range 3,
      (if P (a * 3 ^ K + t + (b * 3 ^ K + s)) (cnt3 (K + 1) (a * 3 ^ K + t) (b * 3 ^ K + s))
        then 1 else 0) =
    ∑ a ∈ range 3, ∑ b ∈ range 3,
      (if P ((a + b) * 3 ^ K + (t + s)) (cnt3 K t s +
        if ¬ (a + b + (if 3 ^ K ≤ t + s then 1 else 0) ≤ 2) then 1 else 0) then 1 else 0) := by
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have ha' := mem_range.1 ha
  have hb' := mem_range.1 hb
  rw [cnt3_succ K a b t s ht hs ha' hb', show a * 3 ^ K + t + (b * 3 ^ K + s) =
    (a + b) * 3 ^ K + (t + s) by ring]
  have hsc := split_cond (3 ^ K) (t + s) (a + b) (by omega) (by omega)
  congr 3
  rw [pow_succ, mul_comm (3 ^ K) 3]
  by_cases h : a + b + (if 3 ^ K ≤ t + s then 1 else 0) ≤ 2
  · rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_pos (by omega), if_pos (by omega)]

theorem countA_succ (K : ℕ) : countA (K + 1) = 6 * countA K + 3 * countB K := by
  rw [countA, sum_sum_three_pow_succ, countA, countB, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  have ht' := mem_range.1 ht
  have hs' := mem_range.1 hs
  rw [inner_rewrite K t s ht' hs' (fun x c => x < 3 ^ (K + 1) ∧ c = 1)]
  rw [sum_nine (fun j => if j * 3 ^ K + (t + s) < 3 ^ (K + 1) ∧ cnt3 K t s +
    (if ¬ (j + (if 3 ^ K ≤ t + s then 1 else 0) ≤ 2) then 1 else 0) = 1 then 1 else 0)]
  rw [pow_succ, mul_comm (3 ^ K) 3]
  by_cases hd : 3 ^ K ≤ t + s <;> by_cases hc : cnt3 K t s = 1 <;>
    simp [hd, hc] <;> (try split_ifs) <;> omega

theorem countB_succ (K : ℕ) : countB (K + 1) = 3 * countC K := by
  rw [countB, sum_sum_three_pow_succ, countC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have ht' := mem_range.1 ht
  have hs' := mem_range.1 hs
  rw [inner_rewrite K t s ht' hs' (fun x c => 3 ^ (K + 1) ≤ x ∧ c = 1)]
  rw [sum_nine (fun j => if 3 ^ (K + 1) ≤ j * 3 ^ K + (t + s) ∧ cnt3 K t s +
    (if ¬ (j + (if 3 ^ K ≤ t + s then 1 else 0) ≤ 2) then 1 else 0) = 1 then 1 else 0)]
  rw [pow_succ, mul_comm (3 ^ K) 3]
  have hpos := cnt3_pos K t s ht' hs'
  by_cases hd : 3 ^ K ≤ t + s <;> by_cases hc : cnt3 K t s = 0 <;>
    simp [hd, hc] <;> (try split_ifs) <;> omega

theorem countC_succ (K : ℕ) : countC (K + 1) = 6 * countC K := by
  rw [countC, sum_sum_three_pow_succ, countC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have ht' := mem_range.1 ht
  have hs' := mem_range.1 hs
  rw [inner_rewrite K t s ht' hs' (fun _ c => c = 0)]
  rw [sum_nine (fun j => if cnt3 K t s +
    (if ¬ (j + (if 3 ^ K ≤ t + s then 1 else 0) ≤ 2) then 1 else 0) = 0 then 1 else 0)]
  have hpos := cnt3_pos K t s ht' hs'
  by_cases hd : 3 ^ K ≤ t + s <;> by_cases hc : cnt3 K t s = 0 <;>
    (simp [hd, hc]; try omega)

/-- `C_k = 6^k` (`paper.tex`, proof of Theorem `thm:asymptotic-ratio`). -/
theorem countC_eq (K : ℕ) : countC K = 6 ^ K := by
  induction K with
  | zero => simp [countC, cnt3]
  | succ K ih => rw [countC_succ, ih, pow_succ]; ring

/-- `B_k = 3 · 6^{k-1}` for `k ≥ 1` (`paper.tex`, proof of Theorem `thm:asymptotic-ratio`). -/
theorem countB_eq (K : ℕ) : countB (K + 1) = 3 * 6 ^ K := by
  rw [countB_succ, countC_eq]

/-- `A_k = 9(k-1)6^{k-2}` for `k ≥ 2`, and `A_1 = 0` (`paper.tex`, proof of
Theorem `thm:asymptotic-ratio`). -/
theorem countA_eq (K : ℕ) : countA (K + 2) = 9 * (K + 1) * 6 ^ K := by
  induction K with
  | zero =>
    rw [countA_succ, countB_eq, countA_succ]
    simp [countA, countB, cnt3]
  | succ K ih =>
    rw [countA_succ, ih, countB_eq]; ring

/-! ### The ratio `P(M)` -/

/-- The numerator of `P(M)` (`paper.tex`, Theorem `thm:asymptotic-ratio`):
`#{(n,t) ∈ [1,M]² : n - 1 ≥ t, v_3 \binom{n-1}{t} = 1}`. -/
def pairCount (M : ℕ) : ℕ :=
  ((Icc 1 M ×ˢ Icc 1 M).filter fun x : ℕ × ℕ =>
    x.2 ≤ x.1 - 1 ∧ padicValNat 3 ((x.1 - 1).choose x.2) = 1).card

/-- The denominator of `P(M)`: `#{(n,t) ∈ [1,M]² : n - 1 ≥ t}`. -/
def pairTotal (M : ℕ) : ℕ :=
  ((Icc 1 M ×ˢ Icc 1 M).filter fun x : ℕ × ℕ => x.2 ≤ x.1 - 1).card

/-- **The ratio `P(M)`** of Theorem `thm:asymptotic-ratio` (`paper.tex`, Section 5). -/
noncomputable def ratioP (M : ℕ) : ℝ := (pairCount M : ℝ) / (pairTotal M : ℝ)

/-- `#{(n,t) ∈ [1,M]² : n - 1 ≥ t} = M(M-1)/2` (`paper.tex`, Section 5). -/
theorem pairTotal_mul_two (M : ℕ) : pairTotal M * 2 = M * (M - 1) := by
  have h1 : pairTotal M = ∑ n ∈ Icc 1 M, (n - 1) := by
    rw [pairTotal, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Finset.card_filter]
    have : (Icc 1 M).filter (fun t => t ≤ n - 1) = Icc 1 (n - 1) := by
      ext t; simp only [mem_filter, mem_Icc] at hn ⊢; omega
    rw [this, Nat.card_Icc]; omega
  rw [h1]
  clear h1
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    cases M <;> simp
    ring

/-- The number `E(M)` of pairs `(t,s) ∈ ℕ²` with `t + s < M` whose base-`3` addition has exactly
one carry (`paper.tex`, proof of Theorem `thm:asymptotic-ratio`). -/
def countE (M : ℕ) : ℕ :=
  ((range M ×ˢ range M).filter fun x : ℕ × ℕ => x.1 + x.2 < M ∧ carries 3 x.1 x.2 = 1).card

lemma carries_zero_left (s : ℕ) : carries 3 0 s = 0 := by
  rw [← kummer 3 0 s]; simp

/-- The numerator of `P(M)` equals `E(M)` (Kummer's theorem, `paper.tex`, proof of
Theorem `thm:asymptotic-ratio`). -/
theorem pairCount_eq_countE (M : ℕ) : pairCount M = countE M := by
  refine Finset.card_nbij' (fun x => (x.2, x.1 - 1 - x.2)) (fun y => (y.1 + y.2 + 1, y.1))
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_Icc] at hx
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_range]
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    rw [← kummer' 3 hx.2.1, hx.2.2]
  · intro y hy
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_range] at hy
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_Icc]
    have h1 : 1 ≤ y.1 := by
      rcases Nat.eq_zero_or_pos y.1 with h | h
      · have := hy.2.2; rw [h, carries_zero_left] at this; omega
      · exact h
    refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega, ?_⟩
    rw [show y.1 + y.2 + 1 - 1 = y.1 + y.2 by omega, kummer, hy.2.2]
  · intro x hx
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_Icc] at hx
    ext <;> simp
    omega
  · intro y hy
    ext <;> simp

lemma countE_mono {M M' : ℕ} (h : M ≤ M') : countE M ≤ countE M' := by
  apply Finset.card_le_card
  intro x hx
  simp only [mem_filter, mem_product, mem_range] at hx ⊢
  omega

lemma countE_three_pow (K : ℕ) : countE (3 ^ K) = countA K := by
  rw [countE, Finset.card_filter, Finset.sum_product, countA]
  refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun s hs => ?_
  rw [carries_eq_cnt3 K t s (mem_range.1 ht) (mem_range.1 hs)]

/-- `E(3^k) = A_k = 9(k-1)6^{k-2}` for `k ≥ 2`. -/
theorem countE_three_pow_add_two (K : ℕ) : countE (3 ^ (K + 2)) = 9 * (K + 1) * 6 ^ K := by
  rw [countE_three_pow, countA_eq]

lemma rpow_logb_three_two_thirds (x : ℝ) (hx : 0 < x) :
    x ^ Real.logb 3 (2 / 3) = x ^ Real.logb 3 6 / x ^ 2 := by
  have h : Real.logb 3 (2 / 3) = Real.logb 3 6 - 2 := by
    rw [show (2 / 3 : ℝ) = 6 / 3 ^ 2 by norm_num, Real.logb_div (by norm_num) (by norm_num),
      Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    ring
  rw [h, Real.rpow_sub hx, Real.rpow_two]

lemma three_pow_rpow_logb_six (k : ℕ) : ((3 : ℝ) ^ k) ^ Real.logb 3 6 = 6 ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]

/-- **Theorem `thm:asymptotic-ratio`** (`paper.tex`, Section 5): for every `M ≥ 9`,
`P(M) = #{(n,t) ∈ [1,M]² : n-1 ≥ t, v_3 \binom{n-1}{t} = 1} / #{(n,t) ∈ [1,M]² : n-1 ≥ t}`
satisfies the explicit two-sided bound established in the proof,
`(1/(36 ln 3)) M^{log_3(2/3)} ln M ≤ P(M) ≤ (6/ln 3) M^{log_3(2/3)} ln M`;
in particular `P(M) = Θ(M^{log_3(2/3)} ln M)`. -/
theorem ratioP_bounds (M : ℕ) (hM : 9 ≤ M) :
    1 / (36 * Real.log 3) * (M : ℝ) ^ Real.logb 3 (2 / 3) * Real.log M ≤ ratioP M ∧
      ratioP M ≤ 6 / Real.log 3 * (M : ℝ) ^ Real.logb 3 (2 / 3) * Real.log M := by
  set k := Nat.log 3 M with hk
  have hk1 : 3 ^ k ≤ M := Nat.pow_log_le_self 3 (by omega)
  have hk2 : M < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
  have hk3 : 2 ≤ k := by
    rw [hk]; exact Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  obtain ⟨j, hj⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [hj] at hk1 hk2
  -- bounds on the count
  have hEu : (pairCount M : ℝ) ≤ 54 * (j + 2) * 6 ^ j := by
    rw [pairCount_eq_countE]
    have := countE_mono hk2.le
    rw [show j + 2 + 1 = (j + 1) + 2 by ring, countE_three_pow_add_two] at this
    have h' : (countE M : ℝ) ≤ ((9 * (j + 1 + 1) * 6 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'; rw [pow_succ] at h'; linarith
  have hEl : 9 * (j + 1) * 6 ^ j ≤ (pairCount M : ℝ) := by
    rw [pairCount_eq_countE]
    have := countE_mono hk1
    rw [countE_three_pow_add_two] at this
    have h' : ((9 * (j + 1) * 6 ^ j : ℕ) : ℝ) ≤ (countE M : ℝ) := by exact_mod_cast this
    push_cast at h'; linarith
  have hT : (pairTotal M : ℝ) = M * (M - 1) / 2 := by
    have := pairTotal_mul_two M
    have h' : ((pairTotal M * 2 : ℕ) : ℝ) = ((M * (M - 1) : ℕ) : ℝ) := by rw [this]
    push_cast [Nat.cast_sub (show 1 ≤ M by omega)] at h'
    linarith
  set x : ℝ := (M : ℝ) with hx
  have hx9 : (9 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hM
  have hxpos : 0 < x := by linarith
  set a : ℝ := 6 ^ j with ha
  have hapos : 0 < a := by positivity
  -- bounds on `y = x^{log_3 6}`
  set y : ℝ := x ^ Real.logb 3 6 with hy
  have hlog6 : 0 ≤ Real.logb 3 6 := Real.logb_nonneg (by norm_num) (by norm_num)
  have hyl : 36 * a ≤ y := by
    have h1 : ((3 : ℝ) ^ (j + 2)) ^ Real.logb 3 6 ≤ y :=
      Real.rpow_le_rpow (by positivity) (by rw [hx]; exact_mod_cast hk1) hlog6
    rw [three_pow_rpow_logb_six, pow_add] at h1; linarith
  have hyu : y ≤ 216 * a := by
    have h1 : y ≤ ((3 : ℝ) ^ (j + 2 + 1)) ^ Real.logb 3 6 :=
      Real.rpow_le_rpow hxpos.le (by rw [hx]; exact_mod_cast hk2.le) hlog6
    rw [three_pow_rpow_logb_six, pow_add, pow_add] at h1; linarith
  -- bounds on `L = ln x`
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLl : (j + 2) * Real.log 3 ≤ Real.log x := by
    have := Real.log_le_log (by positivity) (show ((3 : ℝ) ^ (j + 2)) ≤ x by
      rw [hx]; exact_mod_cast hk1)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hLu : Real.log x ≤ (j + 3) * Real.log 3 := by
    have := Real.log_le_log hxpos (show x ≤ ((3 : ℝ) ^ (j + 3)) by
      rw [hx]; exact_mod_cast hk2.le)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hLpos : 0 < Real.log x := by nlinarith
  rw [ratioP, hT, rpow_logb_three_two_thirds x hxpos, ← hy]
  have hx1 : 0 < x * (x - 1) := by nlinarith
  have hjn : (0 : ℝ) ≤ j := by positivity
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have e : 1 / (36 * Real.log 3) * (y / x ^ 2) * Real.log x * (x * (x - 1) / 2) =
        (y * (Real.log x / Real.log 3)) * ((x - 1) / x) / 72 := by
      field_simp
      ring
    rw [e]
    have hq : Real.log x / Real.log 3 ≤ j + 3 := by rw [div_le_iff₀ hl3]; linarith
    have hq0 : 0 ≤ Real.log x / Real.log 3 := by positivity
    have hr : (x - 1) / x ≤ 1 := by rw [div_le_one hxpos]; linarith
    have hr0 : 0 ≤ (x - 1) / x := div_nonneg (by linarith) hxpos.le
    calc (y * (Real.log x / Real.log 3)) * ((x - 1) / x) / 72
        ≤ (216 * a * (j + 3)) * 1 / 72 := by gcongr
      _ ≤ 9 * (j + 1) * a := by nlinarith
      _ ≤ _ := hEl
  · rw [div_le_iff₀ (by positivity)]
    have e : 6 / Real.log 3 * (y / x ^ 2) * Real.log x * (x * (x - 1) / 2) =
        3 * (y * (Real.log x / Real.log 3)) * ((x - 1) / x) := by
      field_simp
      ring
    rw [e]
    have hq : j + 2 ≤ Real.log x / Real.log 3 := by rw [le_div_iff₀ hl3]; linarith
    have hr : 1 / 2 ≤ (x - 1) / x := by rw [le_div_iff₀ hxpos]; linarith
    calc (pairCount M : ℝ) ≤ 54 * (j + 2) * a := hEu
      _ = 3 * (36 * a * (j + 2)) * (1 / 2) := by ring
      _ ≤ 3 * (y * (Real.log x / Real.log 3)) * ((x - 1) / x) := by gcongr

/-- **Theorem `thm:asymptotic-ratio`, "in particular"** (`paper.tex`, Section 5):
`P(M) → 0` as `M → ∞`. -/
theorem tendsto_ratioP : Filter.Tendsto ratioP Filter.atTop (nhds 0) := by
  set l := Real.logb 3 (2 / 3)
  have hl : l < 0 := Real.logb_neg (by norm_num) (by norm_num) (by norm_num)
  have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x ^ (-l)) Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by linarith)).tendsto_div_nhds_zero
  have h2 : Filter.Tendsto (fun x : ℝ => 6 / Real.log 3 * x ^ l * Real.log x) Filter.atTop
      (nhds 0) := by
    have := h1.const_mul (6 / Real.log 3)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [Real.rpow_neg hx.le]
    field_simp
  have h3 := h2.comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3 ?_ ?_
  · exact Filter.Eventually.of_forall fun M => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop 9] with M hM
    exact (ratioP_bounds M hM).2

lemma countE_eq_filter_cnt3 (M K : ℕ) (h : M ≤ 3 ^ K) : countE M =
    ((range M ×ˢ range M).filter fun x : ℕ × ℕ => x.1 + x.2 < M ∧ cnt3 K x.1 x.2 = 1).card := by
  rw [countE]
  congr 1
  refine Finset.filter_congr fun x hx => ?_
  simp only [mem_product, mem_range] at hx
  rw [carries_eq_cnt3 K x.1 x.2 (by omega) (by omega)]

/-- **The numerical table** of `paper.tex`, Section 5 (before Theorem `thm:asymptotic-ratio`):
for `M = 100, 500, 1000` the count of pairs `(n,t) ∈ [1,M]²` with `n - 1 ≥ t` and
`v_3 \binom{n-1}{t} = 1` is `1292, 27546, 90954`, and the total number of pairs is
`4950, 124750, 499500`. (The decimal ratios of the table are the quotients of these numbers.) -/
theorem numerical_table :
    pairCount 100 = 1292 ∧ pairTotal 100 = 4950 ∧
    pairCount 500 = 27546 ∧ pairTotal 500 = 124750 ∧
    pairCount 1000 = 90954 ∧ pairTotal 1000 = 499500 := by
  have t1 := pairTotal_mul_two 100
  have t2 := pairTotal_mul_two 500
  have t3 := pairTotal_mul_two 1000
  refine ⟨?_, by omega, ?_, by omega, ?_, by omega⟩
  · rw [pairCount_eq_countE, countE_eq_filter_cnt3 100 5 (by norm_num)]; native_decide
  · rw [pairCount_eq_countE, countE_eq_filter_cnt3 500 6 (by norm_num)]; native_decide
  · rw [pairCount_eq_countE, countE_eq_filter_cnt3 1000 7 (by norm_num)]; native_decide

end LatticeTiling
