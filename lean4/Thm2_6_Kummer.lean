module

public import RequestProject.Def2_7_Defs

/-!
# Kummer's theorem

Formalization of `paper.tex`, Section 2.3, Theorem `thm:kummer`. We define the number of carries
in the schoolbook base-`p` addition of two natural numbers and deduce Kummer's theorem from
Mathlib's version (which is phrased with the condition `p^i ≤ a % p^i + b % p^i`).
-/

@[expose] public section

open Finset

namespace LatticeTiling

/-- The carry `c_i` into digit position `i` in the schoolbook base-`p` addition of `a` and `b`:
`c_0 = 0` and `c_{i+1} = ⌊(a_i + b_i + c_i)/p⌋`, where `a_i = ⌊a/p^i⌋ mod p` and
`b_i = ⌊b/p^i⌋ mod p` are the `i`-th base-`p` digits. -/
def carry (p a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (a / p ^ i % p + b / p ^ i % p + carry p a b i) / p

/-- The **number of carries** when `a` and `b` are added in base `p`: the number of digit
positions `i` producing a carry `c_{i+1} = 1` (`paper.tex`, Theorem `thm:kummer`). Only the
positions `0 ≤ i < a + b` can produce a carry (for `p ≥ 2`), so the sum is finite. -/
def carries (p a b : ℕ) : ℕ := ∑ i ∈ Ico 1 (a + b + 1), carry p a b i

/-- The carry into position `i` equals `⌊(a mod p^i + b mod p^i)/p^i⌋`. -/
lemma carry_eq_div (p a b : ℕ) (hp : 1 < p) (i : ℕ) :
    carry p a b i = (a % p ^ i + b % p ^ i) / p ^ i := by
  induction i with
  | zero => simp [carry, Nat.mod_one]
  | succ i ih =>
    rw [carry, ih]
    have hpi : 0 < p ^ i := pow_pos (by omega) i
    have ha : a % p ^ (i + 1) = a % p ^ i + p ^ i * (a / p ^ i % p) := by
      rw [pow_succ, Nat.mod_mul]
    have hb : b % p ^ (i + 1) = b % p ^ i + p ^ i * (b / p ^ i % p) := by
      rw [pow_succ, Nat.mod_mul]
    rw [ha, hb]
    set S := a % p ^ i + b % p ^ i with hSdef
    have e : a % p ^ i + p ^ i * (a / p ^ i % p) + (b % p ^ i + p ^ i * (b / p ^ i % p)) =
        S % p ^ i + p ^ i * (a / p ^ i % p + b / p ^ i % p + S / p ^ i) := by
      have h0 := Nat.div_add_mod S (p ^ i)
      simp only [mul_add]
      omega
    rw [e, pow_succ, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hpi,
      Nat.div_eq_of_lt (Nat.mod_lt _ hpi), zero_add]

/-- The carry into position `i` is `1` exactly when `p^i ≤ a mod p^i + b mod p^i`, and `0`
otherwise. -/
lemma carry_eq_ite (p a b : ℕ) (hp : 1 < p) (i : ℕ) :
    carry p a b i = if p ^ i ≤ a % p ^ i + b % p ^ i then 1 else 0 := by
  rw [carry_eq_div p a b hp]
  have hpi : 0 < p ^ i := pow_pos (by omega) i
  have h1 := Nat.mod_lt a hpi
  have h2 := Nat.mod_lt b hpi
  split_ifs with h
  · apply le_antisymm
    · rw [Nat.div_le_iff_le_mul_add_pred hpi]; omega
    · exact (Nat.one_le_div_iff hpi).2 h
  · exact Nat.div_eq_of_lt (by omega)

/-- **Kummer's theorem** (`paper.tex`, Theorem `thm:kummer`; Kummer 1852): for a prime `p` and
nonnegative integers `a, b`, the `p`-adic valuation `v_p \binom{a+b}{a}` equals the number of
carries when `a` and `b` are added in base `p`. -/
theorem kummer (p : ℕ) [hp : Fact p.Prime] (a b : ℕ) :
    padicValNat p ((a + b).choose a) = carries p a b := by
  have hlog : Nat.log p (b + a) < a + b + 1 := by
    have := Nat.log_lt_self p (show b + a + 1 ≠ 0 by omega)
    have h2 := Nat.log_mono_right (b := p) (show b + a ≤ b + a + 1 by omega)
    omega
  rw [add_comm a b, padicValNat_choose' hlog, carries, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [carry_eq_ite p a b hp.out.one_lt]

/-- **Kummer's theorem, second form** (`paper.tex`, Theorem `thm:kummer`, "in particular"):
for `0 ≤ u ≤ n`, `v_p \binom{n}{u}` equals the number of carries when `u` and `n - u` are added
in base `p`. -/
theorem kummer' (p : ℕ) [Fact p.Prime] {n u : ℕ} (hun : u ≤ n) :
    padicValNat p (n.choose u) = carries p u (n - u) := by
  rw [← kummer, Nat.add_sub_cancel' hun]

end LatticeTiling
