import RequestProject.Ex4_3_6_Examples

/-!
# Corollaries `cor:t6k1`, `cor:t3k2`, `cor:t4k3`

`paper.tex`, Section 1 (established in Examples `ex:t6k1p5`, `ex:t3k2p5`, `ex:t4k3p11` of
Section 4). Each corollary is derived from Theorem `thm:ideal` through the finite criterion
`LatticeTiling.no_lattice_tiling_of_residue`; the finitely many residue-class checks (which the
paper performs in Maple) are carried out here by evaluation with `native_decide`.

This file is not a `module`, so that the evaluation can use the compiled code of the imported
definitions.
-/

open Finset

namespace LatticeTiling

set_option linter.style.nativeDecide false

/-- **Corollary `cor:t6k1`** (`paper.tex`, Section 1; established in Example `ex:t6k1p5`,
`k = 1`, `t = 6`, `p = 5`): there is no lattice tiling of `ℤⁿ` by `𝓑(n,6,1,1)` if
`n ≡ 38, 63, 88, 113 (mod 125)`. -/
theorem no_lattice_tiling_t6k1 (n : ℕ) (hn : n % 125 ∈ ({38, 63, 88, 113} : Finset ℕ)) :
    ¬ HasLatticeTiling (ball n 6 1 1 : Set (Fin n → ℤ)) := by
  have hden : ∀ r < (5 - 1) / 2 + 1, ∀ μ : r.Partition, ∀ j < 6 + 1,
      (cWeightP 1 r μ j).den = 1 := by native_decide
  have hcheck : ∀ n₀ ∈ ({38, 63, 88, 113} : Finset ℕ),
      bsize n₀ 6 1 % 5 = 0 ∧ bsize n₀ 6 1 % 5 ^ 2 ≠ 0 ∧
      (∀ j < 1 + 1, 1 ≤ j → cIntZ n₀ 6 1 j (Nat.Partition.indiscrete j) % 5 ≠ 0) ∧
      (∀ μ : ((5 - 1) / 2).Partition, cIntZ n₀ 6 1 _ μ % 5 = 0 ∨ ¬ ∀ i ∈ μ.parts, 1 < i) := by
    native_decide
  obtain ⟨h1, h2, h3, h4⟩ := hcheck _ hn
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact no_lattice_tiling_of_residue 6 1 5 1 _ (by norm_num) (by norm_num) h1 h2 hden h3 h4 n
    (by rw [show 2 + Nat.log 5 6 = 3 by rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 1) (by norm_num) (by norm_num)]]; rfl)

/-- **Corollary `cor:t3k2`** (`paper.tex`, Section 1; established in Example `ex:t3k2p5`,
`k = 2`, `t = 3`, `p = 5`): there is no lattice tiling of `ℤⁿ` by `𝓑(n,3,2,2)` if
`n ≡ 7, 8, 12, 13, 17, 18, 22, 23 (mod 25)`. -/
theorem no_lattice_tiling_t3k2 (n : ℕ)
    (hn : n % 25 ∈ ({7, 8, 12, 13, 17, 18, 22, 23} : Finset ℕ)) :
    ¬ HasLatticeTiling (ball n 3 2 2 : Set (Fin n → ℤ)) := by
  have hden : ∀ r < (5 - 1) / 2 + 1, ∀ μ : r.Partition, ∀ j < 3 + 1,
      (cWeightP 2 r μ j).den = 1 := by native_decide
  have hcheck : ∀ n₀ ∈ ({7, 8, 12, 13, 17, 18, 22, 23} : Finset ℕ),
      bsize n₀ 3 2 % 5 = 0 ∧ bsize n₀ 3 2 % 5 ^ 2 ≠ 0 ∧
      (∀ j < 0 + 1, 1 ≤ j → cIntZ n₀ 3 2 j (Nat.Partition.indiscrete j) % 5 ≠ 0) ∧
      (∀ μ : ((5 - 1) / 2).Partition, cIntZ n₀ 3 2 _ μ % 5 = 0 ∨ ¬ ∀ i ∈ μ.parts, 0 < i) := by
    native_decide
  obtain ⟨h1, h2, h3, h4⟩ := hcheck _ hn
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact no_lattice_tiling_of_residue 3 2 5 0 _ (by norm_num) (by norm_num) h1 h2 hden h3 h4 n
    (by rw [show 2 + Nat.log 5 3 = 2 by rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 0) (by norm_num) (by norm_num)]]; rfl)

/-- **Corollary `cor:t4k3`** (`paper.tex`, Section 1; established in Example `ex:t4k3p11`,
`k = 3`, `t = 4`, `p = 11`): there is no lattice tiling of `ℤⁿ` by `𝓑(n,4,3,3)` if
`n ≡ 8, 19, 30, 41, 52, 63, 74, 85, 96, 107, 118 (mod 121)`. -/
theorem no_lattice_tiling_t4k3 (n : ℕ)
    (hn : n % 121 ∈ ({8, 19, 30, 41, 52, 63, 74, 85, 96, 107, 118} : Finset ℕ)) :
    ¬ HasLatticeTiling (ball n 4 3 3 : Set (Fin n → ℤ)) := by
  have hden : ∀ r < (11 - 1) / 2 + 1, ∀ μ : r.Partition, ∀ j < 4 + 1,
      (cWeightP 3 r μ j).den = 1 := by native_decide
  have hcheck : ∀ n₀ ∈ ({8, 19, 30, 41, 52, 63, 74, 85, 96, 107, 118} : Finset ℕ),
      bsize n₀ 4 3 % 11 = 0 ∧ bsize n₀ 4 3 % 11 ^ 2 ≠ 0 ∧
      (∀ j < 3 + 1, 1 ≤ j → cIntZ n₀ 4 3 j (Nat.Partition.indiscrete j) % 11 ≠ 0) ∧
      (∀ μ : ((11 - 1) / 2).Partition, cIntZ n₀ 4 3 _ μ % 11 = 0 ∨ ¬ ∀ i ∈ μ.parts, 3 < i) := by
    native_decide
  obtain ⟨h1, h2, h3, h4⟩ := hcheck _ hn
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact no_lattice_tiling_of_residue 4 3 11 3 _ (by norm_num) (by norm_num) h1 h2 hden h3 h4 n
    (by rw [show 2 + Nat.log 11 4 = 2 by rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 0) (by norm_num) (by norm_num)]]; rfl)

/-- **Example `ex:table-data`** (`paper.tex`, Section 4), the excluded residue classes for
`(t,k) = (7,4)`: there is no lattice tiling of `ℤⁿ` by `𝓑(n,7,4,4)` if
`n ≡ 11,12,14,15,20,21,23,24 (mod 27)` (from `p = 3`), or
`n ≡ 16,17,41,42,67,91,116,117 (mod 125)` (from `p = 5`), or
`n ≡ 23,72,85,121,134,170,183,219,232,268,281,330 (mod 343)` (from `p = 7`).

(Only the exclusion is formalized; the assertion of the paper that these are *all* residue
classes excluded by Theorem `thm:ideal` for `p ≤ 29` rests on its Maple computation.) -/
theorem no_lattice_tiling_t7k4 (n : ℕ)
    (hn : n % 27 ∈ ({11, 12, 14, 15, 20, 21, 23, 24} : Finset ℕ) ∨
      n % 125 ∈ ({16, 17, 41, 42, 67, 91, 116, 117} : Finset ℕ) ∨
      n % 343 ∈ ({23, 72, 85, 121, 134, 170, 183, 219, 232, 268, 281, 330} : Finset ℕ)) :
    ¬ HasLatticeTiling (ball n 7 4 4 : Set (Fin n → ℤ)) := by
  rcases hn with hn | hn | hn
  · have hden : ∀ r < (3 - 1) / 2 + 1, ∀ μ : r.Partition, ∀ j < 7 + 1,
        (cWeightP 4 r μ j).den = 1 := by native_decide
    have hcheck : ∀ n₀ ∈ ({11, 12, 14, 15, 20, 21, 23, 24} : Finset ℕ),
        bsize n₀ 7 4 % 3 = 0 ∧ bsize n₀ 7 4 % 3 ^ 2 ≠ 0 ∧
        (∀ j < 0 + 1, 1 ≤ j → cIntZ n₀ 7 4 j (Nat.Partition.indiscrete j) % 3 ≠ 0) ∧
        (∀ μ : ((3 - 1) / 2).Partition, cIntZ n₀ 7 4 _ μ % 3 = 0 ∨ ¬ ∀ i ∈ μ.parts, 0 < i) := by
      native_decide
    obtain ⟨h1, h2, h3, h4⟩ := hcheck _ hn
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact no_lattice_tiling_of_residue 7 4 3 0 _ (by norm_num) (by norm_num) h1 h2 hden h3 h4 n
      (by rw [show 2 + Nat.log 3 7 = 3 by
        rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 1) (by norm_num) (by norm_num)]]; rfl)
  · have hden : ∀ r < (5 - 1) / 2 + 1, ∀ μ : r.Partition, ∀ j < 7 + 1,
        (cWeightP 4 r μ j).den = 1 := by native_decide
    have hcheck : ∀ n₀ ∈ ({16, 17, 41, 42, 67, 91, 116, 117} : Finset ℕ),
        bsize n₀ 7 4 % 5 = 0 ∧ bsize n₀ 7 4 % 5 ^ 2 ≠ 0 ∧
        (∀ j < 0 + 1, 1 ≤ j → cIntZ n₀ 7 4 j (Nat.Partition.indiscrete j) % 5 ≠ 0) ∧
        (∀ μ : ((5 - 1) / 2).Partition, cIntZ n₀ 7 4 _ μ % 5 = 0 ∨ ¬ ∀ i ∈ μ.parts, 0 < i) := by
      native_decide
    obtain ⟨h1, h2, h3, h4⟩ := hcheck _ hn
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact no_lattice_tiling_of_residue 7 4 5 0 _ (by norm_num) (by norm_num) h1 h2 hden h3 h4 n
      (by rw [show 2 + Nat.log 5 7 = 3 by
        rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 1) (by norm_num) (by norm_num)]]; rfl)
  · have hden : ∀ r < (7 - 1) / 2 + 1, ∀ μ : r.Partition, ∀ j < 7 + 1,
        (cWeightP 4 r μ j).den = 1 := by native_decide
    have hcheck : ∀ n₀ ∈ ({23, 72, 85, 121, 134, 170, 183, 219, 232, 268, 281, 330} : Finset ℕ),
        bsize n₀ 7 4 % 7 = 0 ∧ bsize n₀ 7 4 % 7 ^ 2 ≠ 0 ∧
        (∀ j < 1 + 1, 1 ≤ j → cIntZ n₀ 7 4 j (Nat.Partition.indiscrete j) % 7 ≠ 0) ∧
        (∀ μ : ((7 - 1) / 2).Partition, cIntZ n₀ 7 4 _ μ % 7 = 0 ∨ ¬ ∀ i ∈ μ.parts, 1 < i) := by
      native_decide
    obtain ⟨h1, h2, h3, h4⟩ := hcheck _ hn
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact no_lattice_tiling_of_residue 7 4 7 1 _ (by norm_num) (by norm_num) h1 h2 hden h3 h4 n
      (by rw [show 2 + Nat.log 7 7 = 3 by
        rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 1) (by norm_num) (by norm_num)]]; rfl)

/-- **Example `ex:table-data`** (`paper.tex`, Section 4), the excluded fraction for
`(t,k) = (7,4)`: modulo `27 · 125 · 343`, the residue classes excluded by
`no_lattice_tiling_t7k4` number exactly `27·125·343 − 19·117·331`, i.e. they form the fraction
`1 − (1 − 8/27)(1 − 8/125)(1 − 12/343) = 1 − (19·117·331)/(27·125·343)` of all integers. -/
theorem card_excluded_t7k4 :
    ((range (27 * 125 * 343)).filter fun n =>
      n % 27 ∈ ({11, 12, 14, 15, 20, 21, 23, 24} : Finset ℕ) ∨
      n % 125 ∈ ({16, 17, 41, 42, 67, 91, 116, 117} : Finset ℕ) ∨
      n % 343 ∈ ({23, 72, 85, 121, 134, 170, 183, 219, 232, 268, 281, 330} : Finset ℕ)).card =
      27 * 125 * 343 - 19 * 117 * 331 := by
  native_decide

/-- **Example `ex:table-data`** (`paper.tex`, Section 4), the arithmetic:
`1 − (1 − 8/27)(1 − 8/125)(1 − 12/343) = 1 − (19·117·331)/(27·125·343) ≈ 0.3644`, which is the
entry `36.44%` of Table `tab:excluded`. -/
theorem excluded_fraction_t7k4 :
    (1 - (1 - 8 / 27) * (1 - 8 / 125) * (1 - 12 / 343) : ℚ) =
        1 - (19 * 117 * 331) / (27 * 125 * 343) ∧
      0.36435 ≤ (1 - (19 * 117 * 331) / (27 * 125 * 343) : ℚ) ∧
      (1 - (19 * 117 * 331) / (27 * 125 * 343) : ℚ) < 0.36445 := by
  norm_num

end LatticeTiling
