module

public import Mathlib

/-!
# Basic definitions

Formalization of the basic objects of the paper `paper.tex`
("On Lattice Tilings by Symmetric Limited Magnitude Error Balls: Q-Polynomials and Ideal
Characterization"): limited magnitude error balls, tilings, lattice tilings, Q-polynomials,
power sums, and the size of the symmetric error ball.
-/

@[expose] public section

open Finset

namespace LatticeTiling

variable {n : ℕ}

/-- The Hamming weight `wt(a)` of a vector `a ∈ ℤⁿ`, i.e. the number of nonzero coordinates
(`paper.tex`, Section 1, definition of `\mathcal{B}(n,t,k_1,k_2)`). -/
def wt (a : Fin n → ℤ) : ℕ := (univ.filter fun i => a i ≠ 0).card

/-- The box `([-k₂, k₁] ∩ ℤ)ⁿ`. -/
def box (n k₁ k₂ : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Icc (-(k₂ : ℤ)) k₁

/-- **Limited magnitude error ball** (`paper.tex`, Section 1, first display):
`𝓑(n,t,k₁,k₂) = {a ∈ ℤⁿ : aᵢ ∈ [-k₂,k₁], wt(a) ≤ t}`. -/
def ball (n t k₁ k₂ : ℕ) : Finset (Fin n → ℤ) :=
  (box n k₁ k₂).filter fun a => wt a ≤ t

/-- The **weight-exact shell** `𝓢(n,t,k,k) = {a ∈ ℤⁿ : aᵢ ∈ [-k,k], wt(a) = t}`
(`paper.tex`, Section 3, definition of `\mathcal{S}(n,t,k,k)`; we allow general `k₁, k₂`). -/
def shell (n t k₁ k₂ : ℕ) : Finset (Fin n → ℤ) :=
  (box n k₁ k₂).filter fun a => wt a = t

/-- A set `C ⊆ ℤⁿ` forms a **tiling** by `B` if the translates `{B + c : c ∈ C}` partition `ℤⁿ`,
i.e. every `x ∈ ℤⁿ` lies in exactly one translate `B + c` with `c ∈ C`
(`paper.tex`, Section 1, definition of tiling). -/
def IsTiling (B C : Set (Fin n → ℤ)) : Prop :=
  ∀ x : Fin n → ℤ, ∃! c : Fin n → ℤ, c ∈ C ∧ x - c ∈ B

/-- There exists a **lattice tiling** of `ℤⁿ` by translates of `B`: a tiling `C` of `ℤⁿ` by `B`
where `C` is a lattice, i.e. an additive subgroup of `ℤⁿ` (`paper.tex`, Section 1). -/
def HasLatticeTiling (B : Set (Fin n → ℤ)) : Prop :=
  ∃ L : AddSubgroup (Fin n → ℤ), IsTiling B (L : Set (Fin n → ℤ))

/-- The standard inner product `⟨X, b⟩ = ∑ᵢ bᵢ Xᵢ` of the vector of variables
`X = (X₁, …, Xₙ)` with an integer vector `b`, as a polynomial over a commutative ring `R`. -/
noncomputable def innerX (R : Type*) [CommRing R] (b : Fin n → ℤ) : MvPolynomial (Fin n) R :=
  ∑ i, (b i : MvPolynomial (Fin n) R) * MvPolynomial.X i

/-- **Q-polynomial** (`paper.tex`, Definition `def:Qpoly`): for a finite set `B ⊆ ℤⁿ` and `r`,
`Q_B^r(X) = ∑_{b ∈ B} ⟨X, b⟩^{2r}`, as a polynomial with integer coefficients.
(The paper takes `r ∈ ℤ⁺`; the definition makes sense for every `r ∈ ℕ`.) -/
noncomputable def QPoly (B : Finset (Fin n → ℤ)) (r : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∑ b ∈ B, innerX ℤ b ^ (2 * r)

/-- The power sum symmetric polynomial `s_j(X) = ∑_{i=1}^n X_i^j` (`paper.tex`, Section 2.1;
note `s_0(X) = n`). This is Mathlib's `MvPolynomial.psum`. -/
noncomputable abbrev powerSum (R : Type*) [CommRing R] (n j : ℕ) : MvPolynomial (Fin n) R :=
  MvPolynomial.psum (Fin n) R j

lemma sum_Icc_ite_ne_zero (R : Type*) [CommSemiring R] (k : ℕ) (q : R) :
    ∑ β ∈ Icc (-(k : ℤ)) k, (if β ≠ 0 then q else 1) = 1 + 2 * k * q := by
  rw [Finset.sum_ite]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  have h1 : ((Icc (-(k : ℤ)) k).filter (fun β => ¬ β ≠ 0)) = {0} := by
    ext x; simp; omega
  have h2 : ((Icc (-(k : ℤ)) k).filter (fun β => β ≠ 0)).card = 2 * k := by
    have := Finset.card_filter_add_card_filter_not (s := Icc (-(k : ℤ)) k) (fun β => β ≠ 0)
    rw [h1] at this
    simp only [Int.card_Icc, card_singleton] at this
    omega
  rw [h1, h2]; push_cast; simp; ring

/-- The weight enumerator of the box: `∑_{b ∈ [-k,k]ⁿ} q^{wt(b)} = (1 + 2kq)ⁿ`. -/
lemma sum_box_pow_wt (R : Type*) [CommSemiring R] (n k : ℕ) (q : R) :
    ∑ b ∈ box n k k, q ^ wt b = (1 + 2 * k * q) ^ n := by
  have : ∀ b : Fin n → ℤ, q ^ wt b = ∏ i, (if b i ≠ 0 then q else 1) := by
    intro b
    rw [Finset.prod_ite, prod_const_one, mul_one, prod_const]; rfl
  simp_rw [this]
  unfold box
  rw [show (∑ x ∈ Fintype.piFinset fun _ => Icc (-(k:ℤ)) k, ∏ i, if x i ≠ 0 then q else 1) =
      ∏ _i : Fin n, ∑ β ∈ Icc (-(k:ℤ)) k, (if β ≠ 0 then q else 1) from
    (Finset.prod_univ_sum (fun _ => Icc (-(k:ℤ)) k) (fun _ β => if β ≠ 0 then q else 1)).symm]
  rw [sum_Icc_ite_ne_zero, prod_const, card_univ, Fintype.card_fin]

/-- Size of the shell: `|𝓢(n,s,k,k)| = (2k)^s \binom{n}{s}`. -/
lemma card_shell (n s k : ℕ) : (shell n s k k).card = (2 * k) ^ s * n.choose s := by
  have h := congrArg (Polynomial.coeff · s) (sum_box_pow_wt (Polynomial ℕ) n k Polynomial.X)
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow] at h
  rw [Finset.sum_boole] at h
  simp only [Nat.cast_id] at h
  rw [show (1 + 2 * (k : Polynomial ℕ) * Polynomial.X) =
    Polynomial.C (2 * k) * Polynomial.X + 1 by simp; ring] at h
  rw [add_pow] at h
  simp only [mul_pow, one_pow, mul_one, ← Polynomial.C_pow, Polynomial.finset_sum_coeff] at h
  simp only [← Polynomial.C_eq_natCast, mul_right_comm _ (Polynomial.X ^ _), ← Polynomial.C_mul,
    Polynomial.coeff_C_mul_X_pow] at h
  rw [Finset.sum_eq_single s] at h
  · simp only [if_true, Nat.cast_id] at h
    rw [mul_pow, ← h]; unfold shell; congr 1; ext a; simp [eq_comm]
  · intro b _ hb; simp [Ne.symm hb]
  · intro hs; simp at hs; simp [Nat.choose_eq_zero_of_lt (by omega : n < s)]

/-- The ball is the disjoint union of the shells of weight `s ≤ t`. -/
lemma card_ball_eq_sum_card_shell (n t k₁ k₂ : ℕ) :
    (ball n t k₁ k₂).card = ∑ s ∈ range (t + 1), (shell n s k₁ k₂).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := wt) (t := range (t + 1))]
  · apply Finset.sum_congr rfl
    intro s hs
    unfold ball shell
    rw [Finset.filter_filter]
    congr 1; ext a; simp only [mem_filter, mem_range] at hs ⊢
    constructor
    · rintro ⟨h0, _, h2⟩; exact ⟨h0, h2⟩
    · rintro ⟨h0, rfl⟩; exact ⟨h0, by omega, rfl⟩
  · intro a ha; simp [ball] at ha ⊢; omega

/-- **Size of the symmetric error ball** (`paper.tex`, Section 2.1, display after
Definition `def:Qpoly`, second equality): `|𝓑(n,t,k,k)| = ∑_{i=0}^t (2k)^i \binom{n}{i}`. -/
theorem card_ball (n t k : ℕ) :
    (ball n t k k).card = ∑ i ∈ range (t + 1), (2 * k) ^ i * n.choose i := by
  rw [card_ball_eq_sum_card_shell]
  exact Finset.sum_congr rfl fun s _ => card_shell n s k

/-- **Size of the symmetric error ball as a coefficient** (`paper.tex`, Section 2.1, display
after Definition `def:Qpoly`, first equality): `|𝓑(n,t,k,k)| = [q^t] (1+2qk)^n/(1-q)`.
Here `1/(1-q)` is the power series `∑_{i ≥ 0} q^i = PowerSeries.mk 1`. -/
theorem card_ball_eq_coeff (n t k : ℕ) :
    ((ball n t k k).card : ℚ) =
      PowerSeries.coeff t ((1 + PowerSeries.C (2 * k : ℚ) * PowerSeries.X) ^ n *
        PowerSeries.mk 1) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk, Pi.one_apply, mul_one]
  rw [show (1 + PowerSeries.C (2 * k : ℚ) * PowerSeries.X) = 1 + 2 * (k : PowerSeries ℚ) * PowerSeries.X by
    simp [map_mul, map_natCast, map_ofNat]]
  rw [← sum_box_pow_wt, card_ball_eq_sum_card_shell]
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  simp only [map_sum, PowerSeries.coeff_X_pow]
  rw [Finset.sum_boole]
  unfold shell
  congr 2; ext a; simp [eq_comm]

end LatticeTiling
