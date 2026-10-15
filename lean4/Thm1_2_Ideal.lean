module

public import RequestProject.Lem2_1_3_TilingGroup

/-!
# Ideal characterization of lattice tilings

Formalization of `paper.tex`, Section 4 (`sec:ideal`): Lemma `lem:conditionX`,
Theorem `thm:conditionY` and Theorem `thm:ideal`, proved through the chain of implications
`eq:idealchain`.

The coefficients `c_λ` of equation `eq:defclambda` enter the statements as an arbitrary family of
integers `c r λ` (for `λ ⊢ r`) satisfying
`Q^r_{𝓑(n,t,k,k)}(X) = ∑_{λ ⊢ r} c_λ ∏_i s_{2λ_i}(X)` for `1 ≤ r ≤ (p-1)/2`; the existence of such
a family is proved in `RequestProject.CLambda`.
-/

@[expose] public section

open Finset MvPolynomial

namespace LatticeTiling

variable {n : ℕ}

/-- The ring homomorphism `ℤ[X] → 𝔽_p[X]` reducing coefficients modulo `p`. -/
noncomputable abbrev modP (p : ℕ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) (ZMod p) :=
  MvPolynomial.map (Int.castRingHom (ZMod p))

lemma eval_modP_innerX (p : ℕ) (ψ : (Fin n → ℤ) →+ ZMod p) (b : Fin n → ℤ) :
    eval (fun i => ψ (Pi.single i 1)) (modP p (innerX ℤ b)) = ψ b := by
  conv_rhs => rw [show b = ∑ i, b i • Pi.single i (1 : ℤ) by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  simp_rw [map_zsmul]
  simp [innerX, map_sum, zsmul_eq_mul]

/-- The heart of the proof of Lemma `lem:conditionX` (`paper.tex`, Section 4): if a finite set
`B ⊆ ℤⁿ` with `|B| = pM` tiles `ℤⁿ` by a lattice, then there is `x ∈ 𝔽_pⁿ` with
`Q^r_B(x) = ∑_{b ∈ B} ⟨x,b⟩^{2r} = 0` if `p - 1 ∤ 2r` and `= -M` if `p - 1 ∣ 2r` (for `r ≥ 1`). -/
theorem exists_eval_QPoly_of_hasLatticeTiling (B : Finset (Fin n → ℤ)) (p M : ℕ)
    [Fact p.Prime] (hcard : B.card = p * M) (hT : HasLatticeTiling (B : Set (Fin n → ℤ))) :
    ∃ x : Fin n → ZMod p, ∀ r, 1 ≤ r →
      eval x (modP p (QPoly B r)) = M * (if p - 1 ∣ 2 * r then -1 else 0) := by
  classical
  obtain ⟨G, _, _, hG, φ, hφ⟩ := (hasLatticeTiling_iff_exists_hom B).1 hT
  obtain ⟨Φ, hΦ, hfib⟩ := exists_surjective_hom_zmod_card_fiber (G := G) p M (hG.trans hcard)
  set ψ := Φ.comp φ
  refine ⟨fun i => ψ (Pi.single i 1), fun r hr => ?_⟩
  have h1 : eval (fun i => ψ (Pi.single i 1)) (modP p (QPoly B r)) =
      ∑ g : G, Φ g ^ (2 * r) := by
    simp only [QPoly, map_sum, map_pow, eval_modP_innerX]
    refine Finset.sum_bij (fun b _ => φ b) (fun _ _ => mem_univ _)
      (fun b₁ h₁ b₂ h₂ h => hφ.injOn h₁ h₂ h) (fun g _ => ?_) (fun b _ => rfl)
    obtain ⟨b, hb, rfl⟩ := hφ.surjOn (Set.mem_univ g)
    exact ⟨b, hb, rfl⟩
  have h2 : ∑ g : G, Φ g ^ (2 * r) = ∑ a : ZMod p, (M : ZMod p) * a ^ (2 * r) := by
    rw [Finset.sum_comp (fun a => a ^ (2 * r)) Φ]
    have himg : (univ : Finset G).image Φ = univ :=
      eq_univ_of_forall fun a => by obtain ⟨g, rfl⟩ := hΦ a; exact mem_image_of_mem _ (mem_univ g)
    rw [himg]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hfib a, nsmul_eq_mul]
  rw [h1, h2, ← Finset.mul_sum, sum_zmod_pow p _ (by omega)]

/-- **Lemma `lem:conditionX`** (`paper.tex`, Section 4): let `p > 2` be a prime and assume
`|𝓑(n,t,k,k)| = pM`. If there is no `X ∈ 𝔽_pⁿ` with `Q^r_{𝓑(n,t,k,k)}(X) ≡ 0 (mod p)` for
`1 ≤ r < (p-1)/2` and `Q^{(p-1)/2}_{𝓑(n,t,k,k)}(X) ≡ -M (mod p)` (system `eq:systemX`), then there
is no lattice tiling of `ℤⁿ` by `𝓑(n,t,k,k)`. -/
theorem no_lattice_tiling_of_conditionX (t k p M : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hcard : (ball n t k k).card = p * M)
    (hX : ¬ ∃ x : Fin n → ZMod p,
      (∀ r, 1 ≤ r → r < (p - 1) / 2 → eval x (modP p (QPoly (ball n t k k) r)) = 0) ∧
        eval x (modP p (QPoly (ball n t k k) ((p - 1) / 2))) = -M) :
    ¬ HasLatticeTiling (ball n t k k : Set (Fin n → ℤ)) := by
  intro hT
  obtain ⟨x, hx⟩ := exists_eval_QPoly_of_hasLatticeTiling _ p M hcard hT
  have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  refine hX ⟨x, fun r hr1 hr2 => ?_, ?_⟩
  · rw [hx r hr1, if_neg, mul_zero]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  · rw [hx _ (by omega), if_pos ⟨1, by omega⟩, mul_neg_one]

/-- The variable `Y_j` of `𝔽_p[Y_1, …, Y_m]` (with `Y_j = 0` if `j = 0` or `j > m`); the ring
`𝔽_p[Y_1,…,Y_m]` is modelled as `MvPolynomial (Fin m) (ZMod p)`, `Y_j` being the variable
indexed by `j - 1`. -/
noncomputable def yVar (p m j : ℕ) : MvPolynomial (Fin m) (ZMod p) :=
  if h : 1 ≤ j ∧ j - 1 < m then X ⟨j - 1, h.2⟩ else 0

/-- **The polynomials `f_r`** (`paper.tex`, Theorem `thm:ideal`): for a family of integers
`c_λ` (`λ ⊢ r`, `c = c r λ`),
`f_r = ∑_{λ ∈ 𝓟(r)} c_λ ∏_{i=1}^{ℓ(λ)} Y_{λ_i} ∈ 𝔽_p[Y_1, …, Y_{(p-1)/2}]`. -/
noncomputable def fPoly (p : ℕ) (c : (r : ℕ) → r.Partition → ℤ) (r : ℕ) :
    MvPolynomial (Fin ((p - 1) / 2)) (ZMod p) :=
  ∑ μ : r.Partition, C ((c r μ : ℤ) : ZMod p) * (μ.parts.map fun j => yVar p ((p - 1) / 2) j).prod

/-- The expansion `eq:defclambda` of the Q-polynomials of `𝓑(n,t,k,k)` in power sums, for
`1 ≤ r ≤ R`: `Q^r(X) = ∑_{λ ⊢ r} c_λ ∏_i s_{2λ_i}(X)` with integer `c_λ`. -/
def IsCLambdaExpansion (n t k R : ℕ) (c : (r : ℕ) → r.Partition → ℤ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ R → QPoly (ball n t k k) r =
    ∑ μ : r.Partition, C (c r μ) * (μ.parts.map fun j => powerSum ℤ n (2 * j)).prod

/-- From a solution `x` of `eq:systemX` to the solution `Y_j = ∑_i x_i^{2j}` of `eq:systemY`
(`paper.tex`, proof of the chain `eq:idealchain`): `f_r(Y) = Q^r(x)` for `1 ≤ r ≤ (p-1)/2`. -/
lemma eval_fPoly_eq (t k p : ℕ) (c : (r : ℕ) → r.Partition → ℤ)
    (hc : IsCLambdaExpansion n t k ((p - 1) / 2) c) (x : Fin n → ZMod p) (r : ℕ) (hr1 : 1 ≤ r)
    (hr : r ≤ (p - 1) / 2) :
    eval (fun j : Fin ((p - 1) / 2) => ∑ i, x i ^ (2 * ((j : ℕ) + 1))) (fPoly p c r) =
      eval x (modP p (QPoly (ball n t k k) r)) := by
  rw [hc r hr1 hr, fPoly, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_mul, map_mul, map_mul, eval_C, MvPolynomial.map_C, eval_C, map_multiset_prod,
    map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  congr 1
  congr 1
  refine Multiset.map_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := μ.parts_pos hj
  have hjr : j ≤ r := by
    have := Multiset.le_sum_of_mem hj
    rw [μ.parts_sum] at this; exact this
  simp only [Function.comp_apply, yVar, dif_pos (⟨hj1, by omega⟩ : 1 ≤ j ∧ j - 1 < (p - 1) / 2),
    eval_X, powerSum, MvPolynomial.psum]
  rw [show j - 1 + 1 = j by omega]
  simp

/-- **Theorem `thm:conditionY`** (`paper.tex`, Section 4): let `p > 2` be a prime and assume
`|𝓑(n,t,k,k)| = pM`. Let `c_λ` be integers as in `eq:defclambda`. If there do not exist
`Y_1, …, Y_{(p-1)/2} ∈ 𝔽_p` with `∑_{λ ⊢ r} c_λ Y_λ ≡ 0 (mod p)` for `1 ≤ r < (p-1)/2` and
`∑_{λ ⊢ (p-1)/2} c_λ Y_λ ≡ -M (mod p)` (system `eq:systemY`; here `∑_{λ ⊢ r} c_λ Y_λ` is the
evaluation of `f_r` at `Y`), then there is no lattice tiling of `ℤⁿ` by `𝓑(n,t,k,k)`. -/
theorem no_lattice_tiling_of_conditionY (t k p M : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hcard : (ball n t k k).card = p * M) (c : (r : ℕ) → r.Partition → ℤ)
    (hc : IsCLambdaExpansion n t k ((p - 1) / 2) c)
    (hY : ¬ ∃ Y : Fin ((p - 1) / 2) → ZMod p,
      (∀ r, 1 ≤ r → r < (p - 1) / 2 → eval Y (fPoly p c r) = 0) ∧
        eval Y (fPoly p c ((p - 1) / 2)) = -M) :
    ¬ HasLatticeTiling (ball n t k k : Set (Fin n → ℤ)) := by
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le; have := (hp.out.eq_two_or_odd).resolve_left hp2; omega
  refine no_lattice_tiling_of_conditionX t k p M hp2 hcard ?_
  rintro ⟨x, hx1, hx2⟩
  refine hY ⟨fun j : Fin ((p - 1) / 2) => ∑ i, x i ^ (2 * ((j : ℕ) + 1)),
    fun r hr1 hr2 => ?_, ?_⟩
  · rw [eval_fPoly_eq t k p c hc x r hr1 hr2.le, hx1 r hr1 hr2]
  · rw [eval_fPoly_eq t k p c hc x _ (by omega) le_rfl, hx2]

/-- **Theorem `thm:ideal`** (`paper.tex`, Section 1, proved in Section 4): let `p > 2` be a prime
and assume `|𝓑(n,t,k,k)| = pM` with `p ∤ M`. Let `c_λ` be integers as in `eq:defclambda` and,
in `𝔽_p[Y_1, …, Y_{(p-1)/2}]`, let `f_r = ∑_{λ ⊢ r} c_λ ∏_i Y_{λ_i}`. If
`f_{(p-1)/2} ∈ (f_1, f_2, …, f_{(p-1)/2 - 1})`, then no lattice tiling of `ℤⁿ` by
`𝓑(n,t,k,k)` exists. -/
theorem no_lattice_tiling_of_mem_ideal (t k p M : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hcard : (ball n t k k).card = p * M) (hM : ¬ p ∣ M) (c : (r : ℕ) → r.Partition → ℤ)
    (hc : IsCLambdaExpansion n t k ((p - 1) / 2) c)
    (hmem : fPoly p c ((p - 1) / 2) ∈ Ideal.span (fPoly p c '' Set.Ico 1 ((p - 1) / 2))) :
    ¬ HasLatticeTiling (ball n t k k : Set (Fin n → ℤ)) := by
  refine no_lattice_tiling_of_conditionY t k p M hp2 hcard c hc ?_
  rintro ⟨Y, hY1, hY2⟩
  have hker : Ideal.span (fPoly p c '' Set.Ico 1 ((p - 1) / 2)) ≤ RingHom.ker (eval Y) := by
    rw [Ideal.span_le]
    rintro _ ⟨r, ⟨hr1, hr2⟩, rfl⟩
    exact hY1 r hr1 hr2
  have h0 := hker hmem
  rw [RingHom.mem_ker, hY2, neg_eq_zero, ZMod.natCast_eq_zero_iff] at h0
  exact hM h0

end LatticeTiling
