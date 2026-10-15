module

public import RequestProject.Def2_7_Defs

/-!
# Group-theoretic and finite-field preliminaries

Formalization of `paper.tex`, Section 2.2: Lemma `lem:tiling-group`, Lemma `lem:mto1` and
Lemma `lem:powersumFF`.
-/

@[expose] public section

open Finset

namespace LatticeTiling

variable {n : ℕ}

/-- **Lemma `lem:tiling-group`** (`paper.tex`, Section 2.2; Horak–Grošek):
Let `B` be a finite subset of `ℤⁿ` with `|B| = N`. There is a lattice tiling of `ℤⁿ` by
translates of `B` if and only if there is a finite abelian group `G` of order `N` and a group
homomorphism `φ : ℤⁿ → G` whose restriction `φ|_B : B → G` is a bijection. -/
theorem hasLatticeTiling_iff_exists_hom (B : Finset (Fin n → ℤ)) :
    HasLatticeTiling (B : Set (Fin n → ℤ)) ↔
      ∃ (G : Type) (_ : AddCommGroup G) (_ : Fintype G), Fintype.card G = B.card ∧
        ∃ φ : (Fin n → ℤ) →+ G, Set.BijOn φ (B : Set (Fin n → ℤ)) Set.univ := by
  constructor
  · rintro ⟨L, hL⟩
    let φ := QuotientAddGroup.mk' L
    have hbij : Set.BijOn φ (B : Set (Fin n → ℤ)) Set.univ := by
      refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
      · intro b₁ hb₁ b₂ hb₂ h
        have h' : b₁ - b₂ ∈ L := by
          simpa [sub_eq_neg_add] using (QuotientAddGroup.eq (s := L)).1 h.symm
        obtain ⟨c, _, hc⟩ := hL b₁
        have e1 := hc 0 ⟨L.zero_mem, by simpa using hb₁⟩
        have e2 := hc (b₁ - b₂) ⟨h', by simpa using hb₂⟩
        have : b₁ - b₂ = 0 := e2.trans e1.symm
        exact sub_eq_zero.1 this
      · intro y _
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L y
        obtain ⟨c, ⟨hcL, hcB⟩, _⟩ := hL x
        refine ⟨x - c, hcB, ?_⟩
        simp only [φ, QuotientAddGroup.mk'_apply]
        exact (QuotientAddGroup.eq (s := L)).2 (by simpa [sub_eq_neg_add] using hcL)
    have hfin : Finite ((Fin n → ℤ) ⧸ L) := by
      have : Set.univ ⊆ φ '' (B : Set (Fin n → ℤ)) := hbij.surjOn
      have hf : (φ '' (B : Set (Fin n → ℤ))).Finite := (B.finite_toSet).image φ
      exact Set.finite_univ_iff.1 (hf.subset this)
    letI : Fintype ((Fin n → ℤ) ⧸ L) := Fintype.ofFinite _
    refine ⟨(Fin n → ℤ) ⧸ L, inferInstance, inferInstance, ?_, φ, hbij⟩
    rw [Fintype.card_eq_nat_card, ← Set.ncard_univ, ← hbij.image_eq, hbij.injOn.ncard_image,
      Set.ncard_coe_finset]
  · rintro ⟨G, _, _, -, φ, hφ⟩
    refine ⟨φ.ker, fun x => ?_⟩
    obtain ⟨b, hb, hbx⟩ := hφ.surjOn (Set.mem_univ (φ x))
    refine ⟨x - b, ⟨?_, by simpa using hb⟩, ?_⟩
    · simp [AddMonoidHom.mem_ker, map_sub, hbx]
    · rintro c ⟨hc, hcB⟩
      have hc' : φ c = 0 := hc
      have : x - c = b := hφ.injOn hcB hb (by simp [map_sub, hc', hbx])
      rw [← this]; abel

/-- A nonzero vector in an `𝔽_p`-vector space is detected by a surjective linear form. -/
lemma exists_surjective_hom_zmod_of_module {V : Type*} [AddCommGroup V] (p : ℕ)
    [Fact p.Prime] [Module (ZMod p) V] {y : V} (hy : y ≠ 0) :
    ∃ Φ : V →+ ZMod p, Function.Surjective Φ := by
  let b := Module.Free.chooseBasis (ZMod p) V
  have hr : b.repr y ≠ 0 := by simpa using hy
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hr
  let f := b.coord j
  have hf : f y ≠ 0 := by simpa [f] using hj
  refine ⟨f.toAddMonoidHom, fun a => ⟨(a * (f y)⁻¹) • y, ?_⟩⟩
  change f ((a * (f y)⁻¹) • y) = a
  rw [LinearMap.map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hf, mul_one]

/-- A nontrivial abelian group killed by a prime `p` admits a surjection onto `𝔽_p`. -/
lemma exists_surjective_hom_zmod_of_torsion {V : Type*} [AddCommGroup V] (p : ℕ)
    [Fact p.Prime] (htors : ∀ y : V, p • y = 0) {y : V} (hy : y ≠ 0) :
    ∃ Φ : V →+ ZMod p, Function.Surjective Φ := by
  letI : Module (ZMod p) V := AddCommGroup.zmodModule htors
  exact exists_surjective_hom_zmod_of_module p hy

/-- In a finite abelian group of order divisible by a prime `p`, the subgroup `pG` is proper,
so `G ⧸ pG` is a nontrivial `𝔽_p`-vector space; this yields a surjection `G → 𝔽_p`. -/
lemma exists_surjective_hom_zmod {G : Type*} [AddCommGroup G] [Fintype G] (p : ℕ)
    [hp : Fact p.Prime] (hdvd : p ∣ Fintype.card G) :
    ∃ Φ : G →+ ZMod p, Function.Surjective Φ := by
  classical
  let H : AddSubgroup G := (nsmulAddMonoidHom (α := G) p).range
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have hnot : ∃ y : G ⧸ H, y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsurj : Function.Surjective (nsmulAddMonoidHom (α := G) p) := by
      intro x
      have := hcon (QuotientAddGroup.mk x)
      rw [QuotientAddGroup.eq_zero_iff] at this
      exact this
    have hinj := (Finite.injective_iff_surjective).2 hsurj
    have h1 : (nsmulAddMonoidHom (α := G) p) g = (nsmulAddMonoidHom (α := G) p) 0 := by
      simp [← hg, addOrderOf_nsmul_eq_zero]
    have := hinj h1
    rw [this, addOrderOf_zero] at hg
    exact hp.out.one_lt.ne' hg.symm
  have htors : ∀ y : G ⧸ H, p • y = 0 := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H x =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hnot
  obtain ⟨f, fsurj⟩ := exists_surjective_hom_zmod_of_torsion p htors hy
  refine ⟨f.comp (QuotientAddGroup.mk' H), ?_⟩
  exact fsurj.comp (QuotientAddGroup.mk'_surjective H)

/-- **Lemma `lem:mto1`** (`paper.tex`, Section 2.2): Let `G` be a finite abelian group of order
`pM`, where `p` is a prime. Then there is a surjective homomorphism `Φ : G → 𝔽_p`; in
particular `Φ` is an `M`-to-`1` map (every fibre has exactly `M` elements). -/
theorem exists_surjective_hom_zmod_card_fiber {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (p M : ℕ) [Fact p.Prime] (hcard : Fintype.card G = p * M) :
    ∃ Φ : G →+ ZMod p, Function.Surjective Φ ∧
      ∀ a : ZMod p, (univ.filter fun g => Φ g = a).card = M := by
  obtain ⟨Φ, hΦ⟩ := exists_surjective_hom_zmod p (G := G) ⟨M, hcard⟩
  refine ⟨Φ, hΦ, ?_⟩
  have hall : ∀ a : ZMod p, (univ.filter fun g => Φ g = a).card =
      (univ.filter fun g => Φ g = 0).card := fun a =>
    AddMonoidHom.card_fiber_eq_of_mem_range Φ (hΦ a) (hΦ 0)
  have hsum : ∑ a : ZMod p, (univ.filter fun g => Φ g = a).card = Fintype.card G := by
    rw [← Finset.card_univ (α := G), Finset.card_eq_sum_card_fiberwise (f := Φ) (t := univ)]
    intro x _; simp
  rw [Finset.sum_congr rfl (fun a _ => hall a), Finset.sum_const, Finset.card_univ,
    ZMod.card, smul_eq_mul, hcard] at hsum
  intro a
  rw [hall a]
  exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos hsum

/-- **Lemma `lem:powersumFF`** (`paper.tex`, Section 2.2): for a prime `p` and every integer
`k ≥ 1`, `∑_{α ∈ 𝔽_p} α^k = -1` if `p - 1 ∣ k` and `= 0` otherwise. -/
theorem sum_zmod_pow (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) :
    ∑ α : ZMod p, α ^ k = if p - 1 ∣ k then -1 else 0 := by
  classical
  have h := FiniteField.sum_pow_units (ZMod p) k
  rw [ZMod.card] at h
  rw [← h]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p)), zero_pow (by omega), add_zero]
  refine Finset.sum_bij' (fun a ha => Units.mk0 a (Finset.ne_of_mem_erase ha))
    (fun u _ => (u : ZMod p)) (by simp) (by simp) (by simp) (by simp) (by simp)

end LatticeTiling
