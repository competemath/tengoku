/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.StringDiagramsLean.StringDiagrams.Super.LaurentBasis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parity-compatible representatives of grading-shift orbits

For the corrected first preliminary fact of BE2 §11, parity acts on the
integer-shift orbits of indecomposables. A fixed orbit cannot carry a nonzero
integer twist: squaring parity would give a nonzero shift stabilizer. Thus one
can choose representatives compatibly with parity, without introducing powers
of q in its action on the Laurent basis.
-/

noncomputable section
namespace StringDiagrams.LaurentBasis
variable {ι : Type*} [AddAction ℤ ι]
  (σ : ι → ι) (hσ : Function.Involutive σ)
  (hc : ∀ (n : ℤ) (i : ι), σ (n +ᵥ i) = n +ᵥ σ i)
  (hf : ∀ (i : ι) (n : ℤ), n +ᵥ i = i → n = 0)

include hσ hc hf in
/-- An involution commuting with a free integer action has no twisted fixed points.
@isnad1 id=eq.4h4v.s7.6863619a529f from=translated src=- shape=4097157d vocab=421b8ee8
-/
theorem parity_shift_rigid (i : ι) (n : ℤ) (h : σ i = n +ᵥ i) : n = 0 := by
  have hn : (n + n) +ᵥ i = i := by
    rw [add_vadd, ← h, ← hc, ← h, hσ]
  have := hf i (n + n) hn
  omega

/-- The induced parity involution on integer-shift orbits.-/
def orbitParity : Orbit (ι := ι) → Orbit (ι := ι) :=
  Quotient.map σ (by
    rintro i j ⟨n, hn⟩
    exact ⟨n, (hc n j).symm.trans (congrArg σ hn)⟩)

include hσ in
/-- Parity still squares to the identity after quotienting integer shifts.
@isnad1 id=involuti.2h2v.s6.10a21e25e5f3 from=translated src=- shape=9e440647 vocab=7f8211e4
-/
theorem orbitParity_involutive : Function.Involutive (orbitParity σ hc) := by
  intro o
  induction o using Quotient.inductionOn with
  | h i => change Quotient.mk _ (σ (σ i)) = Quotient.mk _ i; rw [hσ]

include hσ hf in
/-- A parity-fixed shift orbit consists of parity-fixed representatives.
@isnad1 id=iff.3h3v.s7.c8fc44b13967 from=translated src=- shape=7115e023 vocab=8a9fd0de
-/
theorem orbitParity_fixed_iff (i : ι) :
    orbitParity σ hc (Quotient.mk _ i) = Quotient.mk _ i ↔ σ i = i := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Quotient.exact h
    have hz := parity_shift_rigid σ hσ hc hf i n hn.symm
    simpa only [hz, zero_vadd] using hn.symm
  · intro h
    change Quotient.mk _ (σ i) = Quotient.mk _ i
    rw [h]

section Ordered
variable [LinearOrder (Orbit (ι := ι))]

/-- Choose the representative on the smaller parity orbit; transport it on its partner.-/
def paritySection (o : Orbit (ι := ι)) : ι :=
  if orbitParity σ hc o < o then σ (orbitParity σ hc o).out else o.out

include hσ in
/-- The chosen representative has the prescribed integer-shift orbit.
@isnad1 id=eq.2h3v.s6.4aa86ede2cbb from=translated src=- shape=d927f8ac vocab=f99974c0
-/
theorem paritySection_spec (o : Orbit (ι := ι)) :
    Quotient.mk (AddAction.orbitRel ℤ ι) (paritySection σ hc o) = o := by
  classical
  unfold paritySection
  split_ifs
  · change orbitParity σ hc (Quotient.mk _ (orbitParity σ hc o).out) = o
    rw [Quotient.out_eq, orbitParity_involutive σ hσ hc]
  · exact Quotient.out_eq o

include hσ hf in
/-- The section is equivariant for parity, including fixed orbits.
@isnad1 id=eq.3h3v.s7.63302fdff5ed from=translated src=- shape=95b68670 vocab=b284181d
-/
theorem paritySection_parity (o : Orbit (ι := ι)) :
    paritySection σ hc (orbitParity σ hc o) = σ (paritySection σ hc o) := by
  classical
  have hs := orbitParity_involutive σ hσ hc
  rcases lt_trichotomy o (orbitParity σ hc o) with h | h | h
  · simp only [paritySection, hs o]
    rw [ite_eq_left h, ite_eq_right (not_lt_of_gt h)]
  · have hfix : σ o.out = o.out := by
      apply (orbitParity_fixed_iff σ hσ hc hf o.out).1
      rw [Quotient.out_eq, ← h]
    simp only [paritySection, ← h, lt_self_iff_false, ↓reduceIte, hfix]
  · simp only [paritySection, hs o]
    rw [ite_eq_right (not_lt_of_gt h), ite_eq_left h, hσ]

end Ordered

/-- Any section of a free shift action gives integer coordinates on each orbit.-/
def orbitEquivOfSection (r : Orbit (ι := ι) → ι)
    (hr : ∀ o, Quotient.mk (AddAction.orbitRel ℤ ι) (r o) = o) :
    Orbit (ι := ι) × ℤ ≃ ι :=
  Equiv.ofBijective (fun p => p.2 +ᵥ r p.1) (by
    constructor
    · rintro ⟨o, m⟩ ⟨p, n⟩ h
      have hop : o = p := by
        have := congrArg (Quotient.mk (AddAction.orbitRel ℤ ι)) h
        simpa only [AddAction.orbitRel.Quotient.quotient_vadd_eq, hr] using this
      subst p
      have hmn : m - n = 0 := hf (r o) (m - n) (by
        have := congrArg (fun i => (-n) +ᵥ i) h
        simpa only [← add_vadd, neg_add_cancel, zero_vadd, sub_eq_add_neg,
          add_comm m (-n)] using this)
      congr 1
      omega
    · intro i
      let o : Orbit (ι := ι) := Quotient.mk _ i
      have h : AddAction.orbitRel ℤ ι i (r o) := Quotient.exact (hr o).symm
      obtain ⟨n, hn⟩ := h
      exact ⟨(o, n), hn⟩)

variable {M : Type*} [AddCommGroup M] [Module (LaurentPolynomial ℤ) M]
open Module LaurentPolynomial

/-- Laurent basis using a prescribed section, rather than quotient choice.-/
def ofSection (b : Basis ι ℤ M)
    (hb : ∀ n i, (T n : LaurentPolynomial ℤ) • b i = b (n +ᵥ i))
    (r : Orbit (ι := ι) → ι)
    (hr : ∀ o, Quotient.mk (AddAction.orbitRel ℤ ι) (r o) = o) :
    Basis (Orbit (ι := ι)) (LaurentPolynomial ℤ) M :=
  ofProduct (b.reindex (orbitEquivOfSection hf r hr).symm) (by
    intro o n
    simp only [Basis.reindex_apply, Equiv.symm_symm]
    change (T n : LaurentPolynomial ℤ) • b ((0 : ℤ) +ᵥ r o) = b (n +ᵥ r o)
    simpa only [zero_vadd] using hb n (r o))

/--
@isnad1 id=eq.3h5v.s8.1b0aa74a27a8 from=translated src=- shape=5f5642af vocab=935b2030
-/
@[simp] theorem ofSection_apply (b : Basis ι ℤ M)
    (hb : ∀ n i, (T n : LaurentPolynomial ℤ) • b i = b (n +ᵥ i))
    (r : Orbit (ι := ι) → ι)
    (hr : ∀ o, Quotient.mk (AddAction.orbitRel ℤ ι) (r o) = o)
    (o : Orbit (ι := ι)) : ofSection hf b hb r hr o = b (r o) := by
  rw [ofSection, ofProduct_apply]
  simp only [Basis.reindex_apply, Equiv.symm_symm]
  change b ((0 : ℤ) +ᵥ r o) = b (r o)
  rw [zero_vadd]

variable [LinearOrder (Orbit (ι := ι))]

/-- A Laurent basis whose representatives are compatible with parity.-/
def parityCompatibleBasis (b : Basis ι ℤ M)
    (hb : ∀ n i, (T n : LaurentPolynomial ℤ) • b i = b (n +ᵥ i)) :
    Basis (Orbit (ι := ι)) (LaurentPolynomial ℤ) M :=
  ofSection hf b hb (paritySection σ hc) (paritySection_spec σ hσ hc)

/-- Parity permutes the normalized Laurent basis without grading factors.
@isnad1 id=eq.5h6v.s8.90eb1e7a40b8 from=translated src=- shape=eb6e4410 vocab=b18b1d3d
-/
theorem parityCompatibleBasis_parity (b : Basis ι ℤ M)
    (hb : ∀ n i, (T n : LaurentPolynomial ℤ) • b i = b (n +ᵥ i))
    (p : M → M) (hp : ∀ i, p (b i) = b (σ i)) (o : Orbit (ι := ι)) :
    p (parityCompatibleBasis σ hσ hc hf b hb o) =
      parityCompatibleBasis σ hσ hc hf b hb (orbitParity σ hc o) := by
  simp only [parityCompatibleBasis, ofSection_apply, hp,
    paritySection_parity σ hσ hc hf]

end StringDiagrams.LaurentBasis
