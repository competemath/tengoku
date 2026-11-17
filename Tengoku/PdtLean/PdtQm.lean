/-
PDT — the complex-number arithmetic behind single-qubit quantum kinematics.

Every theorem below is a fact about ℂ, kernel-checked by `lake build`: the Born form
`|z|²`, positivity, the dagger = complex conjugation = `starRingEnd ℂ`, Hermitian ⟹ real,
and unitary ⟹ norm-preserving.

THE NAMED POSIT (T4, kept explicit): `QisHilbert H` says a physical state space is
ℝ-linearly the complex place of Q's field (≃ₗ[ℝ] ℂ). The theorems below are about ℂ
directly and do NOT use this equivalence — the posit is stated, not yet load-bearing —
and the identification with physical QM and with Q's complex place is interpretive, not
kernel-checked. The oracle is the Lean kernel: a green build is the verification.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace PDT
open Complex

/-- THE NAMED POSIT (T4) — the one hypothesis everything hangs off, kept explicit.
    A physical one-qubit state space `H` is ℝ-linearly equivalent to Q's complex place ℂ.-/
abbrev QisHilbert (H : Type*) [AddCommGroup H] [Module ℝ H] : Type _ := H ≃ₗ[ℝ] ℂ

/-- Born form = the conjugate-twisted trace form = |z|². The SQUARE is forced by [ℂ:ℝ]=2.
@isnad1 id=eq.0h1v.s6.032fb09f9c9c from=translated src=- shape=b4a015a4 vocab=0e947930
-/
theorem born_form (z : ℂ) : (z * (starRingEnd ℂ) z).re = normSq z := by
  rw [Complex.mul_conj]; simp

/-- Born positivity: |z|² ≥ 0 always, and > 0 for a nonzero amplitude (a genuine probability).
@isnad1 id=le.0h1v.s5.e5b7382d9d1a from=translated src=- shape=904cabbd vocab=b0900fee
-/
theorem born_nonneg (z : ℂ) : 0 ≤ normSq z := normSq_nonneg z
/--
@isnad1 id=lt.1h1v.s5.d2aa63d6ead0 from=translated src=- shape=8b4c4c0b vocab=15795c85
-/
theorem born_pos {z : ℂ} (hz : z ≠ 0) : 0 < normSq z := normSq_pos.mpr hz

/-- dagger = Galois conjugation is an involution (F² = +1).
@isnad1 id=involuti.0h0v.s5.51185416e321 from=translated src=- shape=a53faaaa vocab=bcd1bdb2
-/
theorem dagger_invol : Function.Involutive (starRingEnd ℂ) := Complex.conj_conj

/-- dagger is multiplicative (a ring hom): (a·z)† = a†·z†.
@isnad1 id=eq.0h2v.s7.25be3182b2f3 from=translated src=- shape=dde8cb37 vocab=08c3b1d2
-/
theorem dagger_mul (a z : ℂ) :
    (starRingEnd ℂ) (a * z) = (starRingEnd ℂ) a * (starRingEnd ℂ) z := map_mul _ a z

/-- Hermitian = Galois-FIXED ⇒ real. Observables (the Galois-fixed elements) have real
    values — this is the pointer basis.
@isnad1 id=eq.1h1v.s5.6b653d598c9d from=translated src=- shape=c179ddf2 vocab=9af8f9c8
-/
theorem hermitian_real {z : ℂ} (h : (starRingEnd ℂ) z = z) : z.im = 0 := by
  have h2 : -z.im = z.im := by rw [← Complex.conj_im]; exact congrArg Complex.im h
  linarith

/-- Unitary scalar (z·z† = 1) ⇒ |z|² = 1: evolution preserves the Born norm.
@isnad1 id=eq.1h1v.s6.1335668de0d6 from=translated src=- shape=83a6d7b5 vocab=5d093edd
-/
theorem unitary_normSq_one {z : ℂ} (h : z * (starRingEnd ℂ) z = 1) : normSq z = 1 := by
  have h2 := congrArg Complex.re h
  rw [Complex.mul_conj] at h2
  simpa using h2

/-- THE CAPSTONE: for normalized two-outcome amplitudes `a b : ℂ`, the Born probabilities
    are `|z|²` (the conjugate-twisted trace form), nonnegative, and sum to one — a genuine
    probability rule assembling `born_form`/`normSq_nonneg`, with NO independent Born
    postulate. A theorem about ℂ; `QisHilbert` is not used.
@isnad1 id=and.1h2v.s8.fa366540e46c from=translated src=- shape=a05ea74e vocab=87df8a4b
-/
theorem QM_from_Q {a b : ℂ} (hnorm : normSq a + normSq b = 1) :
    (a * (starRingEnd ℂ) a).re = normSq a ∧
    (b * (starRingEnd ℂ) b).re = normSq b ∧
    0 ≤ normSq a ∧ 0 ≤ normSq b ∧
    normSq a + normSq b = 1 :=
  ⟨born_form a, born_form b, normSq_nonneg a, normSq_nonneg b, hnorm⟩

/-- `born_nonneg` for `P ψ`, where `P : QisHilbert H`. NOTE: this uses only that `P ψ : ℂ`
    (via `normSq_nonneg`); the ℝ-linear-equivalence STRUCTURE of `P` is never used, so this
    does NOT make the posit load-bearing — the theorems above are about ℂ directly. Making
    the posit genuinely do work is future formalization, not yet done.
@isnad1 id=le.0h3v.s6.f2a5ff54de40 from=translated src=- shape=c4ddaa61 vocab=5304dd01
-/
theorem born_nonneg_physical {H : Type*} [AddCommGroup H] [Module ℝ H]
    (P : QisHilbert H) (ψ : H) : 0 ≤ normSq (P ψ) := normSq_nonneg _

end PDT
