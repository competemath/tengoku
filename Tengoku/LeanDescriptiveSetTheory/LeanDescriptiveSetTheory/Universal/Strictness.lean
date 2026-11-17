/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.FiniteHierarchy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strictness of the finite Borel hierarchy on Cantor space

Given a universal additive relation `U` on Cantor space, its complement along the diagonal is not
an additive set at the same level. Otherwise universality would produce a parameter `p` whose
section equals the diagonal complement, forcing membership of `(p, p)` in `U` to be equivalent to
its negation.

The relation itself has the advertised additive complexity, so the diagonal complement is
multiplicative. Complementing once more yields the dual additive-not-multiplicative witness. Thus
the two polarities differ at every positive finite level on Cantor space.
-/

open Set TopologicalSpace

namespace DescriptiveSetTheory

/-- The diagonal map from Cantor space to its square.-/
def cantorDiagonal (p : ℕ → Bool) : (ℕ → Bool) × (ℕ → Bool) :=
  (p, p)

/-- The Cantor-space diagonal map is continuous.
@isnad1 id=continuo.0h0v.s5.66e9aae7ba54 from=translated src=- shape=5dbdefd2 vocab=56ccd271
-/
theorem continuous_cantorDiagonal : Continuous cantorDiagonal :=
  continuous_id.prodMk continuous_id

/-- The complement of a relation pulled back along the Cantor-space diagonal.-/
def diagonalComplement (U : Set ((ℕ → Bool) × (ℕ → Bool))) : Set (ℕ → Bool) :=
  cantorDiagonal ⁻¹' Uᶜ

/-- Membership in the diagonal complement means failure of self-membership in the relation.
@isnad1 id=iff.0h2v.s6.edafb243f416 from=translated src=- shape=2595729d vocab=38670e02
-/
@[simp] theorem mem_diagonalComplement {U : Set ((ℕ → Bool) × (ℕ → Bool))}
    {p : ℕ → Bool} : p ∈ diagonalComplement U ↔ (p, p) ∉ U :=
  Iff.rfl

/-- The diagonal complement of an additive relation is multiplicative at the same level.
@isnad1 id=pi0.1h2v.s5.c504bb5993dc from=translated src=- shape=eb0b75ce vocab=29f07791
-/
theorem Sigma0.diagonalComplement {n : ℕ} {U : Set ((ℕ → Bool) × (ℕ → Bool))}
    (hU : Sigma0 n U) : Pi0 n (diagonalComplement U) :=
  hU.compl.preimage continuous_cantorDiagonal

/-- Diagonalization prevents a universal additive relation from coding its own diagonal
complement.
@isnad1 id=not.1h2v.s5.f8ff3082a803 from=translated src=- shape=f67a7685 vocab=7c9d15e0
-/
theorem IsUniversalFor.not_sigma0_diagonalComplement {n : ℕ}
    {U : Set ((ℕ → Bool) × (ℕ → Bool))} (hU : IsUniversalFor (Sigma0 n) U) :
    ¬ Sigma0 n (diagonalComplement U) := by
  intro hdiagonal
  obtain ⟨p, hp⟩ := (hU (diagonalComplement U)).1 hdiagonal
  have hself := Set.ext_iff.mp hp p
  simp only [verticalSection, mem_diagonalComplement, mem_ofPred_eq] at hself
  tauto

/-- A canonical level `n + 1` multiplicative set that is not additive at that level.-/
def cantorPiNotSigma (n : ℕ) : Set (ℕ → Bool) :=
  diagonalComplement (cantorUniversalSigma n)

/-- The canonical multiplicative witness belongs to level `n + 1`.
@isnad1 id=pi0.0h1v.s4.0bf0d043467b from=translated src=- shape=ffbe7984 vocab=88efbf5d
-/
theorem pi0_cantorPiNotSigma (n : ℕ) : Pi0 (n + 1) (cantorPiNotSigma n) :=
  (sigma0_cantorUniversalSigma n).diagonalComplement

/-- The canonical multiplicative witness does not belong to the same additive level.
@isnad1 id=not.0h1v.s4.05f6cc0313d4 from=translated src=- shape=2ef82b2c vocab=fca81f07
-/
theorem not_sigma0_cantorPiNotSigma (n : ℕ) : ¬ Sigma0 (n + 1) (cantorPiNotSigma n) :=
  (isUniversalFor_cantorUniversalSigma n).not_sigma0_diagonalComplement

/-- A canonical level `n + 1` additive set that is not multiplicative at that level.-/
def cantorSigmaNotPi (n : ℕ) : Set (ℕ → Bool) :=
  (cantorPiNotSigma n)ᶜ

/-- The canonical additive witness belongs to level `n + 1`.
@isnad1 id=sigma0.0h1v.s4.c0face2fae1e from=translated src=- shape=ffbe7984 vocab=8585a6f4
-/
theorem sigma0_cantorSigmaNotPi (n : ℕ) : Sigma0 (n + 1) (cantorSigmaNotPi n) :=
  (pi0_cantorPiNotSigma n).compl

/-- The canonical additive witness does not belong to the same multiplicative level.
@isnad1 id=not.0h1v.s4.2e914517d762 from=translated src=- shape=2ef82b2c vocab=02f5141d
-/
theorem not_pi0_cantorSigmaNotPi (n : ℕ) : ¬ Pi0 (n + 1) (cantorSigmaNotPi n) := by
  intro hpi
  apply not_sigma0_cantorPiNotSigma n
  simpa [cantorSigmaNotPi] using hpi.compl

/-- At every positive finite level, some Cantor-space multiplicative set is not additive.
@isnad1 id=ex.0h1v.s6.268a82e2f8cc from=translated src=- shape=e7a7784a vocab=d25e7cc1
-/
theorem exists_pi0_not_sigma0_cantor (n : ℕ) :
    ∃ s : Set (ℕ → Bool), Pi0 (n + 1) s ∧ ¬ Sigma0 (n + 1) s :=
  ⟨cantorPiNotSigma n, pi0_cantorPiNotSigma n, not_sigma0_cantorPiNotSigma n⟩

/-- At every positive finite level, some Cantor-space additive set is not multiplicative.
@isnad1 id=ex.0h1v.s6.978e5cb5f869 from=translated src=- shape=e7a7784a vocab=d25e7cc1
-/
theorem exists_sigma0_not_pi0_cantor (n : ℕ) :
    ∃ s : Set (ℕ → Bool), Sigma0 (n + 1) s ∧ ¬ Pi0 (n + 1) s :=
  ⟨cantorSigmaNotPi n, sigma0_cantorSigmaNotPi n, not_pi0_cantorSigmaNotPi n⟩

end DescriptiveSetTheory
