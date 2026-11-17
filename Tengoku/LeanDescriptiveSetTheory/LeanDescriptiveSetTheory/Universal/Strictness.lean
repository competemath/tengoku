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

/-- The Cantor-space diagonal map is continuous.-/
theorem continuous_cantorDiagonal : Continuous cantorDiagonal :=
  continuous_id.prodMk continuous_id

/-- The complement of a relation pulled back along the Cantor-space diagonal.-/
def diagonalComplement (U : Set ((ℕ → Bool) × (ℕ → Bool))) : Set (ℕ → Bool) :=
  cantorDiagonal ⁻¹' Uᶜ

/-- Membership in the diagonal complement means failure of self-membership in the relation.-/
@[simp] theorem mem_diagonalComplement {U : Set ((ℕ → Bool) × (ℕ → Bool))}
    {p : ℕ → Bool} : p ∈ diagonalComplement U ↔ (p, p) ∉ U :=
  Iff.rfl

/-- The diagonal complement of an additive relation is multiplicative at the same level.-/
theorem Sigma0.diagonalComplement {n : ℕ} {U : Set ((ℕ → Bool) × (ℕ → Bool))}
    (hU : Sigma0 n U) : Pi0 n (diagonalComplement U) :=
  hU.compl.preimage continuous_cantorDiagonal

/-- Diagonalization prevents a universal additive relation from coding its own diagonal
complement.-/
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

/-- The canonical multiplicative witness belongs to level `n + 1`.-/
theorem pi0_cantorPiNotSigma (n : ℕ) : Pi0 (n + 1) (cantorPiNotSigma n) :=
  (sigma0_cantorUniversalSigma n).diagonalComplement

/-- The canonical multiplicative witness does not belong to the same additive level.-/
theorem not_sigma0_cantorPiNotSigma (n : ℕ) : ¬ Sigma0 (n + 1) (cantorPiNotSigma n) :=
  (isUniversalFor_cantorUniversalSigma n).not_sigma0_diagonalComplement

/-- A canonical level `n + 1` additive set that is not multiplicative at that level.-/
def cantorSigmaNotPi (n : ℕ) : Set (ℕ → Bool) :=
  (cantorPiNotSigma n)ᶜ

/-- The canonical additive witness belongs to level `n + 1`.-/
theorem sigma0_cantorSigmaNotPi (n : ℕ) : Sigma0 (n + 1) (cantorSigmaNotPi n) :=
  (pi0_cantorPiNotSigma n).compl

/-- The canonical additive witness does not belong to the same multiplicative level.-/
theorem not_pi0_cantorSigmaNotPi (n : ℕ) : ¬ Pi0 (n + 1) (cantorSigmaNotPi n) := by
  intro hpi
  apply not_sigma0_cantorPiNotSigma n
  simpa [cantorSigmaNotPi] using hpi.compl

/-- At every positive finite level, some Cantor-space multiplicative set is not additive.-/
theorem exists_pi0_not_sigma0_cantor (n : ℕ) :
    ∃ s : Set (ℕ → Bool), Pi0 (n + 1) s ∧ ¬ Sigma0 (n + 1) s :=
  ⟨cantorPiNotSigma n, pi0_cantorPiNotSigma n, not_sigma0_cantorPiNotSigma n⟩

/-- At every positive finite level, some Cantor-space additive set is not multiplicative.-/
theorem exists_sigma0_not_pi0_cantor (n : ℕ) :
    ∃ s : Set (ℕ → Bool), Sigma0 (n + 1) s ∧ ¬ Pi0 (n + 1) s :=
  ⟨cantorSigmaNotPi n, sigma0_cantorSigmaNotPi n, not_pi0_cantorSigmaNotPi n⟩

end DescriptiveSetTheory
