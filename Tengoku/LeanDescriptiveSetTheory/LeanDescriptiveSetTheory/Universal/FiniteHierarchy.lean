/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal sets for the finite Borel hierarchy

Starting from a universal open relation, alternate relation complementation with countable section
union. The parameter is always Cantor space. Index `n` in `finiteUniversalSigma b n` represents the
one-based Borel level `n + 1`; the reserved empty level zero is deliberately omitted because no
relation over a nonempty parameter space can have no vertical sections.

The construction is generic in a natural-number-indexed topological basis. Baire and Cantor space
specializations use the cylinder bases from `Spaces.Cylinders`.
-/

open Set TopologicalSpace

universe u

namespace DescriptiveSetTheory

variable {X : Type u}

/-- Universal additive relations generated recursively from an enumerated topological basis.-/
def finiteUniversalSigma (b : ℕ → Set X) : ℕ → Set ((ℕ → Bool) × X)
  | 0 => universalOpen b
  | n + 1 => cantorIUnion (finiteUniversalSigma b n)ᶜ

/-- The multiplicative universal relation at the same positive finite level.-/
def finiteUniversalPi (b : ℕ → Set X) (n : ℕ) : Set ((ℕ → Bool) × X) :=
  (finiteUniversalSigma b n)ᶜ

/-- The additive recursion begins with the universal open relation.-/
@[simp] theorem finiteUniversalSigma_zero (b : ℕ → Set X) :
    finiteUniversalSigma b 0 = universalOpen b :=
  rfl

/-- Each successor additive relation is the section union of the preceding complement.-/
@[simp] theorem finiteUniversalSigma_succ (b : ℕ → Set X) (n : ℕ) :
    finiteUniversalSigma b (n + 1) = cantorIUnion (finiteUniversalSigma b n)ᶜ :=
  rfl

/-- Multiplicative universal relations are complements of the additive relations.-/
@[simp] theorem finiteUniversalPi_eq_compl (b : ℕ → Set X) (n : ℕ) :
    finiteUniversalPi b n = (finiteUniversalSigma b n)ᶜ :=
  rfl

/-- The recursively generated additive relation has the advertised finite Borel complexity.-/
theorem sigma0_finiteUniversalSigma [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) (n : ℕ) :
    Sigma0 (n + 1) (finiteUniversalSigma b n) := by
  induction n with
  | zero =>
      have hbo : ∀ i, IsOpen (b i) := fun i => hb.isOpen (Set.mem_range_self i)
      exact sigma0_one_of_isOpen (isOpen_universalOpen hbo)
  | succ n ih =>
      have hpi : Pi0 (n + 1) (finiteUniversalSigma b n)ᶜ := ih.compl
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hpi.cantorIUnion

/-- The corresponding multiplicative relation has the advertised finite Borel complexity.-/
theorem pi0_finiteUniversalPi [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) (n : ℕ) :
    Pi0 (n + 1) (finiteUniversalPi b n) :=
  (sigma0_finiteUniversalSigma hb n).compl

/-- Every additive set at a positive finite level is exactly one vertical section.-/
theorem isUniversalFor_finiteUniversalSigma [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) (n : ℕ) :
    IsUniversalFor (Sigma0 (n + 1)) (finiteUniversalSigma b n) := by
  induction n with
  | zero =>
      simpa only [IsUniversalFor, finiteUniversalSigma_zero, Nat.zero_add, sigma0_one_iff] using
        (isUniversalOpen_universalOpen hb).2
  | succ n ih =>
      have hpi : IsUniversalFor (Pi0 (n + 1)) (finiteUniversalSigma b n)ᶜ :=
        ih.compl_sigma0
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hpi.cantorIUnion

/-- Every multiplicative set at a positive finite level is exactly one vertical section.-/
theorem isUniversalFor_finiteUniversalPi [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) (n : ℕ) :
    IsUniversalFor (Pi0 (n + 1)) (finiteUniversalPi b n) :=
  (isUniversalFor_finiteUniversalSigma hb n).compl_sigma0

/-- The universal additive relation for level `n + 1` subsets of Baire space.-/
def baireUniversalSigma (n : ℕ) : Set ((ℕ → Bool) × (ℕ → ℕ)) :=
  finiteUniversalSigma baireCylinderBasisSequence n

/-- The universal multiplicative relation for level `n + 1` subsets of Baire space.-/
def baireUniversalPi (n : ℕ) : Set ((ℕ → Bool) × (ℕ → ℕ)) :=
  finiteUniversalPi baireCylinderBasisSequence n

/-- The universal additive relation for level `n + 1` subsets of Cantor space.-/
def cantorUniversalSigma (n : ℕ) : Set ((ℕ → Bool) × (ℕ → Bool)) :=
  finiteUniversalSigma cantorCylinderBasisSequence n

/-- The universal multiplicative relation for level `n + 1` subsets of Cantor space.-/
def cantorUniversalPi (n : ℕ) : Set ((ℕ → Bool) × (ℕ → Bool)) :=
  finiteUniversalPi cantorCylinderBasisSequence n

/-- The level-one Baire additive relation is the previously defined universal open set.-/
@[simp] theorem baireUniversalSigma_zero : baireUniversalSigma 0 = baireUniversalOpen :=
  rfl

/-- The level-one Cantor additive relation is the previously defined universal open set.-/
@[simp] theorem cantorUniversalSigma_zero : cantorUniversalSigma 0 = cantorUniversalOpen :=
  rfl

/-- The Baire additive universal relation belongs to level `n + 1`.-/
theorem sigma0_baireUniversalSigma (n : ℕ) : Sigma0 (n + 1) (baireUniversalSigma n) :=
  sigma0_finiteUniversalSigma isTopologicalBasis_range_baireCylinderBasisSequence n

/-- The Baire multiplicative universal relation belongs to level `n + 1`.-/
theorem pi0_baireUniversalPi (n : ℕ) : Pi0 (n + 1) (baireUniversalPi n) :=
  pi0_finiteUniversalPi isTopologicalBasis_range_baireCylinderBasisSequence n

/-- The Cantor additive universal relation belongs to level `n + 1`.-/
theorem sigma0_cantorUniversalSigma (n : ℕ) : Sigma0 (n + 1) (cantorUniversalSigma n) :=
  sigma0_finiteUniversalSigma isTopologicalBasis_range_cantorCylinderBasisSequence n

/-- The Cantor multiplicative universal relation belongs to level `n + 1`.-/
theorem pi0_cantorUniversalPi (n : ℕ) : Pi0 (n + 1) (cantorUniversalPi n) :=
  pi0_finiteUniversalPi isTopologicalBasis_range_cantorCylinderBasisSequence n

/-- The Baire additive relation is universal for all level `n + 1` additive sets.-/
theorem isUniversalFor_baireUniversalSigma (n : ℕ) :
    IsUniversalFor (Sigma0 (n + 1)) (baireUniversalSigma n) :=
  isUniversalFor_finiteUniversalSigma isTopologicalBasis_range_baireCylinderBasisSequence n

/-- The Baire multiplicative relation is universal for all level `n + 1` multiplicative sets.-/
theorem isUniversalFor_baireUniversalPi (n : ℕ) :
    IsUniversalFor (Pi0 (n + 1)) (baireUniversalPi n) :=
  isUniversalFor_finiteUniversalPi isTopologicalBasis_range_baireCylinderBasisSequence n

/-- The Cantor additive relation is universal for all level `n + 1` additive sets.-/
theorem isUniversalFor_cantorUniversalSigma (n : ℕ) :
    IsUniversalFor (Sigma0 (n + 1)) (cantorUniversalSigma n) :=
  isUniversalFor_finiteUniversalSigma isTopologicalBasis_range_cantorCylinderBasisSequence n

/-- The Cantor multiplicative relation is universal for all level `n + 1` multiplicative sets.-/
theorem isUniversalFor_cantorUniversalPi (n : ℕ) :
    IsUniversalFor (Pi0 (n + 1)) (cantorUniversalPi n) :=
  isUniversalFor_finiteUniversalPi isTopologicalBasis_range_cantorCylinderBasisSequence n

end DescriptiveSetTheory
