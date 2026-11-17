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

/-- The additive recursion begins with the universal open relation.
@isnad1 id=eq.0h2v.s4.2407b99baba4 from=translated src=- shape=1a95c549 vocab=027dc93b
-/
@[simp] theorem finiteUniversalSigma_zero (b : ℕ → Set X) :
    finiteUniversalSigma b 0 = universalOpen b :=
  rfl

/-- Each successor additive relation is the section union of the preceding complement.
@isnad1 id=eq.0h3v.s5.5a9624391b39 from=translated src=- shape=bb27b073 vocab=4c7ab618
-/
@[simp] theorem finiteUniversalSigma_succ (b : ℕ → Set X) (n : ℕ) :
    finiteUniversalSigma b (n + 1) = cantorIUnion (finiteUniversalSigma b n)ᶜ :=
  rfl

/-- Multiplicative universal relations are complements of the additive relations.
@isnad1 id=eq.0h3v.s5.74a7735f723a from=translated src=- shape=5f5847a9 vocab=dc9394e0
-/
@[simp] theorem finiteUniversalPi_eq_compl (b : ℕ → Set X) (n : ℕ) :
    finiteUniversalPi b n = (finiteUniversalSigma b n)ᶜ :=
  rfl

/-- The recursively generated additive relation has the advertised finite Borel complexity.
@isnad1 id=sigma0.1h3v.s5.23c0a5d4f726 from=translated src=- shape=9b6694e5 vocab=557be210
-/
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

/-- The corresponding multiplicative relation has the advertised finite Borel complexity.
@isnad1 id=pi0.1h3v.s5.e62b8e9bda96 from=translated src=- shape=9b6694e5 vocab=4974167f
-/
theorem pi0_finiteUniversalPi [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) (n : ℕ) :
    Pi0 (n + 1) (finiteUniversalPi b n) :=
  (sigma0_finiteUniversalSigma hb n).compl

/-- Every additive set at a positive finite level is exactly one vertical section.
@isnad1 id=isuniver.1h3v.s5.21b6dd004a9f from=translated src=- shape=43ba1f1e vocab=f4d05a2f
-/
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

/-- Every multiplicative set at a positive finite level is exactly one vertical section.
@isnad1 id=isuniver.1h3v.s5.73a8b7c0b269 from=translated src=- shape=43ba1f1e vocab=42abd8e4
-/
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

/-- The level-one Baire additive relation is the previously defined universal open set.
@isnad1 id=eq.0h0v.s4.98deb656144a from=translated src=- shape=b8e8ca6b vocab=8b1c3d24
-/
@[simp] theorem baireUniversalSigma_zero : baireUniversalSigma 0 = baireUniversalOpen :=
  rfl

/-- The level-one Cantor additive relation is the previously defined universal open set.
@isnad1 id=eq.0h0v.s4.efe78d9efbf8 from=translated src=- shape=f0b44324 vocab=0ba05add
-/
@[simp] theorem cantorUniversalSigma_zero : cantorUniversalSigma 0 = cantorUniversalOpen :=
  rfl

/-- The Baire additive universal relation belongs to level `n + 1`.
@isnad1 id=sigma0.0h1v.s5.79f954b4f5e8 from=translated src=- shape=74b9925b vocab=29bf3276
-/
theorem sigma0_baireUniversalSigma (n : ℕ) : Sigma0 (n + 1) (baireUniversalSigma n) :=
  sigma0_finiteUniversalSigma isTopologicalBasis_range_baireCylinderBasisSequence n

/-- The Baire multiplicative universal relation belongs to level `n + 1`.
@isnad1 id=pi0.0h1v.s5.b3a2ed75beba from=translated src=- shape=74b9925b vocab=1653280c
-/
theorem pi0_baireUniversalPi (n : ℕ) : Pi0 (n + 1) (baireUniversalPi n) :=
  pi0_finiteUniversalPi isTopologicalBasis_range_baireCylinderBasisSequence n

/-- The Cantor additive universal relation belongs to level `n + 1`.
@isnad1 id=sigma0.0h1v.s5.5df215a28c8a from=translated src=- shape=d226756d vocab=061edf57
-/
theorem sigma0_cantorUniversalSigma (n : ℕ) : Sigma0 (n + 1) (cantorUniversalSigma n) :=
  sigma0_finiteUniversalSigma isTopologicalBasis_range_cantorCylinderBasisSequence n

/-- The Cantor multiplicative universal relation belongs to level `n + 1`.
@isnad1 id=pi0.0h1v.s5.221a129b74fb from=translated src=- shape=d226756d vocab=35374960
-/
theorem pi0_cantorUniversalPi (n : ℕ) : Pi0 (n + 1) (cantorUniversalPi n) :=
  pi0_finiteUniversalPi isTopologicalBasis_range_cantorCylinderBasisSequence n

/-- The Baire additive relation is universal for all level `n + 1` additive sets.
@isnad1 id=isuniver.0h1v.s5.af3e0c3dba71 from=translated src=- shape=a7405721 vocab=4a16aeb5
-/
theorem isUniversalFor_baireUniversalSigma (n : ℕ) :
    IsUniversalFor (Sigma0 (n + 1)) (baireUniversalSigma n) :=
  isUniversalFor_finiteUniversalSigma isTopologicalBasis_range_baireCylinderBasisSequence n

/-- The Baire multiplicative relation is universal for all level `n + 1` multiplicative sets.
@isnad1 id=isuniver.0h1v.s5.6f4e4a390910 from=translated src=- shape=a7405721 vocab=65226b9d
-/
theorem isUniversalFor_baireUniversalPi (n : ℕ) :
    IsUniversalFor (Pi0 (n + 1)) (baireUniversalPi n) :=
  isUniversalFor_finiteUniversalPi isTopologicalBasis_range_baireCylinderBasisSequence n

/-- The Cantor additive relation is universal for all level `n + 1` additive sets.
@isnad1 id=isuniver.0h1v.s5.4b270bb9b091 from=translated src=- shape=03faf015 vocab=23c5f4a5
-/
theorem isUniversalFor_cantorUniversalSigma (n : ℕ) :
    IsUniversalFor (Sigma0 (n + 1)) (cantorUniversalSigma n) :=
  isUniversalFor_finiteUniversalSigma isTopologicalBasis_range_cantorCylinderBasisSequence n

/-- The Cantor multiplicative relation is universal for all level `n + 1` multiplicative sets.
@isnad1 id=isuniver.0h1v.s5.f03cb440cf5b from=translated src=- shape=03faf015 vocab=01e4ba10
-/
theorem isUniversalFor_cantorUniversalPi (n : ℕ) :
    IsUniversalFor (Pi0 (n + 1)) (cantorUniversalPi n) :=
  isUniversalFor_finiteUniversalPi isTopologicalBasis_range_cantorCylinderBasisSequence n

end DescriptiveSetTheory
