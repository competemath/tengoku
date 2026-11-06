/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Ideal.Height
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.Normalization.Normal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The punctured spectrum of a local ring

This module supplies the canonical open complement of the closed point and
its basic nonemptiness criterion.
-/

noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

universe u

namespace Scheme

/-- The complement of the closed point in the spectrum of a local ring.-/
def puncturedSpectrumOpen (R : Type u) [CommRing R] [IsLocalRing R] :
    (Spec (.of R)).Opens :=
  ⟨{closedPoint R}ᶜ, (isClosed_singleton_closedPoint R).isOpen_compl⟩

/-- The punctured spectrum of a local ring.-/
abbrev puncturedSpectrum (R : Type u) [CommRing R] [IsLocalRing R] :
    Scheme.{u} :=
  (puncturedSpectrumOpen R).toScheme

/-- The canonical open immersion from the punctured spectrum into the full
local spectrum.-/
def puncturedSpectrumInclusion (R : Type u) [CommRing R] [IsLocalRing R] :
    puncturedSpectrum R ⟶ Spec (.of R) :=
  (puncturedSpectrumOpen R).ι

/--
@isnad1 id=iff.0h2v.s6.fcb5f56e4dbd from=translated src=- shape=d1ef6d0c vocab=0ab490a3
-/
@[simp]
theorem mem_puncturedSpectrumOpen_iff
    (R : Type u) [CommRing R] [IsLocalRing R]
    (x : PrimeSpectrum R) :
    x ∈ puncturedSpectrumOpen R ↔ x ≠ closedPoint R := by
  change x ∈ ({closedPoint R}ᶜ : Set (PrimeSpectrum R)) ↔
    x ≠ closedPoint R
  exact Iff.rfl

/-- A positive-dimensional local domain has a nonempty punctured spectrum:
its generic point is different from the closed point.
@isnad1 id=nonempty.1h1v.s5.dc55eb61fa2c from=translated src=- shape=99d0ec00 vocab=a3414fd7
-/
theorem puncturedSpectrum_nonempty_of_one_le_ringKrullDim
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R) :
    Nonempty (puncturedSpectrum R) := by
  have hmaximal : maximalIdeal R ≠ ⊥ := by
    intro hmaximal
    have hdimZero : ringKrullDim R = 0 := by
      rw [← maximalIdeal_height_eq_ringKrullDim, hmaximal,
        Ideal.height_bot]
      rfl
    rw [hdimZero] at hdim
    exact (not_le_of_gt (by norm_num : (0 : WithBot ℕ∞) < 1)) hdim
  let η : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  have hη : η ≠ closedPoint R := by
    intro h
    apply hmaximal
    exact (congrArg PrimeSpectrum.asIdeal h).symm
  exact ⟨⟨η, (mem_puncturedSpectrumOpen_iff R η).2 hη⟩⟩

end Scheme

end AlgebraicGeometry

end
