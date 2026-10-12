/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.AlgebraicTopology.UniversalCover.Deck.Basic

/-!
# Conjugating deck transformations

An isomorphism of maps over the same base transports deck transformations by conjugation.
This file packages that transport as a multiplicative equivalence of deck groups, so that
covers identified up to isomorphism over the base have their deck groups identified by
conjugating along the chosen total-space homeomorphism.

## Main definitions

* `TauCeti.Deck.conjMulEquiv`: if `h : E ≃ₜ F` satisfies `q (h e) = p e`, then
  conjugation by `h` gives `deck p ≃* deck q`.
* `TauCeti.Deck.conjMulEquivRefl`: the identity over-base homeomorphism induces the
  identity deck-group equivalence.
* `TauCeti.Deck.conjMulEquivTrans`: conjugating along a composite over-base
  homeomorphism is the composite of the conjugation equivalences.
-/

public section

namespace TauCeti

namespace Deck

variable {E F G B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  {p : E → B} {q : F → B} {r : G → B}

/-- If `h : E ≃ₜ F` lies over the base, then its inverse also lies over the base in the
opposite direction. -/
lemma map_symm_eq_of_map_eq (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (f : F) :
    p (h.symm f) = q f := by
  rw [← hpq (h.symm f), h.apply_symm_apply]

/-- The homeomorphism obtained by conjugating an end-homeomorphism by `h`. -/
private def conjHomeomorph (h : E ≃ₜ F) (φ : E ≃ₜ E) : F ≃ₜ F :=
  (h.symm.trans φ).trans h

/-- Conjugating by the identity homeomorphism leaves an end-homeomorphism unchanged. -/
@[simp]
private lemma conjHomeomorph_refl (φ : E ≃ₜ E) :
    conjHomeomorph (Homeomorph.refl E) φ = φ := by
  ext e
  simp [conjHomeomorph]

/-- Conjugation by a homeomorphism evaluates by `h.symm`, then `φ`, then `h`. -/
@[simp]
private lemma conjHomeomorph_apply (h : E ≃ₜ F) (φ : E ≃ₜ E) (f : F) :
    conjHomeomorph h φ f = h (φ (h.symm f)) := by
  rfl

/-- The inverse of a conjugated homeomorphism is the conjugate of the inverse. -/
@[simp]
private lemma conjHomeomorph_symm (h : E ≃ₜ F) (φ : E ≃ₜ E) :
    (conjHomeomorph h φ).symm = conjHomeomorph h φ.symm := by
  ext f
  simp [conjHomeomorph]

/-- Conjugation sends the identity homeomorphism to the identity homeomorphism. -/
@[simp]
private lemma conjHomeomorph_one (h : E ≃ₜ F) :
    conjHomeomorph h 1 = 1 := by
  ext f
  simp [conjHomeomorph]

/-- Conjugation sends composition of homeomorphisms to composition of the conjugates. -/
@[simp]
private lemma conjHomeomorph_mul (h : E ≃ₜ F) (φ ψ : E ≃ₜ E) :
    conjHomeomorph h (φ * ψ) = conjHomeomorph h φ * conjHomeomorph h ψ := by
  ext f
  simp [conjHomeomorph, Homeomorph.mul_apply]

/-- Conjugating twice is the same as conjugating by the composite homeomorphism. -/
@[simp]
private lemma conjHomeomorph_trans (h : E ≃ₜ F) (k : F ≃ₜ G) (φ : E ≃ₜ E) :
    conjHomeomorph k (conjHomeomorph h φ) = conjHomeomorph (h.trans k) φ := by
  ext g
  simp [conjHomeomorph]

/-- Conjugation by a homeomorphism as a multiplicative equivalence of homeomorphism groups. -/
private def conjHomeomorphMulEquiv (h : E ≃ₜ F) : (E ≃ₜ E) ≃* (F ≃ₜ F) where
  toFun := conjHomeomorph h
  invFun := conjHomeomorph h.symm
  left_inv φ := by
    ext e
    simp [conjHomeomorph]
  right_inv ψ := by
    ext f
    simp [conjHomeomorph]
  map_mul' φ ψ := by
    ext f
    simp [conjHomeomorph, Homeomorph.mul_apply]

end Deck

end TauCeti
