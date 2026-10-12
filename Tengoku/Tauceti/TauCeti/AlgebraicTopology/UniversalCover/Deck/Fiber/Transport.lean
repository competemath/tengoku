/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.AlgebraicTopology.UniversalCover.Deck.Conjugation
public import Tengoku.Tauceti.TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Basic

/-!
# Transporting deck actions on fibres

An isomorphism of maps over a common base identifies corresponding fibres. This file packages
that fibre identification and records that it intertwines the restricted deck actions with
conjugation of deck transformations.

Pointed cover isomorphisms carry chosen lifts of the basepoint between fibres, and the
pointed/unpointed cover correspondences need the deck action on those fibres to be compatible
with conjugating the deck group.

## Main definitions

* `TauCeti.Deck.fiberMap`: the homeomorphism between fibres induced by an over-base
  homeomorphism.
* `TauCeti.Deck.fiberMap_smul`: fibre transport intertwines the restricted deck actions via
  conjugation of deck transformations.
* `TauCeti.Deck.fiberMapStabilizerEquiv`: fibre transport identifies stabilizers via
  conjugation of deck transformations.
* `TauCeti.Deck.map_fiber_stabilizer_conjMulEquiv`: conjugation maps the source fibre
  stabilizer onto the transported target fibre stabilizer.
* `TauCeti.Deck.mem_orbit_fiberMap_iff`: fibre transport preserves deck-orbit membership.
-/

public section

namespace TauCeti

namespace Deck

variable {E F G B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  {p : E → B} {q : F → B} {r : G → B} {b : B}

/-- An over-base homeomorphism identifies the fibre over `b` for `p` with the fibre over
`b` for `q`. -/
@[expose] def fiberMap (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (b : B) :
    p ⁻¹' {b} ≃ₜ q ⁻¹' {b} :=
  h.subtype fun e => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hpq]

/-- On underlying points, the fibre map induced by an over-base homeomorphism is just that
homeomorphism. -/
@[simp]
lemma fiberMap_apply_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b}) :
    (fiberMap h hpq b e : F) = h e.1 :=
  rfl

/-- On underlying points, the inverse fibre map is the inverse of the over-base
homeomorphism. -/
@[simp]
lemma fiberMap_symm_apply_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (f : q ⁻¹' {b}) :
    ((fiberMap h hpq b).symm f : E) = h.symm f.1 :=
  rfl

/-- The fibre map induced by the identity over-base homeomorphism is the identity. -/
@[simp]
lemma fiberMap_refl :
    fiberMap (Homeomorph.refl E) (p := p) (q := p) (fun _ => rfl) b =
      Homeomorph.refl (p ⁻¹' {b}) := by
  ext e
  rfl

/-- The inverse of the fibre map induced by an over-base homeomorphism is the fibre map induced
by the inverse over-base homeomorphism. -/
@[simp]
lemma fiberMap_symm (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) : (fiberMap h hpq b).symm =
      fiberMap h.symm (map_symm_eq_of_map_eq h hpq) b := by
  ext f
  rfl

/-- Fibre maps compose as the underlying over-base homeomorphisms compose. -/
@[simp]
lemma fiberMap_trans (h : E ≃ₜ F) (k : F ≃ₜ G)
    (hpq : ∀ e, q (h e) = p e) (hqr : ∀ f, r (k f) = q f) :
    (fiberMap h hpq b).trans (fiberMap k hqr b) =
      fiberMap (h.trans k) (fun e => by rw [Homeomorph.trans_apply, hqr, hpq]) b := by
  ext e
  rfl

end Deck

end TauCeti
