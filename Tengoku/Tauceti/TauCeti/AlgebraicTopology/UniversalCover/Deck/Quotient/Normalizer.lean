/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.Group.NormalizerQuotient.Basic
public import Tengoku.Tauceti.TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.ActingGroup
public import Tengoku.Tauceti.TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# The deck group of an intermediate quotient is a normalizer quotient

Let `p : E → X` be a quotient covering map for a group `Γ` acting on `E`, let `H ≤ Γ`, and let
`q : E → F` present `F` as the quotient of `E` by `H`, so that `p` factors as `r ∘ q` for a
covering map `r : F → X`. This file computes the deck transformation group of the intermediate
covering `r`:

  `deck r ≃* N(H) ⧸ H`,

where `N(H)` is the normalizer of `H` in `Γ`. Taking `H = ⊥` recovers
`TauCeti.Deck.IsQuotientCoveringMap.deckMulEquiv`, which identifies `deck p` with `Γ` itself.

Only a normalizer element descends to the quotient as a deck transformation: translation by
`γ` respects the `H`-orbit relation, so descends as a map, exactly when `γ H γ⁻¹ ⊆ H`, while
the descended map is invertible, hence a homeomorphism, exactly when `γ H γ⁻¹ = H`, that is,
when `γ` normalizes `H`.

Conversely every deck transformation of `r` arises this way, by uniqueness of lifts. A deck
transformation `φ` of `r`, precomposed with `q`, and translation by a suitable `γ` followed by
`q`, are two lifts of `p` through `r` which agree at one point of the preconnected space `E`,
hence agree everywhere; comparing the translates of a single point then forces `γ` to
normalize `H`.

## Main declarations

* `TauCeti.Deck.IsQuotientCoveringMap.normalizerMap`: translation by a normalizer element,
  descended to the orbit quotient.
* `TauCeti.Deck.IsQuotientCoveringMap.normalizerDeckHom`: the resulting homomorphism from the
  normalizer to `deck r`.
* `TauCeti.Deck.IsQuotientCoveringMap.ker_normalizerDeckHom`: its kernel is `H`.
* `TauCeti.Deck.IsQuotientCoveringMap.normalizerDeckHom_surjective`: it is surjective when `E`
  is preconnected and `r` is a covering map.
* `TauCeti.Deck.IsQuotientCoveringMap.normalizerQuotientDeckMulEquiv`: **the deck group of `r`
  is `N(H) ⧸ H`.**
* `TauCeti.Deck.IsQuotientCoveringMap.quotientDeckMulEquivOfNormal`: for normal `H` this reads
  `deck r ≃* Γ ⧸ H`.

## References

The cover attached to `H ≤ π₁(X, x₀)` has deck group `N(H)/H`, and `π₁(X, x₀)/H` when `H` is
normal. The quotient-covering-map interface it
consumes (`Mathlib/Topology/Covering/Quotient.lean`) is due to Junyan Xu, and uniqueness of
lifts, `IsCoveringMap.eq_of_comp_eq` in `Mathlib/Topology/Covering/Basic.lean`, is due to
Thomas Browning after Hatcher, *Algebraic Topology*, Proposition 1.34.
-/

public section
noncomputable section

namespace TauCeti

namespace Deck

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
variable {Γ : Type*} [Group Γ] [MulAction Γ E]
variable {p : E → X} {q : E → F} {r : F → X} {H : Subgroup Γ}

namespace IsQuotientCoveringMap

section Descend

variable (hq : IsQuotientCoveringMap q H)
include hq

/-- Translation by an element of the normalizer of `H`, descended to the quotient of `E` by the
`H`-action. It is well defined because `γ H γ⁻¹ = H`. -/
def normalizerMap (γ : _root_.Subgroup.normalizer (H : Set Γ)) (y : F) : F :=
  q ((γ : Γ) • Function.surjInv hq.surjective y)

/-- The descended translation sends the class of `e` to the class of `γ • e`. -/
@[simp]
theorem normalizerMap_apply (γ : _root_.Subgroup.normalizer (H : Set Γ)) (e : E) :
    normalizerMap hq γ (q e) = q ((γ : Γ) • e) := by
  obtain ⟨h, hh⟩ :=
    hq.apply_eq_iff_mem_orbit.mp (Function.surjInv_eq hq.surjective (q e))
  have hsurj : Function.surjInv hq.surjective (q e) = (h : Γ) • e := hh.symm
  have hconj : (γ : Γ) * (h : Γ) * (γ : Γ)⁻¹ ∈ H :=
    (_root_.Subgroup.mem_normalizer_iff.mp γ.2 (h : Γ)).mp h.2
  have hstep : (γ : Γ) • ((h : Γ) • e) = ((⟨_, hconj⟩ : H) : Γ) • ((γ : Γ) • e) := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  rw [normalizerMap, hsurj, hstep]
  exact hq.map_smul (⟨_, hconj⟩ : H)

/-- The identity of the normalizer descends to the identity. -/
@[simp]
theorem normalizerMap_one (y : F) : normalizerMap hq 1 y = y := by
  obtain ⟨e, rfl⟩ := hq.surjective y
  rw [normalizerMap_apply]
  simp

/-- Descending translations is multiplicative, the right factor acting first. -/
@[simp]
theorem normalizerMap_mul (γ γ' : _root_.Subgroup.normalizer (H : Set Γ)) (y : F) :
    normalizerMap hq (γ * γ') y = normalizerMap hq γ (normalizerMap hq γ' y) := by
  obtain ⟨e, rfl⟩ := hq.surjective y
  rw [normalizerMap_apply, normalizerMap_apply, normalizerMap_apply, Subgroup.coe_mul, mul_smul]

variable [ContinuousConstSMul Γ E]

/-- The descended translation is continuous, because `q` is a quotient map. -/
theorem continuous_normalizerMap (γ : _root_.Subgroup.normalizer (H : Set Γ)) :
    Continuous (normalizerMap hq γ) := by
  rw [hq.toIsQuotientMap.continuous_iff]
  have h : normalizerMap hq γ ∘ q = fun e => q ((γ : Γ) • e) :=
    funext fun e => normalizerMap_apply hq γ e
  rw [h]
  exact hq.isCoveringMap.continuous.comp (continuous_const_smul _)

/-- Translation by a normalizer element, as a homeomorphism of the orbit quotient. -/
def normalizerHomeomorph (γ : _root_.Subgroup.normalizer (H : Set Γ)) : F ≃ₜ F where
  toFun := normalizerMap hq γ
  invFun := normalizerMap hq γ⁻¹
  left_inv y := by rw [← normalizerMap_mul, inv_mul_cancel, normalizerMap_one]
  right_inv y := by rw [← normalizerMap_mul, mul_inv_cancel, normalizerMap_one]
  continuous_toFun := continuous_normalizerMap hq γ
  continuous_invFun := continuous_normalizerMap hq γ⁻¹

@[simp]
theorem normalizerHomeomorph_apply (γ : _root_.Subgroup.normalizer (H : Set Γ)) (e : E) :
    normalizerHomeomorph hq γ (q e) = q ((γ : Γ) • e) :=
  normalizerMap_apply hq γ e

/-- The inverse of the descended translation is translation by the inverse. -/
@[simp]
theorem normalizerHomeomorph_symm_apply (γ : _root_.Subgroup.normalizer (H : Set Γ)) (e : E) :
    (normalizerHomeomorph hq γ).symm (q e) = q ((γ : Γ)⁻¹ • e) := by
  rw [Homeomorph.symm_apply_eq, normalizerHomeomorph_apply, smul_inv_smul]

end Descend

section DeckHom

variable (hp : IsQuotientCoveringMap p Γ) (hq : IsQuotientCoveringMap q H) (hr : r ∘ q = p)
include hp hq hr

end DeckHom

section Normal

variable (hp : IsQuotientCoveringMap p Γ) (hq : IsQuotientCoveringMap q H) (hr : r ∘ q = p)
variable [H.Normal]
include hp hq hr

omit hp hq hr in
/-- For a normal subgroup, the identity is a homomorphism onto the normalizer. -/
private def toNormalizerOfNormal : Γ →* _root_.Subgroup.normalizer (H : Set Γ) where
  toFun γ := ⟨γ, _root_.Subgroup.subset_normalizer_of_normal (Set.mem_univ γ)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Normal

end IsQuotientCoveringMap

end Deck

end TauCeti
