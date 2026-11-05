/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.Local.Chart
public import Tengoku.Hironaka.Hironaka.Algebra.Local.ChartLocal
public import Tengoku.Seed.RingTheory.Derivation.Lie

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinates on the local ring of the chart at its origin

On the chart `x_r ≠ 0` of the blow-up of `⟨x₀, …, x_r⟩` the functions `yᵢ = xᵢ/x_r` (`i < r`),
`y_r = x_r`, `yⱼ = xⱼ` (`j > r`) are local coordinates [Kol07, Definition 60], and the
transformed derivations `∂'ⱼ` of `Hironaka/Algebra/Local/ChartRing.lean` (`∂'ⱼ = x_r ∂ⱼ` for `j <
r`, `∂'_r = ∂_r + ∑_{i<r} yᵢ ∂ᵢ`, `∂'ⱼ = ∂ⱼ` for `j > r`) satisfy `∂'ⱼ yₖ = δⱼₖ`
(`Hironaka/Algebra/Local/Chart.lean`).  This module packages `A' = R'_{𝔪'}` with the images of the
`yᵢ` and the localized `∂'ⱼ` as a `RegularCoords A' n`, the coordinate structure of the chart at its
origin:

* the ring-theoretic fields (regularity, `𝔪' A' = ⟨yᵢ⟩`, `dim A' = n`) are proved in
  `Hironaka/Algebra/Local/ChartLocal.lean`;
* `∂'ⱼ yₖ = δⱼₖ` transfers along the localization map (`Derivation.localization_algebraMap`);
* the `∂'ⱼ` commute.  The `∂ⱼ` extended to `R[1/x_r]` commute (the extension of a commutator is
  the commutator of the extensions, `Derivation.localization_comm`), and for two commuting
  derivations `D₁`, `D₂` and ring elements `f`, `g` one has the derivation identity
  `[f D₁, g D₂] = f (D₁ g) D₂ − g (D₂ f) D₁`; the five cases `i < j < r`, `i < j = r`,
  `i < r < j`, `i = r < j`, `r < i < j` are then read off the table `∂ⱼ x_r = δⱼᵣ`,
  `∂ⱼ yₖ = δⱼₖ u − δⱼᵣ xₖ u²` (`k < r`, `u = 1/x_r`) of `Hironaka/Algebra/Local/Chart.lean` — e.g.
  for `i < j = r`,
  `[x_r ∂ᵢ, ∂_r] = −∂ᵢ` and `∑_{k<r} [x_r ∂ᵢ, yₖ ∂ₖ] = ∑_{k<r} δᵢₖ x_r u ∂ₖ = ∂ᵢ`.  The
  commutation then descends to `R'` (`chartDerivRing`) and extends to `A'`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

/-! ### Commutators of scaled derivations -/

section Commutator

variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]

/-- `[f D₁, g D₂] = f (D₁ g) D₂ − g (D₂ f) D₁` for commuting derivations `D₁`, `D₂`.-/
theorem _root_.Derivation.commutator_smul_smul (D₁ D₂ : Derivation k B B) (h : ⁅D₁, D₂⁆ = 0)
    (f g : B) : ⁅f • D₁, g • D₂⁆ = (f * D₁ g) • D₂ - (g * D₂ f) • D₁ := by
  ext z
  have h' : D₁ (D₂ z) = D₂ (D₁ z) := by
    have := congrArg (fun D : Derivation k B B => D z) h
    simpa [Derivation.commutator_apply, sub_eq_zero] using this
  simp only [Derivation.commutator_apply, Derivation.smul_apply, Derivation.sub_apply,
    Derivation.leibniz, smul_eq_mul, h']
  ring

end Commutator

namespace RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n) (r : Fin n)

/-- The extended coordinate derivations `∂ᵢ`, `∂ⱼ` of `R[1/x_r]` commute.
@isnad1 id=eq.0h6v.s11.e9a83dc0fd05 from=translated src=- shape=7c5fbb9c vocab=c1a4f0aa
-/
theorem awayPderiv_commutator (i j : Fin n) : ⁅c.awayPderiv r i, c.awayPderiv r j⁆ = 0 := by
  ext z
  rw [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero]
  exact Derivation.localization_comm _ (c.pderiv i) (c.pderiv j) (c.pderiv_comm i j) z

/-! ### The coordinate structure on `R'_{𝔪'}` -/

section ChartCoords

end ChartCoords

end RegularCoords

end IsLocalRing
