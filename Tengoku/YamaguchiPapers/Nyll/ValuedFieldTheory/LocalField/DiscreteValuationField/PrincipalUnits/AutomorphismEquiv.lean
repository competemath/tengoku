/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport
import Tengoku.Seed.Algebra.Group.Subgroup.Map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Automorphisms of the concrete principal-unit groups

A field automorphism preserving the valuation ring restricts to every level
of the principal-unit filtration, with its original action on field elements.
-/

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

universe u v

variable {K : Type u} [Field K]
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- Restriction of a valuation-ring-preserving automorphism to `U^n`.-/
noncomputable def equivOfPreserves
    (e : K ≃+* K)
    (hmem : ∀ x : K, x ∈ F.valuation.valuationSubring ↔ e x ∈ F.valuation.valuationSubring)
    (n : ℕ) : higherPrincipalUnitGroup F n ≃* higherPrincipalUnitGroup F n :=
  ((valuationSubringUnitEquivOfPreserves F e hmem).subgroupMap
    (higherPrincipalUnitGroup F n)).trans
      (MulEquiv.subgroupCongr
        (higherPrincipalUnitGroup_map_valuationSubringUnitEquivOfPreserves F e hmem n))

/-- The restricted automorphism retains the original action on field elements.
@isnad1 id=eq.1h5v.s13.26079ac43322 from=translated src=- shape=36e7a243 vocab=70c33a93
-/
@[simp] theorem equivOfPreserves_apply_coe
    (e : K ≃+* K)
    (hmem : ∀ x : K, x ∈ F.valuation.valuationSubring ↔ e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (a : higherPrincipalUnitGroup F n) :
    (((equivOfPreserves F e hmem n a : F.valuationSubringˣ) : F.valuationSubring) : K) =
      e (((a : F.valuationSubringˣ) : F.valuationSubring) : K) := by
  change (((valuationSubringUnitEquivOfPreserves F e hmem
    (a : F.valuationSubringˣ) : F.valuationSubringˣ) : F.valuationSubring) : K) =
      e (((a : F.valuationSubringˣ) : F.valuationSubring) : K)
  rw [valuationSubringUnitEquivOfPreserves_apply]
  rfl

/-- Restriction preserves the identity automorphism.
@isnad1 id=eq.0h3v.s11.00f7a7682a7d from=translated src=- shape=4fdd61fa vocab=6b47a074
-/
@[simp] theorem equivOfPreserves_refl (n : ℕ) :
    equivOfPreserves F (RingEquiv.refl K) (fun _ => Iff.rfl) n =
      MulEquiv.refl (higherPrincipalUnitGroup F n) := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact equivOfPreserves_apply_coe F (RingEquiv.refl K) (fun _ => Iff.rfl) n a

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
