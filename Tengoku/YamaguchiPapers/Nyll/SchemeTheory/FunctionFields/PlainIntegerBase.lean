/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.AlgebraicGeometry.FunctionField
import Tengoku.Seed.AlgebraicGeometry.ResidueField
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The generic residue field of the ordinary integer spectrum -/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The generic residue field of the ordinary spectrum of the integers is
canonically isomorphic to the rationals.-/
noncomputable def specZGenericResidueFieldEquivQ :
    (Spec (CommRingCat.of ℤ)).residueField
      (genericPoint (Spec (CommRingCat.of ℤ))) ≃+* ℚ := by
  let X := Spec (CommRingCat.of ℤ)
  let x : PrimeSpectrum ℤ := genericPoint X
  let e : X.residueField x ≃+* x.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso (CommRingCat.of ℤ) x).commRingCatIsoToRingEquiv
  let : Algebra ℤ (X.residueField x) :=
    (e.symm.toRingHom.comp (algebraMap ℤ x.asIdeal.ResidueField)).toAlgebra
  let eAlg : X.residueField x ≃ₐ[ℤ] x.asIdeal.ResidueField :=
    AlgEquiv.ofRingEquiv (f := e) (by
      intro z
      rw [RingHom.algebraMap_toAlgebra]
      exact e.apply_symm_apply _)
  have hx : x = (⊥ : PrimeSpectrum ℤ) := genericPoint_eq_bot_of_affine (CommRingCat.of ℤ)
  let : IsFractionRing ℤ x.asIdeal.ResidueField := by
    rw [hx]
    change IsFractionRing ℤ ((⊥ : Ideal ℤ).ResidueField)
    infer_instance
  let : IsFractionRing ℤ (X.residueField x) := IsFractionRing.of_algEquiv eAlg.symm
  exact IsFractionRing.ringEquivOfRingEquiv
    (K := X.residueField x) (L := ℚ) (RingEquiv.refl ℤ)

end AlgebraicGeometry
