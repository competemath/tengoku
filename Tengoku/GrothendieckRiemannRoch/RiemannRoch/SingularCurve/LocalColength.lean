/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.LinearAlgebra.FreeModule.Finite.Quotient
import Tengoku.Seed.LinearAlgebra.Determinant
import Tengoku.Seed.RingTheory.OrderOfVanishing.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local colength and determinant order

For a full-rank submodule over a principal ideal domain, Smith normal form identifies the
length of the quotient with the order of the determinant of the inclusion.  This is the local
algebra input needed to compare common-lattice quotient lengths with determinant divisors.
-/

noncomputable section

open Module

universe u

namespace Submodule

variable {R M ι : Type u} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι]

/-- In Smith bases, the determinant of the inclusion is the product of the Smith
coefficients.
@isnad1 id=eq.1h5v.s9.88beb7176159 from=translated src=- shape=c7206877 vocab=c4c46c0f
-/
theorem det_smithNormalFormBotBasis_eq_prod_smithCoeffs
    (N : Submodule R M) (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    (N.smithNormalFormTopBasis b h).det
        (fun i ↦ (N.smithNormalFormBotBasis b h i : M)) =
      ∏ i, N.smithNormalFormCoeffs b h i := by
  simp_rw [N.smithNormalFormBotBasis_def b h]
  rw [AlternatingMap.map_smul_univ]
  rw [Basis.det_self, smul_eq_mul, mul_one]

/-- The inclusion determinant computed in arbitrary source and target bases is associated to
the determinant computed in the canonical Smith bases.
@isnad1 id=associat.1h6v.s9.601b012bdce0 from=translated src=- shape=7fffa19c vocab=624b8e60
-/
theorem associated_det_basis_with_det_smithNormalForm
    (N : Submodule R M) (bM : Basis ι R M) (bN : Basis ι R N)
    (h : Module.finrank R N = Module.finrank R M) :
    Associated (bM.det (fun i ↦ (bN i : M)))
      ((N.smithNormalFormTopBasis bM h).det
        (fun i ↦ (N.smithNormalFormBotBasis bM h i : M))) := by
  change Associated (bM.det (N.subtype ∘ bN))
    ((N.smithNormalFormTopBasis bM h).det
      (N.subtype ∘ N.smithNormalFormBotBasis bM h))
  rw [bN.det_comp_basis bM N.subtype]
  rw [(N.smithNormalFormBotBasis bM h).det_comp_basis
    (N.smithNormalFormTopBasis bM h) N.subtype]
  exact LinearMap.associated_det_comp_equiv N.subtype
    (bM.equiv bN (Equiv.refl ι))
    ((N.smithNormalFormTopBasis bM h).equiv
      (N.smithNormalFormBotBasis bM h) (Equiv.refl ι))

end Submodule
