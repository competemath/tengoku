/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveHyperplane

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Standard projective space is integral

Over a field, the standard graded polynomial ring is a domain, so its zero ideal is a relevant
homogeneous prime: a point of `ℙⁿ_k` lying in every nonempty open.  This proves irreducibility.
Every stalk embeds into the ordinary localization of the polynomial ring at a prime through
`Proj.stalkIso'` and `HomogeneousLocalization.val`, hence is a domain; reducedness follows
stalkwise, and `ℙⁿ_k` is an integral scheme.

Integrality is the ambient hypothesis of the transversality and locally-principal Serre--Tor
machinery, so this brick lets every divisor-pair theorem apply to standard projective space.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace SchemeProjectiveSpace

attribute [local instance] gradedAlgebra

variable (k : Type u) [CommRing k] [IsDomain k] (n : ℕ)

/-- The zero homogeneous ideal of the standard graded polynomial ring is a relevant prime: the
generic point of projective space.-/
noncomputable def genericProjPoint : space k n :=
  show ProjectiveSpectrum (grading k n) from
    { asHomogeneousIdeal := ⊥
      isPrime := by
        rw [HomogeneousIdeal.toIdeal_bot]
        exact Ideal.isPrime_bot
      not_irrelevant_le := by
        intro h
        have hmem := h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
          (coordinate_mem_degree_one k n 0))
        exact MvPolynomial.X_ne_zero (R := k) (0 : Fin (n + 1))
          (Ideal.mem_bot.mp hmem) }

@[simp]
theorem asHomogeneousIdeal_genericProjPoint :
    (show ProjectiveSpectrum (grading k n) from genericProjPoint k n).asHomogeneousIdeal =
      ⊥ :=
  rfl

end SchemeProjectiveSpace
