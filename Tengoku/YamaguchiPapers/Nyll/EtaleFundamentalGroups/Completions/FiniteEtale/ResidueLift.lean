/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Polynomial.Lifts
import Tengoku.Seed.FieldTheory.PrimitiveElement
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Instances
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ResidueClassification
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.FormallyEtale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifting a finite separable residue extension

Let `R` be a local ring and let `l / κ(R)` be finite separable.  We choose a
power-basis generator of `l`, lift its minimal polynomial coefficientwise to a
monic polynomial over `R`, and adjoin a root.  The resulting algebra is local,
finite, and étale over `R`, and its residue extension is `l / κ(R)`.

The local structure is not registered globally.  It is produced from the
explicit special fibre: quotienting the adjoined-root algebra by the extended
maximal ideal gives the adjoined root of the residue minimal polynomial, hence
a field.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial

universe u

variable (R l : Type u) [CommRing R] [IsLocalRing R]
  [Field l] [Algebra (IsLocalRing.ResidueField R) l]
  [FiniteDimensional (IsLocalRing.ResidueField R) l]
  [Algebra.IsSeparable (IsLocalRing.ResidueField R) l]

/-- A chosen power basis for a finite separable residue extension.-/
noncomputable def finiteEtaleResidueLiftPowerBasis :
    PowerBasis (IsLocalRing.ResidueField R) l :=
  Field.powerBasisOfFiniteOfSeparable _ _

private theorem exists_monic_residue_polynomial_lift :
    ∃ f : R[X],
      f.map (IsLocalRing.residue R) =
          minpoly (IsLocalRing.ResidueField R)
            (finiteEtaleResidueLiftPowerBasis R l).gen ∧
        f.natDegree =
          (minpoly (IsLocalRing.ResidueField R)
            (finiteEtaleResidueLiftPowerBasis R l).gen).natDegree ∧
        f.Monic := by
  let p := minpoly (IsLocalRing.ResidueField R)
    (finiteEtaleResidueLiftPowerBasis R l).gen
  have hp : p.Monic :=
    minpoly.monic (finiteEtaleResidueLiftPowerBasis R l).isIntegral_gen
  apply Polynomial.lifts_and_natDegree_eq_and_monic
  · rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ IsLocalRing.residue_surjective p
  · exact hp

/-- A monic lift of the minimal polynomial of a chosen residue generator.-/
noncomputable def finiteEtaleResidueLiftPolynomial : R[X] :=
  Classical.choose (exists_monic_residue_polynomial_lift R l)

theorem finiteEtaleResidueLiftPolynomial_map :
    (finiteEtaleResidueLiftPolynomial R l).map (IsLocalRing.residue R) =
      minpoly (IsLocalRing.ResidueField R)
        (finiteEtaleResidueLiftPowerBasis R l).gen :=
  (Classical.choose_spec (exists_monic_residue_polynomial_lift R l)).1

theorem finiteEtaleResidueLiftPolynomial_natDegree :
    (finiteEtaleResidueLiftPolynomial R l).natDegree =
      (minpoly (IsLocalRing.ResidueField R)
        (finiteEtaleResidueLiftPowerBasis R l).gen).natDegree :=
  (Classical.choose_spec (exists_monic_residue_polynomial_lift R l)).2.1

theorem finiteEtaleResidueLiftPolynomial_monic :
    (finiteEtaleResidueLiftPolynomial R l).Monic :=
  (Classical.choose_spec (exists_monic_residue_polynomial_lift R l)).2.2

/-- The explicit local lift of a finite separable residue extension.-/
abbrev FiniteEtaleResidueLift :=
  AdjoinRoot (finiteEtaleResidueLiftPolynomial R l)

/-- The extended closed-point ideal in the explicit residue lift.-/
def finiteEtaleResidueLiftClosedIdeal :
    Ideal (FiniteEtaleResidueLift R l) :=
  (IsLocalRing.maximalIdeal R).map
    (AdjoinRoot.of (finiteEtaleResidueLiftPolynomial R l))

/-- The special fibre of the explicit lift is the adjoined-root presentation
of the given residue extension.-/
noncomputable def finiteEtaleResidueLiftSpecialFiberRingEquiv :
    FiniteEtaleResidueLift R l ⧸ finiteEtaleResidueLiftClosedIdeal R l ≃+*
      AdjoinRoot
        ((finiteEtaleResidueLiftPolynomial R l).map
          (IsLocalRing.residue R)) :=
  AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
    (IsLocalRing.maximalIdeal R)
    (finiteEtaleResidueLiftPolynomial R l)

@[simp]
theorem finiteEtaleResidueLiftSpecialFiberRingEquiv_mk (g : R[X]) :
    finiteEtaleResidueLiftSpecialFiberRingEquiv R l
        (Ideal.Quotient.mk (finiteEtaleResidueLiftClosedIdeal R l)
          (AdjoinRoot.mk (finiteEtaleResidueLiftPolynomial R l) g)) =
      AdjoinRoot.mk
        ((finiteEtaleResidueLiftPolynomial R l).map
          (IsLocalRing.residue R))
        (g.map (IsLocalRing.residue R)) :=
  AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of
    (IsLocalRing.maximalIdeal R)
    (finiteEtaleResidueLiftPolynomial R l) g

/-- The extended closed point in the explicit lift is maximal.-/
theorem finiteEtaleResidueLiftClosedIdeal_isMaximal :
    (finiteEtaleResidueLiftClosedIdeal R l).IsMaximal := by
  let q := (finiteEtaleResidueLiftPolynomial R l).map
    (IsLocalRing.residue R)
  let : Fact (Irreducible q) := ⟨by
    change Irreducible
      ((finiteEtaleResidueLiftPolynomial R l).map
        (IsLocalRing.residue R))
    rw [finiteEtaleResidueLiftPolynomial_map]
    exact minpoly.irreducible
      (finiteEtaleResidueLiftPowerBasis R l).isIntegral_gen⟩
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact
    (finiteEtaleResidueLiftSpecialFiberRingEquiv R l).toMulEquiv.isField
      (Field.toIsField (AdjoinRoot q))

/-- The maximal ideal of the explicit lift is the extended base maximal ideal.-/
theorem maximalIdeal_finiteEtaleResidueLift
    [IsLocalRing (FiniteEtaleResidueLift R l)] :
    IsLocalRing.maximalIdeal (FiniteEtaleResidueLift R l) =
      finiteEtaleResidueLiftClosedIdeal R l :=
  (IsLocalRing.eq_maximalIdeal
    (finiteEtaleResidueLiftClosedIdeal_isMaximal R l)).symm

/-- The explicit residue lift is finite as a module.-/
theorem moduleFinite_finiteEtaleResidueLift :
    Module.Finite R (FiniteEtaleResidueLift R l) :=
  (finiteEtaleResidueLiftPolynomial_monic R l).finite_adjoinRoot

end EtaleFundamentalGroups

end
