module
public import Tengoku.Seed.Tactic.NoncommRing
public import Tengoku.Seed.Tactic.Ring
public import Tengoku.Stafford38Formal.Stafford38.ChallengeDefinitions
public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# The linear symplectic layer of the A₂ reduction

This file isolates the part of the generic-monic reduction which is purely
linear algebra.  A Weyl presentation is encoded by a finite family `z` whose
pairwise commutators are the entries of a fixed skew matrix.  A matrix `M`
preserving that form gives a new family by linear combination, and the new
family has exactly the same Weyl commutators.

The result is deliberately stated for an arbitrary finite index type and an
arbitrary symplectic form.  The A₂ instance is obtained with
`ι = Fin 2 ⊕ Fin 2` and `Matrix.J (Fin 2) k`, so this is not a list of
hand-picked coordinate changes.

This is the algebraic prerequisite for applying Stafford's
ring-equivalence transport to a Weyl change of generators.  The final section
also descends a form-preserving change to a homomorphism of the presented
quotient and proves the A₂ symplectic change is invertible using the inverse
matrix and generator-extensionality. The PBW identification and generic monic
normalization belong to the downstream Weyl modules, outside this module's
linear-algebra scope. Reusable commutator identities are imported from
AlgebraicAnalysis.
-/

namespace Stafford

variable {k A ι : Type*} [Field k] [Ring A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]

/-! ### The standard A₂ specialization -/

abbrev A2Index := Fin 2 ⊕ Fin 2

abbrev A2SymplecticForm (k : Type*) [CommRing k] :
    Matrix A2Index A2Index k := Matrix.J (Fin 2) k

/-! ### Descent to the presented Weyl algebra

`RingQuot` is Mathlib's universal quotient for a possibly noncommutative ring.
The following definitions use it to make the universal-property step
explicit.  This is still presentation-level algebra: identifying the
quotient with a PBW Weyl algebra remains separate, while the inverse-matrix
argument below proves the form-preserving A₂ map is an automorphism. -/

abbrev freeWeylLinearCombination
    (M : Matrix ι ι k) (z : ι → FreeWeyl k ι omega) (i : ι) :
    FreeWeyl k ι omega :=
  linearCombination M z i

def freeWeylMap (M : Matrix ι ι k) (omega : Matrix ι ι k) :
    FreeAlgebra k ι →ₐ[k] FreeWeyl k ι omega :=
  FreeAlgebra.lift k (fun i => freeWeylLinearCombination M
    (freeWeylGenerator omega) i)

lemma freeWeylLinearCombination_one
    (omega : Matrix ι ι k) (i : ι) :
    freeWeylLinearCombination (1 : Matrix ι ι k)
        (freeWeylGenerator omega) i = freeWeylGenerator omega i := by
  simp [freeWeylLinearCombination, linearCombination, Matrix.one_apply]

end Stafford
