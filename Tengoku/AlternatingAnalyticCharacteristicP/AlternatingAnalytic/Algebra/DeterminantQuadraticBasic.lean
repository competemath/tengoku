import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.Algebra.Polynomial.RingDivision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Determinant generators over an arbitrary field

Polynomial models, over any field `K`, of the spaces `G_0` and `C_0` from the
section "A missing coefficient" of Appendix H, and of the Toeplitz minors used in
the proof of Lemma H.7. The definitions of the same names in
`Analysis/DeterminantCoefficientSpecialization.lean` are these at a specific field.
-/

noncomputable section
open scoped BigOperators

namespace AlternatingAnalytic.DeterminantQuadratic

variable (K : Type*) [Field K] (p : ℕ)

abbrev Poly := MvPolynomial (Fin p) K
abbrev GeneratorIndex := Fin p ⊕ (Fin p ⊕ Unit)

def genPoly : GeneratorIndex p → Fin p → Poly K p
  | Sum.inl i => fun k => if i = k then 1 else 0
  | Sum.inr (Sum.inl i) => fun k =>
      ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (k : ℕ) then MvPolynomial.X j else 0
  | Sum.inr (Sum.inr _) => fun k =>
      ∑ i : Fin p, ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (k : ℕ)
        then MvPolynomial.X i * MvPolynomial.X j else 0

def detPoly (s : Fin p → GeneratorIndex p) : Poly K p :=
  Matrix.det (Matrix.of (fun i j => genPoly K p (s j) i))

def G0poly : Submodule K (Poly K p) :=
  Submodule.span K (Set.range (detPoly K p))

def C0poly : Submodule K (Poly K p) :=
  G0poly K p ⊓ ⨅ i : Fin p,
    (G0poly K p).comap (LinearMap.mulLeft K (MvPolynomial.X i))

/--
@isnad1 id=iff.0h3v.s9.f0d7da7e1dd3 from=translated src=- shape=fc1ff67d vocab=8e7d3222
-/
@[simp] theorem mem_C0poly {P : Poly K p} :
    P ∈ C0poly K p ↔ P ∈ G0poly K p ∧
      ∀ i : Fin p, MvPolynomial.X i * P ∈ G0poly K p := by
  simp [C0poly]

def generatorDegree : GeneratorIndex p → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

/-- The lower triangular Toeplitz matrix of multiplication by `a`.-/
def toeplitz (r i : Fin p) : Poly K p :=
  if h : i.val ≤ r.val then MvPolynomial.X ⟨r.val - i.val, by omega⟩ else 0

def minor (r s i j : Fin p) : Poly K p :=
  toeplitz K p r i * toeplitz K p s j - toeplitz K p r j * toeplitz K p s i

def squareCoordinate (r : Fin p) : Poly K p :=
  ∑ i : Fin p, ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (r : ℕ)
    then MvPolynomial.X i * MvPolynomial.X j else 0

def quadraticSpan : Submodule K (Poly K p) :=
  Submodule.span K
    ({P | ∃ r s i j : Fin p, P = minor K p r s i j} ∪ Set.range (squareCoordinate K p))

end AlternatingAnalytic.DeterminantQuadratic
