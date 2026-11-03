import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualAction
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairDephase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms recoveryAutToSourceAut` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceAutComp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenSourceAut` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenSourceAut_apply_v` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenSourceAut_apply_diagonal` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Triality.SourceVectorPairDephase

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint StructuredProduct
open SourceEvenReflections SourceEvenAutomorphism
open AlbertLean.Generic

universe u
variable {K : Type u} [Field K] [CharZero K]

def recoveryAutToSourceAut
    (g : CubicAutomorphism.RecoveryPresentation.Aut
      (StructuredAdjoint.sourceRecoveryData (K := K))) :
    ResidualAction.SourceAut (K := K) where
  linear := g.linear
  map_one := g.map_one
  map_product := g.map_product

def sourceAutComp (g2 g1 : ResidualAction.SourceAut (K := K)) :
    ResidualAction.SourceAut (K := K) where
  linear := g1.linear.trans g2.linear
  map_one := by
    change g2.linear (g1.linear sourceOne) = sourceOne
    rw [g1.map_one, g2.map_one]
  map_product x y := by
    change g2.linear (g1.linear (sourceProduct x y)) = _
    rw [g1.map_product, g2.map_product] <;> rfl

def evenSourceAut (A B : VCoord K) (rho : K)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0)
    (hrho : rho ^ 2 = nV A * nV B) (hrho0 : rho ≠ 0) :
    ResidualAction.SourceAut (K := K) :=
  recoveryAutToSourceAut (sourceEvenAut A B rho hA hB hrho hrho0)

@[simp] theorem evenSourceAut_apply_v (A B : VCoord K) (rho : K)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0)
    (hrho : rho ^ 2 = nV A * nV B) (hrho0 : rho ≠ 0) (x : JCoord K) :
    ((evenSourceAut A B rho hA hB hrho hrho0).linear x).v = evenV A B x.v := rfl

@[simp] theorem evenSourceAut_apply_diagonal (A B : VCoord K) (rho : K)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0)
    (hrho : rho ^ 2 = nV A * nV B) (hrho0 : rho ≠ 0) (x : JCoord K) :
    (((evenSourceAut A B rho hA hB hrho hrho0).linear x).d1,
      ((evenSourceAut A B rho hA hB hrho hrho0).linear x).d2,
      ((evenSourceAut A B rho hA hB hrho hrho0).linear x).d3) =
      (x.d1, x.d2, x.d3) := rfl

end AlbertLean.Triality.SourceVectorPairDephase
