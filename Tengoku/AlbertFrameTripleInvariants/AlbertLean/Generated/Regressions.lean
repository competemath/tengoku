import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0ProductTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Deterministically generated convention-corruption definitions. -/
namespace AlbertLean

open Generated

def m01TensorProduct (x y : Coord) : Coord :=
  tensorProduct x y - (x 0 * y 11) • basisVec 11

def m02Product (x y : Coord) : Coord :=
  cross x y + traceN x • y + traceN y • x - spurBilinear x y • one

def m05ThetaMK : Coord := thetaMK + basisVec 0
def m05WitnessThetaM : WitnessTriple := ⟨thetaME, thetaMF, m05ThetaMK⟩

def m06W0 (X : WitnessTriple) : Coord :=
  structuredProduct X.cF (structuredProduct X.cE X.cK) -
    structuredProduct X.cE (structuredProduct X.cF X.cK)
def m06TraceCubeDetector (X : WitnessTriple) : ℚ :=
  traceForm (m06W0 X) (structuredProduct (m06W0 X) (m06W0 X))

def m07W0 (X : WitnessTriple) : Coord :=
  structuredProduct (structuredProduct X.cE X.cF) X.cK -
    structuredProduct X.cF (structuredProduct X.cE X.cK)
def m07TraceCubeDetector (X : WitnessTriple) : ℚ :=
  traceForm (m07W0 X) (structuredProduct (m07W0 X) (m07W0 X))

def m09LedgerTheta1 : Ledger :=
  let L := ledger witnessTheta1
  ⟨(fun i j => L.P j i), L.Q, L.R, L.C0⟩

def m04TTheta1E : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 1
  | 2 => q (1) 1
  | _ => 0

def m04TTheta1F : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-1) 1
  | 2 => q (4) 3
  | 3 => q (1) 1
  | 11 => q (1) 1
  | 15 => q (3) 2
  | 16 => q (-2) 1
  | 18 => q (3) 2
  | 21 => q (1) 1
  | 23 => q (-245) 54
  | 24 => q (-3) 2
  | 25 => q (-35) 18
  | _ => 0

def m04TTheta1K : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-1) 1
  | 2 => q (4) 3
  | 4 => q (1) 1
  | 12 => q (1) 1
  | 15 => q (-2) 1
  | 16 => q (1) 1
  | 17 => q (-2) 1
  | 18 => q (-91) 27
  | 22 => q (1) 1
  | 23 => q (-3) 2
  | 24 => q (1) 1
  | 25 => q (2) 1
  | 26 => q (-13) 9
  | _ => 0

def m04TTheta1 : WitnessTriple := ⟨m04TTheta1E, m04TTheta1F, m04TTheta1K⟩

def m04TThetaME : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 1
  | 2 => q (1) 1
  | _ => 0

def m04TThetaMF : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-1) 1
  | 2 => q (4) 3
  | 3 => q (1) 1
  | 11 => q (1) 1
  | 15 => q (3) 2
  | 16 => q (-2) 1
  | 18 => q (8748) 410231
  | 21 => q (1) 1
  | 23 => q (-245) 54
  | 24 => q (-3) 2
  | 25 => q (-35) 18
  | _ => 0

def m04TThetaMK : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-1) 1
  | 2 => q (4) 3
  | 4 => q (1) 1
  | 12 => q (1) 1
  | 15 => q (-2) 1
  | 16 => q (1) 1
  | 17 => q (-2) 1
  | 18 => q (-19656) 410231
  | 22 => q (1) 1
  | 23 => q (-3) 2
  | 24 => q (1) 1
  | 25 => q (2) 1
  | 26 => q (-8424) 410231
  | _ => 0

def m04TThetaM : WitnessTriple := ⟨m04TThetaME, m04TThetaMF, m04TThetaMK⟩

def m11ProductTrace (x : Coord) : ℚ := leftMulMatrixTrace x / 8

end AlbertLean
