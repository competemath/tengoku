import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Compact.Definitions
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Compact.DualDictionary
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Solution
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dictionary between the compact and original coordinate surfaces

Every lemma here compares a compact definition directly with the independently
completed coordinate statement.  The witness conversions retain the literal
order E, F, K.
-/

noncomputable section
namespace CompactOneBit

open scoped BigOperators

theorem unit_eq : unit = AlbertLean.one := by
  funext i
  fin_cases i <;> simp [unit, AlbertLean.one, AlbertLean.q]

theorem cubic_eq (x : Coord) : cubic x = AlbertLean.cubicNorm x := by
  simp [cubic, AlbertLean.cubicNorm, AlbertLean.v, AlbertLean.q]
  ring

theorem polar_eq (x y z : Coord) :
    polar x y z = AlbertLean.cubicPolar x y z := by
  simp only [polar, AlbertLean.cubicPolar, cubic_eq]

theorem trace_eq (x : Coord) : trace x = AlbertLean.traceN x := by
  simp [trace, AlbertLean.traceN, polar_eq, unit_eq]

theorem spur_eq (x : Coord) : spur x = AlbertLean.spurN x := by
  simp [spur, AlbertLean.spurN, polar_eq, unit_eq]

theorem pairing_eq (x y : Coord) :
    pairing x y = AlbertLean.traceForm x y := by
  simp [pairing, AlbertLean.traceForm, AlbertLean.spurBilinear,
    trace_eq, polar_eq, unit_eq]

theorem single_eq_basisVec (i : Fin 27) :
    Pi.single i (1 : ℚ) = AlbertLean.basisVec i := by
  funext j
  simp [Pi.single_apply, AlbertLean.basisVec, eq_comm]

theorem adjoint_eq (x : Coord) : adjoint x = AlbertLean.sharp x := by
  rw [adjoint, dual_eq_oldDual]
  funext k
  simp only [oldDual, AlbertLean.sharp, polar_eq, single_eq_basisVec]

theorem product_eq (x y : Coord) :
    product x y = AlbertLean.structuredProduct x y := by
  simp [product, AlbertLean.structuredProduct, AlbertLean.cross, adjoint_eq,
    trace_eq, polar_eq, unit_eq, AlbertLean.spurBilinear]

theorem operatorTrace_eq (x : Coord) :
    operatorTrace x = AlbertLean.productTrace x := by
  simp [operatorTrace, AlbertLean.productTrace, AlbertLean.leftMulMatrixTrace,
    product_eq, single_eq_basisVec]

theorem operatorSpur_eq (x : Coord) :
    operatorSpur x = AlbertLean.productSpur x := by
  simp [operatorSpur, AlbertLean.productSpur, operatorTrace_eq, product_eq]

theorem operatorNorm_eq (x : Coord) :
    operatorNorm x = AlbertLean.productNorm x := by
  simp [operatorNorm, AlbertLean.productNorm, operatorTrace_eq, product_eq]

def oldTriple (X : Triple) : AlbertLean.WitnessTriple :=
  ⟨X 0, X 1, X 2⟩

def newTriple (X : AlbertLean.WitnessTriple) : Triple :=
  ![X.cE, X.cF, X.cK]

theorem newTriple_oldTriple (X : Triple) : newTriple (oldTriple X) = X := by
  funext r
  fin_cases r <;> rfl

theorem oldTriple_newTriple (X : AlbertLean.WitnessTriple) :
    oldTriple (newTriple X) = X := by
  rcases X with ⟨E, F, K⟩
  rfl

theorem projector_eq (x : Coord) :
    projector x = AlbertLean.projector x := by
  unfold projector AlbertLean.projector
  rw [show product x x = AlbertLean.structuredProduct x x from product_eq x x,
    unit_eq]
  funext i
  fin_cases i <;> rfl

theorem frame_eq (x : Coord) : Frame x ↔ AlbertLean.LawfulFrame x := by
  simp only [Frame, AlbertLean.LawfulFrame, AlbertLean.LawfulEncoder,
    trace_eq, spur_eq, cubic_eq, projector_eq, product_eq, unit_eq]
  tauto

theorem encoder_oldTriple (X : Triple) (r : Fin 3) :
    AlbertLean.encoder (oldTriple X) r = X r := by
  fin_cases r <;> rfl

theorem pairs_eq (X : Triple) :
    pairs X 0 = (AlbertLean.ledger (oldTriple X)).P ∧
    pairs X 1 = (AlbertLean.ledger (oldTriple X)).Q ∧
    pairs X 2 = (AlbertLean.ledger (oldTriple X)).R := by
  constructor
  · funext i j
    simp [pairs, AlbertLean.ledger, oldTriple, pairing_eq, projector_eq]
  constructor
  · funext i j
    simp [pairs, AlbertLean.ledger, oldTriple, pairing_eq, projector_eq]
  · funext i j
    simp [pairs, AlbertLean.ledger, oldTriple, pairing_eq, projector_eq]

theorem centered_eq (X : Triple) :
    centered X = (AlbertLean.ledger (oldTriple X)).C0 := by
  funext i j k
  simp only [centered]
  rw [congrFun (congrFun (pairs_eq X).1 i) j,
    congrFun (congrFun (pairs_eq X).2.1 j) k,
    congrFun (congrFun (pairs_eq X).2.2 k) i]
  simp [AlbertLean.ledger, oldTriple, pairing_eq, projector_eq,
    product_eq]

theorem word_eq (X : Triple) :
    word X = AlbertLean.W0 (oldTriple X) := by
  simp [word, AlbertLean.W0, oldTriple, product_eq]

theorem detector_eq (X : Triple) :
    detector X = AlbertLean.traceCubeDetector (oldTriple X) := by
  simp [detector, AlbertLean.traceCubeDetector, word_eq, pairing_eq, product_eq]

theorem E_eq : E = AlbertLean.theta1E := by
  funext i
  fin_cases i <;> norm_num [E, AlbertLean.theta1E, AlbertLean.q]

theorem F_eq : F = AlbertLean.theta1F := by
  funext i
  fin_cases i <;> norm_num [F, AlbertLean.theta1F, AlbertLean.q]

theorem K_eq : K = AlbertLean.theta1K := by
  funext i
  fin_cases i <;> norm_num [K, AlbertLean.theta1K, AlbertLean.q]

theorem F'_eq : F' = AlbertLean.thetaMF := by
  funext i
  fin_cases i <;>
    simp [F', F, AlbertLean.thetaMF, AlbertLean.q, Function.update,
      Fin.ext_iff] <;> norm_num

theorem K'_eq : K' = AlbertLean.thetaMK := by
  funext i
  fin_cases i <;>
    simp [K', K, AlbertLean.thetaMK, AlbertLean.q, Function.update,
      Fin.ext_iff] <;> norm_num

theorem E_eq_thetaME : E = AlbertLean.thetaME := by
  funext i
  fin_cases i <;> norm_num [E, AlbertLean.thetaME, AlbertLean.q]

theorem oldTriple_first : oldTriple first = AlbertLean.witnessTheta1 := by
  simp [oldTriple, first, AlbertLean.witnessTheta1, E_eq, F_eq, K_eq]

theorem oldTriple_second : oldTriple second = AlbertLean.witnessThetaM := by
  simp [oldTriple, second, AlbertLean.witnessThetaM, E_eq_thetaME, F'_eq, K'_eq]

end CompactOneBit
