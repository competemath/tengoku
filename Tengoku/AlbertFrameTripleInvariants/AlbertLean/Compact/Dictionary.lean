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

/--
@isnad1 id=eq.0h0v.s2.fa61ca9c05f1 from=translated src=- shape=54c8eceb vocab=9f578fad
-/
theorem unit_eq : unit = AlbertLean.one := by
  funext i
  fin_cases i <;> simp [unit, AlbertLean.one, AlbertLean.q]

/--
@isnad1 id=eq.0h1v.s3.5159740578d6 from=translated src=- shape=b70c6bb1 vocab=e66e76c4
-/
theorem cubic_eq (x : Coord) : cubic x = AlbertLean.cubicNorm x := by
  simp [cubic, AlbertLean.cubicNorm, AlbertLean.v, AlbertLean.q]
  ring

/--
@isnad1 id=eq.0h3v.s4.a5b58db2c590 from=translated src=- shape=ea9ef4de vocab=5d008b2c
-/
theorem polar_eq (x y z : Coord) :
    polar x y z = AlbertLean.cubicPolar x y z := by
  simp only [polar, AlbertLean.cubicPolar, cubic_eq]

/--
@isnad1 id=eq.0h1v.s3.3cf5c390fd54 from=translated src=- shape=b70c6bb1 vocab=588bf042
-/
theorem trace_eq (x : Coord) : trace x = AlbertLean.traceN x := by
  simp [trace, AlbertLean.traceN, polar_eq, unit_eq]

/--
@isnad1 id=eq.0h1v.s3.0446be308583 from=translated src=- shape=b70c6bb1 vocab=3d6e1d86
-/
theorem spur_eq (x : Coord) : spur x = AlbertLean.spurN x := by
  simp [spur, AlbertLean.spurN, polar_eq, unit_eq]

/--
@isnad1 id=eq.0h2v.s3.a6eff09b5fde from=translated src=- shape=e4af5fdd vocab=658df250
-/
theorem pairing_eq (x y : Coord) :
    pairing x y = AlbertLean.traceForm x y := by
  simp [pairing, AlbertLean.traceForm, AlbertLean.spurBilinear,
    trace_eq, polar_eq, unit_eq]

/--
@isnad1 id=eq.0h1v.s5.c2406e95badc from=translated src=- shape=e72a3f4b vocab=cc35a7d4
-/
theorem single_eq_basisVec (i : Fin 27) :
    Pi.single i (1 : ℚ) = AlbertLean.basisVec i := by
  funext j
  simp [Pi.single_apply, AlbertLean.basisVec, eq_comm]

/--
@isnad1 id=eq.0h1v.s3.e5b906b78c03 from=translated src=- shape=0fc427d2 vocab=9a688e8e
-/
theorem adjoint_eq (x : Coord) : adjoint x = AlbertLean.sharp x := by
  rw [adjoint, dual_eq_oldDual]
  funext k
  simp only [oldDual, AlbertLean.sharp, polar_eq, single_eq_basisVec]

/--
@isnad1 id=eq.0h2v.s3.42df8ba9c9e9 from=translated src=- shape=6c8684e5 vocab=b107076c
-/
theorem product_eq (x y : Coord) :
    product x y = AlbertLean.structuredProduct x y := by
  simp [product, AlbertLean.structuredProduct, AlbertLean.cross, adjoint_eq,
    trace_eq, polar_eq, unit_eq, AlbertLean.spurBilinear]

/--
@isnad1 id=eq.0h1v.s3.4a3091be1dc0 from=translated src=- shape=b70c6bb1 vocab=78d7156b
-/
theorem operatorTrace_eq (x : Coord) :
    operatorTrace x = AlbertLean.productTrace x := by
  simp [operatorTrace, AlbertLean.productTrace, AlbertLean.leftMulMatrixTrace,
    product_eq, single_eq_basisVec]

/--
@isnad1 id=eq.0h1v.s3.f64176e35b1b from=translated src=- shape=b70c6bb1 vocab=94afb83a
-/
theorem operatorSpur_eq (x : Coord) :
    operatorSpur x = AlbertLean.productSpur x := by
  simp [operatorSpur, AlbertLean.productSpur, operatorTrace_eq, product_eq]

/--
@isnad1 id=eq.0h1v.s3.9acf5233ea24 from=translated src=- shape=b70c6bb1 vocab=f1cdd583
-/
theorem operatorNorm_eq (x : Coord) :
    operatorNorm x = AlbertLean.productNorm x := by
  simp [operatorNorm, AlbertLean.productNorm, operatorTrace_eq, product_eq]

def oldTriple (X : Triple) : AlbertLean.WitnessTriple :=
  ⟨X 0, X 1, X 2⟩

def newTriple (X : AlbertLean.WitnessTriple) : Triple :=
  ![X.cE, X.cF, X.cK]

/--
@isnad1 id=eq.0h1v.s3.57f7a097f699 from=translated src=- shape=47dcad53 vocab=44e309f9
-/
theorem newTriple_oldTriple (X : Triple) : newTriple (oldTriple X) = X := by
  funext r
  fin_cases r <;> rfl

/--
@isnad1 id=eq.0h1v.s3.7140e088de70 from=translated src=- shape=47dcad53 vocab=04409eb1
-/
theorem oldTriple_newTriple (X : AlbertLean.WitnessTriple) :
    oldTriple (newTriple X) = X := by
  rcases X with ⟨E, F, K⟩
  rfl

/--
@isnad1 id=eq.0h1v.s3.2479e16ca743 from=translated src=- shape=9a282f00 vocab=8e3ed88e
-/
theorem projector_eq (x : Coord) :
    projector x = AlbertLean.projector x := by
  unfold projector AlbertLean.projector
  rw [show product x x = AlbertLean.structuredProduct x x from product_eq x x,
    unit_eq]
  funext i
  fin_cases i <;> rfl

/--
@isnad1 id=iff.0h1v.s2.000b25abd8d4 from=translated src=- shape=fc2c1e2b vocab=e6b62e44
-/
theorem frame_eq (x : Coord) : Frame x ↔ AlbertLean.LawfulFrame x := by
  simp only [Frame, AlbertLean.LawfulFrame, AlbertLean.LawfulEncoder,
    trace_eq, spur_eq, cubic_eq, projector_eq, product_eq, unit_eq]
  tauto

/--
@isnad1 id=eq.0h2v.s4.e539fac21f66 from=translated src=- shape=8117a265 vocab=15d0481a
-/
theorem encoder_oldTriple (X : Triple) (r : Fin 3) :
    AlbertLean.encoder (oldTriple X) r = X r := by
  fin_cases r <;> rfl

/--
@isnad1 id=and.0h1v.s6.6b699488ddaa from=translated src=- shape=0783bcf4 vocab=990f1d37
-/
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

/--
@isnad1 id=eq.0h1v.s4.aeb4c378d973 from=translated src=- shape=b79f85b7 vocab=1694031a
-/
theorem centered_eq (X : Triple) :
    centered X = (AlbertLean.ledger (oldTriple X)).C0 := by
  funext i j k
  simp only [centered]
  rw [congrFun (congrFun (pairs_eq X).1 i) j,
    congrFun (congrFun (pairs_eq X).2.1 j) k,
    congrFun (congrFun (pairs_eq X).2.2 k) i]
  simp [AlbertLean.ledger, oldTriple, pairing_eq, projector_eq,
    product_eq]

/--
@isnad1 id=eq.0h1v.s3.d6b952fdcf44 from=translated src=- shape=69b989be vocab=bf7964fd
-/
theorem word_eq (X : Triple) :
    word X = AlbertLean.W0 (oldTriple X) := by
  simp [word, AlbertLean.W0, oldTriple, product_eq]

/--
@isnad1 id=eq.0h1v.s3.82fed89e1aff from=translated src=- shape=69b989be vocab=388edbeb
-/
theorem detector_eq (X : Triple) :
    detector X = AlbertLean.traceCubeDetector (oldTriple X) := by
  simp [detector, AlbertLean.traceCubeDetector, word_eq, pairing_eq, product_eq]

/--
@isnad1 id=eq.0h0v.s2.612e92d87588 from=translated src=- shape=54c8eceb vocab=6189cf95
-/
theorem E_eq : E = AlbertLean.theta1E := by
  funext i
  fin_cases i <;> norm_num [E, AlbertLean.theta1E, AlbertLean.q]

/--
@isnad1 id=eq.0h0v.s2.f796fa88bf05 from=translated src=- shape=54c8eceb vocab=09d86ee9
-/
theorem F_eq : F = AlbertLean.theta1F := by
  funext i
  fin_cases i <;> norm_num [F, AlbertLean.theta1F, AlbertLean.q]

/--
@isnad1 id=eq.0h0v.s2.af9a3cc52032 from=translated src=- shape=54c8eceb vocab=6ab53b07
-/
theorem K_eq : K = AlbertLean.theta1K := by
  funext i
  fin_cases i <;> norm_num [K, AlbertLean.theta1K, AlbertLean.q]

/--
@isnad1 id=eq.0h0v.s2.50664af290be from=translated src=- shape=54c8eceb vocab=2fd0bc09
-/
theorem F'_eq : F' = AlbertLean.thetaMF := by
  funext i
  fin_cases i <;>
    simp [F', F, AlbertLean.thetaMF, AlbertLean.q, Function.update,
      Fin.ext_iff] <;> norm_num

/--
@isnad1 id=eq.0h0v.s2.d6555591fcb8 from=translated src=- shape=54c8eceb vocab=58f66149
-/
theorem K'_eq : K' = AlbertLean.thetaMK := by
  funext i
  fin_cases i <;>
    simp [K', K, AlbertLean.thetaMK, AlbertLean.q, Function.update,
      Fin.ext_iff] <;> norm_num

/--
@isnad1 id=eq.0h0v.s2.ed3f4aa0480e from=translated src=- shape=54c8eceb vocab=96db0211
-/
theorem E_eq_thetaME : E = AlbertLean.thetaME := by
  funext i
  fin_cases i <;> norm_num [E, AlbertLean.thetaME, AlbertLean.q]

/--
@isnad1 id=eq.0h0v.s2.dd6d455cf4b8 from=translated src=- shape=4b736592 vocab=f9235fb7
-/
theorem oldTriple_first : oldTriple first = AlbertLean.witnessTheta1 := by
  simp [oldTriple, first, AlbertLean.witnessTheta1, E_eq, F_eq, K_eq]

/--
@isnad1 id=eq.0h0v.s2.a5dab06c85ff from=translated src=- shape=4b736592 vocab=30efc61a
-/
theorem oldTriple_second : oldTriple second = AlbertLean.witnessThetaM := by
  simp [oldTriple, second, AlbertLean.witnessThetaM, E_eq_thetaME, F'_eq, K'_eq]

end CompactOneBit
