import Tengoku.AlbertFrameTripleInvariants.AlbertLean.TensorConformance
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.Regressions
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.ProductTrace
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

/--
@isnad1 id=and.0h0v.s7.f3fb6d262b1b from=translated src=- shape=07ba4c74 vocab=5d753194
-/
theorem regressionM01 :
    m01TensorProduct (basisVec 0) (basisVec 11) (11 : Slot) = q (-1) 2 ∧
    m01TensorProduct (basisVec 11) (basisVec 0) (11 : Slot) = q 1 2 ∧
    m01TensorProduct (basisVec 0) (basisVec 11) ≠
      m01TensorProduct (basisVec 11) (basisVec 0) := by
  constructor
  · rw [show m01TensorProduct (basisVec 0) (basisVec 11) =
        productForm (basisVec 0) (basisVec 11) -
          ((basisVec 0) 0 * (basisVec 11) 11) • basisVec 11 by
      simp [m01TensorProduct, tensorProduct_eq_productForm]]
    norm_num [productForm, basisVec, v, q, Fin.ext_iff]
  constructor
  · rw [show m01TensorProduct (basisVec 11) (basisVec 0) =
        productForm (basisVec 11) (basisVec 0) -
          ((basisVec 11) 0 * (basisVec 0) 11) • basisVec 11 by
      simp [m01TensorProduct, tensorProduct_eq_productForm]]
    norm_num [productForm, basisVec, v, q, Fin.ext_iff]
  · intro h
    have h11 := congrFun h (11 : Slot)
    simp [m01TensorProduct, tensorProduct_eq_productForm] at h11
    norm_num [productForm, basisVec, v, q, Fin.ext_iff] at h11

/--
@isnad1 id=and.0h0v.s6.196a36280d26 from=translated src=- shape=b35ef2c3 vocab=870d0ab8
-/
theorem regressionM02 :
    m02Product one (basisVec 0) (0 : Slot) = q 2 1 ∧
    m02Product one (basisVec 0) ≠ basisVec 0 := by
  have hprod : m02Product one (basisVec 0) = 2 • structuredProduct one (basisVec 0) := by
    funext k
    simp [m02Product, structuredProduct]
  constructor
  · rw [hprod, (unitLaw (basisVec 0)).1]
    norm_num [basisVec, q]
  · intro h
    have h0 := congrFun h (0 : Slot)
    rw [hprod, (unitLaw (basisVec 0)).1] at h0
    norm_num [basisVec, q] at h0

/--
@isnad1 id=and.0h0v.s4.b5535c22072b from=translated src=- shape=68498e05 vocab=ac977899
-/
theorem regressionM05 :
    traceN m05ThetaMK = q 1 1 ∧
    ¬ LawfulFrameTriple m05WitnessThetaM := by
  have htrace : traceN m05ThetaMK = q 1 1 := by
    norm_num [traceN_eq_coords, m05ThetaMK, thetaMK, basisVec, q, Fin.ext_iff]
  refine ⟨htrace, ?_⟩
  intro h
  have hk := h (2 : Fin 3)
  have hzero := hk.1.1
  have hzero' : traceN m05ThetaMK = 0 := by
    simpa [m05WitnessThetaM, encoder] using hzero
  rw [htrace] at hzero'
  norm_num [q] at hzero'

/--
@isnad1 id=and.0h0v.s5.70317f6f80e5 from=translated src=- shape=b6999875 vocab=437b2d3e
-/
theorem regressionM04T :
    cubicNorm m04TTheta1.cF = q 245 54 ∧
    cubicNorm m04TThetaM.cF = q 245 54 ∧
    ¬ LawfulFrameTriple m04TTheta1 ∧
    ¬ LawfulFrameTriple m04TThetaM := by
  have hn1 : cubicNorm m04TTheta1.cF = q 245 54 := by
    norm_num [m04TTheta1, m04TTheta1F, cubicNorm, v, q]
  have hnm : cubicNorm m04TThetaM.cF = q 245 54 := by
    norm_num [m04TThetaM, m04TThetaMF, cubicNorm, v, q]
  refine ⟨hn1, hnm, ?_, ?_⟩
  · intro h
    have hf := h (1 : Fin 3)
    have hzero := hf.1.2.2
    have henc : encoder m04TTheta1 (1 : Fin 3) = m04TTheta1.cF := by rfl
    rw [henc] at hzero
    have hzero' : cubicNorm m04TTheta1.cF = 0 := by
      exact hzero
    rw [hn1] at hzero'
    norm_num [q] at hzero'
  · intro h
    have hf := h (1 : Fin 3)
    have hzero := hf.1.2.2
    have henc : encoder m04TThetaM (1 : Fin 3) = m04TThetaM.cF := by rfl
    rw [henc] at hzero
    have hzero' : cubicNorm m04TThetaM.cF = 0 := by
      exact hzero
    rw [hnm] at hzero'
    norm_num [q] at hzero'

/--
@isnad1 id=and.0h0v.s6.332bb9ea84da from=translated src=- shape=0211ad01 vocab=2e42c446
-/
theorem regressionM11 :
    m11ProductTrace (basisVec 0) = q 9 8 ∧
    m11ProductTrace (basisVec 0) ≠ traceN (basisVec 0) := by
  have hleft : leftMulMatrixTrace (basisVec 0) = 9 := by
    have h := productTrace_eq_traceN (basisVec 0)
    norm_num [productTrace, traceN_eq_coords, basisVec, Fin.ext_iff] at h
    linarith
  have hmut : m11ProductTrace (basisVec 0) = q 9 8 := by
    simp [m11ProductTrace, hleft, q]
  refine ⟨hmut, ?_⟩
  intro h
  rw [hmut] at h
  have htrace : traceN (basisVec 0) = q 1 1 := by
    norm_num [traceN_eq_coords, basisVec, q, Fin.ext_iff]
  rw [htrace] at h
  norm_num [q] at h

end AlbertLean
