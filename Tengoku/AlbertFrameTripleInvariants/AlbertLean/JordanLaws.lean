import Tengoku.AlbertFrameTripleInvariants.AlbertLean.TraceAssociative
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.ProductTrace
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Characteristic
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.CubicJordan
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

theorem traceN_structuredProduct_eq_traceForm (x y : Coord) :
    traceN (structuredProduct x y) = traceForm x y := by
  have h := traceFormAssociative one x y
  rw [(unitLaw x).1, traceForm_one_eq_traceN] at h
  exact h.symm

theorem productSpur_eq_spurN (x : Coord) : productSpur x = spurN x := by
  rw [productSpur, productTrace_eq_traceN, productTrace_eq_traceN,
    traceN_structuredProduct_eq_traceForm]
  simp [traceForm, spurN, spurBilinear]
  ring

theorem productNorm_eq_cubicNorm (x : Coord) : productNorm x = cubicNorm x := by
  have hs := productSpur_eq_spurN x
  rw [productSpur, productTrace_eq_traceN, productTrace_eq_traceN] at hs
  have hc0 := characteristicIdentity x
  have hc := congrArg traceN hc0
  simp only [traceN_sub, traceN_add, traceN_smul, traceN_zero, traceN_one] at hc
  rw [productNorm, productTrace_eq_traceN, productTrace_eq_traceN,
    productTrace_eq_traceN, traceN_structuredProduct_eq_traceForm,
    traceN_structuredProduct_eq_traceForm]
  rw [← traceN_structuredProduct_eq_traceForm,
    ← traceN_structuredProduct_eq_traceForm]
  ring_nf at hs hc ⊢
  linear_combination (1 / 3 : ℚ) * hc + (traceN x / 3) * hs

theorem printedInvariantsAgree : PrintedInvariantsAgree := by
  exact ⟨productTrace_eq_traceN, productSpur_eq_spurN,
    productNorm_eq_cubicNorm⟩

private def productBilinearMap : Coord →ₗ[ℚ] Coord →ₗ[ℚ] Coord where
  toFun := leftMulLinear productQBilinear
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    exact productQBilinear.1 x y z
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    exact productQBilinear.2.1 a x y

private def traceLinearMap : Coord →ₗ[ℚ] ℚ where
  toFun := traceN
  map_add' := traceN_add
  map_smul' := traceN_smul

private theorem cubicTraceResidual (x : Coord) :
    CubicJordan.residual productBilinearMap traceLinearMap one x = 0 := by
  have hs := productSpur_eq_spurN x
  have hn := productNorm_eq_cubicNorm x
  simp only [productSpur, productNorm, productTrace_eq_traceN] at hs hn
  have hc := characteristicIdentity x
  rw [← hs, ← hn] at hc
  calc
    CubicJordan.residual productBilinearMap traceLinearMap one x =
        (6 : ℚ) •
          (structuredProduct x (structuredProduct x x) -
            traceN x • structuredProduct x x +
            ((traceN x ^ 2 - traceN (structuredProduct x x)) / 2) • x -
            (traceN x ^ 3 / 6 -
              traceN x * traceN (structuredProduct x x) / 2 +
              traceN (structuredProduct x (structuredProduct x x)) / 3) • one) := by
      simp only [CubicJordan.residual, productBilinearMap, traceLinearMap,
        leftMulLinear, LinearMap.coe_mk, AddHom.coe_mk]
      module
    _ = 0 := by rw [hc]; simp

theorem jordanIdentity (x y : Coord) :
    structuredProduct (structuredProduct x y) (structuredProduct x x) =
      structuredProduct x (structuredProduct y (structuredProduct x x)) := by
  have htrace (a b c : Coord) :
      traceLinearMap (productBilinearMap (productBilinearMap a b) c) =
        traceLinearMap (productBilinearMap a (productBilinearMap b c)) := by
    change traceN (structuredProduct (structuredProduct a b) c) =
      traceN (structuredProduct a (structuredProduct b c))
    rw [traceN_structuredProduct_eq_traceForm,
      traceN_structuredProduct_eq_traceForm]
    exact traceFormAssociative a b c
  exact CubicJordan.jordan_of_cubic_trace_identity
    productBilinearMap traceLinearMap one productCommutative
    (fun z => (unitLaw z).1) htrace cubicTraceResidual x y

end AlbertLean
