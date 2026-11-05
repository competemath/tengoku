module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylLaurentOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Coefficient-degree closure of the actual Laurent cross, multiplication
and directional operators.  The weights are the literal dual generator
weights and the three actions are the actual coordinates and cyclic root. -/

noncomputable section
namespace ChoppedPlane.QWeyl

open LaurentPairing LaurentChartComplex FiniteCech SymmetricDerivative

variable {K : Type*} [Field K]

@[simp] theorem chartLaurentU_smul (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : Fin 3 → BinaryLaurent K) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    chartU (binaryChartLaurentMap (K := K)) • m = fun i => U * m i := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  change cyclicCoefficientHom ((binaryChartLaurentMap (K := K)) (binaryCubic K))
    ((binaryChartLaurentMap (K := K)) (binaryU K)) • m = _
  rw [cyclicModule_coefficient_smul]
  funext i
  simp

@[simp] theorem chartLaurentV_smul (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : Fin 3 → BinaryLaurent K) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    chartV (binaryChartLaurentMap (K := K)) • m = fun i => V * m i := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  change cyclicCoefficientHom ((binaryChartLaurentMap (K := K)) (binaryCubic K))
    ((binaryChartLaurentMap (K := K)) (binaryV K)) • m = _
  rw [cyclicModule_coefficient_smul]
  funext i
  simp

@[simp] theorem chartLaurentZ_smul (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : Fin 3 → BinaryLaurent K) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    chartZ (binaryChartLaurentMap (K := K)) • m =
      cyclicZDual (fun i => binaryLaurentEmbedding (profileFactors q s i)) m := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  exact cyclicModule_root_smul ((binaryChartLaurentMap (K := K)) (binaryCubic K))
    (chartDualZ (binaryChartLaurentMap (K := K)) q s)
    (chartDualZ_cube (binaryChartLaurentMap (K := K)) q hq s) m

end ChoppedPlane.QWeyl
