module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylChartFiniteMaps
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylLaurentGrading

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Finite operators on the actual binary charts and overlap

The generic cyclic chart operators specialize to the literal `u` chart,
`v` chart, and binary Laurent overlap. The chart embeddings are injective
coefficient maps and commute with cross multiplication and differentiation.
-/

noncomputable section
namespace ChoppedPlane.QWeyl

open BinaryChartRings LaurentPairing

variable {K : Type*} [Field K]

/--
@isnad1 id=eq.0h1v.s7.66474977ead7 from=translated src=- shape=77f5ed07 vocab=d9a7c44e
-/
theorem binaryChartLaurentMap_eq_binaryLaurentEmbedding :
    binaryChartLaurentMap (K := K) = binaryLaurentEmbedding := rfl

abbrev UChartFiniteVector (K : Type*) [Field K] (n : ℕ) :=
  ChartFiniteVector (URing K) n

abbrev VChartFiniteVector (K : Type*) [Field K] (n : ℕ) :=
  ChartFiniteVector (VRing K) n

abbrev OverlapFiniteVector (K : Type*) [Field K] (n : ℕ) :=
  ChartFiniteVector (BinaryLaurent K) n

abbrev uFiniteCross (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :=
  chartFiniteCross (binaryUChart (K := K)) q hq s n

abbrev vFiniteCross (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :=
  chartFiniteCross (binaryVChart (K := K)) q hq s n

abbrev overlapFiniteCross (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :=
  chartFiniteCross (binaryChartLaurentMap (K := K)) q hq s n

abbrev uFiniteMultiply (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :=
  chartFiniteMultiply (binaryUChart (K := K)) q hq s n

abbrev vFiniteMultiply (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :=
  chartFiniteMultiply (binaryVChart (K := K)) q hq s n

abbrev overlapFiniteMultiply (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :=
  chartFiniteMultiply (binaryChartLaurentMap (K := K)) q hq s n

abbrev uFiniteDirectional (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :=
  chartFiniteDirectional (binaryUChart (K := K)) q hq s n

abbrev vFiniteDirectional (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :=
  chartFiniteDirectional (binaryVChart (K := K)) q hq s n

abbrev overlapFiniteDirectional (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :=
  chartFiniteDirectional (binaryChartLaurentMap (K := K)) q hq s n

/-- Embed finite auxiliary coefficient vectors from the actual `u` chart.-/
abbrev uFiniteEmbedding (n : ℕ) :=
  chartFiniteBaseChange (uEmbedding (K := K)) n

/-- Embed finite auxiliary coefficient vectors from the actual `v` chart.-/
abbrev vFiniteEmbedding (n : ℕ) :=
  chartFiniteBaseChange (vEmbedding (K := K)) n

/--
@isnad1 id=eq.0h5v.s10.747c3df37701 from=translated src=- shape=08c7f916 vocab=1dea8359
-/
@[simp] theorem uFiniteEmbedding_apply (n : ℕ) (c : UChartFiniteVector K n)
    (i : Sym (Fin 3) n) (j : Fin 3) :
    uFiniteEmbedding n c i j = uEmbedding (c i j) := rfl

/--
@isnad1 id=eq.0h5v.s10.c75efa305d75 from=translated src=- shape=08c7f916 vocab=90b664b2
-/
@[simp] theorem vFiniteEmbedding_apply (n : ℕ) (c : VChartFiniteVector K n)
    (i : Sym (Fin 3) n) (j : Fin 3) :
    vFiniteEmbedding n c i j = vEmbedding (c i j) := rfl

/--
@isnad1 id=injectiv.0h2v.s10.071e7941ea8e from=translated src=- shape=533ac179 vocab=9a5e4e00
-/
theorem uFiniteEmbedding_injective (n : ℕ) :
    Function.Injective (uFiniteEmbedding (K := K) n) := by
  intro c d h
  funext i j
  apply uEmbedding_injective
  exact congrFun (congrFun h i) j

/--
@isnad1 id=injectiv.0h2v.s10.49065dbb2010 from=translated src=- shape=533ac179 vocab=6b1f265e
-/
theorem vFiniteEmbedding_injective (n : ℕ) :
    Function.Injective (vFiniteEmbedding (K := K) n) := by
  intro c d h
  funext i j
  apply vEmbedding_injective
  exact congrFun (congrFun h i) j

/-- The actual Laurent `u` unit is the image of the inverse in the `u` chart.
@isnad1 id=eq.0h1v.s9.56dd288328fb from=translated src=- shape=56f3056a vocab=699e43bf
-/
theorem binaryChartLaurentMap_U_mul_inv :
    binaryChartLaurentMap (binaryU K) * uEmbedding (uUInv (K := K)) = 1 := by
  simpa only [map_mul, map_one, uEmbedding_u, binaryChartLaurentMap_binaryU] using
    congrArg (uEmbedding (K := K)) (uU_mul_inv (K := K))

section CharacteristicZero

variable [CharZero K]

end CharacteristicZero

end ChoppedPlane.QWeyl
