module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.BinaryChartRings
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Binary polynomial maps into the two actual affine charts

Both chart substitutions become the same binary Laurent substitution after
the chart embeddings. This compatibility uses the literal polynomial rings.
-/

noncomputable section
namespace ChoppedPlane.QWeyl

open MvPolynomial BinaryChartRings LaurentPairing

variable {K : Type*} [Field K]

/-- Substitute the two binary variables into the actual `u` chart.-/
def binaryUChart : BinaryRing K →ₐ[K] URing K :=
  aeval ![uU, vU]

/-- Substitute the two binary variables into the actual `v` chart.-/
def binaryVChart : BinaryRing K →ₐ[K] VRing K :=
  aeval ![uV, vV]

/-- The shared binary substitution into the overlap Laurent ring.-/
def binaryChartLaurentMap : BinaryRing K →ₐ[K] BinaryLaurent K :=
  aeval ![U, V]

/--
@isnad1 id=eq.0h1v.s8.26b8beb89765 from=translated src=- shape=d0481623 vocab=255df374
-/
@[simp] theorem binaryUChart_binaryU :
    binaryUChart (binaryU K) = (uU : URing K) := by
  simp [binaryUChart, binaryU]

/--
@isnad1 id=eq.0h1v.s8.82a16203a83e from=translated src=- shape=d0481623 vocab=9c157c61
-/
@[simp] theorem binaryUChart_binaryV :
    binaryUChart (binaryV K) = (vU : URing K) := by
  simp [binaryUChart, binaryV]

/--
@isnad1 id=eq.0h1v.s8.5152d29e565b from=translated src=- shape=d0481623 vocab=0990505f
-/
@[simp] theorem binaryVChart_binaryU :
    binaryVChart (binaryU K) = (uV : VRing K) := by
  simp [binaryVChart, binaryU]

/--
@isnad1 id=eq.0h1v.s8.546826983de8 from=translated src=- shape=d0481623 vocab=620ef3a0
-/
@[simp] theorem binaryVChart_binaryV :
    binaryVChart (binaryV K) = (vV : VRing K) := by
  simp [binaryVChart, binaryV]

/--
@isnad1 id=eq.0h1v.s8.8b446070acee from=translated src=- shape=d0481623 vocab=675c4d81
-/
@[simp] theorem binaryChartLaurentMap_binaryU :
    binaryChartLaurentMap (binaryU K) = (U : BinaryLaurent K) := by
  simp [binaryChartLaurentMap, binaryU]

/--
@isnad1 id=eq.0h1v.s8.278a5b4d163b from=translated src=- shape=d0481623 vocab=33ffd524
-/
@[simp] theorem binaryChartLaurentMap_binaryV :
    binaryChartLaurentMap (binaryV K) = (V : BinaryLaurent K) := by
  simp [binaryChartLaurentMap, binaryV]

/-- The `u` chart polynomial map agrees with the canonical overlap map.
@isnad1 id=eq.0h1v.s8.f78564b2adb6 from=translated src=- shape=9ec8b135 vocab=52665972
-/
theorem uEmbedding_comp_binaryUChart :
    (uEmbedding (K := K)).comp binaryUChart = binaryChartLaurentMap := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [binaryUChart, binaryChartLaurentMap]

/-- The `v` chart polynomial map agrees with the same canonical overlap map.
@isnad1 id=eq.0h1v.s8.20511827d936 from=translated src=- shape=9ec8b135 vocab=749132a8
-/
theorem vEmbedding_comp_binaryVChart :
    (vEmbedding (K := K)).comp binaryVChart = binaryChartLaurentMap := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [binaryVChart, binaryChartLaurentMap]

/--
@isnad1 id=eq.0h2v.s9.9d491ae6d50c from=translated src=- shape=c6fa4967 vocab=56f4d3c0
-/
@[simp] theorem uEmbedding_binaryUChart (f : BinaryRing K) :
    uEmbedding (binaryUChart f) = binaryChartLaurentMap f := by
  change ((uEmbedding (K := K)).comp binaryUChart) f = _
  rw [uEmbedding_comp_binaryUChart]

/--
@isnad1 id=eq.0h2v.s9.e28ceed2253e from=translated src=- shape=c6fa4967 vocab=da2d829a
-/
@[simp] theorem vEmbedding_binaryVChart (f : BinaryRing K) :
    vEmbedding (binaryVChart f) = binaryChartLaurentMap f := by
  change ((vEmbedding (K := K)).comp binaryVChart) f = _
  rw [vEmbedding_comp_binaryVChart]

/--
@isnad1 id=eq.0h2v.s9.751245d9840a from=translated src=- shape=6b7563d5 vocab=e928a93d
-/
theorem binaryCharts_agree_on_overlap (f : BinaryRing K) :
    uEmbedding (binaryUChart f) = vEmbedding (binaryVChart f) := by
  simp

end ChoppedPlane.QWeyl
