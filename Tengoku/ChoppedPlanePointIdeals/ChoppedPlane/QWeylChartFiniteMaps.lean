module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylLaurentCharts
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.CyclicScalarTower
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.TensorCoefficientBaseChange
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.BinaryChartPolynomialMaps
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.FiniteCrossAnnihilation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The finite coefficient maps on the actual cyclic modules of the two
binary Laurent charts.  The maps retain the original coefficient-field
action; their formulas and exactness are inherited from the actual tensor
operators, rather than postulated for an abstract finite complex. -/

noncomputable section
namespace ChoppedPlane.QWeyl

open MvPolynomial SymmetricDerivative FiniteCech BinaryChartRings LaurentPairing

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Finite auxiliary coefficient vectors on an actual chart.-/
abbrev ChartFiniteVector (A : Type*) (n : ℕ) := Sym (Fin 3) n → Fin 3 → A

/-- Cross substitution on a cyclic chart, with its genuine `K`-linear action.-/
def chartFiniteCross (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :
    ChartFiniteVector A n →ₗ[K] ChartFiniteVector A n := by
  letI := chartDualModuleStructure φ q hq s
  letI := cyclicModuleScalarTower (K := K) (φ (binaryCubic K))
    (chartDualZ φ q s) (chartDualZ_cube φ q hq s)
  exact (finiteCross (chartCrossMatrix φ) n).restrictScalars K

/-- Multiplication by the actual chart linear form.-/
def chartFiniteMultiply (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :
    ChartFiniteVector A n →ₗ[K] ChartFiniteVector A (n + 1) := by
  letI := chartDualModuleStructure φ q hq s
  letI := cyclicModuleScalarTower (K := K) (φ (binaryCubic K))
    (chartDualZ φ q s) (chartDualZ_cube φ q hq s)
  exact (finiteMultiply (chartLinearForm φ) n).restrictScalars K

/-- Directional differentiation for the actual chart linear form.-/
def chartFiniteDirectional (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :
    ChartFiniteVector A (n + 1) →ₗ[K] ChartFiniteVector A n := by
  letI := chartDualModuleStructure φ q hq s
  letI := cyclicModuleScalarTower (K := K) (φ (binaryCubic K))
    (chartDualZ φ q s) (chartDualZ_cube φ q hq s)
  exact (finiteDirectional (chartLinearForm φ) n).restrictScalars K

section CharacteristicZero
variable [CharZero K]

end CharacteristicZero

section BaseChange

variable {A' : Type*} [CommRing A'] [Algebra K A']

/-- The actual cubic quotient-ring map induced by a chart coefficient map.-/
def chartCubicBaseChange (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    ChartCubicRing φ →+* ChartCubicRing (ψ.comp φ) :=
  cyclicBaseChangeHom ψ.toRingHom (φ (binaryCubic K))

/-- Coefficient extension is semilinear for the actual cyclic module action.-/
def chartModuleBaseChange (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A')
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := chartDualModuleStructure φ q hq s
    letI := chartDualModuleStructure (ψ.comp φ) q hq s
    (Fin 3 → A) →ₛₗ[chartCubicBaseChange φ ψ] (Fin 3 → A') := by
  letI := chartDualModuleStructure φ q hq s
  letI := chartDualModuleStructure (ψ.comp φ) q hq s
  exact cyclicModuleBaseChange ψ.toRingHom (φ (binaryCubic K))
    (cyclicVectorBaseChange ψ.toRingHom) (chartDualZ φ q s)
    (chartDualZ (ψ.comp φ) q s) (chartDualZ_cube φ q hq s)
    (chartDualZ_cube (ψ.comp φ) q hq s)
    (cyclicZDual_baseChange ψ.toRingHom (fun i => φ (profileFactors q s i)))

/--
@isnad1 id=eq.1h9v.s11.b66331a776ab from=translated src=- shape=8192258e vocab=79fd901c
-/
@[simp] theorem chartModuleBaseChange_apply
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A')
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (c : Fin 3 → A) (i : Fin 3) :
    chartModuleBaseChange φ ψ q hq s c i = ψ (c i) := rfl

/-- The finite coefficient map is pointwise coefficient extension over `K`.-/
def chartFiniteBaseChange (ψ : A →ₐ[K] A') (n : ℕ) :
    ChartFiniteVector A n →ₗ[K] ChartFiniteVector A' n where
  toFun c i j := ψ (c i j)
  map_add' c d := by funext i j; exact ψ.map_add _ _
  map_smul' k c := by funext i j; exact ψ.toLinearMap.map_smul k _

/--
@isnad1 id=eq.0h8v.s9.ca68d7e54e99 from=translated src=- shape=401b445c vocab=6244db08
-/
@[simp] theorem chartFiniteBaseChange_apply (ψ : A →ₐ[K] A')
    (n : ℕ) (c : ChartFiniteVector A n) (i : Sym (Fin 3) n) (j : Fin 3) :
    chartFiniteBaseChange ψ n c i j = ψ (c i j) := rfl

/--
@isnad1 id=eq.1h9v.s12.3691a40d175a from=translated src=- shape=4b20fa2e vocab=c52e3965
-/
@[simp] theorem finiteCoefficient_chartModuleBaseChange
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A')
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (n : ℕ) (c : ChartFiniteVector A n) :
    letI := chartDualModuleStructure φ q hq s
    letI := chartDualModuleStructure (ψ.comp φ) q hq s
    finiteCoefficientBaseChange (chartModuleBaseChange φ ψ q hq s) n c =
      chartFiniteBaseChange ψ n c := by
  rfl

/--
@isnad1 id=eq.0h5v.s11.3ebc3458a4d5 from=translated src=- shape=9bb20d99 vocab=0192f2c0
-/
@[simp] theorem chartCubicBaseChange_U
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    chartCubicBaseChange φ ψ (chartU φ) = chartU (ψ.comp φ) :=
  cyclicBaseChangeHom_coefficient ψ.toRingHom (φ (binaryCubic K)) (φ (binaryU K))

/--
@isnad1 id=eq.0h5v.s11.fd9af0f6c33b from=translated src=- shape=9bb20d99 vocab=ba11d302
-/
@[simp] theorem chartCubicBaseChange_V
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    chartCubicBaseChange φ ψ (chartV φ) = chartV (ψ.comp φ) :=
  cyclicBaseChangeHom_coefficient ψ.toRingHom (φ (binaryCubic K)) (φ (binaryV K))

/--
@isnad1 id=eq.0h5v.s11.61cdf7f9ae48 from=translated src=- shape=9bb20d99 vocab=1e8d21f7
-/
@[simp] theorem chartCubicBaseChange_Z
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    chartCubicBaseChange φ ψ (chartZ φ) = chartZ (ψ.comp φ) :=
  cyclicBaseChangeHom_root ψ.toRingHom (φ (binaryCubic K))

/--
@isnad1 id=eq.0h5v.s11.c20f3f08a768 from=translated src=- shape=a7c2d505 vocab=26797f96
-/
theorem chartCubicBaseChange_linearForm
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    (fun i => chartCubicBaseChange φ ψ (chartLinearForm φ i)) =
      chartLinearForm (ψ.comp φ) := by
  funext i
  fin_cases i <;> simp [chartLinearForm]

/--
@isnad1 id=eq.0h5v.s11.34863b5e70ca from=translated src=- shape=17d88d09 vocab=3af427fd
-/
@[simp] theorem chartCubicBaseChange_crossMatrix
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    (chartCrossMatrix φ).map (chartCubicBaseChange φ ψ) =
      chartCrossMatrix (ψ.comp φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartCrossMatrix, crossMatrix]

end BaseChange
end ChoppedPlane.QWeyl
