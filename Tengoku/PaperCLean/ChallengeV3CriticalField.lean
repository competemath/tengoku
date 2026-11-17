import Tengoku.Seed.Algebra.Order.Floor.Div
import Tengoku.Seed.Algebra.Order.Ring.Finset
import Tengoku.Seed.Algebra.QuadraticAlgebra.NormDeterminant
import Tengoku.Seed.Analysis.BoxIntegral.UnitPartition
import Tengoku.Seed.Analysis.Normed.Group.Tannery
import Tengoku.Seed.Analysis.PSeries
import Tengoku.Seed.Analysis.Polynomial.CauchyBound
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Base
import Tengoku.Seed.Combinatorics.Enumerative.Catalan.Basic
import Tengoku.Seed.Combinatorics.SimpleGraph.Acyclic
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Finite
import Tengoku.Seed.Combinatorics.SimpleGraph.Trails
import Tengoku.Seed.Data.Finset.Interval
import Tengoku.Seed.Data.Int.AbsoluteValue
import Tengoku.Seed.Data.Int.CardIntervalMod
import Tengoku.Seed.Data.Int.Lemmas
import Tengoku.Seed.Data.Multiset.Interval
import Tengoku.Seed.Data.Nat.ChineseRemainder
import Tengoku.Seed.Data.Nat.Dist
import Tengoku.Seed.InformationTheory.Hamming
import Tengoku.Seed.MeasureTheory.Measure.DiracProba
import Tengoku.Seed.MeasureTheory.Measure.SeparableMeasure
import Tengoku.Seed.NumberTheory.AbelSummation
import Tengoku.Seed.NumberTheory.Harmonic.Bounds
import Tengoku.Seed.NumberTheory.Harmonic.EulerMascheroni
import Tengoku.Seed.NumberTheory.Pell
import Tengoku.Seed.NumberTheory.Primorial
import Tengoku.Seed.NumberTheory.RamificationInertia.Galois
import Tengoku.Seed.Probability.Distributions.Geometric
import Tengoku.Seed.Probability.Distributions.Poisson.Basic
import Tengoku.Seed.Probability.Distributions.Uniform
import Tengoku.Seed.Probability.Independence.InfinitePi
import Tengoku.Seed.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Tengoku.Seed.RingTheory.PowerSeries.Binomial
import Tengoku.Seed.RingTheory.PowerSeries.Trunc
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# V3PREL critical-field and conditional-transfer audit interface

The Challenge imports only Mathlib. Its companion Solution independently
copies these transparent definitions and proves every selected declaration.
Bits encode multiplicative signs. The source is the actual infinite product
of prime signs. All excesses and both signs are retained in the complete field.
The diffuse target is a genuine Poisson number of independent marks, with
uniform positions on [1,2], geometric excesses and fair signs.

Only three published inputs are visible arguments: the ordinary PNT remainder,
the scalar analytic Stein factors, and the finite process AGG inequality with
an exact dependency graph. Arithmetic defects and affine relations are computed
from the windows; no desired arithmetic or Poisson approximation is assumed.
The separate scalar and process intensity domains are retained explicitly.
-/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
namespace PaperCV3Audit
local instance instDecidableProp (p : Prop) : Decidable p := Classical.propDecidable p
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators NNReal ENNReal

abbrev F₂ := ZMod 2
local instance instMeasurableSpaceF2 : MeasurableSpace F₂ := ⊤
abbrev InfiniteSample := ℕ → F₂
def coordinateMeasure : Measure F₂ := (PMF.uniformOfFintype F₂).toMeasure
/--
@isnad1 id=isprobab.0h0v.s2.92e1d3b7c052 from=translated src=- shape=54c8eceb vocab=ed3a2940
-/
instance instProbabilityCoordinate : IsProbabilityMeasure coordinateMeasure := by
  unfold coordinateMeasure; infer_instance
def infiniteRademacherMeasure : Measure InfiniteSample :=
  Measure.infinitePi (fun _ : ℕ => coordinateMeasure)
/--
@isnad1 id=isprobab.0h0v.s3.a43185d2b88d from=translated src=- shape=42e9cbf9 vocab=84d68efe
-/
instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure; infer_instance
def parityVec (n : ℕ) : ℕ →₀ F₂ :=
  n.factorization.mapRange (fun e : ℕ => (e : F₂)) (by simp)
def infiniteValueBit (omega : InfiniteSample) (n : ℕ) : F₂ :=
  (parityVec n).sum (fun p e => omega (Nat.primeCounting' p) * e)
def StartEvent (g : ℕ → F₂) (x L : ℕ) : Prop :=
  g (x-1) + g x = 1 ∧ ∀ j : ℕ, j<L → g (x+j)=g x
def dyadicBlock (N : ℕ) : Finset ℕ := Finset.Ico N (2*N)
def ExactLengthEvent (g : ℕ → F₂) (x q : ℕ) : Prop :=
  g (x-1)+g x=1 ∧ (∀ j : ℕ, 0<j → j+1<q → g x=g (x+j)) ∧ g x+g (x+(q-1))=1
def infiniteExactLengthCount (N L e : ℕ) (omega : InfiniteSample) : ℕ :=
  ∑ x∈dyadicBlock N, if ExactLengthEvent (infiniteValueBit omega) x (L+e+1) then 1 else 0
def maskedCount (L : ℕ) (mask : Finset ℕ) (omega : InfiniteSample) : ℕ :=
  ∑ x∈mask, if StartEvent (infiniteValueBit omega) x L then 1 else 0
def fullRate (N L : ℕ) : ℝ≥0 := ⟨(N : ℝ)/2^L, by positivity⟩
def maskRate (L : ℕ) (mask : Finset ℕ) : ℝ≥0 := ⟨(mask.card : ℝ)/2^L, by positivity⟩
def PrimeUpTo (Y : ℕ) := {p : Fin (Y+1) // Nat.Prime p.val}
abbrev SampleSpace (Y : ℕ) := PrimeUpTo Y → F₂
def restrictToFinite (Y : ℕ) (omega : InfiniteSample) : SampleSpace Y :=
  fun p => omega (Nat.primeCounting' p.val)
@[reducible] def primeSigma (Y : ℕ) : MeasurableSpace InfiniteSample :=
  MeasurableSpace.comap (restrictToFinite Y) inferInstance
def observedAtom (Y : ℕ) (omega : InfiniteSample) : Set InfiniteSample :=
  {eta | restrictToFinite Y eta=restrictToFinite Y omega}
def massTV {α : Type*} (p q : α → ℝ) : ℝ := (2 : ℝ)⁻¹ * ∑' k, |p k-q k|
def observableLaw {Ω α : Type*} [MeasurableSpace Ω] (mu : Measure Ω) (f : Ω → α) : α → ℝ :=
  fun k => mu.real {omega | f omega=k}
def conditionalLaw {Ω α : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (A : Set Ω) (f : Ω → α) : α → ℝ := observableLaw (cond mu A) f
def environmentDistance {α : Type*} (Y : ℕ) (f : InfiniteSample → α)
    (q : α → ℝ) (omega : InfiniteSample) : ℝ :=
  massTV (conditionalLaw infiniteRademacherMeasure (observedAtom Y omega) f) q

namespace Process
/- The only process premise is the published finite AGG bound with an exact
independence graph. Neither its indicators nor its graph are arithmetic. -/
structure FinitePMF (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ a, 0≤prob a
  sum_prob : ∑ a, prob a=1

def eventProbability {Ω : Type*} [Fintype Ω] (mu : FinitePMF Ω) (A : Ω → Prop) : ℝ :=
  ∑ omega, if A omega then mu.prob omega else 0
def marginal {Ω ι : Type*} [Fintype Ω] (mu : FinitePMF Ω) (X : ι → Ω → Bool) (i : ι) : ℝ :=
  eventProbability mu (fun omega => X i omega=true)
/--
@isnad1 id=le.0h5v.s5.48726cf58418 from=translated src=- shape=c181798b vocab=c4fa179b
-/
theorem marginal_nonneg {Ω ι : Type*} [Fintype Ω] (mu : FinitePMF Ω)
    (X : ι → Ω → Bool) (i : ι) : 0 ≤ marginal mu X i := by
  unfold marginal eventProbability
  exact Finset.sum_nonneg (fun omega _ => by split_ifs; exact mu.nonneg omega; exact le_rfl)
def closedNeighborhood {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (i : ι) : Finset ι := Finset.univ.filter (fun j => j=i ∨ G.Adj i j)
def OutsideIndex {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) (i : ι) :=
  {j : ι // j ∉ closedNeighborhood G i}
def HasOutsidePattern {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → Bool) (G : SimpleGraph ι) (i : ι)
    (pattern : OutsideIndex G i → Bool) (omega : Ω) : Prop := ∀ j, X j.val omega=pattern j
def HasExactDependencyGraph {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (mu : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι) : Prop :=
  ∀ (i : ι) (v : Bool) (pattern : OutsideIndex G i → Bool),
    eventProbability mu (fun omega => X i omega=v ∧ HasOutsidePattern X G i pattern omega) =
      eventProbability mu (fun omega => X i omega=v) * eventProbability mu (HasOutsidePattern X G i pattern)
def bOne {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (mu : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι) : ℝ :=
  ∑ i, ∑ j∈closedNeighborhood G i, marginal mu X i*marginal mu X j
def bTwo {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (mu : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι) : ℝ :=
  ∑ i, ∑ j∈(closedNeighborhood G i).erase i,
    eventProbability mu (fun omega => X i omega=true ∧ X j omega=true)
def indicatorField {Ω ι : Type*} (X : ι → Ω → Bool) (omega : Ω) (i : ι) : ℕ :=
  if X i omega=true then 1 else 0
def fieldRates {Ω ι : Type*} [Fintype Ω] (mu : FinitePMF Ω) (X : ι → Ω → Bool) (i : ι) : ℝ≥0 :=
  ⟨marginal mu X i, marginal_nonneg mu X i⟩
def finiteFieldLaw {Ω α : Type*} [Fintype Ω] (mu : FinitePMF Ω) (f : Ω → α) (k : α) : ℝ :=
  ∑ omega, if f omega=k then mu.prob omega else 0
def poissonFieldMass {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) (k : ι → ℕ) : ℝ :=
  ∏ i, (poissonMeasure (rate i)).real {k i}
def ProcessAGGStatement : Prop :=
  ∀ (Ω ι : Type) [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (mu : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι),
    HasExactDependencyGraph mu X G →
    massTV (finiteFieldLaw mu (indicatorField X)) (poissonFieldMass (fieldRates mu X)) ≤
      2*(bOne mu X G+bTwo mu X G)
end Process

namespace Analysis
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

/- The PNT premise is the ordinary prime-counting remainder, not a weighted
estimate or an arithmetic conclusion. Ei has the manuscript normalization. -/
def exponentialIntegralAnchor : ℝ := Real.eulerMascheroniConstant +
  ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) * ((n + 1).factorial : ℝ))
def exponentialIntegral (u : ℝ) : ℝ :=
  exponentialIntegralAnchor + ∫ t in (1 : ℝ)..u, Real.exp t / t
def PrimeNumberTheoremRemainder : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ A : ℝ, 2 ≤ A ∧ ∀ t : ℝ, A ≤ t →
    |(Nat.primeCounting ⌊t⌋₊ : ℝ) - exponentialIntegral (Real.log t)| ≤ eta * t / Real.log t

/- Hard/soft saddle scales are actual functions, with explicit totalization
below their existence threshold. Epsilon selects the unique root above it.
The Solution proves equality to the development's chosen root internally. -/
def saddleCostParam (u : ℝ) : ℝ := Real.exp u - exponentialIntegral u
def saddleRatio (u : ℝ) : ℝ := Real.exp u / u
def saddleParameterBase : ℝ := max 2 (3 - saddleCostParam 2)
def saddleHeight (a u : ℝ) : ℝ := a * saddleRatio u * saddleCostParam u
def saddleThreshold (a : ℝ) : ℝ := saddleHeight a saddleParameterBase
def saddleParameter (a H : ℝ) : ℝ :=
  if 0 < a ∧ saddleThreshold a ≤ H then
    Classical.epsilon (fun u : ℝ => saddleParameterBase ≤ u ∧ saddleHeight a u = H)
  else saddleParameterBase
def saddleCutoff (a H : ℝ) : ℝ := a * saddleCostParam (saddleParameter a H)
def saddleNu (a H : ℝ) : ℝ := H / saddleCutoff a H
def hardCutoff (N : ℕ) : ℕ := ⌊Real.exp (saddleCutoff 1 (Real.log N))⌋₊
def softCutoff (N : ℕ) : ℕ := ⌊Real.exp (saddleCutoff 2 (Real.log N))⌋₊

/- Scalar solution input: Krokowski, arXiv:1505.01417v3, (2.14)-(2.15).
Only existence and the two analytic factors are external theorem arguments. -/
def poissonMass (rate : ℝ≥0) (k : ℕ) : ℝ := (poissonMeasure rate).real {k}
def poissonSetMass (rate : ℝ≥0) (A : Set ℕ) : ℝ :=
  ∑' k, if k ∈ A then poissonMass rate k else 0
def firstSteinFactor (rate : ℝ≥0) : ℝ := if rate = 0 then 1 else min 1 (rate : ℝ)⁻¹
def zeroSteinFactor (rate : ℝ≥0) : ℝ := if rate = 0 then 1 else min 1 (Real.sqrt (rate : ℝ))⁻¹
def SteinSolutionBounds (rate : ℝ≥0) (c d : ℝ) : Prop :=
  ∀ A : Set ℕ, ∃ f : ℕ → ℝ,
    (∀ k : ℕ, (rate : ℝ) * f (k+1) - (k : ℝ) * f k =
      (if k ∈ A then 1 else 0) - poissonSetMass rate A) ∧
    (∀ k, |f k| ≤ c) ∧ (∀ k, |f (k+1)-f k| ≤ d)
def ScalarSteinFactorsStatement : Prop :=
  ∀ rate : ℝ≥0, 0 < rate → SteinSolutionBounds rate (zeroSteinFactor rate) (firstSteinFactor rate)

end Analysis

namespace CriticalField
open Analysis Process
@[reducible] def SpatialIndex (N : ℕ) := Fin N × (ℕ × F₂)
@[reducible] def SpatialConfig (N : ℕ) := SpatialIndex N →₀ ℕ
instance instMeasurableConfig (N : ℕ) : MeasurableSpace (SpatialConfig N) := ⊤
/- Epsilon specifies the unique finitely supported array with these actual
coefficients. Existence is proved internally in the Solution, not assumed. -/
def spatialSource (N L : ℕ) (omega : InfiniteSample) : SpatialConfig N :=
  Classical.epsilon (fun c => ∀ j : SpatialIndex N, c j =
    if ExactLengthEvent (infiniteValueBit omega) (N+j.1.val) (L+j.2.1+1) ∧
      infiniteValueBit omega (N+j.1.val)=j.2.2 then 1 else 0)
instance instMeasurableCluster : MeasurableSpace (ℕ →₀ ℕ) := ⊤
/--
@isnad1 id=measurab.0h0v.s3.ca2b0d9711b0 from=translated src=- shape=049cd614 vocab=fc12ec4a
-/
instance instSingletonCluster : MeasurableSingletonClass (ℕ →₀ ℕ) := by infer_instance
def halfSuccess : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
def geometricClusterMeasure : Measure ℕ := (geometricMeasure halfSuccess).map Nat.succ
def clusterConfiguration (sample : ℕ × (ℕ → ℕ)) : ℕ →₀ ℕ :=
  ∑ i∈Finset.range sample.1, if 0<sample.2 i then Finsupp.single (sample.2 i-1) 1 else 0
/--
@isnad1 id=measurab.0h0v.s4.cc83af12252c from=translated src=- shape=2ed2ed8b vocab=32a6a8c0
-/
theorem measurable_clusterConfiguration : Measurable clusterConfiguration := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → ℕ => ∑ i∈Finset.range n,
    if 0 < marks i then Finsupp.single (marks i-1) 1 else 0)
  exact Finset.measurable_sum _ (fun i _ =>
    (measurable_of_countable (fun h : ℕ => if 0<h then
      (Finsupp.single (h-1) 1 : ℕ →₀ ℕ) else 0)).comp (measurable_pi_apply i))
def configurationMeasure (rate : ℝ≥0) : Measure (ℕ →₀ ℕ) :=
  ((poissonMeasure rate).prod (Measure.infinitePi (fun _ : ℕ => geometricClusterMeasure))).map
    clusterConfiguration
def flattenRows (N : ℕ) (rows : (Fin N × F₂) → (ℕ →₀ ℕ)) : SpatialConfig N :=
  Finsupp.onFinset
    (Finset.univ.biUnion (fun i : Fin N × F₂ =>
      (rows i).support.image (fun e => (i.1,(e,i.2)))))
    (fun j => rows (j.1,j.2.2) j.2.1) (by
      intro j hj
      exact Finset.mem_biUnion.mpr ⟨(j.1,j.2.2),Finset.mem_univ _,
        Finset.mem_image.mpr ⟨j.2.1,Finsupp.mem_support_iff.mpr hj,rfl⟩⟩)
/- Independent rows, each an independent Poisson number of iid geometric
marks, give all independent signed atom rates 2^(-L-e-2). -/
def spatialTarget (N L : ℕ) : Measure (SpatialConfig N) :=
  (Measure.pi (fun _ : Fin N × F₂ => configurationMeasure (1/2^(L+1)))).map (flattenRows N)
def spatialTargetMass (N L : ℕ) : SpatialConfig N → ℝ := observableLaw (spatialTarget N L) id
def spatialDistance (N L : ℕ) : ℝ :=
  massTV (observableLaw infiniteRademacherMeasure (spatialSource N L)) (spatialTargetMass N L)
def scalarMeanDistance (N L Y : ℕ) : ℝ :=
  ∫ omega, environmentDistance Y (maskedCount L (dyadicBlock N)) (poissonMass (fullRate N L)) omega
    ∂infiniteRademacherMeasure
def spatialMeanDistance (N L Y : ℕ) : ℝ :=
  ∫ omega, environmentDistance Y (spatialSource N L) (spatialTargetMass N L) omega
    ∂infiniteRademacherMeasure
def spatialEventDistance (N L : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTV (conditionalLaw infiniteRademacherMeasure A (spatialSource N L)) (spatialTargetMass N L)
def criticalWindow (C : ℝ) (N L : ℕ) : Prop := |(L : ℝ)-Real.log N/Real.log 2| ≤ C
def criticalScale (N : ℕ) : ℝ := Real.sqrt (Real.log N*Real.log (Real.log N))
def hardRate (N L : ℕ) (epsilon eta : ℝ) : ℝ := (fullRate N L : ℝ)*
  (Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
    (N : ℝ)^(-(1/(3 : ℝ))+epsilon))
def softRate (N L : ℕ) (epsilon eta : ℝ) : ℝ :=
  Real.exp (-(saddleCutoff 2 (Real.log N)-max 0 (Real.log (fullRate N L)))/2+
    eta*saddleNu 2 (Real.log N))+(N : ℝ)^(-(1/(3 : ℝ))+epsilon)
def eventInformation (A : Set InfiniteSample) : ℝ := -Real.log (infiniteRademacherMeasure.real A)
end CriticalField

namespace CriticalField
/- Probability laws of finite point measures use the weak topology and its
Borel sigma-algebra. The limiting PPP is an actual independently marked sum. -/
local instance instTopologicalSign : TopologicalSpace F₂ := ⊥
/--
@isnad1 id=discrete.0h0v.s1.572da982c35a from=translated src=- shape=49959d42 vocab=6f9a624f
-/
local instance instDiscreteSign : DiscreteTopology F₂ := ⟨rfl⟩
def PointCloud := FiniteMeasure (ℝ × (ℕ × F₂))
instance instTopologicalPointCloud : TopologicalSpace PointCloud :=
  inferInstanceAs (TopologicalSpace (FiniteMeasure (ℝ × (ℕ × F₂))))
instance instMeasurablePointCloud : MeasurableSpace PointCloud := borel PointCloud
instance instAddPointCloud : AddCommMonoid PointCloud :=
  inferInstanceAs (AddCommMonoid (FiniteMeasure (ℝ × (ℕ × F₂))))
def pointDirac (x : ℝ × (ℕ × F₂)) : PointCloud := (diracProba x).toFiniteMeasure
def spatialEmbedding (N : ℕ) (c : SpatialConfig N) : PointCloud :=
  c.sum (fun j n => n • pointDirac (1+(j.1.val : ℝ)/N,j.2))
def uniformPosition : Measure unitInterval := volume.comap ((↑) : unitInterval → ℝ)
def diffuseMarkMeasure : Measure (unitInterval × (ℕ × F₂)) :=
  uniformPosition.prod ((geometricMeasure halfSuccess).prod coordinateMeasure)
def diffuseSampleCloud (s : ℕ × (ℕ → unitInterval × (ℕ × F₂))) : PointCloud :=
  ∑ i∈Finset.range s.1, pointDirac (1+(s.2 i).1,(s.2 i).2)
def diffuseMeasure (rate : ℝ≥0) : Measure PointCloud :=
  ((poissonMeasure rate).prod (Measure.infinitePi (fun _ : ℕ => diffuseMarkMeasure))).map diffuseSampleCloud
end CriticalField

namespace CriticalField
def measureTV {α : Type*} [MeasurableSpace α] (mu nu : Measure α) : ℝ :=
  sSup {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r=|mu.real A-nu.real A|}
end CriticalField

namespace CriticalField
open Analysis
/--
@isnad1 id=fact.0h0v.s2.2cde8ffc8dda from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
local instance instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance instFinitePrime (M : ℕ) : Fintype (PrimeUpTo M) := Subtype.fintype _
local instance instDecidablePrime (M : ℕ) : DecidableEq (PrimeUpTo M) := Classical.decEq _
def valueLinear (M n : ℕ) : SampleSpace M →ₗ[F₂] F₂ where
  toFun omega := ∑ p : PrimeUpTo M, omega p*parityVec n p.val
  map_add' omega eta := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c omega := by simp [Finset.mul_sum,mul_assoc]
def startRow (M x L : ℕ) (i : Fin L) : SampleSpace M →ₗ[F₂] F₂ :=
  if i.val=0 then valueLinear M (x-1)+valueLinear M x else valueLinear M x+valueLinear M (x+i.val)
def twoStartSystem (M x y L : ℕ) : SampleSpace M →ₗ[F₂] (Sum (Fin L) (Fin L) → F₂) :=
  LinearMap.pi (fun i => match i with | Sum.inl j => startRow M x L j | Sum.inr j => startRow M y L j)
def dotLinear {ι : Type*} [Fintype ι] (w : ι → F₂) : (ι → F₂) →ₗ[F₂] F₂ where
  toFun := dotProduct w
  map_add' y z := dotProduct_add w y z
  map_smul' c y := dotProduct_smul c w y
def relationMap {V ι : Type*} [AddCommGroup V] [Module F₂ V] [Fintype ι]
    (A : V →ₗ[F₂] (ι → F₂)) : (ι → F₂) →ₗ[F₂] (V →ₗ[F₂] F₂) where
  toFun u := (dotLinear u).comp A
  map_add' u v := by ext x; simp [dotLinear,add_dotProduct]
  map_smul' c u := by ext x; simp [dotLinear,smul_dotProduct]
def jointRho (N L : ℕ) (pair : ℕ × ℕ) : ℕ :=
  Module.finrank F₂ (LinearMap.ker (relationMap (twoStartSystem (2*N+L) pair.1 pair.2 L)))
def separatedPairs (mask : Finset ℕ) (L : ℕ) : Finset (ℕ × ℕ) :=
  (mask ×ˢ mask).filter (fun p => L<Nat.dist p.1 p.2)
def jointDefectMass (N L : ℕ) (pairs : Finset (ℕ × ℕ)) : ℕ :=
  ∑ p∈pairs, (2^jointRho N L p-1)
def HDefective (H n : ℕ) : Prop := ∀ p : ℕ, p.Prime → H<p → parityVec n p=0
def defectIndices (H x B : ℕ) : Finset (Fin B) :=
  Finset.univ.filter (fun i => HDefective H (x-1+i.val))
def fullDefectMass (L : ℕ) (mask : Finset ℕ) : ℕ :=
  ∑ x∈mask, (2^(defectIndices (L+1) x (L+1)).card-1)
def treeSupport (x L : ℕ) : Finset ℕ := insert (x-1) ((Finset.range L).image (fun j => x+j))
def fullBadStarts (N L Y : ℕ) : Finset ℕ :=
  (dyadicBlock N).filter (fun x => ∃ n∈treeSupport x L, HDefective Y n)
def retainedRate (N L Y : ℕ) (mask : Finset ℕ) : ℝ≥0 :=
  ⟨((mask \ fullBadStarts N L Y).card : ℝ)/2^L, by positivity⟩
def largeOddSupport (Y n : ℕ) : Finset ℕ :=
  (n.factorization.mapRange (fun e : ℕ => e%2) (by simp)).support.filter (fun p => Y<p)
def primeCoordinates (x L Y : ℕ) : Finset ℕ :=
  (treeSupport x L).biUnion (fun n => largeOddSupport Y n)
def supportEdges (L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  mask.offDiag.filter (fun p => p.1≠p.2 ∧ (primeCoordinates p.1 L Y ∩ primeCoordinates p.2 L Y).Nonempty)
/- These are the actual arithmetic costs: all defective vertices, all removed
sites including the root, and the full two-window relation space. -/
def maskedBudget (N L Y : ℕ) (mask : Finset ℕ) : ℝ :=
  ((fullDefectMass L mask : ℝ)+2*(mask ∩ fullBadStarts N L Y).card)/(2 : ℝ)^L+
    2*firstSteinFactor (retainedRate N L Y mask)*
      (((mask.card : ℝ)+(supportEdges L Y mask).card+
        (jointDefectMass N L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L))
end CriticalField

namespace CriticalField
open Analysis Process

end CriticalField

namespace CriticalField
open Analysis Process
/-- The larger inverse branch of exp(u)/u; totalized to 1 below e.-/
def upperBranch (nu : ℝ) : ℝ :=
  if Real.exp 1≤nu then Classical.epsilon (fun u : ℝ => 1≤u ∧ saddleRatio u=nu) else 1
def deletionCost (nu : ℝ) : ℝ := nu*upperBranch nu-exponentialIntegral (upperBranch nu)
/-- The unique crossing between hard and soft cutoffs, with a stated fallback.-/
def informationCutoff (H I : ℝ) : ℝ :=
  if max (saddleThreshold 1) (saddleThreshold 2)≤H ∧ 0≤I ∧ I≤saddleCutoff 1 H then
    Classical.epsilon (fun w => w∈Set.Icc (saddleCutoff 1 H) (saddleCutoff 2 H) ∧
      2*deletionCost (H/w)=w+I)
  else saddleCutoff 1 H
def informationBudget (H I w : ℝ) : ℝ := min (deletionCost (H/w)-I) ((w-I)/2)
def eventDistance (N L : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTV (conditionalLaw infiniteRademacherMeasure A (spatialSource N L)) (spatialTargetMass N L)
end CriticalField

namespace CriticalField
open Analysis Process

end CriticalField

end PaperCV3Audit
end
