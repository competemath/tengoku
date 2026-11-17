import Tengoku.SingularityCompleteLean.Singularity.ProjectiveMobius
import Tengoku.SingularityCompleteLean.Singularity.MobiusMeasureAction
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Topology
import Tengoku.Seed.Topology.Compactification.OnePoint.Sphere
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The compact real boundary inside the Riemann sphere

The real boundary is ℝ ∪ {∞}, with the genuine projective action at every
point. The ambient compactification ℂ ∪ {∞} also contains the upper half-plane.
Both carry their Borel structures and metrizable compact Hausdorff topology.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint TopologicalSpace
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Use the Borel measurable structure on a one-point compactification.-/
instance projectiveBorelMeasurableSpace (K : Type*) [TopologicalSpace K] :
    MeasurableSpace (OnePoint K) := borel (OnePoint K)

/--
@isnad1 id=borelspa.0h1v.s3.fc263b15d36a from=translated src=- shape=1666ae32 vocab=bf2721e8
-/
instance projectiveBorelSpace (K : Type*) [TopologicalSpace K] : BorelSpace (OnePoint K) := ⟨rfl⟩

/-- The real projective line is metrizable, via its homeomorphism with the circle.
@isnad1 id=metrizab.0h0v.s3.500f1eea8be3 from=translated src=- shape=87ceb31f vocab=7f0cd48b
-/
instance realProjectiveMetrizable : MetrizableSpace (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)).isEmbedding.metrizableSpace

/-- The complex projective line is metrizable, via its homeomorphism with the two-sphere.
@isnad1 id=metrizab.0h0v.s4.c7c19475dd3b from=translated src=- shape=87ceb31f vocab=ba399544
-/
instance complexProjectiveMetrizable : MetrizableSpace (OnePoint ℂ) :=
  (onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)).isEmbedding.metrizableSpace

/-- Real special linear matrices act on a real-algebra projective line.-/
instance projectiveSLAction (K : Type*) [Field K] [Algebra ℝ K] :
    MulAction SL(2, ℝ) (OnePoint K) :=
  MulAction.compHom (OnePoint K) (Matrix.SpecialLinearGroup.mapGL K)

/--
@isnad1 id=continuo.0h1v.s7.a806a3cc5a50 from=translated src=- shape=d4bfee73 vocab=7d926ca2
-/
instance projectiveSLContinuous (K : Type*) [NontriviallyNormedField K] [ProperSpace K]
    [Algebra ℝ K] : ContinuousConstSMul SL(2, ℝ) (OnePoint K) where
  continuous_const_smul g := continuous_projectiveMobius (Matrix.SpecialLinearGroup.mapGL K g)

/--
@isnad1 id=continuo.0h2v.s10.0e59b223db2c from=translated src=- shape=a47c5206 vocab=7e312736
-/
instance projectiveSubgroupContinuous (K : Type*) [NontriviallyNormedField K] [ProperSpace K]
    [Algebra ℝ K] (Γ : Subgroup SL(2, ℝ)) : ContinuousConstSMul Γ (OnePoint K) where
  continuous_const_smul g := continuous_const_smul (g : SL(2, ℝ))

/-- At a finite non-pole, the compact action agrees with the existing real-chart formula.
@isnad1 id=eq.1h2v.s8.4906a616e417 from=translated src=- shape=475d91fd vocab=a75f74bb
-/
theorem compactBoundary_smul_finite (g : SL(2, ℝ)) (u : ℝ)
    (hu : g 1 0 * u + g 1 1 ≠ 0) :
    g • (u : OnePoint ℝ) = (realBoundaryMobius g u : OnePoint ℝ) := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ g) • (u : OnePoint ℝ) = _
  rw [OnePoint.smul_some_eq_ite]
  change (if g 1 0 * u + g 1 1 = 0 then (∞ : OnePoint ℝ) else
    ((g 0 0 * u + g 0 1) / (g 1 0 * u + g 1 1) : ℝ)) = _
  rw [ite_eq_right hu]
  rfl

/-- The compact action sends a real-chart pole to infinity.
@isnad1 id=eq.1h2v.s8.14cbd8eb47e1 from=translated src=- shape=05b4e205 vocab=b028c7cf
-/
theorem compactBoundary_smul_pole (g : SL(2, ℝ)) (u : ℝ)
    (hu : g 1 0 * u + g 1 1 = 0) : g • (u : OnePoint ℝ) = ∞ := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ g) • (u : OnePoint ℝ) = _
  rw [OnePoint.smul_some_eq_ite]
  change (if g 1 0 * u + g 1 1 = 0 then (∞ : OnePoint ℝ) else _) = ∞
  rw [ite_eq_left hu]

/-- Include the upper half-plane into the ambient compact sphere.-/
def hyperbolicCompactEmbedding (z : ℍ) : OnePoint ℂ := (z : ℂ)

/--
@isnad1 id=isopenem.0h0v.s4.59d8d91bdddc from=translated src=- shape=4b736592 vocab=77fe5c96
-/
theorem isOpenEmbedding_hyperbolicCompactEmbedding :
    Topology.IsOpenEmbedding hyperbolicCompactEmbedding :=
  OnePoint.isOpenEmbedding_coe.comp UpperHalfPlane.isOpenEmbedding_coe

/-- The compact sphere action extends the actual upper-half-plane action.
@isnad1 id=eq.0h2v.s8.39418f5d6898 from=translated src=- shape=ebb162f1 vocab=c9e2ac02
-/
theorem hyperbolicCompactEmbedding_smul (g : SL(2, ℝ)) (z : ℍ) :
    hyperbolicCompactEmbedding (g • z) = g • hyperbolicCompactEmbedding z := by
  change (((g • z : ℍ) : ℂ) : OnePoint ℂ) =
    (Matrix.SpecialLinearGroup.mapGL ℂ g) • ((z : ℂ) : OnePoint ℂ)
  rw [OnePoint.smul_some_eq_ite]
  have hd : (g 1 0 : ℂ) * (z : ℂ) + (g 1 1 : ℂ) ≠ 0 :=
    UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.toGL g) z
  change (((g • z : ℍ) : ℂ) : OnePoint ℂ) =
    if (g 1 0 : ℂ) * (z : ℂ) + (g 1 1 : ℂ) = 0 then ∞ else _
  rw [ite_eq_right hd]
  congr 1
  exact UpperHalfPlane.coe_specialLinearGroup_apply g z

/-- The real projective boundary embeds in the complex sphere.-/
def compactBoundaryEmbedding : OnePoint ℝ → OnePoint ℂ := OnePoint.map Complex.ofReal

/--
@isnad1 id=continuo.0h0v.s4.f45530a90e33 from=translated src=- shape=324b2a5c vocab=aa1f1d08
-/
theorem continuous_compactBoundaryEmbedding : Continuous compactBoundaryEmbedding := by
  apply OnePoint.continuous_map Complex.continuous_ofReal
  simpa only [coclosedCompact_eq_cocompact] using
    Complex.isometry_ofReal.isClosedEmbedding.tendsto_cocompact

/-- Boundary inclusion commutes with every real special linear transformation.
@isnad1 id=eq.0h2v.s8.ee996a179e11 from=translated src=- shape=3a5555fd vocab=9f769e6a
-/
theorem compactBoundaryEmbedding_smul (g : SL(2, ℝ)) (p : OnePoint ℝ) :
    compactBoundaryEmbedding (g • p) = g • compactBoundaryEmbedding p := by
  exact OnePoint.map_smul Complex.ofRealHom (Matrix.SpecialLinearGroup.mapGL ℝ g) p

/-- The finite points on the boundary have zero imaginary part; infinity is also included.-/
def compactHyperbolicBoundary : Set (OnePoint ℂ) :=
  {p | ∀ z : ℂ, p = (z : OnePoint ℂ) → z.im = 0}

/--
@isnad1 id=mem.0h0v.s3.9c840e0036ea from=translated src=- shape=fdce6104 vocab=9322a339
-/
theorem compactHyperbolicBoundary_infty : (∞ : OnePoint ℂ) ∈ compactHyperbolicBoundary := by
  intro z h
  exact (OnePoint.infty_ne_coe z h).elim

/--
@isnad1 id=iff.0h1v.s4.a37d32e7bd57 from=translated src=- shape=5593e7c9 vocab=facaa545
-/
theorem compactHyperbolicBoundary_coe (z : ℂ) :
    (z : OnePoint ℂ) ∈ compactHyperbolicBoundary ↔ z.im = 0 := by
  simp [compactHyperbolicBoundary]

/--
@isnad1 id=isclosed.0h0v.s4.d6ddb0d699e9 from=translated src=- shape=545db28e vocab=3bec106d
-/
theorem isClosed_compactHyperbolicBoundary : IsClosed compactHyperbolicBoundary := by
  apply (OnePoint.isClosed_iff_of_mem compactHyperbolicBoundary_infty).mpr
  change IsClosed {z : ℂ | (z : OnePoint ℂ) ∈ compactHyperbolicBoundary}
  simp only [compactHyperbolicBoundary_coe]
  exact isClosed_eq Complex.continuous_im continuous_const

/-- The geometric boundary is compact in the ambient sphere.
@isnad1 id=iscompac.0h0v.s4.47fb40e405e5 from=translated src=- shape=545db28e vocab=406775d4
-/
theorem isCompact_compactHyperbolicBoundary : IsCompact compactHyperbolicBoundary :=
  isClosed_compactHyperbolicBoundary.isCompact

/-- The geometric boundary is precisely the embedded real projective line.
@isnad1 id=eq.0h0v.s3.3cfc8bc8d43b from=translated src=- shape=2a7aa9a6 vocab=200d2909
-/
theorem compactBoundaryEmbedding_range :
    range compactBoundaryEmbedding = compactHyperbolicBoundary := by
  ext p
  cases p with
  | infty =>
    constructor
    · intro _; exact compactHyperbolicBoundary_infty
    · intro _; exact ⟨∞, rfl⟩
  | coe z =>
    rw [compactHyperbolicBoundary_coe]
    constructor
    · rintro ⟨p, hp⟩
      cases p with
      | infty => exact (OnePoint.infty_ne_coe z hp).elim
      | coe x =>
        change ((x : ℂ) : OnePoint ℂ) = (z : OnePoint ℂ) at hp
        have hz := OnePoint.coe_injective hp
        rw [← hz]
        exact Complex.ofReal_im x
    · intro hz
      refine ⟨(z.re : OnePoint ℝ), ?_⟩
      change ((z.re : ℂ) : OnePoint ℂ) = (z : OnePoint ℂ)
      congr 1
      exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using hz.symm)

/-- Boundary inclusion is injective.
@isnad1 id=injectiv.0h0v.s2.32c6b196fa65 from=translated src=- shape=324b2a5c vocab=54e79bb8
-/
theorem compactBoundaryEmbedding_injective : Function.Injective compactBoundaryEmbedding := by
  intro p q hpq
  cases p <;> cases q <;> simp_all [compactBoundaryEmbedding]

/-- The compact real boundary is invariant under the genuine sphere action.
@isnad1 id=mem.1h2v.s7.695763a965c1 from=translated src=- shape=113a089d vocab=8b0eac4a
-/
theorem compactHyperbolicBoundary_smul (g : SL(2, ℝ)) {p : OnePoint ℂ}
    (hp : p ∈ compactHyperbolicBoundary) : g • p ∈ compactHyperbolicBoundary := by
  rw [← compactBoundaryEmbedding_range] at hp ⊢
  obtain ⟨q, rfl⟩ := hp
  exact ⟨g • q, compactBoundaryEmbedding_smul g q⟩

end Singularity
