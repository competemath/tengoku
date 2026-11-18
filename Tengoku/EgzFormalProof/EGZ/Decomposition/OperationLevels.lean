import Tengoku.EgzFormalProof.EGZ.Decomposition.FaceLevels
import Tengoku.EgzFormalProof.EGZ.Decomposition.CompleteLevels
import Tengoku.EgzFormalProof.EGZ.Decomposition.LevelInjectivity
import Tengoku.EgzFormalProof.EGZ.Decomposition.NormalizedFace
import Tengoku.EgzFormalProof.EGZ.Decomposition.NormalizedComplete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Levels and coordinate injectivity of normalized operations

Reduced restriction leaves the level calculations intact. These wrappers
state the comparisons using the actual normalized subdivision maps, ready
for tracking persistent nodes through an iteration.
-/

namespace EGZ.FlagDecomposition

namespace FaceRefinement

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (Γ : (Φ.flag.polytope anchor).Face) (hp : Odd p)
    (C : ∀ x, IntegerLatticeChart
      ((decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).liftedSupport x))
    (hmod : ∀ x, Function.Injective
      ((Rechart.chart (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/--
@isnad1 id=le.3h8v.s11.ebd027f1fccf from=translated src=- shape=984cb8c6 vocab=55927ef7
-/
theorem normalized_level_le (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node) :
    Φ.level ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).node x) ≤
      (normalized Φ anchor Γ hp C hmod hcenter).level x :=
  Rechart.decomposition_level_le (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp)
    C hp hmod hcenter x.1

/--
@isnad1 id=lt.5h8v.s11.cd9579164d65 from=translated src=- shape=27233e87 vocab=fac8c2a8
-/
theorem normalized_lower_level_lt
    (hΓ : Γ.carrier ⊂ (Φ.flag.polytope anchor).carrier)
    (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node) (hx : x.1.1.1.2 = 0) :
    Φ.level anchor < (normalized Φ anchor Γ hp C hmod hcenter).level x :=
  lower_rechart_level_lt Φ anchor hp Γ C hmod hcenter hΓ x.1 hx

/--
@isnad1 id=eq.6h7v.s11.4744e0df2916 from=translated src=- shape=05fd57d1 vocab=505b490f
-/
theorem normalizedTargetNode_level_eq (hΦ : Φ.IsMinimal)
    (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (normalized Φ anchor Γ hp C hmod hcenter).level
      (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred) = Φ.level anchor :=
  upper_rechart_level_eq Φ anchor hp Γ C hmod hcenter hΦ anchor

/-- Face refinement uses injective charts at every surviving node.
@isnad1 id=injectiv.3h8v.s12.51ab43a8a405 from=translated src=- shape=3526f4ab vocab=dd1395a4
-/
theorem normalizedSubdivisionMap_fibre_injective
    (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node) :
    Function.Injective ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).fibre x) :=
  Rechart.chart_real_injective (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x.1

end FaceRefinement

namespace CompletePreparation

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)
    (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)
    (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/--
@isnad1 id=le.5h10v.s11.33e3bf4a3226 from=translated src=- shape=69d28d01 vocab=57d3e00b
-/
theorem normalized_level_le (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node) :
    Φ.level ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node x) ≤
      (D.normalized hp hδ hsmall C hmod hcenter).level x :=
  D.refined_level_le hp hδ hsmall C hmod hcenter x.1

/--
@isnad1 id=lt.7h10v.s11.190ec928f98c from=translated src=- shape=59be664f vocab=1b817c69
-/
theorem normalized_lower_level_lt (hcount : 0 < D.count)
    (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node) (hx : x.1.1.1.2 = 0) :
    Φ.level anchor < (D.normalized hp hδ hsmall C hmod hcenter).level x :=
  D.lower_refined_level_lt hp hδ hsmall C hmod hcenter hcount x.1 hx

/--
@isnad1 id=lt.7h10v.s10.306f624d0791 from=translated src=- shape=5e879ceb vocab=ca920cb5
-/
theorem normalizedCompleteNode_level_lt_of_not_complete
    (T : ℕ) (hwidth : T ≤ t 1) (hnot : ¬ Φ.IsCompleteElement anchor T δ) :
    Φ.level anchor < (D.normalized hp hδ hsmall C hmod hcenter).level
      (D.normalizedCompleteNode hp hδ hsmall C hmod hcenter) :=
  D.completeNode_level_lt_of_not_complete hp hδ hsmall C hmod hcenter T hwidth hnot

/-- At a persistent level, forgetting added coordinates is injective on
the whole real coordinate space of the surviving normalized node.
@isnad1 id=injectiv.6h10v.s12.e73bd0ce8eb5 from=translated src=- shape=9fc97196 vocab=11c912c2
-/
theorem normalizedSubdivisionMap_fibre_injective_of_level_eq
    (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node)
    (hlevel : Φ.level ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node x) =
      (D.normalized hp hδ hsmall C hmod hcenter).level x) :
    Function.Injective ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).fibre x) := by
  exact Φ.representation.factor_real_injective_of_level_eq
    (D.normalized hp hδ hsmall C hmod hcenter).representation
    ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node x) x
    (Augmented.forget (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction hp
      (D.extra_antitone hp hδ hsmall) C x.1)
    (D.refined_space_le_original hp hδ hsmall C hmod hcenter x.1)
    (fun v hv ↦ (D.refined_forget_map hp hδ hsmall C hmod hcenter x.1 v hv).symm) hlevel

end CompletePreparation
end EGZ.FlagDecomposition
