import Tengoku.Q1LeanVerification.Q1.PackedAveraging
import Tengoku.Q1LeanVerification.Q1.RegularFaithfulness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Separate full SRD and RD conclusions for actual closed two-sided ideal
simplicity of the reduced group C*-algebra. The route is direct averaging,
using logarithmic packing, norm density and faithful identity-vector evaluation. -/

noncomputable section
namespace Q1
variable {G : Type*} [Group G]

/-- Finite convolution averages converge toward the identity coefficient.
@isnad1 id=ex.3h4v.s12.d10b3adc7441 from=translated src=- shape=89526e65 vocab=d8fad9f9
-/
theorem finite_coefficient_averaging (L : LengthBall G)
    (hR : AmenableNormalCover (⊥ : Subgroup G)) (hsrd : ReducedSRD L)
    (f : G →₀ ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ t : Fin N → G,
      ‖conjugationAverage regularRepresentation t (regularConvolution f) -
        f 1 • (1 : RegularOperator G)‖ < ε := by
  classical
  let f₀ : G →₀ ℂ := f - Finsupp.single 1 (f 1)
  have hf₀ : f₀ 1 = 0 := by simp [f₀]
  obtain ⟨N, hN, t, ht⟩ := finite_zero_identity_averaging L hR hsrd f₀ hf₀ ε hε
  have he : regularConvolution f₀ = regularConvolution f - f 1 • (1 : RegularOperator G) := by
    apply eq_sub_iff_add_eq.mpr
    have hsingle : f 1 • (1 : RegularOperator G) =
        regularConvolution (Finsupp.single (1 : G) (f 1)) := by
      rw [regularConvolution_single, leftRegular_one_eq_one]
    rw [hsingle, ← regularConvolution_add]
    simp [f₀]
  refine ⟨N, hN, t, ?_⟩
  simpa only [he, conjugationAverage_sub, conjugationAverage_smul,
    conjugationAverage_one regularRepresentation t hN] using ht

/-- Coercion preserves the same finite conjugation average and operator norm.
@isnad1 id=eq.0h4v.s14.7c3e487cc7eb from=translated src=- shape=b62237f9 vocab=14060c17
-/
theorem reduced_conjugationAverage_coe {N : ℕ} (t : Fin N → G)
    (a : ReducedGroupCStarAlgebra G) :
    (conjugationAverage (A := ReducedGroupCStarAlgebra G) reducedLeftRegular t a : RegularOperator G) =
      conjugationAverage regularRepresentation t (a : RegularOperator G) := by
  simp [conjugationAverage]

/-- Finite coefficient operators are dense inside the actual completed algebra.
@isnad1 id=dense.0h1v.s14.766d52cc722c from=translated src=- shape=720088a1 vocab=3aa005f6
-/
theorem dense_reducedPolynomial : Dense (Set.range (reducedPolynomial (G := G))) := by
  intro a
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨f, hf⟩ := exists_reducedPolynomial_near a hε
  exact ⟨reducedPolynomial f, ⟨f, rfl⟩, by simpa [dist_eq_norm, norm_sub_rev] using hf⟩

/-- Ordinary SRD and trivial radical imply the direct averaging property in C*_r(G).
@isnad1 id=hasconju.2h2v.s12.5e753b48c066 from=translated src=- shape=2c95b0b4 vocab=f0bb9b4a
-/
theorem reducedGroup_hasConjugationAveraging (L : LengthBall G)
    (hR : AmenableNormalCover (⊥ : Subgroup G)) (hsrd : ReducedSRD L) :
    HasConjugationAveraging (reducedLeftRegular (G := G)) reducedVectorState := by
  have hτ : ∀ a : ReducedGroupCStarAlgebra G, ‖reducedVectorState a‖ ≤ ‖a‖ := by
    intro a
    change ‖regularVectorState (a : RegularOperator G)‖ ≤ ‖(a : RegularOperator G)‖
    exact norm_regularVectorState_apply_le _
  apply hasConjugationAveraging_of_dense (A := ReducedGroupCStarAlgebra G)
    (reducedLeftRegular (G := G)) (reducedVectorState (G := G))
    (fun g => (norm_reducedLeftRegular g).le) hτ
    (Set.range (reducedPolynomial (G := G))) dense_reducedPolynomial
  rintro a ⟨f, rfl⟩ ε hε
  obtain ⟨N, hN, t, ht⟩ := finite_coefficient_averaging L hR hsrd f ε hε
  refine ⟨N, hN, t, ?_⟩
  rw [reducedVectorState_reducedPolynomial]
  change ‖(conjugationAverage (A := ReducedGroupCStarAlgebra G) reducedLeftRegular t
    (reducedPolynomial f) : RegularOperator G) - f 1 • (1 : RegularOperator G)‖ < ε
  rw [reduced_conjugationAverage_coe]
  exact ht

/-- Full actual closed-ideal simplicity under ordinary reduced-norm SRD and a
trivial normal-amenability cover, in the specified proper group length.
@isnad1 id=cstarsim.2h2v.s13.7812a531a660 from=translated src=- shape=44b44c65 vocab=44fd5d8a
-/
theorem cStarSimple_of_reducedSRD (L : LengthBall G)
    (hR : AmenableNormalCover (⊥ : Subgroup G)) (hsrd : ReducedSRD L) :
    CStarSimple (ReducedGroupCStarAlgebra G) :=
  cStarSimple_of_conjugationAveraging reducedLeftRegular reducedVectorState
    reducedVectorState_faithful (reducedGroup_hasConjugationAveraging L hR hsrd)

/-- The separate polynomial RD conclusion, via the proved RD-to-ordinary-SRD implication.
@isnad1 id=cstarsim.2h2v.s13.513eb3c6c87b from=translated src=- shape=44b44c65 vocab=7e3f48d4
-/
theorem cStarSimple_of_reducedRD (L : LengthBall G)
    (hR : AmenableNormalCover (⊥ : Subgroup G)) (hrd : ReducedRD L) :
    CStarSimple (ReducedGroupCStarAlgebra G) :=
  cStarSimple_of_reducedSRD L hR hrd.subrapid

/-- Q1-SRD for the exact shortest length of a finite symmetric generating set.
The limit is the ordinary full-sequence logarithmic limit; the algebra is C*_r(G).
@isnad1 id=cstarsim.4h2v.s13.98795d4f59ef from=translated src=- shape=80fba686 vocab=b4d425ba
-/
theorem q1_srd (S : Finset G) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hR : IsAmenableRadical (⊥ : Subgroup G))
    (hsrd : ReducedSRD (wordLengthBall S hsym hgen)) :
    CStarSimple (ReducedGroupCStarAlgebra G) :=
  cStarSimple_of_reducedSRD (wordLengthBall S hsym hgen) hR.maximal hsrd

/-- Q1-RD remains a separate polynomial-bound theorem in the same exact word length.
@isnad1 id=cstarsim.4h2v.s13.a6146064bdb2 from=translated src=- shape=80fba686 vocab=1064cb55
-/
theorem q1_rd (S : Finset G) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hR : IsAmenableRadical (⊥ : Subgroup G))
    (hrd : ReducedRD (wordLengthBall S hsym hgen)) :
    CStarSimple (ReducedGroupCStarAlgebra G) :=
  cStarSimple_of_reducedRD (wordLengthBall S hsym hgen) hR.maximal hrd

end Q1
