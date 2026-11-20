import Tengoku.Q1LeanVerification.Q1.RadicalCover
import Tengoku.Q1LeanVerification.Q1.FoelnerExtension
import Tengoku.Q1LeanVerification.Q1.FoelnerCommutative
import Tengoku.Q1LeanVerification.Q1.ConjugacyPackingObstruction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The complete radical-to-exponential-conjugacy-growth argument of written
Lemma 1, using explicit invariant probabilities on all subsets as the
amenability convention. Its application to confinement still requires the
subgroup-volume bound; no reduced C*-algebra or URS theorem is asserted here. -/

namespace Q1

variable {G : Type*} [Group G]

/-- The center is Følner, so a Følner center quotient makes the full group Følner.
@isnad1 id=finitefo.1h1v.s4.c1e64140d207 from=translated src=- shape=0fccc1d0 vocab=f02c175d
-/
theorem finiteFoelner_of_center_quotient (h : FiniteFoelner (G ⧸ Subgroup.center G)) :
    FiniteFoelner G :=
  finiteFoelner_extension (Subgroup.center G) (finiteFoelner_center G) h

/-- A non-Følner normal closure provides an actual finite conjugate tuple
whose center quotient is non-Følner.
@isnad1 id=nonfoeln.1h2v.s5.00b47b1d8dfc from=translated src=- shape=e5ddac08 vocab=6ddd3a96
-/
theorem quotient_witness_of_not_finiteFoelner_normalClosure (g : G)
    (hnot : ¬ FiniteFoelner (Subgroup.normalClosure ({g} : Set G))) :
    NonFoelnerCenterQuotientWitness g := by
  obtain ⟨A, k, hk, x, u, hgen, hx, hA⟩ := exists_conjugate_tuple_not_finiteFoelner g hnot
  refine ⟨A, k, hk, x, u, hgen, hx, ?_⟩
  exact fun hQ => hA (finiteFoelner_of_center_quotient hQ)

/-- The exact normal-amenability domination property is sufficient for the
algebraic witness; neither amenability nor normality of R itself is needed.
@isnad1 id=nonfoeln.2h3v.s5.883df5288721 from=translated src=- shape=ca359bd4 vocab=56324d7c
-/
theorem quotient_witness_of_amenableNormalCover (R : Subgroup G)
    (hR : AmenableNormalCover R) (g : G) (hg : g ∉ R) :
    NonFoelnerCenterQuotientWitness g :=
  quotient_witness_of_not_finiteFoelner_normalClosure g
    (not_finiteFoelner_normalClosure_of_amenableNormalCover R hR g hg)

/-- Every element outside a normal-amenability cover has a uniform exponential
rooted conjugacy-volume lower bound, at all natural radii in the same length.
@isnad1 id=ex.2h4v.s6.f5faa8b293f4 from=translated src=- shape=89315793 vocab=78ff1529
-/
theorem exponential_conjugacy_growth_of_amenableNormalCover
    (L : LengthBall G) (R : Subgroup G) (hR : AmenableNormalCover R)
    (g : G) (hg : g ∉ R) :
    ∃ c δ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < δ ∧
      ∀ r : ℕ, c * Real.exp (δ * r) ≤ ((conjugacyBall L g r).card : ℝ) :=
  exponential_conjugacy_growth_of_witness L g
    (quotient_witness_of_amenableNormalCover R hR g hg)

/-- Written Lemma 1 for a supplied amenable radical with its full defining
properties. The mean is a finitely additive probability on all subsets.
@isnad1 id=ex.2h4v.s6.6d6be43be1d7 from=translated src=- shape=89315793 vocab=7c20bf48
-/
theorem exponential_conjugacy_growth_outside_radical
    (L : LengthBall G) (R : Subgroup G) (hR : IsAmenableRadical R)
    (g : G) (hg : g ∉ R) :
    ∃ c δ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < δ ∧
      ∀ r : ℕ, c * Real.exp (δ * r) ≤ ((conjugacyBall L g r).card : ℝ) :=
  exponential_conjugacy_growth_of_amenableNormalCover L R hR.maximal g hg

/-- The concrete finite symmetric generating-set version, with the exact
shortest-word length constructed in the preceding batch.
@isnad1 id=ex.4h4v.s7.63e523acb921 from=translated src=- shape=ce23d024 vocab=475983c3
-/
theorem exponential_conjugacy_growth_wordLength
    (S : Finset G) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (R : Subgroup G) (hR : IsAmenableRadical R) (g : G) (hg : g ∉ R) :
    ∃ c δ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < δ ∧ ∀ r : ℕ,
      c * Real.exp (δ * r) ≤
        ((conjugacyBall (wordLengthBall S hsym hgen) g r).card : ℝ) :=
  exponential_conjugacy_growth_outside_radical (wordLengthBall S hsym hgen) R hR g hg

/-- At the trivial subgroup the radical structure requires exactly normal
amenability domination: its other two defining properties are proved here.
@isnad1 id=iff.0h1v.s4.6aef7a0d0b26 from=translated src=- shape=2d0d2dce vocab=c66ae9f0
-/
theorem isAmenableRadical_bot_iff :
    IsAmenableRadical (⊥ : Subgroup G) ↔ AmenableNormalCover (⊥ : Subgroup G) := by
  constructor
  · exact fun h => h.maximal
  · intro h
    exact ⟨inferInstance, hasInvariantMean_of_finiteFoelner finiteFoelner_of_finite, h⟩

/-- Ordinary SRD obstruction after removing the prior exponential-growth input.
The witness excludes identity explicitly. The finite confinement and subgroup
volume bound remain inputs; this is not a C*-simplicity theorem.
@isnad1 id=false.6h5v.s6.76ff81209948 from=translated src=- shape=a9c09544 vocab=57fa573e
-/
theorem no_confined_subgroup_of_trivial_radical_srd_volume [DecidableEq G]
    (L : LengthBall G) (hR : AmenableNormalCover (⊥ : Subgroup G))
    (H : Subgroup G) (P : Finset G) (hP : 1 ∉ P) (hconf : ConfinedBy H P)
    (ρ : ℕ → ℝ) (hρ : ∀ r, 0 ≤ ρ r) (hsrd : OrdinarySRD ρ)
    (hvolume : ∀ r, ((subgroupBall L H r).card : ℝ) ≤ (ρ r) ^ 2) : False := by
  apply no_confined_subgroup_of_quotient_witnesses_and_srd_volume
    L H P hconf _ ρ hρ hsrd hvolume
  intro g hg
  apply quotient_witness_of_amenableNormalCover (⊥ : Subgroup G) hR g
  intro hbot
  have he : g = 1 := Subgroup.mem_bot.mp hbot
  exact hP (he ▸ hg)

/-- The polynomial-RD version is a separate corollary, obtained via the proved
polynomial-bound-to-ordinary-SRD implication.
@isnad1 id=false.6h5v.s7.03c47fdd79c3 from=translated src=- shape=0b4dfa34 vocab=5b3267b6
-/
theorem no_confined_subgroup_of_trivial_radical_rd_volume [DecidableEq G]
    (L : LengthBall G) (hR : AmenableNormalCover (⊥ : Subgroup G))
    (H : Subgroup G) (P : Finset G) (hP : 1 ∉ P) (hconf : ConfinedBy H P)
    (ρ : ℕ → ℝ) (hρ : ∀ r, 0 ≤ ρ r)
    (hRD : ∃ C : ℝ, 0 < C ∧ ∃ d : ℝ, 0 ≤ d ∧
      ∀ r : ℕ, ρ r ≤ C * (1 + (r : ℝ)) ^ d)
    (hvolume : ∀ r, ((subgroupBall L H r).card : ℝ) ≤ (ρ r) ^ 2) : False := by
  obtain ⟨C, hC, d, hd, hbound⟩ := hRD
  exact no_confined_subgroup_of_trivial_radical_srd_volume L hR H P hP hconf
    ρ hρ (ordinarySRD_of_polynomial_bound ρ C d hbound) hvolume

end Q1
