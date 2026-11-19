/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Cograph.EndpointCuts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/Cograph/ProfileMaximum.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Profile scattering maximum

Manuscript `cog:prop:profile`: for `A ⊆ U` with nonempty cograph remainder
`K = U \ A`, the integer `δ_A = p(K) - |A|` is an upper bound on
`c(U \ T) - |T|` for every `T` with `A ⊆ T ⊆ U`, including remainders with
zero or one component. The container `T_A = A ∪ F(K)` attains the bound and
is the unique largest maximizer. No toughness or Hamiltonicity hypothesis is
imposed on `U`. Truncated natural subtraction is never used for `δ_A`.
-/

universe u


namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Integer scattering `δ_A = p(U \ A) - |A|`. Negative values are retained.-/
noncomputable def profileDelta (U A : Finset V) : ℤ :=
  (pathCoverNumber G (U \ A) : ℤ) - (A.card : ℤ)

/-- Canonical candidate maximizer `T_A = A ∪ F(U \ A)`.-/
noncomputable def profileContainer (U A : Finset V) : Finset V :=
  A ∪ ineligibleSet G (U \ A)

/--
@isnad1 id=eq.2h4v.s6.68a8a483f62f from=translated src=- shape=f3e4aaad vocab=d41ca743
-/
lemma sdiff_eq_nested_sdiff {A T U : Finset V} (hAT : A ⊆ T) (_hTU : T ⊆ U) :
    U \ T = (U \ A) \ (T \ A) := by
  ext x
  simp only [mem_sdiff]
  constructor
  · intro hx
    exact ⟨⟨hx.1, fun hA => hx.2 (hAT hA)⟩, fun hTA => hx.2 hTA.1⟩
  · intro hx
    exact ⟨hx.1.1, fun hT => hx.2 ⟨hT, hx.1.2⟩⟩

/--
@isnad1 id=eq.1h3v.s5.5f3bb98c2048 from=translated src=- shape=5d299d6c vocab=439620f0
-/
lemma card_eq_add_sdiff {A T : Finset V} (hAT : A ⊆ T) :
    T.card = A.card + (T \ A).card := by
  have hdisj : Disjoint A (T \ A) := disjoint_sdiff
  have hunion : A ∪ (T \ A) = T := union_sdiff_of_subset hAT
  have := card_union_of_disjoint (s := A) (t := T \ A) hdisj
  simpa [hunion] using this

/--
@isnad1 id=le.2h5v.s6.b3865e6b8d6f from=translated src=- shape=c4d90fef vocab=f036d22d
-/
lemma profileDelta_le_of_nested {U A T : Finset V}
    (hAT : A ⊆ T) (hTU : T ⊆ U) :
    (componentCount G (U \ T) : ℤ) - (T.card : ℤ) ≤ profileDelta (G := G) U A := by
  have hEq : U \ T = (U \ A) \ (T \ A) := sdiff_eq_nested_sdiff hAT hTU
  have hXsub : T \ A ⊆ U \ A := sdiff_subset_sdiff hTU (subset_refl _)
  have hcle := componentCount_sdiff_le (G := G) (U \ A) (T \ A) hXsub
  have hcard := card_eq_add_sdiff hAT
  simp only [profileDelta, hEq]
  omega

/--
@isnad1 id=le.1h4v.s5.d69bf73b7050 from=translated src=- shape=556a0ed0 vocab=afb278be
-/
lemma profileContainer_subset {U A : Finset V} (hA : A ⊆ U) :
    profileContainer (G := G) U A ⊆ U := by
  intro x hx
  rcases mem_union.1 hx with hA' | hF
  · exact hA hA'
  · exact (mem_sdiff.1 (ineligibleSet_subset (G := G) (U \ A) hF)).1

/--
@isnad1 id=eq.1h4v.s6.11595580dc0d from=translated src=- shape=201e7a90 vocab=9457a5ca
-/
lemma sdiff_profileContainer {U A : Finset V} (hA : A ⊆ U) :
    U \ profileContainer (G := G) U A =
      (U \ A) \ ineligibleSet G (U \ A) := by
  have hF : ineligibleSet G (U \ A) ⊆ U \ A :=
    ineligibleSet_subset (G := G) (U \ A)
  have hAT : A ⊆ profileContainer (G := G) U A := subset_union_left
  have hTU := profileContainer_subset (G := G) hA
  have hnested := sdiff_eq_nested_sdiff hAT hTU
  have hX : profileContainer (G := G) U A \ A = ineligibleSet G (U \ A) := by
    have hdisj : Disjoint A (ineligibleSet G (U \ A)) := by
      refine disjoint_left.2 ?_
      intro x hxA hxF
      exact (mem_sdiff.1 (hF hxF)).2 hxA
    have : (A ∪ ineligibleSet G (U \ A)) \ A = ineligibleSet G (U \ A) := by
      rw [union_sdiff_left, sdiff_eq_left.2 hdisj.symm]
    simpa [profileContainer] using this
  simpa [hX] using hnested

/--
@isnad1 id=eq.1h4v.s6.a5f7b9e1ccb4 from=translated src=- shape=3fcc9289 vocab=d13b4a12
-/
lemma profileContainer_card {U A : Finset V} (_hA : A ⊆ U) :
    (profileContainer (G := G) U A).card =
      A.card + (ineligibleSet G (U \ A)).card := by
  have hdisj : Disjoint A (ineligibleSet G (U \ A)) := by
    refine disjoint_left.2 ?_
    intro x hxA hxF
    exact (mem_sdiff.1
      (ineligibleSet_subset (G := G) (U \ A) hxF)).2 hxA
  simpa [profileContainer] using
    (card_union_of_disjoint (s := A) (t := ineligibleSet G (U \ A)) hdisj)

/-- `T_A` attains `δ_A` on every nonempty cograph remainder.
@isnad1 id=eq.3h4v.s6.114c82244e0f from=translated src=- shape=689db2e2 vocab=ec9d3835
-/
lemma profileContainer_attains {U A : Finset V}
    (hA : A ⊆ U) (hK : IsCograph G (U \ A))
    (_hKne : (U \ A).Nonempty) :
    (componentCount G (U \ profileContainer (G := G) U A) : ℤ) -
      ((profileContainer (G := G) U A).card : ℤ) =
        profileDelta (G := G) U A := by
  have hF := componentCount_sdiff_ineligibleSet_eq (cotreeOn_of_isCograph hK)
  have hrem := sdiff_profileContainer (G := G) hA
  have hcard := profileContainer_card (G := G) hA
  simp only [profileDelta, hrem, hcard]
  omega

/--
@isnad1 id=eq.3h4v.s6.220e214e5f3e from=translated src=- shape=689db2e2 vocab=92a0f156
-/
lemma profileContainer_attains_of_canonical {U A : Finset V}
    (hA : A ⊆ U) (hK : Nikoghosyan.IsCograph G (U \ A))
    (hKne : (U \ A).Nonempty) :
    (componentCount G (U \ profileContainer (G := G) U A) : ℤ) -
      ((profileContainer (G := G) U A).card : ℤ) =
        profileDelta (G := G) U A :=
  profileContainer_attains hA (isCograph_iff.2 hK) hKne

/-- Every maximizer is contained in `T_A`.
@isnad1 id=le.4h5v.s6.c82896efa99a from=translated src=- shape=5839b5a9 vocab=37e4a75e
-/
lemma profile_maximizer_subset_container {U A T : Finset V}
    (hAT : A ⊆ T) (hTU : T ⊆ U) (_hK : IsCograph G (U \ A))
    (hatt :
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
        profileDelta (G := G) U A) :
    T ⊆ profileContainer (G := G) U A := by
  have hEq : U \ T = (U \ A) \ (T \ A) := sdiff_eq_nested_sdiff hAT hTU
  have hXsub : T \ A ⊆ U \ A := sdiff_subset_sdiff hTU (subset_refl _)
  have hcard := card_eq_add_sdiff hAT
  have hcle := componentCount_sdiff_le (G := G) (U \ A) (T \ A) hXsub
  have heqNat :
      componentCount G ((U \ A) \ (T \ A)) =
        pathCoverNumber G (U \ A) + (T \ A).card := by
    simp only [profileDelta, hEq] at hatt
    omega
  have hXinc :=
    eq_cut_bound_imp_subset_ineligible (G := G) (U := U \ A) (X := T \ A)
      hXsub heqNat
  intro x hxT
  by_cases hxA : x ∈ A
  · exact mem_union.2 (Or.inl hxA)
  · exact mem_union.2 (Or.inr (hXinc (mem_sdiff.2 ⟨hxT, hxA⟩)))

/--
@isnad1 id=le.4h5v.s6.c7d22395c5b7 from=translated src=- shape=5839b5a9 vocab=78b0388e
-/
lemma profile_maximizer_subset_container_of_canonical {U A T : Finset V}
    (hAT : A ⊆ T) (hTU : T ⊆ U) (hK : Nikoghosyan.IsCograph G (U \ A))
    (hatt :
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
        profileDelta (G := G) U A) :
    T ⊆ profileContainer (G := G) U A :=
  profile_maximizer_subset_container hAT hTU (isCograph_iff.2 hK) hatt

/-- Packaged profile-scattering maximum: `δ_A` is the exact maximum of
`c(U \ T) - |T|` over `A ⊆ T ⊆ U`, and `T_A` is the unique largest maximizer.
@isnad1 id=and.3h4v.s8.7cf268be0dea from=translated src=- shape=8dcb1e6d vocab=bfaceb97
-/
lemma profile_scattering_maximum {U A : Finset V}
    (hA : A ⊆ U) (hK : IsCograph G (U \ A)) (hKne : (U \ A).Nonempty) :
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) ≤
        profileDelta (G := G) U A) ∧
    ((componentCount G (U \ profileContainer (G := G) U A) : ℤ) -
      ((profileContainer (G := G) U A).card : ℤ) =
        profileDelta (G := G) U A) ∧
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
          profileDelta (G := G) U A →
        T ⊆ profileContainer (G := G) U A) ∧
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
          profileDelta (G := G) U A →
        T.card ≤ (profileContainer (G := G) U A).card) := by
  refine ⟨?_, profileContainer_attains hA hK hKne, ?_, ?_⟩
  · intro T hAT hTU
    exact profileDelta_le_of_nested hAT hTU
  · intro T hAT hTU hatt
    exact profile_maximizer_subset_container hAT hTU hK hatt
  · intro T hAT hTU hatt
    exact card_le_card
      (profile_maximizer_subset_container hAT hTU hK hatt)

/--
@isnad1 id=and.3h4v.s8.8ec18f4fdfa6 from=translated src=- shape=8dcb1e6d vocab=84614a38
-/
lemma profile_scattering_maximum_of_canonical {U A : Finset V}
    (hA : A ⊆ U) (hK : Nikoghosyan.IsCograph G (U \ A))
    (hKne : (U \ A).Nonempty) :
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) ≤
        profileDelta (G := G) U A) ∧
    ((componentCount G (U \ profileContainer (G := G) U A) : ℤ) -
      ((profileContainer (G := G) U A).card : ℤ) =
        profileDelta (G := G) U A) ∧
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
          profileDelta (G := G) U A →
        T ⊆ profileContainer (G := G) U A) ∧
    (∀ T, A ⊆ T → T ⊆ U →
      (componentCount G (U \ T) : ℤ) - (T.card : ℤ) =
          profileDelta (G := G) U A →
        T.card ≤ (profileContainer (G := G) U A).card) :=
  profile_scattering_maximum hA (isCograph_iff.2 hK) hKne

end Cograph
end Nikoghosyan
