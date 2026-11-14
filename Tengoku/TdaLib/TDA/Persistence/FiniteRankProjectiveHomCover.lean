import Tengoku.TdaLib.TDA.Persistence.FiniteRankProjectiveHomFullyFaithful
import Tengoku.TdaLib.TDA.Persistence.FiniteRankProjectiveResolutionKan
import Tengoku.TdaLib.TDA.Persistence.FiniteRankProjectiveResolutionKanExamples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Minimal rank-projective covers through the hook-generator Hom functor

For a pointwise finite-dimensional source, a rank-projective cover is exactly
an ordinary projective epimorphism of hook-generator Hom modules satisfying
the categorical right-minimality condition. The reverse implication derives
pointwise surjectivity from the principal-upset summands of the generator.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveHomCover

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open TDA.Persistence.FiniteRankProjectiveHomExact
open TDA.Persistence.FiniteRankProjectiveHomFullyFaithful

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

private abbrev F := homFunctor (k := k) (S := S)
private abbrev E := HomScalars (k := k) (S := S)
private abbrev L := FiniteRankProjectiveEndAlgebra.HookSum (k := k) (S := S)

/-- The actual Hom functor preserves and reflects invertibility of persistence
endomorphisms.
@isnad1 id=iff.0h4v.s10.3f3d0563bff2 from=translated src=- shape=76553c60 vocab=01cf9451
-/
theorem isIso_map_iff {A : PModule.{u,0,u} k S} (t : End A) :
    IsIso ((F (k := k) (S := S)).map t) ↔ IsIso t := by
  constructor
  · intro h
    letI : IsIso ((F (k := k) (S := S)).map t) := h
    exact isIso_of_fully_faithful (F (k := k) (S := S)) t
  · intro h
    letI : IsIso t := h
    exact (F (k := k) (S := S)).map_isIso t

/-- The equation fixing a quotient is reflected by the actual Hom functor.
@isnad1 id=iff.0h6v.s11.4da3a9189013 from=translated src=- shape=4c63201c vocab=d0d33a91
-/
theorem map_comp_eq_map_iff {A B : PModule.{u,0,u} k S}
    (π : A ⟶ B) (t : End A) :
    ((F (k := k) (S := S)).map t) ≫ ((F (k := k) (S := S)).map π) =
      (F (k := k) (S := S)).map π ↔ t ≫ π = π := by
  rw [← (F (k := k) (S := S)).map_comp]
  exact (F (k := k) (S := S)).map_injective.eq_iff

/-- Right minimality of a persistence quotient agrees with right minimality
of its actual hook-generator Hom map.
@isnad1 id=iff.0h5v.s11.c0b47a490389 from=translated src=- shape=abb92811 vocab=0b502f25
-/
theorem rightMinimal_iff {A B : PModule.{u,0,u} k S} (π : A ⟶ B) :
    (∀ t : End A, t ≫ π = π → IsIso t) ↔
      (∀ T : End ((F (k := k) (S := S)).obj A),
        T ≫ (F (k := k) (S := S)).map π =
          (F (k := k) (S := S)).map π → IsIso T) := by
  constructor
  · intro h T hT
    let t : End A := (F (k := k) (S := S)).preimage T
    have htmap : (F (k := k) (S := S)).map t = T :=
      (F (k := k) (S := S)).map_preimage T
    have ht : t ≫ π = π :=
      (map_comp_eq_map_iff (k := k) (S := S) π t).mp (htmap ▸ hT)
    rw [← htmap]
    exact (isIso_map_iff (k := k) (S := S) t).mpr (h t ht)
  · intro h t ht
    apply (isIso_map_iff (k := k) (S := S) t).mp
    exact h _ ((map_comp_eq_map_iff (k := k) (S := S) π t).mpr ht)

/-- Surjectivity of Hom postcomposition forces every component of the
persistence quotient to be surjective.
@isnad1 id=surjecti.1h6v.s11.a5de0505e504 from=translated src=- shape=25b50107 vocab=05fe787a
-/
theorem pointwise_surjective_of_postcompose_surjective
    {A B : PModule.{u,0,u} k S} (π : A ⟶ B)
    (hsurj : Function.Surjective (postcompose (k := k) (S := S) π))
    (a : S) : Function.Surjective (π.app a).hom := by
  intro x
  obtain ⟨g, hg⟩ := hsurj (encode B a x)
  let y : A.obj a :=
    (((inclusion (k := k) (S := S) a ≫ g).app a).hom (HookInfinity.birth a))
  refine ⟨y, ?_⟩
  have hg' : g ≫ π = encode B a x := hg
  have h := congrArg (fun f : L (k := k) (S := S) ⟶ B =>
    (((inclusion (k := k) (S := S) a ≫ f).app a).hom
      (HookInfinity.birth a))) hg'
  change (π.app a).hom y =
    (((inclusion (k := k) (S := S) a ≫ encode B a x).app a).hom
      (HookInfinity.birth a)) at h
  rw [encode_birth] at h
  exact h

/-- A pointwise finite-dimensional rank-projective cover is precisely a
projective, surjective and right-minimal map under the actual Hom functor.
@isnad1 id=iff.1h5v.s12.bbe19a8e61a5 from=translated src=- shape=84954377 vocab=4e1368bc
-/
theorem rankProjectiveCover_iff {A B : PModule.{u,0,u} k S}
    (π : A ⟶ B) (hfd : ∀ a, FiniteDimensional k (A.obj a)) :
    IsRankProjectiveCover π ↔
      Module.Projective (E (k := k) (S := S))
        (L (k := k) (S := S) ⟶ A) ∧
      Function.Surjective (postcompose (k := k) (S := S) π) ∧
      (∀ T : End ((F (k := k) (S := S)).obj A),
        T ≫ (F (k := k) (S := S)).map π =
          (F (k := k) (S := S)).map π → IsIso T) := by
  constructor
  · intro h
    refine ⟨(rankProjective_iff_homProjective A hfd).mp h.term_rank_projective,
      ?_, (rightMinimal_iff π).mp h.endomorphism_isIso⟩
    exact (rankExact_iff_postcompose_surjective
      h.row_rank_exact.toIsPointwiseShortExact hfd).mp h.row_rank_exact
  · rintro ⟨hproj, hsurj, hmin⟩
    have hpoint : ∀ a, Function.Surjective (π.app a).hom :=
      pointwise_surjective_of_postcompose_surjective π hsurj
    have hshort : IsPointwiseShortExact (kernel.ι π) π :=
      RankKernel.shortExact π hpoint
    refine ⟨(rankProjective_iff_homProjective A hfd).mpr hproj, ?_,
      (rightMinimal_iff π).mpr hmin⟩
    exact (rankExact_iff_postcompose_surjective hshort hfd).mpr hsurj

/-- Every certified minimal resolution row becomes an ordinary right-minimal
projective epimorphism of hook-generator Hom modules.
@isnad1 id=and.0h5v.s12.ea76f5594ce1 from=translated src=- shape=ae50d294 vocab=d0ffebab
-/
theorem minimalResolution_row_homCover
    {M : PModule.{u,0,u} k S}
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (i : Fin R.resolution.length) :
    Module.Projective (E (k := k) (S := S))
      (L (k := k) (S := S) ⟶ R.resolution.term i) ∧
    Function.Surjective (postcompose (k := k) (S := S)
      (R.resolution.quotient i)) ∧
    (∀ T : End ((F (k := k) (S := S)).obj (R.resolution.term i)),
      T ≫ (F (k := k) (S := S)).map (R.resolution.quotient i) =
        (F (k := k) (S := S)).map (R.resolution.quotient i) → IsIso T) := by
  exact (rankProjectiveCover_iff (R.resolution.quotient i)
    (R.resolution.row_rank_exact i).finiteDimensional).mp (R.quotient_is_cover i)

end

namespace Examples

private noncomputable abbrev QF := F (k := ℚ) (S := Fin 2)
private abbrev QE := E (k := ℚ) (S := Fin 2)
private noncomputable abbrev QL := L (k := ℚ) (S := Fin 2)

/-- The zero identity cover satisfies the ordinary Hom cover conditions.
@isnad1 id=and.0h0v.s14.f5bc837315ef from=translated src=- shape=2f8b8333 vocab=fd183f69
-/
theorem zero_identity_homCover :
    Module.Projective QE (QL ⟶ (0 : PModule ℚ (Fin 2))) ∧
    Function.Surjective (postcompose (k := ℚ) (S := Fin 2)
      (𝟙 (0 : PModule ℚ (Fin 2)))) ∧
    (∀ T : End (QF.obj (0 : PModule ℚ (Fin 2))),
      T ≫ QF.map (𝟙 (0 : PModule ℚ (Fin 2))) =
        QF.map (𝟙 (0 : PModule ℚ (Fin 2))) → IsIso T) := by
  exact (rankProjectiveCover_iff (k := ℚ) (S := Fin 2)
    (𝟙 (0 : PModule ℚ (Fin 2))) (by intro a; infer_instance)).mp
    FiniteRankProjectiveResolutionKanExamples.zero_identity_isRankProjectiveCover

/-- The nonzero principal upset identity cover satisfies the ordinary Hom
conditions, and its birth fiber has a nonzero vector.
@isnad1 id=and.0h1v.s13.53f5b6cc8fe7 from=translated src=- shape=f6ef423f vocab=bf117c28
-/
theorem principalUpset_identity_homCover (a : Fin 2) :
    (Module.Projective QE (QL ⟶ HookInfinity.module (R := ℚ) a) ∧
    Function.Surjective (postcompose (k := ℚ) (S := Fin 2)
      (𝟙 (HookInfinity.module (R := ℚ) a))) ∧
    (∀ T : End (QF.obj (HookInfinity.module (R := ℚ) a)),
      T ≫ QF.map (𝟙 (HookInfinity.module (R := ℚ) a)) =
        QF.map (𝟙 (HookInfinity.module (R := ℚ) a)) → IsIso T)) ∧
    ∃ x : (HookInfinity.module (R := ℚ) a).obj a, x ≠ 0 := by
  constructor
  · exact (rankProjectiveCover_iff (k := ℚ) (S := Fin 2)
      (𝟙 (HookInfinity.module (R := ℚ) a)) (by intro p; infer_instance)).mp
      (FiniteRankProjectiveResolutionKanExamples.principalUpset_identity_isRankProjectiveCover a)
  · exact (FiniteRankProjectiveResolutionKanExamples.principalUpset_identity_iso_minimal_cover a).2

end Examples

end TDA.Persistence.FiniteRankProjectiveHomCover
