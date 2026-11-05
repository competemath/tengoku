import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import Tengoku.Seed.AlgebraicGeometry.FunctionField
import Tengoku.Seed.AlgebraicGeometry.Noetherian
import Tengoku.Seed.AlgebraicGeometry.Normalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normalization in a specified extension of the function field

For an integral scheme `X` and a field extension `L / X.functionField`, the actual
morphism `Spec L → X` factors through Mathlib's relative normalization. Its affine
charts are spectra of integral closures. This construction applies to the same
underlying scheme of a curve; it does not choose a covering curve from an existence
theorem. No Noetherian hypothesis on `X` is needed for the construction: `Spec L`
itself is Noetherian and therefore its morphism to `X` is quasi-compact.

The projection is integral and surjective, and the constructed scheme is integral
and connected. Finiteness for finite field extensions, identification of its
function field with `L`, normality, and the smooth projective curve properties are
separate obligations. In particular, this file does not package a
`SmoothProjectiveCurve` using unproved geometric properties.

Used for the generic weighted lift and the ramified cover (§3 of the paper). Construction
source: Stacks Project, `morphisms.tex`, `definition-normalization-X-in-Y` and
`lemma-characterize-normalization` (relative normalization).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Covers

universe u

variable (X : Scheme.{u}) [IsIntegral X]
variable (L : Type u) [Field L] [Algebra X.functionField L]

/-- The specified field extension maps to `X` through its actual generic stalk.-/
def curveExtensionGenericMap : Spec (CommRingCat.of L) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
    X.fromSpecStalk (genericPoint X)

/-- Every point of the extension field spectrum maps to the generic point of `X`.
@isnad1 id=eq.0h3v.s8.a124e19e288e from=translated src=- shape=659484c2 vocab=4bd0af8a
-/
theorem curveExtensionGenericMap_apply (p : Spec (CommRingCat.of L)) :
    curveExtensionGenericMap X L p = genericPoint X := by
  change X.fromSpecStalk (genericPoint X)
    (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) p) = genericPoint X
  have hp : Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) p =
      IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
  rw [hp]
  exact X.fromSpecStalk_closedPoint

/-- Nonempty opens contain the generic point, so their inverse images are the whole spectrum.
@isnad1 id=eq.0h3v.s8.deb6cf9eec21 from=translated src=- shape=75ad80f8 vocab=1e73fb25
-/
theorem curveExtensionGenericMap_preimage_of_nonempty (U : X.Opens) [Nonempty U] :
    curveExtensionGenericMap X L ⁻¹ᵁ U = ⊤ := by
  apply le_antisymm le_top
  intro p _
  change curveExtensionGenericMap X L p ∈ U
  rw [curveExtensionGenericMap_apply]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
    simpa using (inferInstance : Nonempty U))

/--
@isnad1 id=quasicom.0h2v.s5.c5249bd433a4 from=translated src=- shape=25d578cb vocab=47d20936
-/
instance curveExtensionGenericMap_quasiCompact : QuasiCompact (curveExtensionGenericMap X L) :=
  inferInstance

/--
@isnad1 id=quasisep.0h2v.s5.77a9e91a4eff from=translated src=- shape=25d578cb vocab=b6433795
-/
instance curveExtensionGenericMap_quasiSeparated : QuasiSeparated (curveExtensionGenericMap X L) :=
  inferInstance

/--
@isnad1 id=isdomina.0h2v.s5.ef14ea936ea8 from=translated src=- shape=25d578cb vocab=43de5f63
-/
instance curveExtensionGenericMap_dominant : IsDominant (curveExtensionGenericMap X L) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec X).def]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint L, curveExtensionGenericMap_apply X L _⟩

/-- The actual glued relative normalization of `X` in the specified field extension.-/
def curveFieldNormalization : Scheme.{u} := (curveExtensionGenericMap X L).normalization

/-- The canonical integral projection to the original scheme.-/
def curveFieldNormalizationMap : curveFieldNormalization X L ⟶ X :=
  (curveExtensionGenericMap X L).fromNormalization

/-- The canonical dominant map from the extension field spectrum.-/
def curveFieldNormalizationGenericMap :
    Spec (CommRingCat.of L) ⟶ curveFieldNormalization X L :=
  (curveExtensionGenericMap X L).toNormalization

/--
@isnad1 id=isintegr.0h2v.s5.0a14466176ce from=translated src=- shape=22dda912 vocab=e2938d04
-/
instance curveFieldNormalization_integral : IsIntegral (curveFieldNormalization X L) :=
  inferInstanceAs (IsIntegral (curveExtensionGenericMap X L).normalization)

/--
@isnad1 id=isintegr.0h2v.s5.9b59ebc6261a from=translated src=- shape=b3f164f4 vocab=1b9e123e
-/
instance curveFieldNormalizationMap_integral : IsIntegralHom (curveFieldNormalizationMap X L) :=
  inferInstanceAs (IsIntegralHom (curveExtensionGenericMap X L).fromNormalization)

/--
@isnad1 id=isdomina.0h2v.s5.2898e97cc54d from=translated src=- shape=c89346e3 vocab=37c81e58
-/
instance curveFieldNormalizationGenericMap_dominant :
    IsDominant (curveFieldNormalizationGenericMap X L) :=
  inferInstanceAs (IsDominant (curveExtensionGenericMap X L).toNormalization)

/-- The two canonical arrows factor the original generic extension morphism.
@isnad1 id=eq.0h2v.s6.910a99967995 from=translated src=- shape=1eeac029 vocab=4837850d
-/
theorem curveFieldNormalization_factorization :
    curveFieldNormalizationGenericMap X L ≫ curveFieldNormalizationMap X L =
      curveExtensionGenericMap X L :=
  (curveExtensionGenericMap X L).toNormalization_fromNormalization

/--
@isnad1 id=isdomina.0h2v.s5.079be40173c4 from=translated src=- shape=b3f164f4 vocab=0902866c
-/
instance curveFieldNormalizationMap_dominant : IsDominant (curveFieldNormalizationMap X L) := by
  have : IsDominant
      (curveFieldNormalizationGenericMap X L ≫ curveFieldNormalizationMap X L) := by
    rw [curveFieldNormalization_factorization]
    infer_instance
  exact IsDominant.of_comp (curveFieldNormalizationGenericMap X L) (curveFieldNormalizationMap X L)

/-- Sections over a lifted affine open are the actual integral closure in sections
of the same field spectrum. On nonempty opens that ambient open is the whole spectrum,
as recorded by `curveExtensionGenericMap_preimage_of_nonempty`.-/
def curveFieldNormalizationSectionsIso (U : X.Opens) (hU : IsAffineOpen U) :
    letI := ((curveExtensionGenericMap X L).app U).hom.toAlgebra
    Γ(curveFieldNormalization X L, curveFieldNormalizationMap X L ⁻¹ᵁ U) ≅
      CommRingCat.of (integralClosure Γ(X, U)
        Γ(Spec (CommRingCat.of L), curveExtensionGenericMap X L ⁻¹ᵁ U)) :=
  (curveExtensionGenericMap X L).normalizationObjIso hU

/-- The universal property among integral factorizations of the same extension morphism,
including both commuting triangles and uniqueness.
@isnad1 id=existsun.1h5v.s7.1b3ff3e04af7 from=translated src=- shape=b1ffaab9 vocab=0a2691eb
-/
theorem curveFieldNormalization_universal
    {T : Scheme.{u}} (a : Spec (CommRingCat.of L) ⟶ T) (b : T ⟶ X)
    [IsIntegralHom b] (h : curveExtensionGenericMap X L = a ≫ b) :
    ∃! d : curveFieldNormalization X L ⟶ T,
      curveFieldNormalizationGenericMap X L ≫ d = a ∧ d ≫ b = curveFieldNormalizationMap X L := by
  refine ⟨(curveExtensionGenericMap X L).normalizationDesc a b h, ?_, ?_⟩
  · exact ⟨(curveExtensionGenericMap X L).toNormalization_normalizationDesc a b h,
      (curveExtensionGenericMap X L).normalizationDesc_comp a b h⟩
  · intro d hd
    apply Scheme.Hom.normalization.hom_ext (curveExtensionGenericMap X L) d
      ((curveExtensionGenericMap X L).normalizationDesc a b h) b
    · exact hd.1.trans
        ((curveExtensionGenericMap X L).toNormalization_normalizationDesc a b h).symm
    · exact hd.2
    · exact (curveExtensionGenericMap X L).normalizationDesc_comp a b h

variable {k : Type u} [Field k]

/-- The normalization carries the base-field structure induced by its canonical projection.-/
def curveFieldNormalizationOver (C : AlgebraicGeometry.Proj.SchemeOver k) [IsIntegral C.scheme]
    (L : Type u) [Field L] [Algebra C.scheme.functionField L] : AlgebraicGeometry.Proj.SchemeOver k where
  scheme := curveFieldNormalization C.scheme L
  toBase := curveFieldNormalizationMap C.scheme L ≫ C.toBase

end AlgebraicGeometry.Scheme.Covers
