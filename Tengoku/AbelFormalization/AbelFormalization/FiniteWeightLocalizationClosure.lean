import Tengoku.AbelFormalization.AbelFormalization.FiniteWeightLocalization
import Tengoku.AbelFormalization.AbelFormalization.LocalizedSubmoduleClearing
import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Contraction from a localized finite-weight product

A submodule of the coordinatewise localization has a canonical saturated
contraction to the original finite product.  This file records that extension
and contraction are inverse on localized submodules, and transports
homogeneity and invariance under a localized triangular equivalence back to
the original product.

For a finite ambient module over a Noetherian ring, the contraction is
finitely generated.  Equality after localization then gives a single
denominator which sandwiches any original submodule between a multiple of
the contraction and the contraction itself.
-/

noncomputable section

namespace AbelFormalization

open scoped Pointwise

variable {R : Type*} [CommRing R] {n : ℕ}
variable {M : Fin n → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The saturated contraction of a submodule of the coordinatewise
localization to the original finite product.-/
def finiteWeightLocalizationContraction
    (S : Submonoid R)
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i))) :
    Submodule R (∀ i, M i) :=
  (L.restrictScalars R).comap
    (finiteWeightLocalizationMap (M := M) S)

/--
@isnad1 id=iff.0h6v.s10.4f86f27b0e12 from=translated src=- shape=305d3c3b vocab=1201d0e8
-/
@[simp]
theorem mem_finiteWeightLocalizationContraction
    (S : Submonoid R)
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i)))
    (x : ∀ i, M i) :
    x ∈ finiteWeightLocalizationContraction (M := M) S L ↔
      finiteWeightLocalizationMap (M := M) S x ∈ L :=
  Iff.rfl

/-- The canonical map sends the contraction into the localized submodule.
@isnad1 id=le.0h5v.s10.2878d8ebaeaa from=translated src=- shape=a8aa1695 vocab=b5840f0a
-/
theorem map_finiteWeightLocalizationContraction_le
    (S : Submonoid R)
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i))) :
    (finiteWeightLocalizationContraction (M := M) S L).map
        (finiteWeightLocalizationMap (M := M) S) ≤
      L.restrictScalars R := by
  rw [Submodule.map_le_iff_le_comap]
  exact le_rfl

/-- Localizing the saturated contraction recovers the original localized
submodule.
@isnad1 id=eq.0h5v.s9.5169e6516a64 from=translated src=- shape=b1021689 vocab=55f88e75
-/
@[simp]
theorem localized_finiteWeightLocalizationContraction
    (S : Submonoid R)
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i))) :
    (finiteWeightLocalizationContraction (M := M) S L).localized'
        (Localization S) S
        (finiteWeightLocalizationMap (M := M) S) = L := by
  simpa only [finiteWeightLocalizationContraction] using
    (Submodule.localized'gi (Localization S) S
      (finiteWeightLocalizationMap (M := M) S)).l_u_eq L

/-- Localized inclusion in `L` is equivalent to inclusion in its saturated
contraction.
@isnad1 id=iff.0h6v.s10.56b21d640251 from=translated src=- shape=a8cbce13 vocab=2fe6d8da
-/
theorem localized_le_iff_le_finiteWeightLocalizationContraction
    (S : Submonoid R)
    (N : Submodule R (∀ i, M i))
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i))) :
    N.localized' (Localization S) S
        (finiteWeightLocalizationMap (M := M) S) ≤ L ↔
      N ≤ finiteWeightLocalizationContraction (M := M) S L := by
  simpa only [finiteWeightLocalizationContraction] using
    (Submodule.localized'gi (Localization S) S
      (finiteWeightLocalizationMap (M := M) S)).gc N L

/-- The coordinatewise localization map commutes with insertion into one
coordinate.
@isnad1 id=eq.0h6v.s10.b2b869ca6ad3 from=translated src=- shape=ab121e3f vocab=b25208e7
-/
@[simp]
theorem finiteWeightLocalizationMap_single
    (S : Submonoid R) (i : Fin n) (v : M i) :
    finiteWeightLocalizationMap (M := M) S (Pi.single i v) =
      Pi.single i (LocalizedModule.mkLinearMap S (M i) v) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [finiteWeightLocalizationMap_apply]
  · simp [finiteWeightLocalizationMap_apply, hji]

/-- Contraction preserves coordinatewise homogeneity.
@isnad1 id=mem.2h7v.s11.cbad98620de2 from=translated src=- shape=7c8c6233 vocab=7a29fa93
-/
theorem finiteWeightLocalizationContraction_homogeneous
    (S : Submonoid R)
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i)))
    (hL : ∀ x ∈ L, ∀ i, Pi.single i (x i) ∈ L) :
    ∀ x ∈ finiteWeightLocalizationContraction (M := M) S L, ∀ i,
      Pi.single i (x i) ∈
        finiteWeightLocalizationContraction (M := M) S L := by
  intro x hx i
  have hxL : finiteWeightLocalizationMap (M := M) S x ∈ L :=
    (mem_finiteWeightLocalizationContraction S L x).mp hx
  rw [mem_finiteWeightLocalizationContraction,
    finiteWeightLocalizationMap_single]
  simpa only [finiteWeightLocalizationMap_apply] using
    hL (finiteWeightLocalizationMap (M := M) S x) hxL i

/-- The induced localized equivalence commutes with the canonical
localization map.
@isnad1 id=eq.0h6v.s11.0ac3dcadc93b from=translated src=- shape=21ad6f07 vocab=273db7d7
-/
@[simp]
theorem finiteWeightLocalizedEquiv_localizationMap
    (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (x : ∀ i, M i) :
    finiteWeightLocalizedEquiv (M := M) S J
        (finiteWeightLocalizationMap (M := M) S x) =
      finiteWeightLocalizationMap (M := M) S (J x) := by
  simpa only [IsLocalizedModule.mk'_one] using
    finiteWeightLocalizedEquiv_mk' (M := M) S J x (1 : S)

/-- The inverse localized equivalence commutes with the canonical
localization map as well.
@isnad1 id=eq.0h6v.s12.d8e0f9ff7841 from=translated src=- shape=564ce3a2 vocab=d52d497d
-/
@[simp]
theorem finiteWeightLocalizedEquiv_symm_localizationMap
    (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (x : ∀ i, M i) :
    (finiteWeightLocalizedEquiv (M := M) S J).symm
        (finiteWeightLocalizationMap (M := M) S x) =
      finiteWeightLocalizationMap (M := M) S (J.symm x) := by
  apply (finiteWeightLocalizedEquiv (M := M) S J).injective
  rw [LinearEquiv.apply_symm_apply,
    finiteWeightLocalizedEquiv_localizationMap,
    LinearEquiv.apply_symm_apply]

/-- Mapping a saturated contraction by `J` is contraction after mapping the
localized submodule by the induced localized equivalence.
@isnad1 id=eq.0h6v.s10.5fe7c63a2d4b from=translated src=- shape=be8fafbc vocab=b03c90f2
-/
theorem map_finiteWeightLocalizationContraction
    (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i))) :
    (finiteWeightLocalizationContraction (M := M) S L).map
        J.toLinearMap =
      finiteWeightLocalizationContraction (M := M) S
        (L.map
          (finiteWeightLocalizedEquiv (M := M) S J).toLinearMap) := by
  ext x
  simp only [Submodule.mem_map_equiv,
    mem_finiteWeightLocalizationContraction,
    finiteWeightLocalizedEquiv_symm_localizationMap]

/-- Invariance of a localized submodule descends to invariance of its
saturated contraction.
@isnad1 id=eq.1h6v.s10.f71aa47ae31b from=translated src=- shape=40da0a0b vocab=b03c90f2
-/
theorem finiteWeightLocalizationContraction_invariant
    (S : Submonoid R)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i)))
    (hJL : L.map
      (finiteWeightLocalizedEquiv (M := M) S J).toLinearMap = L) :
    (finiteWeightLocalizationContraction (M := M) S L).map
        J.toLinearMap =
      finiteWeightLocalizationContraction (M := M) S L := by
  rw [map_finiteWeightLocalizationContraction, hJL]

/-- Over a Noetherian ring, a saturated contraction inside a finite ambient
module is finitely generated.
@isnad1 id=fg.0h5v.s8.1f9b19f34686 from=translated src=- shape=9b98fec6 vocab=368e1681
-/
theorem finiteWeightLocalizationContraction_fg
    [IsNoetherianRing R]
    [Module.Finite R (∀ i, M i)]
    (S : Submonoid R)
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i))) :
    (finiteWeightLocalizationContraction (M := M) S L).FG :=
  IsNoetherian.noetherian _

/-- If `N` and a finitely generated saturated contraction have the same
localization, one denominator gives the sandwich
`s • K ≤ N ≤ K`.
@isnad1 id=ex.2h6v.s11.33083b13d25d from=translated src=- shape=eef142f9 vocab=7714b8dc
-/
theorem exists_smul_contraction_le_and_le_contraction_of_fg
    (S : Submonoid R)
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i)))
    (N : Submodule R (∀ i, M i))
    (hKfg : (finiteWeightLocalizationContraction (M := M) S L).FG)
    (hloc : N.localized' (Localization S) S
        (finiteWeightLocalizationMap (M := M) S) =
      (finiteWeightLocalizationContraction (M := M) S L).localized'
        (Localization S) S
        (finiteWeightLocalizationMap (M := M) S)) :
    ∃ s : S,
      s • finiteWeightLocalizationContraction (M := M) S L ≤ N ∧
        N ≤ finiteWeightLocalizationContraction (M := M) S L := by
  obtain ⟨s, hs⟩ := exists_smul_le_of_localized'_le S
    (finiteWeightLocalizationMap (M := M) S) hKfg hloc.ge
  refine ⟨s, hs, ?_⟩
  apply (localized_le_iff_le_finiteWeightLocalizationContraction S N L).mp
  simpa only [localized_finiteWeightLocalizationContraction] using hloc.le

/-- The denominator-clearing sandwich for the canonical contraction in a
finite module over a Noetherian ring.
@isnad1 id=ex.1h6v.s11.19a0fea2ad5b from=translated src=- shape=60fcb1f2 vocab=05669e08
-/
theorem exists_smul_contraction_le_and_le_contraction
    [IsNoetherianRing R]
    [Module.Finite R (∀ i, M i)]
    (S : Submonoid R)
    (L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i)))
    (N : Submodule R (∀ i, M i))
    (hloc : N.localized' (Localization S) S
        (finiteWeightLocalizationMap (M := M) S) =
      (finiteWeightLocalizationContraction (M := M) S L).localized'
        (Localization S) S
        (finiteWeightLocalizationMap (M := M) S)) :
    ∃ s : S,
      s • finiteWeightLocalizationContraction (M := M) S L ≤ N ∧
        N ≤ finiteWeightLocalizationContraction (M := M) S L :=
  exists_smul_contraction_le_and_le_contraction_of_fg S L N
    (finiteWeightLocalizationContraction_fg S L) hloc

end AbelFormalization
