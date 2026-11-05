/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Separated
import Tengoku.Hironaka.Hironaka.Algebra.Smooth.StandardSmoothLift
import Tengoku.Seed.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kollár's Lemma 41: the local ambient lift of a smooth morphism

`exists_smooth_ambient_lift` is [Kol07, Lemma 41]: for `h : Y ⟶ X` smooth, `y : Y` and a closed
immersion `emb : X ⟶ A`, there are opens `UA ∋ emb (h y)` of `A` and `V ∋ y` of `Y`, a scheme `AY`
over `k`, a smooth surjective `hA : AY ⟶ UA` of constant relative dimension and a closed immersion
`j : V ⟶ AY` with `IsPullback j (h.resLE (emb ⁻¹ᵁ UA) V hV) hA (emb.resLE UA (emb ⁻¹ᵁ UA) le_rfl)`:
a smooth morphism to an embedded scheme is, locally, the restriction of a smooth morphism between
ambient schemes.

**The proof**, by the local structure of smooth algebras rather than Kollár's general projection.

1. *Affine reduction.* An affine `UA₀ ∋ emb (h y)` (`exists_isAffineOpen_mem_and_subset`);
   `X₀ := emb ⁻¹ᵁ UA₀` is affine (closed immersions are affine, `IsAffineOpen.preimage`); an affine
   `V₀ ∋ y` inside `h ⁻¹ᵁ X₀`.
2. *The local presentation.* Mathlib's `Smooth h` says that `Γ(X, X₀) → Γ(Y, V₀)` is a smooth ring
   map (`Smooth.smooth_appLE`), hence locally standard smooth
   (`RingHom.smooth_iff_locally_isStandardSmooth`): on a basic open `V := D(t) ∋ y` of `V₀` the
   map `Γ(X, X₀) → Γ(Y, V)` is standard smooth (`exists_basicOpen_isStandardSmooth_appLE`), with
   a submersive presentation `P`. This replaces Kollár's writing of `Y` near `y` as an open of a
   hypersurface in `X × 𝔸^{d+1}` after a general projection, which needs an infinite field.
3. *The lifted ambient* (`Hironaka/Algebra/Smooth/StandardSmoothLift.lean`). `Γ(A, UA₀) ↠ Γ(X, X₀)`
   (`Scheme.Hom.app_surjective`) lifts the relations of `P` (Kollár's extension of the coefficients
   `φ_I` to `Φ_I` on the ambient); `AY := Spec (T[1/Δ])` is standard smooth of relative dimension
   `P.dimension` over `Γ(A, UA₀)`;
   `Spec Γ(Y, V) = Spec Γ(X, X₀) ×_{Spec Γ(A, UA₀)} Spec T` (`isPullback_SpecMap_of_isPushout`) is
   cut at the open `D(Δ)` (`IsPullback.of_comp_mono_fst`) and transported along the `isoSpec`s to
   the `resLE` square (`exists_affine_ambient`, `SpecMap_appLE_isoSpec_inv`); `j` is a closed
   immersion since `T[1/Δ] → Γ(Y, V)` is surjective.
4. *Shrinking to a surjection.* The image of `AY → UA₀ ↪ A` is open (smooth morphisms are flat and
   locally of finite presentation, hence universally open); `UA` is that image, `hA` the lift of
   `AY → UA₀` to `UA` (`IsOpenImmersion.lift`), surjective by construction and still smooth of the
   same relative dimension (`MorphismProperty.IsStableUnderBaseChange` along the square
   `IsPullback (𝟙 AY) hA hA₀ (A.homOfLE _)`); `V ≤ h ⁻¹ᵁ (emb ⁻¹ᵁ UA)` since `emb ∘ h` factors
   through `hA ∘ j` on `V`; the square over `UA` is the restriction of the square over `UA₀`
   (`IsPullback.of_right` against the `homOfLE` square of `emb`).
5. *Over `k`* (`exists_smooth_ambient_lift`). `AY ↘ Spec k := hA ≫ (UA.ι ≫ (A ↘ Spec k))`; as an
   affine scheme over the affine `Spec k`, `AY` is quasi-compact and separated over `k`
   (`isAffineHom_of_isAffine`).

The hypotheses `[CharZero k]`, `[LocallyOfFiniteType]`, `[h.IsOver]`, `[emb.IsOver]` of the main
statement are Kollár's setting for Lemma 41 (schemes of finite type over a field of characteristic
zero, morphisms over `k`) and are kept so that the theorem reads as printed; the proof does not
need them, because it replaces Kollár's general projection, which needs the field infinite, by
Mathlib's local structure of smooth algebras, valid over any base: the field-free form
`exists_smooth_ambient_lift'` is proved first and the main statement is its specialisation. The
conclusion adds to Kollár's the quasi-compactness and separatedness of `AY` over `k` and the
constancy of the relative dimension of `hA`, all read off his construction; `AY` is in fact
affine, which the statement does not record. Compare [Wlo05, Lemma 4.9.1], the extension of an
étale morphism of embedded affine varieties to the ambient spaces. The smooth charts of the
functorial resolution use the field-free form
(`Hironaka/Resolution/Algebraic/Kol07/Thm36/SmoothCharts.lean`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Algebra.StandardSmoothLift

namespace AlgebraicGeometry

/-- A pullback square whose top map factors through a mono can be cut at the mono:
`Spec S = Spec R ×_{Spec R'} Spec T` and `Spec S → Spec T` lands in the open `D(Δ)`, so
`Spec S = Spec R ×_{Spec R'} D(Δ)`.-/
theorem _root_.CategoryTheory.IsPullback.of_comp_mono_fst {C : Type*} [Category C]
    {P X X' Y Z : C} {fst : P ⟶ X} {i : X ⟶ X'} [Mono i] {snd : P ⟶ Y} {f : X' ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback (fst ≫ i) snd f g) : IsPullback fst snd (i ≫ f) g := by
  refine IsPullback.of_isLimit' ⟨by rw [← Category.assoc, H.w]⟩ ?_
  refine PullbackCone.IsLimit.mk _
    (fun s => H.lift (s.fst ≫ i) s.snd (by rw [Category.assoc, s.condition])) ?_ ?_ ?_
  · intro s
    rw [← cancel_mono i, Category.assoc, H.lift_fst]
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h₁ h₂
    apply H.hom_ext
    · rw [H.lift_fst, ← Category.assoc, h₁]
    · rw [H.lift_snd, h₂]

/-- `Spec.map (f.appLE U V e) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ f.resLE U V e` for affine
opens: the comparison of the affine `Spec` square with the `resLE` square.-/
theorem SpecMap_appLE_isoSpec_inv {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) :
    Spec.map (f.appLE U V e) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ f.resLE U V e := by
  rw [← cancel_epi hV.isoSpec.hom, Iso.hom_inv_id_assoc, hV.isoSpec_hom,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- Given affine `U ⊆ X` and affine `V₀ ⊆ h ⁻¹ᵁ U` containing `y`, there is a basic open
`D(t) ⊆ V₀` containing `y` with `Γ(X, U) → Γ(Y, D(t))` standard smooth: Mathlib's `Smooth h` is
`RingHom.Smooth` of every affine `appLE`, and a smooth ring map is locally standard smooth on the
target (the local presentation of `Y` near `y` in the proof of [Kol07, Lemma 41]).-/
theorem exists_basicOpen_isStandardSmooth_appLE {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h]
    {U : X.Opens} (hU : IsAffineOpen U) {V₀ : Y.Opens} (hV₀ : IsAffineOpen V₀)
    (e : V₀ ≤ h ⁻¹ᵁ U) {y : Y} (hy : y ∈ V₀) :
    ∃ t : Γ(Y, V₀), y ∈ Y.basicOpen t ∧
      (h.appLE U (Y.basicOpen t) ((Y.basicOpen_le t).trans e)).hom.IsStandardSmooth := by
  have hsm : (h.appLE U V₀ e).hom.Smooth := Smooth.smooth_appLE h hU hV₀ e
  rw [RingHom.smooth_iff_locally_isStandardSmooth,
    RingHom.locally_iff_isLocalization RingHom.isStandardSmooth_respectsIso] at hsm
  obtain ⟨s, hs, H⟩ := hsm
  have hy' : y ∈ ⨆ i ∈ (s : Set Γ(Y, V₀)), Y.basicOpen i := by
    rwa [iSup_basicOpen_of_span_eq_top V₀ _ hs]
  simp only [TopologicalSpace.Opens.mem_iSup] at hy'
  obtain ⟨t, ht, hyt⟩ := hy'
  refine ⟨t, hyt, ?_⟩
  let : Algebra Γ(Y, V₀) Γ(Y, Y.basicOpen t) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le t)).op).hom.toAlgebra
  have : IsLocalization.Away t Γ(Y, Y.basicOpen t) :=
    hV₀.isLocalization_of_eq_basicOpen t (homOfLE (Y.basicOpen_le t)) rfl
  have := H t ht Γ(Y, Y.basicOpen t)
  rwa [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map] at this

end AlgebraicGeometry
