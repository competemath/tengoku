/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport of homogeneous localizations along element equalities

`HomogeneousLocalization.Away 𝒜 s` depends on the element `s`; propositional
equalities `s = t` therefore change the type. This file provides the transport
ring isomorphism together with a `subst`-derived API on `Away.mk` normal forms and
naturality against `Away.map`, so that downstream proofs never juggle `eqToHom`s.

AINTLIB ModularCurves (T-A5a-iso); upstream candidate.
-/

namespace ModularCurves

open HomogeneousLocalization

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

/-- Transport an `Away` ring along an equality of localization elements.-/
noncomputable def awayCongr {s t : A} (h : s = t) : Away 𝒜 s ≃+* Away 𝒜 t := by
  subst h
  exact RingEquiv.refl _

/--
@isnad1 id=eq.0h5v.s9.1131fc1c4f4a from=translated src=- shape=1773fdf1 vocab=f2877184
-/
@[simp]
lemma awayCongr_rfl {s : A} :
    (awayCongr (rfl : s = s) : Away 𝒜 s ≃+* Away 𝒜 s) = RingEquiv.refl _ :=
  rfl

/--
@isnad1 id=eq.3h9v.s11.7d679b896d74 from=translated src=- shape=373a0a8e vocab=34661dea
-/
lemma awayCongr_mk {s t : A} (h : s = t) {i : ι} (hs : s ∈ 𝒜 i) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • i)) :
    awayCongr (𝒜 := 𝒜) h (Away.mk 𝒜 hs n a ha) =
      Away.mk 𝒜 (h ▸ hs) n a ha := by
  subst h
  rfl

variable {σ B S : Type*} [CommRing S] [CommRing B] [Algebra S B]
  {ℬ : ι → Submodule S B} [GradedAlgebra ℬ]

/-- `awayCongr` is natural against the graded `Away.map`.
@isnad1 id=eq.1h11v.s14.3f0ba744d4b4 from=translated src=- shape=1286c4dd vocab=10164746
-/
lemma awayCongr_map {s t : A} (h : s = t) (g : GradedRingHom 𝒜 ℬ) (x : Away 𝒜 s) :
    Away.map g t (awayCongr (𝒜 := 𝒜) h x) =
      awayCongr (𝒜 := ℬ) (congrArg g h)
        (Away.map g s x) := by
  subst h
  rfl

/--
@isnad1 id=eq.2h8v.s12.39640a60fd39 from=translated src=- shape=de0b57f7 vocab=5cafd231
-/
lemma awayCongr_trans {s t u : A} (h₁ : s = t) (h₂ : t = u) (x : Away 𝒜 s) :
    awayCongr (𝒜 := 𝒜) h₂ (awayCongr (𝒜 := 𝒜) h₁ x) =
      awayCongr (𝒜 := 𝒜) (h₁.trans h₂) x := by
  subst h₁; subst h₂; rfl

/--
@isnad1 id=eq.1h6v.s10.d46670ea357f from=translated src=- shape=6b840c17 vocab=063234b5
-/
lemma awayCongr_self {s : A} (h : s = s) (x : Away 𝒜 s) :
    awayCongr (𝒜 := 𝒜) h x = x := by
  rw [Subsingleton.elim h rfl]
  rfl

/-- `Away.map` only depends on the graded hom up to propositional equality, through
the transport.
@isnad1 id=eq.1h11v.s14.f410da8067eb from=translated src=- shape=a9571af0 vocab=10164746
-/
lemma awayMap_congr {g₁ g₂ : GradedRingHom 𝒜 ℬ} (h : g₁ = g₂) (s : A) (x : Away 𝒜 s) :
    Away.map g₂ s x =
      awayCongr (𝒜 := ℬ) (congrArg (fun g : GradedRingHom 𝒜 ℬ => g s) h)
        (Away.map g₁ s x) := by
  subst h
  exact (awayCongr_self _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The graded `Away.map` commutes with the degree-zero inclusion `fromZeroRingHom`:
`Away.map g s` sends `a/1` (for `a : 𝒜 0`) to `(g a)/1` in `Away ℬ (g s)`. This is the
ring-hom heart of the naturality of `Proj.toSpecZero` under `Proj.map` — when `g` fixes the
degree-zero part it exhibits `Proj.map g` as a morphism over `Spec (𝒜 0)`.
@isnad1 id=eq.0h10v.s13.0a34792b96f6 from=translated src=- shape=6ec85581 vocab=3c4a9ad8
-/
lemma awayMap_fromZeroRingHom (g : GradedRingHom 𝒜 ℬ) (s : A) (a : 𝒜 0) :
    Away.map g s
        (fromZeroRingHom 𝒜 (Submonoid.powers s) a) =
      fromZeroRingHom ℬ (Submonoid.powers (g s))
        ⟨g a, g.map_mem a.2⟩ := by
  ext
  simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Away.map, map_mk, val_mk]
  congr 1
  exact Subtype.ext (by simp)

variable {τ C T : Type*} [CommRing T] [CommRing C] [Algebra T C]
  {𝒞 : ι → Submodule T C} [GradedAlgebra 𝒞]

/-- Applied form of `Away.map_comp`.
@isnad1 id=eq.0h14v.s14.45d7f81a8223 from=translated src=- shape=6b5ce226 vocab=ed9dceea
-/
lemma awayMap_map (f : GradedRingHom 𝒜 ℬ) (g : GradedRingHom ℬ 𝒞) (s : A)
    (x : Away 𝒜 s) :
    Away.map g (f s)
        (Away.map f s x) =
      Away.map (g.comp f) s x :=
  (DFunLike.congr_fun (Away.map_comp f g s) x).symm

variable {S' B' : Type*} [CommRing S'] [CommRing B'] [Algebra S' B']
  {ℬ' : ι → Submodule S' B'} [GradedAlgebra ℬ']

/-- Comparing the two ways around a commuting square of graded homs, with
transports along any equalities of the localization elements.
@isnad1 id=eq.3h20v.s15.91d090afede7 from=translated src=- shape=35995bbd vocab=ec9d2499
-/
lemma awayMap_square {f₁ : GradedRingHom 𝒜 ℬ} {g₁ : GradedRingHom ℬ 𝒞}
    {f₂ : GradedRingHom 𝒜 ℬ'} {g₂ : GradedRingHom ℬ' 𝒞}
    (hsq : g₁.comp f₁ = g₂.comp f₂) (s : A) (x : Away 𝒜 s)
    {t : C} (h₁ : g₁ (f₁ s) = t) (h₂ : g₂ (f₂ s) = t) :
    awayCongr (𝒜 := 𝒞) h₁
        (Away.map g₁ (f₁ s)
          (Away.map f₁ s x)) =
      awayCongr (𝒜 := 𝒞) h₂
        (Away.map g₂ (f₂ s)
          (Away.map f₂ s x)) := by
  rw [awayMap_map, awayMap_map, awayMap_congr hsq s x]
  refine Eq.trans ?_ (awayCongr_trans (𝒜 := 𝒞)
    (congrArg (fun g : GradedRingHom 𝒜 𝒞 => g s) hsq) h₂
    ((Away.map (g₁.comp f₁) s) x)).symm
  exact congrArg (fun hh => awayCongr (𝒜 := 𝒞) hh
    ((Away.map (g₁.comp f₁) s) x)) (Subsingleton.elim _ _)

end ModularCurves
