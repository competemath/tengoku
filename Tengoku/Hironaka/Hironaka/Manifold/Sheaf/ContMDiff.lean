/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Manifold.StructureSheaf.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sheaf of `C^n` functions on a manifold: sections and evaluation

For a manifold `M` modelled on `(EM, HM)` over a nontrivially normed field `𝕜`, a manifold `N`
modelled on `(E, H)` and any smoothness `n : ℕ∞ω`, the sections of the sheaf of `C^n` functions
`contMDiffSheaf IM I n M N` over `U` are, definitionally, the bundled maps `C^n⟮IM, U; I, N⟯`
(`contMDiffSheaf.obj_eq`), and likewise for the sheaf of commutative rings
`contMDiffSheafCommRing IM I n M R` of `C^n` functions valued in a `C^n` commutative ring `R`, on
which restriction is restriction of functions (`contMDiffSheafCommRing.map_apply`).

The evaluation at a point, `contMDiffSheafCommRing.eval IM I n M R x : stalk x →+* R`, takes the
germ of a section to its value at `x` (`eval_germ`) and is surjective, every value being taken by a
constant section (`eval_surjective`); in particular the stalks are nontrivial when `R` is.

This is the sheaf of regular functions of Bierstone–Milman's regular coordinate charts
[BM97, (0.3)]: the coordinates of a chart are sections and the stalks are the local rings of germs
(`contMDiffSheafCommRing.instLocalRing_stalk`).
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (n : ℕ∞ω)
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  (N : Type) [TopologicalSpace N] [ChartedSpace H N]

variable {M}

/-- The sections of `contMDiffSheaf IM I n M N` over `U` are, definitionally, the `C^n` functions
`C^n⟮IM, U; I, N⟯`.
@isnad1 id=eq.0h11v.s8.f82e65d0d27f from=translated src=- shape=37c15ff3 vocab=6850a132
-/
theorem contMDiffSheaf.obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (contMDiffSheaf IM I n M N).presheaf.obj U = C^n⟮IM, (unop U : Opens M); I, N⟯ := rfl

/--
@isnad1 id=contmdif.0h12v.s9.648950b04974 from=translated src=- shape=2e49cd81 vocab=5ca3675e
-/
theorem contMDiffSheaf.contMDiff_section {U : (Opens (TopCat.of M))ᵒᵖ}
    (f : (contMDiffSheaf IM I n M N).presheaf.obj U) : ContMDiff IM I n f :=
  f.2

variable {N}

section CommRing

variable (M) (R : Type) [CommRing R] [TopologicalSpace R] [ChartedSpace H R] [ContMDiffRing I n R]

/-- The sections of `contMDiffSheafCommRing IM I n M R` over `U` are, definitionally, the `C^n`
functions `C^n⟮IM, U; I, R⟯`.
@isnad1 id=eq.0h11v.s8.9c22c0782f0d from=translated src=- shape=bbf4a0c0 vocab=de68edbb
-/
theorem contMDiffSheafCommRing.obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    ((contMDiffSheafCommRing IM I n M R).presheaf.obj U : Type u) =
      C^n⟮IM, (unop U : Opens M); I, R⟯ := rfl

/--
@isnad1 id=contmdif.0h12v.s9.d983f9b850c8 from=translated src=- shape=b2242ffe vocab=35684b90
-/
theorem contMDiffSheafCommRing.contMDiff_section {U : (Opens (TopCat.of M))ᵒᵖ}
    (f : (contMDiffSheafCommRing IM I n M R).presheaf.obj U) : ContMDiff IM I n f :=
  f.2

/-- Restriction is restriction of functions.
@isnad1 id=eq.1h14v.s11.b01195b71993 from=translated src=- shape=8cb33b4f vocab=968c3283
-/
@[simp]
theorem contMDiffSheafCommRing.map_apply {U V : Opens (TopCat.of M)} (h : U ≤ V)
    (f : (contMDiffSheafCommRing IM I n M R).presheaf.obj (op V)) (x : U) :
    ((contMDiffSheafCommRing IM I n M R).presheaf.map (homOfLE h).op f) x =
      f (Set.inclusion h x) := rfl

/-- Evaluation at `x` on the sections over an open neighbourhood `U` of `x`, valued in the lift of
`R` to the universe of `M` (so that it is a morphism of `CommRingCat.{u}`).-/
def contMDiffSheafCommRing.evalAt (x : TopCat.of M) (U : OpenNhds x) :
    (contMDiffSheafCommRing IM I n M R).presheaf.obj (op U.1) ⟶ CommRingCat.of (ULift.{u} R) :=
  CommRingCat.ofHom ((ULift.ringEquiv.symm : R ≃+* ULift.{u} R).toRingHom.comp
    (ContMDiffMap.evalRingHom ⟨x, U.2⟩))

/-- The evaluation at `x`, as a morphism from the stalk of `C^n` functions at `x` to the lift of
`R` in the category of commutative rings.-/
def contMDiffSheafCommRing.evalHom (x : TopCat.of M) :
    (contMDiffSheafCommRing IM I n M R).presheaf.stalk x ⟶ CommRingCat.of (ULift.{u} R) := by
  refine CategoryTheory.Limits.colimit.desc _ ⟨_, ⟨fun U => ?_, ?_⟩⟩
  · apply contMDiffSheafCommRing.evalAt
  · cat_disch

/-- The evaluation `ev_x : 𝒪_x →+* R` at `x` on the stalk of `C^n` functions.-/
def contMDiffSheafCommRing.eval (x : M) :
    (contMDiffSheafCommRing IM I n M R).presheaf.stalk x →+* R :=
  (ULift.ringEquiv : ULift.{u} R ≃+* R).toRingHom.comp
    (contMDiffSheafCommRing.evalHom IM I n M R x).hom

/--
@isnad1 id=eq.0h12v.s10.5fd6bda1dd34 from=translated src=- shape=5ff92fff vocab=1898feec
-/
@[simp, reassoc, elementwise]
theorem contMDiffSheafCommRing.ι_evalHom (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ contMDiffSheafCommRing.evalHom IM I n M R x =
      contMDiffSheafCommRing.evalAt IM I n M R x (unop U) :=
  colimit.ι_desc _ _

/--
@isnad1 id=eq.1h13v.s10.52a9e5df2aae from=translated src=- shape=ab174bf4 vocab=a25e4712
-/
theorem contMDiffSheafCommRing.evalHom_germ (U : Opens (TopCat.of M)) (x : M) (hx : x ∈ U)
    (f : (contMDiffSheafCommRing IM I n M R).presheaf.obj (op U)) :
    contMDiffSheafCommRing.evalHom IM I n M R (x : TopCat.of M)
      ((contMDiffSheafCommRing IM I n M R).presheaf.germ U x hx f) = ULift.up (f ⟨x, hx⟩) :=
  congr_arg (fun a => a f) <| contMDiffSheafCommRing.ι_evalHom IM I n M R x (op ⟨U, hx⟩)

/-- The evaluation at `x` of the germ of a section is the value of the section at `x`.
@isnad1 id=eq.1h13v.s10.3df61dbf72cb from=translated src=- shape=23445d07 vocab=0ba571af
-/
@[simp]
theorem contMDiffSheafCommRing.eval_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (contMDiffSheafCommRing IM I n M R).presheaf.obj (op U)) :
    contMDiffSheafCommRing.eval IM I n M R x
      ((contMDiffSheafCommRing IM I n M R).presheaf.germ U x hx f) = f ⟨x, hx⟩ := by
  unfold contMDiffSheafCommRing.eval
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  change ULift.ringEquiv (contMDiffSheafCommRing.evalHom IM I n M R x _) = _
  rw [contMDiffSheafCommRing.evalHom_germ]
  rfl

/-- The evaluation at `x` is surjective: every value is taken by a constant section.
@isnad1 id=surjecti.0h11v.s9.1d11472416c2 from=translated src=- shape=ba2d69bd vocab=ada68e1c
-/
theorem contMDiffSheafCommRing.eval_surjective (x : M) :
    Function.Surjective (contMDiffSheafCommRing.eval IM I n M R x) := fun r =>
  ⟨(contMDiffSheafCommRing IM I n M R).presheaf.germ ⊤ x trivial
    (⟨fun _ => r, contMDiff_const⟩ : C^n⟮IM, ((⊤ : Opens M) : Opens M); I, R⟯),
    contMDiffSheafCommRing.eval_germ IM I n M R _ _ _ _⟩

instance [Nontrivial R] (x : M) :
    Nontrivial ((contMDiffSheafCommRing IM I n M R).presheaf.stalk x) :=
  (contMDiffSheafCommRing.eval_surjective IM I n M R x).nontrivial

end CommRing

end Manifold
