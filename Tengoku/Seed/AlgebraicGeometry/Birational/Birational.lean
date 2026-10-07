/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.AffineSpace
public import Tengoku.Seed.AlgebraicGeometry.Birational.RationalMap

/-!
# Birationality and Rationality of schemes.

This file defines partial isomorphisms between schemes and uses them to formalize
birationality and rationality.

## Main definitions

- `Scheme.PartialIso X Y`: an isomorphism between a dense open subscheme of `X` and a
  dense open subscheme of `Y`.
- `Scheme.Birational X Y`: `X` and `Y` are birational, i.e. there exists a `PartialIso X Y`.
- `Scheme.BirationalOver sX sY`: `X` and `Y` are birational over `S` via structure maps
  `sX : X ⟶ S` and `sY : Y ⟶ S`.
- `Scheme.IsRationalOver sX`: `X` is rational over `S` via structure map `sX : X ⟶ S`,
  i.e. birational over `S` to some affine space `𝔸(n; S)`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A partial isomorphism from `X` to `Y` is an isomorphism between dense open subschemes
of `X` and `Y`. -/
structure PartialIso (X Y : Scheme.{u}) where
  /-- The source open subscheme of a partial isomorphism. -/
  source : X.Opens
  dense_source : Dense (source : Set X)
  /-- The target open subscheme of a partial isomorphism. -/
  target : Y.Opens
  dense_target : Dense (target : Set Y)
  /-- The underlying isomorphism of a partial isomorphism. -/
  iso : source.toScheme ≅ target.toScheme

namespace PartialIso

variable {X Y Z S : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}

variable (sX sY) in
/-- A partial iso is an `S`-map if the underlying morphism is. -/
abbrev IsOver (f : X.PartialIso Y) : Prop :=
  f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX

/--
@isnad1 id=iff.0h4v.s7.19e8d053b7ed from=seed src=0 shape=42960df5 vocab=30d6d36d
-/
lemma ext_iff (f g : X.PartialIso Y) :
    f = g ↔ ∃ (e : f.source = g.source) (e' : g.target = f.target),
      f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e' := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U₁, hU₁, U₂, hU₂, f⟩ := f
    obtain ⟨V₁, hV₁, V₂, hU₂, g⟩ := g
    simp only [forall_exists_index]
    rintro rfl rfl e
    simpa using e

/--
@isnad1 id=eq.3h4v.s7.d5d6105fb093 from=seed src=0 shape=62a9d975 vocab=30d6d36d
-/
@[ext]
lemma ext (f g : X.PartialIso Y) (e : f.source = g.source) (e' : g.target = f.target)
    (H : f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e') : f = g := by
  rw [ext_iff]
  exact ⟨e, e', H⟩

variable (X) in
/-- The identity partial isomorphism on `X`, defined on all of `X`. -/
@[refl, simps]
def refl : X.PartialIso X where
  source := ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := Iso.refl _

/-- The inverse of a partial isomorphism. -/
@[symm, simps]
def symm (f : X.PartialIso Y) : Y.PartialIso X where
  source := f.target
  dense_source := f.dense_target
  target := f.source
  dense_target := f.dense_source
  iso := f.iso.symm

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=isover.1h6v.s5.ae0b6515492e from=seed src=0 shape=07f76957 vocab=fd2f0720
-/
lemma IsOver.symm {f : X.PartialIso Y} (hf : f.IsOver sX sY) : f.symm.IsOver sY sX := by
  simpa [IsOver, ← cancel_epi f.iso.hom] using Eq.symm hf

/-- Compose two partial isomorphisms along a proof that the target of `f` equals the source
of `g`. See `trans` for the version that does not require this. -/
@[simps]
noncomputable def trans' (f : X.PartialIso Y) (g : Y.PartialIso Z) (e : f.target = g.source) :
    X.PartialIso Z where
  source := f.source
  dense_source := f.dense_source
  target := g.target
  dense_target := g.dense_target
  iso := f.iso ≪≫ Y.isoOfEq e ≪≫ g.iso

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=isover.3h9v.s6.bc38a1636b63 from=seed src=0 shape=bba8db86 vocab=1bc26eb8
-/
lemma IsOver.trans' {f : X.PartialIso Y} {g : Y.PartialIso Z} {e : f.target = g.source}
    (hf : f.IsOver sX sY) (hg : g.IsOver sY sZ) : (trans' f g e).IsOver sX sZ := by
  simp [IsOver, ← hf, hg]

/-- Restrict the source of a partial isomorphism to a smaller dense open. -/
@[simps]
noncomputable def restrictSource (f : X.PartialIso Y) (U : Opens X) (hU : Dense (U : Set X))
    (hU' : U ≤ f.source) : X.PartialIso Y where
  source := U
  dense_source := hU
  target := f.target.ι ''ᵁ f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U
  dense_target :=
    have := Opens.isDominant_ι f.dense_target
    f.target.ι.denseRange.dense_image f.target.ι.continuous <|
      f.iso.hom.denseRange.dense_image f.iso.hom.continuous <|
        hU.preimage f.source.ι.isOpenEmbedding.isOpenMap
  iso := (Opens.isoOfLE hU').symm ≪≫
    (f.iso.hom.isoImage (f.source.ι ⁻¹ᵁ U)) ≪≫
    (f.target.ι.isoImage (f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U))

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=isover.3h7v.s7.011457f5e813 from=seed src=0 shape=63ff8379 vocab=f8fe1552
-/
lemma IsOver.restrictSource {f : X.PartialIso Y} (hf : f.IsOver sX sY) (U : Opens X)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.source) :
    (f.restrictSource U hU hU').IsOver sX sY := by
  simp [IsOver, hf]

/-- Restrict the target of a partial isomorphism to a smaller dense open. -/
@[simps! source target iso]
noncomputable def restrictTarget (f : X.PartialIso Y) (U : Opens Y) (hU : Dense (U : Set Y))
    (hU' : U ≤ f.target) : X.PartialIso Y :=
  (f.symm.restrictSource U hU hU').symm

/--
@isnad1 id=isover.3h7v.s7.3e78717f9a02 from=seed src=0 shape=7e3e5b8a vocab=153019af
-/
lemma IsOver.restrictTarget {f : X.PartialIso Y} (hf : f.IsOver sX sY) (U : Opens Y)
    (hU : Dense (U : Set Y)) (hU' : U ≤ f.target) :
    (f.restrictTarget U hU hU').IsOver sX sY :=
  (hf.symm.restrictSource U hU hU').symm

/-- Compose two partial isomorphisms, restricting to the intersection of the intermediate opens. -/
@[trans, simps! source target iso]
noncomputable def trans (f : X.PartialIso Y) (g : Y.PartialIso Z) : X.PartialIso Z :=
  have := f.dense_target.inter_of_isOpen_right g.dense_source g.source.2
  (f.restrictTarget _ this inf_le_left).trans' (g.restrictSource _ this inf_le_right) rfl

/--
@isnad1 id=isover.2h9v.s6.c219b827d49b from=seed src=0 shape=ab3a2455 vocab=72dd6f26
-/
lemma IsOver.trans {f : X.PartialIso Y} {g : Y.PartialIso Z} (hf : f.IsOver sX sY)
    (hg : g.IsOver sY sZ) : (f.trans g).IsOver sX sZ :=
  (hf.restrictTarget _ _ _).trans' (hg.restrictSource _ _ _)

/-- The underlying partial map of a partial isomorphism. -/
@[simps]
def toPartialMap (f : X.PartialIso Y) : X.PartialMap Y where
  domain := f.source
  dense_domain := f.dense_source
  hom := f.iso.hom ≫ f.target.ι

/-- The underlying rational map of a partial isomorphism. -/
abbrev toRationalMap (f : X.PartialIso Y) : X ⤏ Y := f.toPartialMap.toRationalMap

/-- A scheme isomorphism viewed as a partial isomorphism defined on all of `X` and `Y`. -/
@[simps]
noncomputable def ofIso (f : X ≅ Y) : X.PartialIso Y where
  source := ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := X.topIso ≪≫ f ≪≫ Y.topIso.symm

end PartialIso

/-- `X` and `Y` are birational if there exists a partial isomorphism between them. -/
@[stacks 0A20 "(1)"]
def Birational (X Y : Scheme.{u}) : Prop := Nonempty (PartialIso X Y)

/-- Choose a partial isomorphism witnessing that `X` and `Y` are birational. -/
noncomputable def Birational.partialIso {X Y : Scheme.{u}} (h : Birational X Y) :
    PartialIso X Y :=
  Classical.choice h

/--
@isnad1 id=biration.0h1v.s2.ff676f039896 from=seed src=0 shape=b3bac8d8 vocab=5dcac670
-/
@[refl]
lemma Birational.refl (X : Scheme.{u}) : Birational X X :=
  ⟨.refl X⟩

/--
@isnad1 id=biration.1h2v.s3.4216d70dbafe from=seed src=0 shape=7e524d71 vocab=5dcac670
-/
@[symm]
lemma Birational.symm {X Y : Scheme.{u}} (h : Birational X Y) : Birational Y X :=
  ⟨h.partialIso.symm⟩

/--
@isnad1 id=biration.2h3v.s4.27d405f340e8 from=seed src=0 shape=0bc0c4a6 vocab=5dcac670
-/
@[trans]
lemma Birational.trans {X Y Z : Scheme.{u}} (h₁ : Birational X Y) (h₂ : Birational Y Z) :
    Birational X Z :=
  ⟨h₁.partialIso.trans h₂.partialIso⟩

/-- `X` and `Y` are birational over `S` if there exists a partial isomorphism between them
that is compatible with the structure maps to `S`. -/
def BirationalOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) : Prop :=
  ∃ f : PartialIso X Y, f.IsOver sX sY

/-- Choose a partial isomorphism witnessing that `X` and `Y` are birational over `S`. -/
noncomputable def BirationalOver.partialIso {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (h : BirationalOver sX sY) :=
  h.choose

/--
@isnad1 id=isover.1h5v.s5.1ff0ddae8fe9 from=seed src=0 shape=1127e983 vocab=c495b9e0
-/
lemma BirationalOver.partialIso_isOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (h : BirationalOver sX sY) : h.partialIso.IsOver sX sY :=
  h.choose_spec

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=biration.0h3v.s4.8e7d944ffff8 from=seed src=0 shape=ff1b5904 vocab=3a204ec4
-/
lemma BirationalOver.refl {S X : Scheme.{u}} (sX : X ⟶ S) : BirationalOver sX sX :=
  ⟨.refl X, by simp [PartialIso.IsOver]⟩

/--
@isnad1 id=biration.1h5v.s5.d79146e631ae from=seed src=0 shape=a5a1fdfc vocab=3a204ec4
-/
lemma BirationalOver.symm {S X Y : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S}
    (h : BirationalOver sX sY) : BirationalOver sY sX :=
  ⟨h.partialIso.symm, h.partialIso_isOver.symm⟩

/--
@isnad1 id=biration.2h7v.s5.d2d60df064d4 from=seed src=0 shape=958f7761 vocab=3a204ec4
-/
lemma BirationalOver.trans {S X Y Z : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}
    (h₁ : BirationalOver sX sY) (h₂ : BirationalOver sY sZ) :
    BirationalOver sX sZ :=
  ⟨h₁.partialIso.trans h₂.partialIso, h₁.partialIso_isOver.trans h₂.partialIso_isOver⟩

/-- `X` is rational over `S` (or `S`-rational) if it is birational over `S` to some
affine space `𝔸(n; S)`. Note that we do not require `n` to be finite here. -/
@[mk_iff]
class IsRationalOver {S X : Scheme.{u}} (sX : X ⟶ S) : Prop where
  exists_birationalOver_affineSpace (sX) : ∃ (n : Type u), BirationalOver sX (𝔸(n; S) ↘ S)

instance (S : Scheme.{u}) (n : Type u) : IsRationalOver (𝔸(n; S) ↘ S) where
  exists_birationalOver_affineSpace := ⟨n, .refl _⟩

/-- If a scheme `X` is `S`-birational to an `S`-rational scheme `Y`, then `X` is `S`-rational.
@isnad1 id=isration.1h5v.s5.0edfee02553f from=seed src=0 shape=9738ee9d vocab=8304a525
-/
lemma BirationalOver.isRationalOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsRationalOver sY] (h : BirationalOver sX sY) : IsRationalOver sX := by
  obtain ⟨n, hn⟩ := IsRationalOver.exists_birationalOver_affineSpace sY
  exact ⟨n, h.trans hn⟩

section DenseOpen

variable {X S : Scheme.{u}} (U : Opens X) (sX : X ⟶ S)

/-- A dense open set `U : Opens X` induces a partial isomorphism between `U` and `X`. -/
@[simps]
def Opens.partialIsoOfDense (hU : Dense (U : Set X)) : PartialIso U X where
  source := ⊤
  dense_source := dense_univ
  target := U
  dense_target := hU
  iso := U.toScheme.topIso

/-- A dense open set `U : Opens X` is birational to `X`.
@isnad1 id=biration.1h2v.s5.f040ee776508 from=seed src=0 shape=abfcd986 vocab=b6f4f6db
-/
lemma Opens.birational_of_dense (hU : Dense (U : Set X)) : Birational U X :=
  ⟨U.partialIsoOfDense hU⟩

set_option backward.defeqAttrib.useBackward true in
/-- A dense open set `U : Opens X` of a scheme `X` over `S` is `S`-birational to `X`.
@isnad1 id=biration.1h4v.s6.95b6dc344ea5 from=seed src=0 shape=82bc5d47 vocab=156c29b5
-/
lemma Opens.birationalOver_of_dense (hU : Dense (U : Set X)) : BirationalOver (U.ι ≫ sX) sX :=
  ⟨U.partialIsoOfDense hU, by simp [PartialIso.IsOver]⟩

/-- A dense open set `U : Opens X` of a `S`-rational scheme `X` is `S`-rational.
@isnad1 id=isration.1h4v.s6.c9877ddbb5c5 from=seed src=0 shape=e784461c vocab=1118a34f
-/
lemma Opens.isRationalOver_of_dense (hU : Dense (U : Set X)) [IsRationalOver sX] :
    IsRationalOver (U.ι ≫ sX) := by
  obtain ⟨n, hn⟩ := IsRationalOver.exists_birationalOver_affineSpace sX
  exact ⟨n, (U.birationalOver_of_dense sX hU).trans hn⟩

end DenseOpen

section OpenImmersion

variable {X U S : Scheme.{u}}

/-- A dominant open immersion `f : U ⟶ X` induces a partial isomorphism between `U` and `X`. -/
@[simps! source target iso]
noncomputable def Hom.partialIso (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] : U.PartialIso X :=
  (PartialIso.ofIso f.isoOpensRange).trans' (f.opensRange.partialIsoOfDense f.denseRange) rfl

/--
@isnad1 id=biration.0h3v.s4.6b3bf4363716 from=seed src=0 shape=616b0b27 vocab=e7c88fe6
-/
lemma Hom.birational (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] : Birational U X :=
  ⟨f.partialIso⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=biration.1h6v.s6.755c8f7fd958 from=seed src=0 shape=06b2c656 vocab=77624c7b
-/
lemma Hom.birationalOver (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] (sX : X ⟶ S) (sU : U ⟶ S)
    (hf : f ≫ sX = sU) : BirationalOver sU sX :=
  ⟨f.partialIso, by simp [PartialIso.IsOver, hf]⟩

end OpenImmersion

end AlgebraicGeometry.Scheme
