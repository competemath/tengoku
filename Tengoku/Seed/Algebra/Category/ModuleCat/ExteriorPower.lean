/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.LinearAlgebra.ExteriorPower.Basic
public import Tengoku.Seed.Algebra.Category.ModuleCat.Basic

/-!
# The exterior powers as functors on the category of modules

In this file, given `M : ModuleCat R` and `n : ℕ`, we define `M.exteriorPower n : ModuleCat R`,
and this extends to a functor `ModuleCat.exteriorPower.functor : ModuleCat R ⥤ ModuleCat R`.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The exterior power of an object in `ModuleCat R`. -/
def exteriorPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⋀[R]^n M)

-- this could be an abbrev, but using a def eases automation
/-- The type of `n`-alternating maps on `M : ModuleCat R` to `N : ModuleCat R`. -/
def AlternatingMap (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : ℕ) :=
  _root_.AlternatingMap R M N (Fin n)

instance (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : ℕ) :
    FunLike (M.AlternatingMap N n) (Fin n → M) N :=
  inferInstanceAs (FunLike (M [⋀^(Fin n)]→ₗ[R] N) (Fin n → M) N)

namespace AlternatingMap

variable {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}

/--
@isnad1 id=eq.1h6v.s7.9aabe39b49a3 from=seed src=0 shape=f2374774 vocab=feaa896d
-/
@[ext]
lemma ext {φ φ' : M.AlternatingMap N n} (h : ∀ (x : Fin n → M), φ x = φ' x) :
    φ = φ' :=
  _root_.AlternatingMap.ext h

variable (φ : M.AlternatingMap N n) {N' : ModuleCat.{max u v} R} (g : N ⟶ N')

/-- The postcomposition of an alternating map by a linear map. -/
def postcomp : M.AlternatingMap N' n :=
  g.hom.compAlternatingMap φ

/--
@isnad1 id=eq.0h8v.s9.a110f7bfbb1c from=seed src=0 shape=0e588688 vocab=e5e3df0a
-/
@[simp]
lemma postcomp_apply (x : Fin n → M) :
    φ.postcomp g x = g (φ x) := rfl

end AlternatingMap

namespace exteriorPower

/-- Constructor for elements in `M.exteriorPower n` when `M` is an object of `ModuleCat R`
and `n : ℕ`. -/
def mk {M : ModuleCat.{v} R} {n : ℕ} :
    M.AlternatingMap (M.exteriorPower n) n :=
  exteriorPower.ιMulti _ _

/--
@isnad1 id=eq.1h6v.s7.4466b599f694 from=seed src=0 shape=3abb8186 vocab=9bbaae9a
-/
@[ext]
lemma hom_ext {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}
    {f g : M.exteriorPower n ⟶ N}
    (h : mk.postcomp f = mk.postcomp g) : f = g := by
  ext : 1
  exact exteriorPower.linearMap_ext h

/-- The morphism `M.exteriorPower n ⟶ N` induced by an alternating map. -/
noncomputable def desc {M : ModuleCat.{v} R} {n : ℕ} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) : M.exteriorPower n ⟶ N :=
  ofHom (exteriorPower.alternatingMapLinearEquiv φ)

/--
@isnad1 id=eq.0h6v.s9.fc1fcc6df0d4 from=seed src=0 shape=6f907277 vocab=7b878526
-/
@[simp]
lemma desc_mk {M : ModuleCat.{v} R} {n : ℕ} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) (x : Fin n → M) :
    desc φ (mk x) = φ x := by
  apply exteriorPower.alternatingMapLinearEquiv_apply_ιMulti

/-- The morphism `M.exteriorPower n ⟶ N.exteriorPower n` induced by a morphism `M ⟶ N`
in `ModuleCat R`. -/
noncomputable def map {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℕ) :
    M.exteriorPower n ⟶ N.exteriorPower n :=
  ofHom (_root_.exteriorPower.map n f.hom)

/--
@isnad1 id=eq.0h6v.s9.70ede31abb8c from=seed src=0 shape=6921c4c6 vocab=3660515a
-/
@[simp]
lemma map_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : ℕ} (x : Fin n → M) :
    map f n (mk x) = mk (f ∘ x) := by
  apply exteriorPower.map_apply_ιMulti

variable (R) in
/-- The functor `ModuleCat R ⥤ ModuleCat R` which sends a module to its
`n`th exterior power. -/
@[simps]
noncomputable def functor (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} R where
  obj M := M.exteriorPower n
  map f := map f n

/-- The isomorphism `M.exteriorPower 0 ≅ ModuleCat.of R R`. -/
noncomputable def iso₀ (M : ModuleCat.{u} R) : M.exteriorPower 0 ≅ ModuleCat.of R R :=
  (exteriorPower.zeroEquiv R M).toModuleIso

/--
@isnad1 id=eq.0h3v.s9.3b6a5e550286 from=seed src=0 shape=59ee8040 vocab=1b06de16
-/
@[simp]
lemma iso₀_hom_apply {M : ModuleCat.{u} R} (f : Fin 0 → M) :
    (iso₀ M).hom (mk f) = 1 :=
  exteriorPower.zeroEquiv_ιMulti _

/--
@isnad1 id=eq.0h4v.s7.395d69a870e8 from=seed src=0 shape=728acaa5 vocab=471b2bf9
-/
@[reassoc (attr := simp)]
lemma iso₀_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    map f 0 ≫ (iso₀ N).hom = (iso₀ M).hom :=
  ModuleCat.hom_ext (exteriorPower.zeroEquiv_naturality f.hom)

/-- The isomorphism `M.exteriorPower 1 ≅ M`. -/
noncomputable def iso₁ (M : ModuleCat.{u} R) : M.exteriorPower 1 ≅ M :=
  (exteriorPower.oneEquiv R M).toModuleIso

/--
@isnad1 id=eq.0h3v.s9.a25b79be5940 from=seed src=0 shape=ac46fb3e vocab=cc4473af
-/
@[simp]
lemma iso₁_hom_apply {M : ModuleCat.{u} R} (f : Fin 1 → M) :
    (iso₁ M).hom (mk f) = f 0 :=
  exteriorPower.oneEquiv_ιMulti _

/--
@isnad1 id=eq.0h4v.s7.c163b5e22882 from=seed src=0 shape=d0432d4c vocab=5d433457
-/
@[reassoc (attr := simp)]
lemma iso₁_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    map f 1 ≫ (iso₁ N).hom = (iso₁ M).hom ≫ f :=
  ModuleCat.hom_ext (exteriorPower.oneEquiv_naturality f.hom)

variable (R)

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `M.exteriorPower 0 ≅ ModuleCat.of R R`. -/
noncomputable def natIso₀ : functor.{u} R 0 ≅ (Functor.const _).obj (ModuleCat.of R R) :=
  NatIso.ofComponents iso₀

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `M.exteriorPower 1 ≅ M`. -/
noncomputable def natIso₁ : functor.{u} R 1 ≅ 𝟭 _ :=
  NatIso.ofComponents iso₁

end exteriorPower

end ModuleCat
