/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Algebra.Category.ModuleCat.Sheaf.Colimits
import Tengoku.LanaOka.Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules
import Tengoku.LanaOka.Oka.Topology.Sheaves.Cohomology.PullbackZero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cohomology of sheaves of modules on locally ringed spaces

For a locally ringed space `Y` and a sheaf of `𝒪_Y`-modules `M`, the cohomology `Hᵠ(Y, M)` is
the sheaf cohomology of the underlying abelian sheaf `M.toAb`. The forgetful functor
`SheafOfModules 𝒪_Y ⥤ AbSheaf Y` is exact, so a short exact sequence of sheaves of modules has
a long exact cohomology sequence.

For a morphism `f : X ⟶ Y` of locally ringed spaces there is a canonical morphism of abelian
sheaves `f⁻¹ M ⟶ f^* M = 𝒪_X ⊗_{f⁻¹ 𝒪_Y} f⁻¹ M`, adjoint to the underlying morphism of abelian
sheaves of the unit `M ⟶ f_* f^* M`. Composing the pullback map `Hᵠ(Y, M) → Hᵠ(X, f⁻¹ M)` with
it gives the comparison map `Hᵠ(Y, M) → Hᵠ(X, f^* M)`.

## Main definitions and results

* `AlgebraicGeometry.LocallyRingedSpace.modulesToAb Y`: the exact forgetful functor
  `SheafOfModules 𝒪_Y ⥤ AbSheaf Y`, and `SheafOfModules.toAb M` its value on `M`.
* `AlgebraicGeometry.LocallyRingedSpace.H M q`: the cohomology `Hᵠ(Y, M)`, with
  `H.map`, `H.equiv₀`, the connecting homomorphisms `H.δ` and exactness `H.exact₁`, `H.exact₂`,
  `H.exact₃`.
* `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackAbToPullbackModules f`: the natural
  transformation `f⁻¹ M ⟶ f^* M` of abelian sheaves.
* `AlgebraicGeometry.LocallyRingedSpace.Hom.cohomologyMap f M q : Hᵠ(Y, M) →+ Hᵠ(X, f^* M)`,
  natural in `M` (`Hom.cohomologyMap_map`), compatible with connecting homomorphisms whenever
  `f^*` preserves the short exact sequence (`Hom.cohomologyMap_δ`), and given in degree zero by
  the unit `M(Y) → (f^* M)(X)` (`Hom.equiv₀_cohomologyMap`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

section Forget

variable (Y : LocallyRingedSpace.{u})

/-- The forgetful functor from sheaves of `𝒪_Y`-modules to abelian sheaves on `Y`
(`SheafOfModules.toSheaf`, typed as a functor to `TopCat.AbSheaf`). -/
noncomputable def modulesToAb :
    SheafOfModules.{u} Y.ringSheaf ⥤ TopCat.AbSheaf Y.toPresheafedSpace :=
  SheafOfModules.toSheaf.{u} Y.ringSheaf

instance : (modulesToAb Y).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} Y.ringSheaf).Additive

instance : PreservesFiniteLimits (modulesToAb Y) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} Y.ringSheaf))

instance : PreservesFiniteColimits (modulesToAb Y) :=
  inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} Y.ringSheaf))

variable {Y}

/--
@isnad1 id=eq.0h6v.s15.529256981225 from=translated src=- shape=98bff2ae vocab=7e675a28
-/
@[simp]
lemma modulesToAb_map_hom_app_apply {M N : SheafOfModules.{u} Y.ringSheaf} (φ : M ⟶ N)
    (U : (Opens Y.toPresheafedSpace)ᵒᵖ) (s : M.val.obj U) :
    ((modulesToAb Y).map φ).hom.app U s = φ.val.app U s :=
  rfl

/-- The forgetful functor to abelian sheaves preserves short exact sequences.
@isnad1 id=shortexa.1h2v.s11.82597d1fa6e9 from=translated src=- shape=e83693bb vocab=bc1f217a
-/
lemma shortExact_map_modulesToAb {S : ShortComplex (SheafOfModules.{u} Y.ringSheaf)}
    (hS : S.ShortExact) : (S.map (modulesToAb Y)).ShortExact :=
  hS.map_of_exact _

end Forget

/-- The underlying abelian sheaf of a sheaf of modules on a locally ringed space. -/
noncomputable abbrev _root_.SheafOfModules.toAb {Y : LocallyRingedSpace.{u}}
    (M : SheafOfModules.{u} Y.ringSheaf) : TopCat.AbSheaf Y.toPresheafedSpace :=
  (modulesToAb Y).obj M

section Cohomology

variable {Y : LocallyRingedSpace.{u}}

/-- The cohomology `Hᵠ(Y, M)` of a sheaf of modules on a locally ringed space: the sheaf
cohomology of the underlying abelian sheaf. -/
abbrev H (M : SheafOfModules.{u} Y.ringSheaf) (q : ℕ) : Type u :=
  TopCat.Sheaf.H M.toAb q

namespace H

variable {M N K : SheafOfModules.{u} Y.ringSheaf}

/-- The map `Hᵠ(Y, M) → Hᵠ(Y, N)` induced by a morphism of sheaves of modules. -/
noncomputable def map (φ : M ⟶ N) (q : ℕ) : H M q →+ H N q :=
  TopCat.Sheaf.H.map ((modulesToAb Y).map φ) q

/--
@isnad1 id=eq.0h4v.s12.d4e18605bc62 from=translated src=- shape=a4d7dd17 vocab=a16d84e1
-/
@[simp]
lemma map_id_apply {q : ℕ} (x : H M q) : map (𝟙 M) q x = x := by
  simp [map]

/--
@isnad1 id=eq.0h8v.s13.a0a97bcf999e from=translated src=- shape=e03efb4b vocab=4c15836a
-/
lemma map_comp_apply (φ : M ⟶ N) (ψ : N ⟶ K) {q : ℕ} (x : H M q) :
    map (φ ≫ ψ) q x = map ψ q (map φ q x) := by
  simp only [map, Functor.map_comp, TopCat.Sheaf.H.map_comp_apply]

/-- Degree zero cohomology is the module of global sections (as an additive group). -/
noncomputable def equiv₀ (M : SheafOfModules.{u} Y.ringSheaf) : H M 0 ≃+ M.toAb.obj.obj (op ⊤) :=
  TopCat.Sheaf.H.equiv₀ M.toAb

/--
@isnad1 id=eq.0h5v.s17.e16107d2ce02 from=translated src=- shape=e0a2b762 vocab=6ffe0460
-/
lemma equiv₀_map (φ : M ⟶ N) (x : H M 0) :
    equiv₀ N (map φ 0 x) = φ.val.app (op ⊤) (equiv₀ M x) :=
  TopCat.Sheaf.H.equiv₀_map _ x

section LongExactSequence

variable {S : ShortComplex (SheafOfModules.{u} Y.ringSheaf)} (hS : S.ShortExact)

/-- The connecting homomorphism `Hⁿ⁰(Y, S.X₃) → Hⁿ¹(Y, S.X₁)` (with `n₁ = n₀ + 1`) of a short
exact sequence of sheaves of modules. -/
noncomputable def δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : H S.X₃ n₀ →+ H S.X₁ n₁ :=
  TopCat.Sheaf.H.δ (shortExact_map_modulesToAb hS) n₀ n₁ h

include hS in
/-- Exactness of `Hⁿ(S.X₁) → Hⁿ(S.X₂) → Hⁿ(S.X₃)`.
@isnad1 id=exact.1h3v.s15.881ebe503958 from=translated src=- shape=0f2e837d vocab=8e3045d5
-/
lemma exact₂ (n : ℕ) : Function.Exact (map S.f n) (map S.g n) :=
  TopCat.Sheaf.H.exact₂ (shortExact_map_modulesToAb hS) n

/-- Exactness of `Hⁿ⁰(S.X₂) → Hⁿ⁰(S.X₃) → Hⁿ¹(S.X₁)`.
@isnad1 id=exact.2h4v.s15.e6a86a987e3a from=translated src=- shape=c60f85d1 vocab=5c6a3f41
-/
lemma exact₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Function.Exact (map S.g n₀) (δ hS n₀ n₁ h) :=
  TopCat.Sheaf.H.exact₃ (shortExact_map_modulesToAb hS) n₀ n₁ h

/-- Exactness of `Hⁿ⁰(S.X₃) → Hⁿ¹(S.X₁) → Hⁿ¹(S.X₂)`.
@isnad1 id=exact.2h4v.s15.963ed2524cb2 from=translated src=- shape=451008c9 vocab=6121ab0a
-/
lemma exact₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Function.Exact (δ hS n₀ n₁ h) (map S.f n₁) :=
  TopCat.Sheaf.H.exact₁ (shortExact_map_modulesToAb hS) n₀ n₁ h

include hS in
/-- `H⁰(S.X₁) → H⁰(S.X₂)` is injective.
@isnad1 id=injectiv.1h2v.s14.0104024240a6 from=translated src=- shape=62355e39 vocab=3ef2424e
-/
lemma map_f_injective_zero : Function.Injective (map S.f 0) :=
  fun _ _ hab => TopCat.Sheaf.H.map_f_injective_zero (shortExact_map_modulesToAb hS) hab

end LongExactSequence

end H

end Cohomology

section Comparison

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- The pushforward `f_*` of abelian sheaves along the continuous map underlying a morphism of
locally ringed spaces, typed as a functor between categories of `TopCat.AbSheaf`. -/
noncomputable abbrev Hom.pushforwardAb :
    TopCat.AbSheaf X.toPresheafedSpace ⥤ TopCat.AbSheaf Y.toPresheafedSpace :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base

/-- The adjunction `f⁻¹ ⊣ f_*` for abelian sheaves along the continuous map underlying a
morphism of locally ringed spaces. -/
noncomputable abbrev Hom.pullbackAbAdj :
    TopCat.Sheaf.pullbackAb f.base ⊣ f.pushforwardAb :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base

end Comparison

end AlgebraicGeometry.LocallyRingedSpace
