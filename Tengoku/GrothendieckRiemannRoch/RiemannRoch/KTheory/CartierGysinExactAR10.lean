/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.CartierGysinBaseChangeAR8

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kernel/cokernel preservation from exactness on a class (route AR10)

Abstract abelian-category lemmas discharging the `hker`/`hcok` hypotheses of
`CartierGysinAR8.cartierGysin_comp_map` when `Φ` is exact on short exact sequences with terms in a
`KerCokerClosed` class `P` (geometrically: finite pushforward on coherent sheaves).

* `isIso_cokernelComparison_of_exactOn`: `Φ` preserves the cokernel of `f : A ⟶ B` with
  `A, B ∈ P`, via `0 → ker p → A → ker π → 0` and `0 → ker π → B → coker f → 0`
  (`π = coker.π f`, `p : A → ker π` the induced epimorphism).
* `isIso_kernelComparison_of_exactOn`: the dual statement.
-/

set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open ExactGrothendieck.PrincipalGysin (KerCokerClosed)

universe u v

namespace ExactGrothendieck

namespace CartierGysinAR10

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u} [Category.{v} D] [Abelian D]
variable {P : C → Prop}

/-- An additive functor, exact on short exact sequences with terms in a kernel/cokernel-closed
class `P`, preserves the cokernel of every morphism between members of `P`.
@isnad1 id=preserve.2h9v.s7.259227a3b0e2 from=translated src=- shape=37c2c723 vocab=002041bf
-/
theorem preservesColimit_cokernel_of_exactOn (Φ : C ⥤ D) [Φ.Additive] (hP : KerCokerClosed P)
    (hΦ : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
      (S.map Φ).ShortExact)
    {A B : C} (f : A ⟶ B) (hA : P A) (hB : P B) :
    PreservesColimit (parallelPair f 0) Φ := by
  let π := cokernel.π f
  let p : A ⟶ kernel π := kernel.lift π f (cokernel.condition f)
  have hp : Epi p := by
    have : (ShortComplex.mk f π (cokernel.condition f)).Exact := ShortComplex.exact_cokernel f
    exact (ShortComplex.exact_iff_epi_kernel_lift _).1 this
  have hK : P (kernel π) := hP.kernel π hB (hP.cokernel f hA hB)
  have hKp : P (kernel p) := hP.kernel p hA hK
  let S1 : ShortComplex C := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS1 : S1.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance hp
  let S2 : ShortComplex C := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS2 : S2.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel π) inferInstance inferInstance
  have e1 := hΦ S1 hS1 hKp hA hK
  have e2 := hΦ S2 hS2 hK hB (hP.cokernel f hA hB)
  have hepi : Epi (Φ.map p) := e1.epi_g
  let S3 : ShortComplex D := ShortComplex.mk (Φ.map f) (Φ.map π) (by
    rw [← Φ.map_comp, cokernel.condition, Functor.map_zero])
  let φ : S3 ⟶ S2.map Φ :=
    { τ₁ := Φ.map p
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        change Φ.map p ≫ Φ.map (kernel.ι π) = Φ.map f ≫ 𝟙 _
        rw [← Φ.map_comp, Category.comp_id]
        simp [p]
      comm₂₃ := by
        change 𝟙 _ ≫ Φ.map π = Φ.map π ≫ 𝟙 _
        simp }
  haveI : Epi φ.τ₁ := hepi
  haveI : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  haveI : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  have hex : S3.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 e2.exact
  haveI : Epi S3.g := e2.epi_g
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f) ?_
  apply (CokernelCofork.isColimitMapCoconeEquiv _ Φ).2
  exact hex.gIsCokernel

/--
@isnad1 id=isiso.2h9v.s7.b398026d2e20 from=translated src=- shape=5e918ba5 vocab=2a4a3890
-/
theorem isIso_cokernelComparison_of_exactOn (Φ : C ⥤ D) [Φ.Additive] (hP : KerCokerClosed P)
    (hΦ : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
      (S.map Φ).ShortExact)
    {A B : C} (f : A ⟶ B) (hA : P A) (hB : P B) :
    IsIso (cokernelComparison f Φ) := by
  haveI := preservesColimit_cokernel_of_exactOn Φ hP hΦ f hA hB
  infer_instance

end CartierGysinAR10

end ExactGrothendieck
