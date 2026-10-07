/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Homology.HomologicalComplexLimits

/-!
# Kernels and cokernels in categories of homological complexes

-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι C : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  {K L : HomologicalComplex C c} (f : K ⟶ L)

/--
@isnad1 id=haskerne.0h6v.s6.72b1a985de67 from=seed src=0 shape=5ff75f88 vocab=5c068070
-/
lemma hasKernel_of_hasKernel_f [∀ i, HasKernel (f.f i)] : HasKernel f :=
  have (i : ι) : HasLimit (parallelPair f 0 ⋙ eval C c i) :=
    hasLimit_of_iso (F := (parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  ⟨_, isLimitConeOfHasLimitEval _⟩

/--
@isnad1 id=hascoker.0h6v.s6.e0ea858d62db from=seed src=0 shape=5ff75f88 vocab=88a9a178
-/
lemma hasCokernel_of_hasCokernel_f [∀ i, HasCokernel (f.f i)] : HasCokernel f :=
  have (i : ι) : HasColimit (parallelPair f 0 ⋙ eval C c i) :=
    hasColimit_of_iso (F := (parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  ⟨_, isColimitCoconeOfHasColimitEval _⟩

/--
@isnad1 id=preserve.0h7v.s7.7001e53733ae from=seed src=0 shape=d0381863 vocab=af70178b
-/
lemma eval_preservesLimit_of_hasKernel_f [∀ i, HasKernel (f.f i)] (i : ι) :
    PreservesLimit (parallelPair f 0) (eval C c i) :=
  have (i : ι) : HasLimit (parallelPair f 0 ⋙ eval C c i) :=
    hasLimit_of_iso (F := (parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  preservesLimit_of_preserves_limit_cone
    (isLimitConeOfHasLimitEval _) (limit.isLimit _)

/--
@isnad1 id=preserve.0h7v.s7.4bc96e43247e from=seed src=0 shape=d0381863 vocab=6cfb5bee
-/
lemma eval_preservesColimit_of_hasCokernel_f [∀ i, HasCokernel (f.f i)] (i : ι) :
    PreservesColimit (parallelPair f 0) (eval C c i) :=
  have (i : ι) : HasColimit (parallelPair f 0 ⋙ eval C c i) :=
    hasColimit_of_iso (F := (parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  preservesColimit_of_preserves_colimit_cocone
    (isColimitCoconeOfHasColimitEval _) (colimit.isColimit _)

end HomologicalComplex
