/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The idele topology

The idele group `I_K` carries the restricted-product topology. This file records
the topological-group structure and the continuity of every local
component map.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The local integral-unit subgroup is open in the multiplicative group of a
finite completion.
@isnad1 id=isopen.0h2v.s10.1b509b5d9337 from=translated src=- shape=755de787 vocab=0a03a71a
-/
theorem isOpen_finiteLocalUnits (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen
      ((v.adicCompletionIntegers K).units :
        Set (v.adicCompletion K)ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)

/--
@isnad1 id=fact.0h1v.s10.54938189a126 from=translated src=- shape=af7addbb vocab=83e296d3
-/
instance finiteLocalUnitsOpen :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen
        ((v.adicCompletionIntegers K).units :
          Set (v.adicCompletion K)ˣ)) :=
  ⟨isOpen_finiteLocalUnits K⟩

/--
@isnad1 id=istopolo.0h1v.s10.c11febcf4244 from=translated src=- shape=9499e9bc vocab=c159b0bc
-/
instance finiteIdeleGroupIsTopologicalGroup :
    IsTopologicalGroup (FiniteIdeleGroup K) :=
  inferInstance

/--
@isnad1 id=istopolo.0h1v.s11.25e0c0de3564 from=translated src=- shape=9499e9bc vocab=3bf6e429
-/
instance ideleGroupIsTopologicalGroup :
    IsTopologicalGroup (IdeleGroup K) :=
  inferInstance

namespace IdeleGroup

variable {K}

/-- Evaluation at an archimedean place is a continuous homomorphism.-/
def infiniteComponentContinuous (v : InfinitePlace K) :
    IdeleGroup K →ₜ* v.Completionˣ where
  __ := infiniteComponent v
  continuous_toFun :=
    (continuous_apply v).comp
      (ContinuousMulEquiv.piUnits.continuous.comp continuous_fst)

/-- Evaluation at a finite place is a continuous homomorphism.-/
def finiteComponentContinuous (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K →ₜ* (v.adicCompletion K)ˣ where
  __ := finiteComponent v
  continuous_toFun :=
    (RestrictedProduct.continuous_eval v).comp continuous_snd

/--
@isnad1 id=eq.0h3v.s12.2acdf79a79c7 from=translated src=- shape=b1a4d47a vocab=623efb79
-/
@[simp]
theorem infiniteComponentContinuous_apply
    (a : IdeleGroup K) (v : InfinitePlace K) :
    infiniteComponentContinuous v a =
      ContinuousMulEquiv.piUnits a.1 v :=
  rfl

/--
@isnad1 id=eq.0h3v.s12.f08e38c313de from=translated src=- shape=3516b842 vocab=26c2c668
-/
@[simp]
theorem finiteComponentContinuous_apply
    (a : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponentContinuous v a = a.2 v :=
  rfl

end IdeleGroup
