/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Tengoku

/-!
# Low-degree group cohomology compatibility

This file restores upstream aliases and multiplicative cocycle closure lemmas.
-/

@[expose] public section

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] {f g : G × G → M}

/--
@isnad1 id=ismulcoc.1h3v.s9.809e635c36f0 from=translated src=- shape=89cf417c vocab=e9665359
-/
alias groupCohomology.IsMulCocycle₂.of_mem_cocycles₂ :=
  groupCohomology.isMulCocycle₂_of_mem_cocycles₂

/--
@isnad1 id=ismulcoc.2h4v.s7.883da0ab4674 from=translated src=- shape=0b3770fa vocab=20a4c33e
-/
lemma groupCohomology.IsMulCocycle₂.mul
    (hf : groupCohomology.IsMulCocycle₂ f) (hg : groupCohomology.IsMulCocycle₂ g) :
    groupCohomology.IsMulCocycle₂ (f * g) :=
  fun a b c ↦ by simp [hf a, hg a, smul_mul', mul_mul_mul_comm]
