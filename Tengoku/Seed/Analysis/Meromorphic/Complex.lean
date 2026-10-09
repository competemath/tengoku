/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Meromorphic.NormalForm
public import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Gamma function is meromorphic
-/

public section

open Set Complex

/--
@isnad1 id=meromorp.0h0v.s4.77f8cfac19fa from=seed src=0 shape=a94d82b8 vocab=1123223a
-/
lemma MeromorphicNFOn.Gamma : MeromorphicNFOn Gamma univ :=
  meromorphicNFOn_inv.mp <| AnalyticOnNhd.meromorphicNFOn <|
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_one_div_Gamma

-- TODO: restate `MeromorphicNFOn.Gamma` when `MeromorphicNF` is defined

/--
@isnad1 id=meromorp.0h0v.s4.2d92b1c91dd5 from=seed src=0 shape=e3d48bcb vocab=f2ed4627
-/
@[fun_prop]
lemma Meromorphic.Gamma : Meromorphic Gamma :=
  meromorphicOn_univ.mp MeromorphicNFOn.Gamma.meromorphicOn

/--
@isnad1 id=meromorp.0h1v.s4.ab842f82f87c from=seed src=0 shape=89f438f7 vocab=a9cbd88c
-/
@[fun_prop]
lemma MeromorphicOn.Gamma {s} : MeromorphicOn Gamma s :=
  Meromorphic.Gamma.meromorphicOn
