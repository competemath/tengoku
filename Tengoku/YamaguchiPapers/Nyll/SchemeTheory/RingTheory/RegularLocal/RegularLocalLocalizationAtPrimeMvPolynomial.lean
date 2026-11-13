/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Tengoku.Seed.RingTheory.RegularLocalRing.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# is Regular Local Ring localization at Prime mv Polynomial
-/

section ProofImplementation
namespace Tengoku.YamaguchiPapers end Tengoku.YamaguchiPapers open Tengoku.YamaguchiPapers 
namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace isRegularLocalRing_localization_atPrime_mvPolynomial

/--
@isnad1 id=isregula.0h3v.s7.49bf1e90e0b4 from=translated src=- shape=0acd5df9 vocab=e95e7179
-/
theorem _root_.Tengoku.YamaguchiPapers.isRegularLocalRing_localization_atPrime_mvPolynomial (k : Type*) [Field k] (n : ℕ)
  (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  IsRegularRing.isRegularLocalRing_localization q
end isRegularLocalRing_localization_atPrime_mvPolynomial
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
-- Tengoku: root names of this library moved to Tengoku.YamaguchiPapers so they do not collide with other libraries (generated)
