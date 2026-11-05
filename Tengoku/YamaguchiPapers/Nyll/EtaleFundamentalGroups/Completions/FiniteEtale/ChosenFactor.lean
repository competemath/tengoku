/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ResidueLift
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.FiniteEtale.HenselianAscent
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedCompletion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trivializing a chosen finite étale local factor after a finite residue lift

Suppose `R → B` is a local map inducing an isomorphism on residue fields and
`D / B` is finite étale local.  Lift the actual finite separable residue field
`κ(D) / κ(R)` to the explicit finite étale local `R`-algebra constructed in
`CompleteFiniteEtaleResidueLift`.  After base change to `B`, that lift is
isomorphic to `D`.

The proof is concrete.  Hensel's lemma lifts the distinguished residue
generator to a root in `D`; residue generation and Nakayama make the resulting
tensor-product map surjective, and equality of the finite free ranks makes it
an isomorphism.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial
open scoped TensorProduct

universe u

namespace Kummer

end Kummer

end EtaleFundamentalGroups

end
