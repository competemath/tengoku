/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.AdicCompletion.AsTensorProduct
import Tengoku.Seed.RingTheory.AdicCompletion.LocalRing
import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Algebra
import Tengoku.Seed.RingTheory.RingHom.Etale
import Tengoku.Seed.RingTheory.TensorProduct.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closed primes in a completion base change

The closed prime selected in a finite algebra need not be the unique closed
prime.  Nevertheless, extension along a faithfully flat local base change
with unchanged residue field carries that particular prime to a maximal
ideal of the tensor product.  For maximal-adic completion this gives the
canonical completed closed point before any local factor is split off.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uR' uS

end EtaleFundamentalGroups

end
