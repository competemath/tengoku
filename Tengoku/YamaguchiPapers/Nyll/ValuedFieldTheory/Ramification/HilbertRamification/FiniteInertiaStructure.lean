/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteRamificationPrimary
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteOrderValuation
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap
import Tengoku.Seed.Algebra.CharP.Reduced
import Tengoku.Seed.GroupTheory.Sylow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Structure of finite inertia

The actual residue-unit character has ramification kernel. Finite inertia fixes
values, so this character is defined on all inertia. In residue characteristic
zero its kernel is trivial and inertia is commutative. In residue characteristic
p every p-subgroup lies in the ramification kernel, which is itself a p-group.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

end RamificationTheory.HilbertRamification.ValuationSubring
