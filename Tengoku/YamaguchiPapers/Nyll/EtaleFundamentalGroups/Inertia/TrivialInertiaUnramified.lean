/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.NumberTheory.RamificationInertia.Galois
import Tengoku.Seed.RingTheory.RamificationInertia.Ramification
import Tengoku.Seed.LinearAlgebra.FreeModule.Finite.Matrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trivial inertia gives unramifiedness in every characteristic

The fundamental degree identity and orbit-stabilizer count show that trivial
inertia forces both ramification index one and separability of the residue
extension. No perfectness hypothesis on the residue field is needed.
-/

noncomputable section

open Algebra
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
  (G : Type w) [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]

end EtaleFundamentalGroups.Inertia
