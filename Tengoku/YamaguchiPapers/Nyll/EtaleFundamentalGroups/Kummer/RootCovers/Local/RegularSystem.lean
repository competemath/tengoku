/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Regularity
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A regular system under one local Kummer root

Adjoining a positive root of the first member of a regular system replaces
that member by the new root.  The resulting list is again a regular system
generating the maximal ideal.  Consequently the root cover is a domain and
every member of the replacement system is prime.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped Pointwise
open Polynomial
open IsLocalRing
open RingTheory.Sequence

universe u

attribute [local instance] RingHomInvPair.of_ringEquiv

end EtaleFundamentalGroups.Kummer

end
