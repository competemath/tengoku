/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.Basic
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Locality of finite iterated Kummer root covers

If every radicand belongs to the closed point of a local base ring, adjoining positive roots of
those radicands one after another stays local.  The proof also keeps track of the closed point:
the image of the original maximal ideal remains inside the maximal ideal at every stage.

The resulting `IsLocalRing` proofs are theorems, not global recursive instances.  Consumers install
one proof locally when needed.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

end EtaleFundamentalGroups.Kummer

end
