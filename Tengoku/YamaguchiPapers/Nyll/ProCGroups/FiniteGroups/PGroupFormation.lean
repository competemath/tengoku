/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ProCGroups.FiniteGroups.StandardClasses

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The full formation of finite p-groups

The existing formation, subgroup closure and extension closure proofs supply
the full-formation property used by maximal pro-p residual quotients.
-/

namespace ProCGroups.FiniteGroupClass

/-- Finite p-groups form a full formation, using their established subgroup
and extension closure properties.
@isnad1 id=fullform.0h1v.s3.ac6d2ba5da4e from=translated src=- shape=9ee3c16b vocab=3e52010c
-/
theorem pGroup_fullFormation (p : ℕ) [Fact p.Prime] : FullFormation (pGroup p) where
  melnikovFormation :=
    { formation := pGroup_formation p
      normalSubgroupClosed := fun N _ hG => pGroup_subgroupClosed p N hG
      extensionClosed := pGroup_extensionClosed p }
  subgroupClosed := pGroup_subgroupClosed p

end ProCGroups.FiniteGroupClass
