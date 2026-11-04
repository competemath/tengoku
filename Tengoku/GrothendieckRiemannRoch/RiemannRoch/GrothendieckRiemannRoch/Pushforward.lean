/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.Presentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Functorial maps on exact Grothendieck groups

An object map preserving the declared exact triples induces an additive map on the corresponding
Grothendieck groups. Identity and composition are proved from the quotient presentation. In a
geometric instantiation this is the algebraic skeleton of pullback on `K₀`, or of a finite/Tor
dimension derived pushforward on `G₀` or perfect-complex `K`-theory.
-/

noncomputable section
