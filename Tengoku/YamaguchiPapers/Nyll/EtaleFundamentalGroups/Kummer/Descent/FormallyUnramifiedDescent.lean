/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Etale.Kaehler
import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Faithfully flat descent of formal unramifiedness

Formal unramifiedness of a composite descends across a formally etale,
faithfully flat final map.  The proof identifies the base change of the
Kaehler differentials with the differentials of the composite and then uses
faithful flatness to reflect triviality.
-/

namespace EtaleFundamentalGroups.Kummer

open scoped TensorProduct

universe uR uS uT

/--
If `T` is formally unramified over `R`, and `T/S` is both formally etale and
faithfully flat, then `S` is formally unramified over `R`.
@isnad1 id=formally.0h3v.s7.287506855aff from=translated src=- shape=a89a38ec vocab=8dcc239a
-/
theorem formallyUnramified_of_formallyEtale_faithfullyFlat
    {R : Type uR} {S : Type uS} {T : Type uT}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyUnramified R T] [Algebra.FormallyEtale S T]
    [Module.FaithfullyFlat S T] :
    Algebra.FormallyUnramified R S := by
  let : Subsingleton (T ⊗[S] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).toEquiv.injective.subsingleton
  exact
    ⟨Module.FaithfullyFlat.lTensor_reflects_triviality S T Ω[S⁄R]⟩

end EtaleFundamentalGroups.Kummer
