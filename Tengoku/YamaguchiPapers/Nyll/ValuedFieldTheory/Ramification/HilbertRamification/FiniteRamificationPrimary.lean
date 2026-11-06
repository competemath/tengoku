/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationPrimeToResidueTorsion
import Tengoku.Seed.Algebra.Group.Subgroup.Finite
import Tengoku.Seed.Algebra.CharP.Defs
import Tengoku.Seed.Data.Nat.Factorization.Basic
import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.Seed.GroupTheory.PGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite ramification groups in positive and zero residue characteristic

In positive residue characteristic p, factoring a finite annihilating order
as p^a times a prime-to-p integer reduces the assertion to prime-to-residue
torsion triviality. In residue characteristic zero, every positive finite
order is nonzero in the residue field, so the ramification group is trivial.

All groups and principal-unit conditions are the actual valuation-subring
constructions. Only finiteness of the ramification group is used;
no normality, Henselianity, discreteness, perfectness, or finite residue field
is required.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The actual finite ramification group is trivial in residue characteristic zero.
@isnad1 id=eq.0h3v.s14.c4cebb450709 from=translated src=- shape=b3df4301 vocab=8eea1301
-/
theorem ramificationGroup_eq_bot_of_residueCharZero
    (A : _root_.ValuationSubring L) [CharZero (IsLocalRing.ResidueField A)]
    [Finite (ramificationGroup K A)] :
    ramificationGroup K A = ⊥ := by
  apply bot_unique
  intro σ hσ
  change σ = 1
  let τ : ramificationGroup K A := ⟨σ, hσ⟩
  have hτ : τ = 1 :=
    ramificationGroup_eq_one_of_pow_eq_one_of_residue_natCast_ne_zero K A
      τ (orderOf τ) (Nat.cast_ne_zero.mpr (orderOf_pos τ).ne') (pow_orderOf_eq_one τ)
  exact congrArg (fun t : ramificationGroup K A => (t : inertiaGroup K A)) hτ

end RamificationTheory.HilbertRamification.ValuationSubring
