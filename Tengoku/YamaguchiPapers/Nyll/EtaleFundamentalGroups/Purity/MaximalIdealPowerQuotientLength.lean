/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.RingTheory.FiniteLength
import Tengoku.Seed.RingTheory.Ideal.KrullsHeightTheorem
import Tengoku.Seed.RingTheory.Ideal.Operations
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite length of maximal-ideal-power quotients

A positive power of the maximal ideal has that same maximal ideal as its
only minimal prime.  Its quotient is Artinian, and restriction of scalars
gives finite length over the original Noetherian local ring.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Quotients of a Noetherian local ring by powers of its maximal ideal
have finite length as modules over the original ring.
@isnad1 id=isfinite.0h2v.s7.3d26d02d5b0d from=translated src=- shape=26ad63ae vocab=89baec26
-/
theorem isFiniteLength_quotient_maximalIdeal_pow (n : ℕ) :
    IsFiniteLength R (R ⧸ maximalIdeal R ^ n) := by
  have hart : IsArtinianRing (R ⧸ maximalIdeal R ^ n) := by
    cases n with
    | zero =>
        rw [pow_zero, Ideal.one_eq_top]
        infer_instance
    | succ n =>
        apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
        rw [← Ideal.radical_minimalPrimes,
          (maximalIdeal R).radical_pow (Nat.succ_ne_zero n),
          (maximalIdeal.isMaximal R).isPrime.isRadical.radical,
          Ideal.minimalPrimes_eq_subsingleton_self]
        exact Set.mem_singleton (maximalIdeal R)
  let : IsArtinianRing (R ⧸ maximalIdeal R ^ n) := hart
  have hartR : IsArtinian R (R ⧸ maximalIdeal R ^ n) :=
    isArtinian_of_surjective_algebraMap
      (R := R ⧸ maximalIdeal R ^ n) (S := R) (M := R ⧸ maximalIdeal R ^ n)
      Ideal.Quotient.mk_surjective
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hartR⟩

end EtaleFundamentalGroups.Purity
