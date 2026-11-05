/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.GroupTheory.FiniteAbelian.Duality
import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Kummer.Concrete.FiniteCharacterEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# finite actual-field form

Let `L/K` be a finite abelian Galois extension whose Galois group is killed by
`n`, and suppose that `K` contains a primitive `n`-th root of unity.  This file
proves that `L` is generated over `K` by all nonzero `beta : L` such that
`beta ^ n` belongs to `K`.

The proof uses finite-abelian character separation and the finite Kummer
character isomorphism.  It is the finite `n`-th-power, actual-field form of
the Kummer generation theorem; it is not the general abstract-module or infinite statement.
-/

noncomputable section

namespace KummerTheory

open scoped IsMulCommutative

section FiniteKummerGeneration

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- All nonzero elements of `L` whose `n`-th power comes from `K`.-/
def finiteKummerRootSet (n : ℕ+) : Set L :=
  {beta | beta ≠ 0 ∧
    ∃ a : Kˣ, beta ^ (n : ℕ) = algebraMap K L (a : K)}

/-- A primitive `n`-th root in `K` implies the field-level hypothesis that
all `n`-th roots of unity occurring in `L` come from `K`.
@isnad1 id=nthroots.1h3v.s5.6b0e75445ba3 from=translated src=- shape=084f9c87 vocab=54236ba2
-/
theorem nthRootsOfUnityInBase_of_primitiveRoots
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    NthRootsOfUnityInBase (K := K) (L := L) n := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  intro u hu
  let eta : rootsOfUnity (n : ℕ) L := ⟨u, hu⟩
  let e : rootsOfUnity (n : ℕ) K ≃* rootsOfUnity (n : ℕ) L :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective hmu
  refine ⟨(e.symm eta : rootsOfUnity (n : ℕ) K).1, ?_⟩
  apply Units.ext
  exact rootsOfUnityEquivOfPrimitiveRoots_symm_apply
    (algebraMap K L).injective hmu eta

end FiniteKummerGeneration

end KummerTheory
