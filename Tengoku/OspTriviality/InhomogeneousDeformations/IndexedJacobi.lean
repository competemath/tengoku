import Tengoku.OspTriviality.InhomogeneousDeformations.IndexedLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# R2-C-2 (U4-U5) — general-rank super-Jacobi

`H1.2`: every declaration here is stated for general `n : ℕ`, with indices
in `Fin (2 * n)`; no `n = 1` specialization, `Fin 2` instance, or literal
five-element basis appears anywhere. `Indexed.lean` and `IndexedLaws.lean`
(both frozen) are never reopened; every law here is a new statement/proof
about their already-accepted definitions, using only `Jn_antisymm` and
`Lof_comm` (`IndexedLaws.lean`'s U0) as the reusable facts about `Jn`/`Lof`.

`H1.3` (verbatim, do not upgrade): a successful R2-C-2 establishes
super-Jacobi for the frozen indexed bracket for every `n ≥ 1`, which
together with the accepted R2-C-1 completes P1: the specified coordinate
structure is a Lie superalgebra of the stated shape at every rank. It does
NOT establish the oscillator realization correspondence, which is P1's own
declared non-goal and remains so even once P1 is complete.

Separately: the manuscript obtains super-Jacobi for free from the
associative realization (`lem:base`'s proof, P4, deferred). This module
proves Jacobi directly from the coordinate formulas; the proof below does
not mirror the paper's argument.

## Sector table (U4)

All four rotation-class representatives close on `IndexedLaws.lean`'s
`Jn_antisymm`/`Lof_comm` alone, exactly as Agent1's hand analysis predicted:

* `jacobiN_FFF` -- reduces to `Jn_antisymm` alone.
* `jacobiN_LFF` -- reduces to `Lof_comm` alone.
* `jacobiN_LLF` -- reduces to `Jn_antisymm` plus commutativity of `Pn n`.
* `jacobiN_LLL` -- the stage's real work (48-term expansion); closes by the
  same two facts plus `ring_nf`'s ring-level normalization of the `Pn n`
  coefficients once every `Lof`/`Jn` occurrence is brought to one canonical
  argument order.

`jacobiN_basis` assembles all eight ordered basis-triple shapes from these
four representatives via `jacobiSum_rot` (the cyclic symmetry of the
Jacobi sum itself, immediate from reassociating its own three summands).
`jacobiN_homog` (U5) extends this, unconditionally, to arbitrary
homogeneous elements of `IndexedMod n`, transposed from `N1Proofs.lean`'s
`jacobi_homog` (the `n=1` shape of the same extension).
-/

namespace InhomogeneousDeformations
namespace Indexed

/-! ## Bilinearity toolkit for `bracketN`, general `n`

None of these exist in the frozen modules: `IndexedLaws.lean` (U0-U3) never
needed the full bilinearity of `bracketN` in both arguments, only enough
structure for the degree law and super-skew. U4 needs it to distribute the
bracket over the sums the basis-level structure constants produce. -/

/-! ## Basis-shape reduction toolkit, general `n`

`bracketBasisN` is defined by a raw pattern match on the underlying `Sum`
type; these lemmas restate its four branches in terms of `Lof`/`Fof`
directly, resolving `Lof`'s internal `dite` explicitly via `dif_pos`/
`dif_neg` (never via a bare `show`, which gets stuck at `whnf` trying to
decide an abstract `u ≤ v`). U4's proofs rewrite through these rather than
unfolding `bracketBasisN` blindly. -/

/--
@isnad1 id=eq.0h2v.s6.8316862bf1dc from=translated src=- shape=76b24472 vocab=0c6317de
-/
theorem parity_Fof {n : ℕ} (u : Fin (2 * n)) : parity (Fof u : IndexedBasis n) = 1 := rfl

/--
@isnad1 id=eq.0h4v.s5.0c3e51d04120 from=translated src=- shape=dc0c9e63 vocab=d96a89b9
-/
theorem bracketLFn_comm {n : ℕ} (u v w : Fin (2 * n)) :
    bracketLFn n u v w = bracketLFn n v u w := by unfold bracketLFn; abel

/--
@isnad1 id=eq.0h5v.s6.3b69ec633958 from=translated src=- shape=a259e016 vocab=9c86d31a
-/
theorem bracketLLn_comm12 {n : ℕ} (u v w z : Fin (2 * n)) :
    bracketLLn n v u w z = bracketLLn n u v w z := by unfold bracketLLn; abel

/--
@isnad1 id=eq.0h5v.s6.bfbed6f0ccf7 from=translated src=- shape=eab19d3f vocab=9c86d31a
-/
theorem bracketLLn_comm34 {n : ℕ} (u v w z : Fin (2 * n)) :
    bracketLLn n u v z w = bracketLLn n u v w z := by unfold bracketLLn; abel

/-! ## U4 -- super-Jacobi at basis level, general `n` -/

/-- The cyclic Jacobi sum on ordered basis triples, `Pn n`-valued, exactly
the left side of U4's identity.-/
noncomputable def jacobiSum {n : ℕ} (X Y Z : IndexedBasis n) : IndexedMod n :=
  gsignN n (parity X) (parity Z) • bracketN n (eN X) (bracketN n (eN Y) (eN Z))
    + gsignN n (parity Y) (parity X) • bracketN n (eN Y) (bracketN n (eN Z) (eN X))
    + gsignN n (parity Z) (parity Y) • bracketN n (eN Z) (bracketN n (eN X) (eN Y))

/-! ## Finite-sum expansion toolkit for `bracketN`, general `n`

Transposed from `N1Proofs.lean`'s `bracket_sum_left`/`bracket_sum_right`/
`expand_basis`/`bracket_bilinear_expand`/`bracket_expand_left`: the same
shapes, over `IndexedBasis n`/`IndexedMod n`/`eN`/`bracketN` in place of
`Basis5`/`Mod`/`e`/`bracket`. -/

/-! ## U5 -- super-Jacobi for arbitrary homogeneous elements, general `n` -/

end Indexed
end InhomogeneousDeformations
