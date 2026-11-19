import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.Core
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# LN97 Lemma 6.52: auxiliary polynomial, first assembly step

This file begins the formalization of Lemma 6.52 on pp. 305--308 of
Lidl--Niederreiter.

At this point the project already contains:

* Corollary 6.49 (Hasse derivatives of `w * f^t`, including the degree bound),
* Corollary 6.50 (substitution `y = x^(p^s)`),
* Lemma 6.51 (vanishing Hasse derivatives imply root multiplicity), and
* the recursive/block-elimination part of Lemma 6.46, conditional on
  `QuotientPowerIndependent`.

The purpose of this file is to package the auxiliary polynomial from (6.22)
and prove the exact bridge used near the end of the proof of Lemma 6.52:
if the coefficient family is nontrivial, Lemma 6.46 makes the auxiliary
polynomial nonzero; if its first `M` Hasse derivatives vanish at a point,
Lemma 6.51 then gives multiplicity at least `M` there.

`Lemma652.Complete` proves the full book statement using the completed
Lemma 6.46 directly, including translation when `f(0)=0`.  It also derives
the variable-degree coefficient count from the book's numerical hypotheses.
The quotient-independence wrappers here remain available as lower-level APIs.
-/

/-- The bracketed sum in LN97 (6.22):

`sum_i h_i(x) g(x)^i`, where each `h_i` is stored in base-`q` blocks and
`blockEval q` performs the substitution of the block variable by `X^q`.-/
noncomputable def stepanovBracket
    {m : ℕ} (q : ℕ) (g : Polynomial F)
    (E : Fin m → Polynomial (Polynomial F)) : Polynomial F :=
  ∑ i : Fin m, blockEval q (E i) * g ^ (i : ℕ)

/-- The auxiliary polynomial from LN97 (6.22):

`h(x) = f(x)^M * sum_i h_i(x) g(x)^i`.-/
noncomputable def stepanovAuxiliary
    {m : ℕ} (q M : ℕ) (f g : Polynomial F)
    (E : Fin m → Polynomial (Polynomial F)) : Polynomial F :=
  f ^ M * stepanovBracket q g E

omit [Fintype F] [DecidableEq F] in
/-- `BlockRelation` is exactly the assertion that the Stepanov bracket
vanishes.  This small bridge keeps the later Lemma 6.52 code readable.
@isnad1 id=iff.0h5v.s6.8813c6c8fb37 from=translated src=- shape=627794dc vocab=e9e15a61
-/
theorem blockRelation_iff_stepanovBracket_eq_zero
    {m q : ℕ} (g : Polynomial F)
    (E : Fin m → Polynomial (Polynomial F)) :
    BlockRelation q g E ↔ stepanovBracket q g E = 0 := by
  rfl

omit [Fintype F] [DecidableEq F] in
/-- Under the first-block independence hypothesis from Lemma 6.46, a
nontrivial coefficient family cannot have zero Stepanov bracket.

This is the formal version of the sentence on p. 308 that `h = 0` would,
by Lemma 6.46, force all the coefficients `e_{ij}` to vanish.
@isnad1 id=ne.3h6v.s7.5e9a4aa438f5 from=translated src=- shape=8d54374e vocab=6aa8dfe6
-/
theorem stepanovBracket_ne_zero_of_nontrivial_coefficients
    {m q D : ℕ} {g : Polynomial F}
    (hind : QuotientPowerIndependent (F := F) m q D g)
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, ((E i).coeff j).natDegree ≤ D)
    (hne : ∃ i, E i ≠ 0) :
    stepanovBracket q g E ≠ 0 := by
  intro hz
  have hrel : BlockRelation q g E := by
    exact (blockRelation_iff_stepanovBracket_eq_zero (F := F) g E).2 hz
  have hall :=
    ln97_6_46_of_quotientPowerIndependent (F := F) hind E hdeg hrel
  rcases hne with ⟨i, hi⟩
  exact hi (hall i)

omit [Fintype F] [DecidableEq F] in
/-- Consequently, if `f` is nonzero and the coefficient family is
nontrivial, then the whole auxiliary polynomial (6.22) is nonzero.
@isnad1 id=ne.4h8v.s8.cf0ee4bd2567 from=translated src=- shape=19b36395 vocab=3c038a0c
-/
theorem stepanovAuxiliary_ne_zero_of_nontrivial_coefficients
    {m q D M : ℕ} {f g : Polynomial F}
    (hf : f ≠ 0)
    (hind : QuotientPowerIndependent (F := F) m q D g)
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, ((E i).coeff j).natDegree ≤ D)
    (hne : ∃ i, E i ≠ 0) :
    stepanovAuxiliary q M f g E ≠ 0 := by
  unfold stepanovAuxiliary
  exact mul_ne_zero (pow_ne_zero _ hf)
    (stepanovBracket_ne_zero_of_nontrivial_coefficients
      (F := F) hind E hdeg hne)

omit [Fintype F] [DecidableEq F] in
/-- A direct Lemma 6.51 wrapper for the auxiliary polynomial: if the first
`M` Hasse derivatives vanish at `c`, then `(X-c)^M` divides `h`.
@isnad1 id=dvd.1h8v.s9.6aa786fbc79a from=translated src=- shape=ac09ccdb vocab=cbebddd9
-/
theorem stepanovAuxiliary_pow_dvd_of_hasse_vanish
    {m q M : ℕ}
    (f g : Polynomial F)
    (E : Fin m → Polynomial (Polynomial F))
    (c : F)
    (hvanish : ∀ n < M,
      eval c ((hasseDeriv n) (stepanovAuxiliary q M f g E)) = 0) :
    (X - C c) ^ M ∣ stepanovAuxiliary q M f g E := by
  exact ln97_6_51_pow_dvd
    (stepanovAuxiliary q M f g E) c M hvanish

omit [Fintype F] [DecidableEq F] in
/-- Combining the already-formalized parts of Lemmas 6.46 and 6.51:
under quotient-power independence, a nontrivial coefficient family plus
vanishing of the first `M` Hasse derivatives makes `c` a root of the
auxiliary polynomial with multiplicity at least `M`.

This is the exact endpoint needed after the linear system in the proof of
LN97 Lemma 6.52 has been solved.
@isnad1 id=le.5h9v.s9.e7e0d831b091 from=translated src=- shape=b2a8ae83 vocab=b79544a8
-/
theorem stepanovAuxiliary_rootMultiplicity_of_quotientPowerIndependent
    {m q D M : ℕ} {f g : Polynomial F}
    (hf : f ≠ 0)
    (hind : QuotientPowerIndependent (F := F) m q D g)
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, ((E i).coeff j).natDegree ≤ D)
    (hne : ∃ i, E i ≠ 0)
    (c : F)
    (hvanish : ∀ n < M,
      eval c ((hasseDeriv n) (stepanovAuxiliary q M f g E)) = 0) :
    M ≤ rootMultiplicity c (stepanovAuxiliary q M f g E) := by
  apply ln97_6_51_rootMultiplicity
  · exact stepanovAuxiliary_ne_zero_of_nontrivial_coefficients
      (F := F) hf hind E hdeg hne
  · exact hvanish

end LN97
end MagicSquares
