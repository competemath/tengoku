/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Internal

/-!
# The finite retained-seed leftover-hash lemma

A universal hash family extracts from every finite flat source. For a support
of cardinality `N` and an output type of cardinality `M`, every joint test of
the seed and output has squared discrepancy at most `M / (4 * N)` from the
independent uniform distribution. The factor `1/4` is included in the checked
bound. Neither pairwise independence nor a uniform output for each fixed
input is assumed.

The standard collision-to-second-moment argument is credited to the
leftover-hash lemma, as presented in Guruswami, Umans, and Vadhan,
*Unbalanced Expanders and Randomness Extractors from Parvaresh--Vardy Codes*,
Section 5.1, Lemma 5.1, and Barak, Dodis, Krawczyk, Pereira, Pietrzak,
Standaert, and Yu, *Leftover Hash Lemma, Revisited*, Definition 2 and Lemma 1.
The proof here works directly with finite real sums and retained-seed tests.

* https://people.seas.harvard.edu/~salil/research/PVcondenser-jacm.pdf
* https://www.iacr.org/archive/crypto2011/68410001/68410001.pdf
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Restricting the input domain along an injection preserves universality.
@isnad1 id=universa.2h6v.s5.888278941118 from=translated src=- shape=ce26ee69 vocab=6e686e8b
-/
theorem UniversalHashFamily.comp_injective {α β Seed Ω : Type*} [Fintype Seed]
    [Fintype Ω] {E : α → Seed → Ω} (universal : UniversalHashFamily E)
    (f : β → α) (injective : Function.Injective f) :
    UniversalHashFamily (fun x y => E (f x) y) :=
  Internal.universalHashFamily_comp_injective universal f injective

/-- The sharp squared leftover-hash bound for a uniform finite input type,
against every joint test of the retained seed and output.
@isnad1 id=le.1h5v.s6.1d84573d4150 from=translated src=- shape=0603bf26 vocab=3b8dee38
-/
theorem UniversalHashFamily.seededTestProb_sub_uniform_sq_le {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty α] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} (universal : UniversalHashFamily E) (T : Finset (Seed × Ω)) :
    (seededTestProb E T - uniformSeededTestProb T) ^ 2 ≤
      (Fintype.card Ω : ℝ) / (4 * Fintype.card α) :=
  Internal.universalHashFamily_seededTestProb_sub_uniform_sq_le universal T

/-- The sharp squared leftover-hash bound for any nonempty finite flat support.
@isnad1 id=le.2h6v.s7.97aae96ab970 from=translated src=- shape=48a16f2c vocab=c18e57fd
-/
theorem UniversalHashFamily.flat_test_sq_le {α Seed Ω : Type*} [Fintype Seed]
    [Fintype Ω] [Nonempty Seed] [Nonempty Ω] {E : α → Seed → Ω}
    (universal : UniversalHashFamily E) (P : Finset α) (nonempty : P.Nonempty)
    (T : Finset (Seed × Ω)) :
    (seededTestProb (fun x : P => E x.val) T - uniformSeededTestProb T) ^ 2 ≤
      (Fintype.card Ω : ℝ) / (4 * P.card) :=
  Internal.universalHashFamily_flat_test_sq_le universal P nonempty T

/-- A universal family is a strong extractor whenever the output size fits
the sharp leftover-hash error budget.
@isnad1 id=flatstro.4h6v.s6.bf3526983609 from=translated src=- shape=c05faab1 vocab=cad14050
-/
theorem UniversalHashFamily.flatStrongSeededExtractor {α Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω] {E : α → Seed → Ω}
    (universal : UniversalHashFamily E) {K : Nat} {ε : ℝ} (positive : 0 < K)
    (error : 0 ≤ ε) (budget : (Fintype.card Ω : ℝ) ≤ 4 * ε ^ 2 * K) :
    FlatStrongSeededExtractor E K ε :=
  Internal.universalHashFamily_flatStrongSeededExtractor universal positive error budget

end Algebraic.Cutwidth.Extractor
