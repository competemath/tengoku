import Tengoku.Seed.Data.Nat.ChineseRemainder
import Tengoku.Seed.Data.Int.ModEq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite CRT certificates

This module isolates the exact algebraic content of the CRT certificates used
in Section 7 of Paper C.  A finite list of pairwise coprime congruences defines
one residue class modulo the product of the moduli.  Counting representatives
of that class in an interval is handled separately by
`PaperC.Arithmetic.IntervalCongruence`.
-/

namespace PaperC

open scoped Function

namespace CRT

variable {ι : Type*}

/--
Any two natural numbers satisfying the same pairwise-coprime CRT certificate
are congruent modulo the product of its moduli.
@isnad1 id=modeq.3h6v.s6.a7ced832ce90 from=translated src=- shape=c26086d6 vocab=274640eb
-/
theorem solutions_modEq
    (residue modulus : ι → ℕ) (indices : List ι)
    (hcoprime : indices.Pairwise (Nat.Coprime on modulus))
    {x y : ℕ}
    (hx : ∀ i ∈ indices, x ≡ residue i [MOD modulus i])
    (hy : ∀ i ∈ indices, y ≡ residue i [MOD modulus i]) :
    x ≡ y [MOD (indices.map modulus).prod] := by
  have hxrep :=
    Nat.chineseRemainderOfList_modEq_unique
      residue modulus indices hcoprime hx
  have hyrep :=
    Nat.chineseRemainderOfList_modEq_unique
      residue modulus indices hcoprime hy
  exact hxrep.trans hyrep.symm

/--
Membership in a CRT certificate is equivalent to membership in the single
residue class represented by `Nat.chineseRemainderOfList`.
@isnad1 id=iff.1h5v.s6.f26eb2f2e035 from=translated src=- shape=d2aaf8a1 vocab=9330240b
-/
theorem satisfies_iff_modEq_representative
    (residue modulus : ι → ℕ) (indices : List ι)
    (hcoprime : indices.Pairwise (Nat.Coprime on modulus))
    (x : ℕ) :
    (∀ i ∈ indices, x ≡ residue i [MOD modulus i]) ↔
      x ≡
        Nat.chineseRemainderOfList residue modulus indices hcoprime
          [MOD (indices.map modulus).prod] := by
  constructor
  · exact Nat.chineseRemainderOfList_modEq_unique
      residue modulus indices hcoprime
  · intro hx i hi
    have hall :
        ∀ j ∈ indices,
          x ≡
            (Nat.chineseRemainderOfList
              residue modulus indices hcoprime : ℕ)
              [MOD modulus j] :=
      (Nat.modEq_list_map_prod_iff hcoprime).mp hx
    exact (hall i hi).trans
      ((Nat.chineseRemainderOfList
        residue modulus indices hcoprime).property i hi)

/--
Integer-congruence interface for the same certificate.  This is the bridge
between the natural-number CRT API and the interval counts, which use
`Int.ModEq`.  The variable itself and all residues/moduli are natural, while
the displayed congruences are their casts to `ℤ`.
@isnad1 id=iff.1h5v.s6.6efbe2ac8f27 from=translated src=- shape=ab4ca863 vocab=24aa7c06
-/
theorem satisfies_iff_intModEq_representative
    (residue modulus : ι → ℕ) (indices : List ι)
    (hcoprime : indices.Pairwise (Nat.Coprime on modulus))
    (x : ℕ) :
    (∀ i ∈ indices,
        (x : ℤ) ≡ (residue i : ℤ) [ZMOD (modulus i : ℤ)]) ↔
      (x : ℤ) ≡
        (Nat.chineseRemainderOfList
          residue modulus indices hcoprime : ℕ)
        [ZMOD ((indices.map modulus).prod : ℤ)] := by
  simpa only [Int.natCast_modEq_iff] using
    satisfies_iff_modEq_representative
      residue modulus indices hcoprime x

/--
The canonical CRT representative lies strictly below the product modulus when
all selected moduli are nonzero.
@isnad1 id=lt.2h4v.s6.235724687244 from=translated src=- shape=b0a329a9 vocab=38868745
-/
theorem representative_lt_product
    (residue modulus : ι → ℕ) (indices : List ι)
    (hcoprime : indices.Pairwise (Nat.Coprime on modulus))
    (hnonzero : ∀ i ∈ indices, modulus i ≠ 0) :
    (Nat.chineseRemainderOfList
        residue modulus indices hcoprime : ℕ) <
      (indices.map modulus).prod :=
  Nat.chineseRemainderOfList_lt_prod
    residue modulus indices hcoprime hnonzero

end CRT

end PaperC
