/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.Multiplicative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sharp multiplicativity of torsion counts for divisible groups

`EllipticCurves.Torsion.Multiplicative` builds the homomorphism

```
AddSubgroup.torsionSmulHom A m n : A[m * n] →+ A[m],      P ↦ n • P
```

and derives the *inequality* `#A[m * n] ≤ #A[m] · #A[n]` from the first isomorphism theorem: its
kernel injects into `A[n]` and its range into `A[m]`. This file shows that **both injections are
equalities under a divisibility hypothesis**, so the inequality becomes an equality:

* the kernel is *exactly* `A[n]`, with no hypothesis at all — an element killed by `n` is
  automatically killed by `m * n`, so it already lies in `A[m * n]`;
* the range is *all* of `A[m]` as soon as `[n] : A → A` is surjective — lift `Q ∈ A[m]` to `a` with
  `n • a = Q`, and then `(m * n) • a = m • Q = 0`.

Hence

```
Nat.card A[m * n] = Nat.card A[m] * Nat.card A[n]        whenever `[n]` is surjective on `A`,
```

with **no finiteness hypothesis**: `AddSubgroup.card_mul_index` is unconditional, and the
`Nat.card = 0` convention makes both sides vanish together in the infinite case (`A[n]` embeds in
`A[m * n]`, and `A[m]` is a quotient of it, so either one being infinite forces `A[m * n]` to be
infinite).

## The three siblings

There are now three multiplicativity statements for torsion counts, and **none subsumes another**:

| file | hypothesis | conclusion |
|---|---|---|
| `Torsion.Multiplicative` | none (but `Finite`) | `#A[mn] ≤ #A[m]·#A[n]` |
| `Torsion.Coprime` | `IsCoprime m n` | `#A[mn] = #A[m]·#A[n]` |
| this file | `[n]` surjective on `A` | `#A[mn] = #A[m]·#A[n]` |

(the lemmas are `card_torsionBy_mul_le`, `card_torsionBy_mul_of_isCoprime` and
`card_torsionBy_mul_of_surjective` respectively).

The coprime statement says nothing at `m = n`, which is exactly the case the divisibility statement
is designed for: it is what turns `#E[2] = 4` into the whole `2`-primary tower `#E[2^k] = 4^k`.

## Main statements

* `AddSubgroup.kerTorsionSmulHom_bijective`: the kernel of `torsionSmulHom A m n` is exactly `A[n]`.
* `AddSubgroup.card_ker_torsionSmulHom`: the resulting cardinality identity.
* `AddSubgroup.torsionSmulHom_surjective`: surjectivity of `[n]` on `A` makes the homomorphism
  `torsionSmulHom A m n` surjective.
* `AddSubgroup.card_torsionBy_mul_of_surjective`: the sharp count.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

open scoped AddSubgroup

namespace AddSubgroup

variable (A : Type*) [AddCommGroup A] (m n : ℤ)

/-! ## The kernel is exactly `A[n]` -/

/-- **Every element of `A[n]` already lies in the kernel of `torsionSmulHom A m n`.** If `n • a = 0`
then `(m * n) • a = m • (n • a) = 0`, so `a` lies in `A[m * n]`, and by construction it is killed by
multiplication by `n`. Together with `kerTorsionSmulHom_injective` this identifies the kernel with
`A[n]` on the nose; no hypothesis on `m` or `n` is needed. -/
theorem kerTorsionSmulHom_surjective : Function.Surjective (kerTorsionSmulHom A m n) := by
  intro a
  have han : n • (a : A) = 0 := torsionBy.zsmul_iff.mp a.2
  have hmn : (a : A) ∈ A[m * n] := by
    rw [torsionBy.zsmul_iff, mul_smul, han, smul_zero]
  refine ⟨⟨⟨(a : A), hmn⟩, ?_⟩, rfl⟩
  exact AddMonoidHom.mem_ker.mpr (Subtype.ext (by simp))

/-- **The kernel of `torsionSmulHom A m n` is exactly `A[n]`.** -/
theorem kerTorsionSmulHom_bijective : Function.Bijective (kerTorsionSmulHom A m n) :=
  ⟨kerTorsionSmulHom_injective A m n, kerTorsionSmulHom_surjective A m n⟩

/-- The cardinality form of `kerTorsionSmulHom_bijective`, valid with no finiteness hypothesis. -/
theorem card_ker_torsionSmulHom :
    Nat.card (torsionSmulHom A m n).ker = Nat.card A[n] :=
  Nat.card_eq_of_bijective _ (kerTorsionSmulHom_bijective A m n)

/-! ## The range is all of `A[m]` for a divisible group -/

variable {A n}

/-- **If `[n]` is surjective on `A`, then `torsionSmulHom A m n` is surjective.** Given `Q ∈ A[m]`,
choose `a` with `n • a = Q`; then `(m * n) • a = m • Q = 0`, so `a` defines an element of `A[m * n]`
mapping to `Q`. -/
theorem torsionSmulHom_surjective (hn : Function.Surjective fun a : A => n • a) :
    Function.Surjective (torsionSmulHom A m n) := by
  intro Q
  obtain ⟨a, ha⟩ := hn (Q : A)
  have ha' : n • a = (Q : A) := ha
  have hmn : a ∈ A[m * n] := by
    rw [torsionBy.zsmul_iff, mul_smul, ha']
    exact torsionBy.zsmul_iff.mp Q.2
  exact ⟨⟨a, hmn⟩, Subtype.ext ha'⟩

/-- **The torsion count is sharply multiplicative for a divisible group.** If multiplication by `n`
is surjective on `A`, then

```
Nat.card A[m * n] = Nat.card A[m] * Nat.card A[n].
```

There is deliberately **no `Finite` hypothesis**: `AddSubgroup.card_mul_index` is unconditional, and
under the `Nat.card = 0` convention both sides vanish together in the infinite case, since `A[n]`
embeds into `A[m * n]` and `A[m]` is a quotient of it.

Compare `card_torsionBy_mul_le` (the inequality, always) and `card_torsionBy_mul_of_isCoprime` (the
equality for coprime `m`, `n`); this is the third, independent, sharpening. -/
theorem card_torsionBy_mul_of_surjective (hn : Function.Surjective fun a : A => n • a) :
    Nat.card A[m * n] = Nat.card A[m] * Nat.card A[n] := by
  have hcard := (torsionSmulHom A m n).ker.card_mul_index
  rw [AddSubgroup.index_ker, card_ker_torsionSmulHom,
    AddMonoidHom.range_eq_top.mpr (torsionSmulHom_surjective m hn),
    Nat.card_congr (AddSubgroup.topEquiv (G := A[m])).toEquiv] at hcard
  rw [← hcard, mul_comm]

end AddSubgroup
