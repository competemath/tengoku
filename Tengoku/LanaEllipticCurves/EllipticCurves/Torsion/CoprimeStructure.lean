/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.Coprime
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.ThreeTorsionStructure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The structure theorem `E[n] ≅ (ℤ/nℤ)²` along coprime factorisations

`EllipticCurves.Torsion.Coprime` proves that torsion decomposes along coprime factorisations,
`E[mn] ≃+ E[m] × E[n]` for `Nat.Coprime m n`. This file turns that decomposition into a gluing
principle for the **structure theorem** `E[n] ≅ (ℤ/nℤ)²` (Silverman, *AEC*, III.6, Corollary 6.4):

```
E[m] ≃+ (ℤ/mℤ)²  →  E[n] ≃+ (ℤ/nℤ)²  →  Nat.Coprime m n  →  E[mn] ≃+ (ℤ/mnℤ)²,
```

the point being that `ZMod (m * n) ≃+ ZMod m × ZMod n` by the Chinese remainder theorem, so the
four cyclic factors regroup.

Feeding in the two sharp cases already available — `#E[2] = 4`, `E[2] ≃+ (ℤ/2ℤ)²`
(`EllipticCurves.Torsion.TwoTorsion`) and `#E[3] = 9`, `E[3] ≃+ (ℤ/3ℤ)²`
(`EllipticCurves.Torsion.ThreeTorsionStructure`) — gives the first **composite** instance of the
structure theorem: for an elliptic curve over an algebraically closed field in which `2 ≠ 0` and
`3 ≠ 0`,

```
Nat.card (W.torsion 6) = 36        and        W.torsion 6 ≃+ ZMod 6 × ZMod 6.
```

Like everything it builds on, this is **independent of the elliptic-net recurrence and of the
multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`**.

## What this reduces

Together with `EllipticCurves.Torsion.Coprime` (exact gluing at coprime factors) and
`EllipticCurves.Torsion.Multiplicative` (the bound `#E[mn] ≤ #E[m] · #E[n]` in general), the
structure theorem for a general `n` is now reduced to **prime powers**. Those genuinely need
surjectivity of `[p]` on `E(F̄)`. ⚠️ Two clauses this paragraph used to carry about that are false
and are replaced. The first, *"which is not available"*, is false at `p = 2`
(`nsmul_two_surjective`, `EllipticCurves.Torsion.DoublingSurjective`) and at `p = 3`
(`nsmul_three_surjective`, `EllipticCurves.Torsion.TriplingSurjective`).  ⚠️ **Its continuation —
*"it stands verbatim for every prime `p ≥ 5`, which still needs the general coordinate formula
`x(nP) = Φₙ/ΨSqₙ`"* — is false now too**: `nsmul_surjective_of_two_ne_zero`
(`EllipticCurves.Torsion.TwoTorsionOrder`) gives `[p]`-surjectivity at **every** nonzero index over
`F̄` with `(2 : F) ≠ 0`, and the coordinate formula it named is itself proved at every index with
`(2 : F) ≠ 0` (`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`).  ⚠️ **A
third clause is now false as well.** It read *"what still stops the prime-power reduction from
closing at `p ≥ 5` is the count `#E[p] = p²`, not surjectivity"*; that count is
`card_torsion_eq_sq_of_odd` (`EllipticCurves.Torsion.OmegaChordSum`) at every odd index, so the
prime-power reduction closes at every odd `p` — see `EllipticCurves.Torsion.PrimaryTowerOdd`, which
also settles `E[n] ≃+ (ℤ/nℤ)²` at every odd `n` directly, without going through a factorisation at
all.  What still holds is that the gate list is `EllipticCurves.Torsion.PrimaryTower`'s and that
this file does not re-measure it.  The second, *"only the exponent-one cases `p = 2` and `p = 3` are
known"*, is false at every exponent: `nonempty_torsionTwoPow_addEquiv`
(`EllipticCurves.Torsion.TwoPrimary`) and `nonempty_torsionThreePow_addEquiv`
(`EllipticCurves.Torsion.ThreePrimary`) give every `2 ^ k` and every `3 ^ k`, and gluing them gives
every `3`-smooth `n` (`nonempty_torsion_addEquiv_zmod_sq_of_smooth`). The concrete result at `n = 6`
below is one instance of that.

⚠️ **In particular this file does *not* give `#E[4] = 16` or `#E[9] = 81`.** That sentence is about
*this file's contents*, not about the development, and it is still true: those counts live in
`EllipticCurves.Torsion.TwoPrimary` and `EllipticCurves.Torsion.ThreePrimary`.

## Main statements

* `WeierstrassCurve.Affine.nonempty_torsion_addEquiv_zmod_sq_of_coprime`: the structure theorem
  glues along coprime factorisations.
* `WeierstrassCurve.Affine.card_torsion_six`: `#E[6] = 36`.
* `WeierstrassCurve.Affine.nonempty_torsionSix_addEquiv`: `E[6] ≃+ ℤ/6ℤ × ℤ/6ℤ`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-! ## Gluing the structure theorem along a coprime factorisation -/

/-- **The structure theorem glues along coprime factorisations.** If `E[m] ≅ (ℤ/mℤ)²` and
`E[n] ≅ (ℤ/nℤ)²` with `m` and `n` coprime, then `E[mn] ≅ (ℤ/mnℤ)²`.

The four cyclic factors regroup: `E[mn] ≃+ E[m] × E[n] ≃+ (ℤ/mℤ)² × (ℤ/nℤ)²`, then
`AddEquiv.prodProdProdComm` rearranges this to `(ℤ/mℤ × ℤ/nℤ)²`, and the Chinese remainder theorem
`ZMod.chineseRemainder` identifies each factor with `ℤ/mnℤ`.

This is the reusable form: it assembles `E[n] ≅ (ℤ/nℤ)²` for a general `n` out of its prime-power
factors. -/
theorem nonempty_torsion_addEquiv_zmod_sq_of_coprime {m n : ℕ} (h : Nat.Coprime m n)
    (hm : Nonempty (W.torsion m ≃+ ZMod m × ZMod m))
    (hn : Nonempty (W.torsion n ≃+ ZMod n × ZMod n)) :
    Nonempty (W.torsion (m * n) ≃+ ZMod (m * n) × ZMod (m * n)) := by
  obtain ⟨em⟩ := hm
  obtain ⟨en⟩ := hn
  have crt : ZMod (m * n) ≃+ ZMod m × ZMod n := (ZMod.chineseRemainder h).toAddEquiv
  exact ⟨((torsionMulAddEquiv h).trans (em.prodCongr en)).trans
    ((AddEquiv.prodProdProdComm (ZMod m) (ZMod m) (ZMod n) (ZMod n)).trans
      (crt.symm.prodCongr crt.symm))⟩

/-! ## The `6`-torsion subgroup -/

variable [IsAlgClosed F] [W.IsElliptic]

/-- **`#E[6] = 36`** for an elliptic curve over an algebraically closed field in which `2 ≠ 0` and
`3 ≠ 0`, from `#E[2] = 4` and `#E[3] = 9` by coprime multiplicativity.

This attains the bound `#E[n] ≤ n²` at `n = 6`. -/
theorem card_torsion_six (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (W.torsion 6) = 36 := by
  have h : Nat.Coprime 2 3 := by decide
  have hmul := card_torsion_mul (W := W) h
  rwa [show (2 * 3 : ℕ) = 6 from rfl, card_torsion_two h2, card_torsion_three h2 h3] at hmul

/-- **The structure theorem for `E[6]`**: over an algebraically closed field in which `2 ≠ 0` and
`3 ≠ 0`, the `6`-torsion subgroup of an elliptic curve is isomorphic to `ℤ/6ℤ × ℤ/6ℤ`.

This is the first *composite* instance of `E[n] ≅ (ℤ/nℤ)²`, glued from the `n = 2` and `n = 3`
cases. -/
theorem nonempty_torsionSix_addEquiv (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nonempty (W.torsion 6 ≃+ ZMod 6 × ZMod 6) := by
  have h : Nat.Coprime 2 3 := by decide
  have hsix := nonempty_torsion_addEquiv_zmod_sq_of_coprime (W := W) h
    (nonempty_torsionTwo_addEquiv h2) (nonempty_torsionThree_addEquiv h2 h3)
  rwa [show (2 * 3 : ℕ) = 6 from rfl] at hsix

end WeierstrassCurve.Affine
