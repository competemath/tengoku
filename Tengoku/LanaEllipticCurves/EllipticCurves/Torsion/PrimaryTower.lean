/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.AbelianStructure
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.Divisible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `p`-primary tower of the torsion structure theorem, at a general index

`EllipticCurves.Torsion.TwoPrimary` and `EllipticCurves.Torsion.ThreePrimary` climb from `E[2]` to
`E[2 ^ k]` and from `E[3]` to `E[3 ^ k]`.  Read side by side, **the two ascents are the same
argument**, and only two of their inputs mention the index at all:

1. surjectivity of `[p]` on `E(F̄)`, and
2. the count `#E[p] = p²`.

Everything else — the multiplicativity step `#E[np] = #E[p] · #E[n]`, the induction that turns it
into `#E[pᵏ] = (p²)ᵏ`, the finiteness read off that count, its restatement as `pᵏ · pᵏ`, and the
prime-by-prime rank check feeding `AddCommGroup.equiv_zmod_sq_of_card_sq` — is uniform in `p`.  This
file writes that uniform half **once**, taking (1) and (2) as hypotheses;
`EllipticCurves.Torsion.TwoPrimary` and `EllipticCurves.Torsion.ThreePrimary`, which **import this
file**, supply them at `p = 2` and `p = 3` and obtain their towers as one-line instances.

## What this does and does not settle

⚠️ **Nothing is proved here at any `p`.**  This file contains no instance of either hypothesis;
taken alone its statements are conditional, with no witness.  **Both are now witnessed downstream at
every `p` this file's consumers need**, and neither in this file: (1) at every nonzero index with
`(2 : F) ≠ 0` by `nsmul_surjective_of_two_ne_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`), and
(2) at every odd `p` with `(2 : F) ≠ 0` and `(p : F) ≠ 0` by `card_torsion_eq_sq_of_odd`
(`EllipticCurves.Torsion.OmegaChordSum`), which ⚠️ used to be witnessed at `p = 2` and `p = 3`
only.  ⚠️ **Both value hypotheses, and this clause used to name only the index one** (`#1137`):
witness (2) does not reach characteristic `2` at any `p`, which is invisible if only `(p : F) ≠ 0`
is written down.  ⚠️ **Witness (1)'s clause took the same insertion one repair later** (`#1679`),
and the census that found witness (2) could not see it: PR #605 wrote the pair into (2) and left
(1) naming the index alone, so from that commit on a sentence-keyed test reads this whole sentence
as clear on (2)'s strength.  See the gate list below.

What the file *does* settle is **how much is needed, and that it is exactly two things**.  Composed
with `nsmul_surjective_of_hasXCoordFormula` (`EllipticCurves.Torsion.NsmulSurjective`), which
supplies (1) from the coordinate formula `HasXCoordFormula W p` and the pointwise statement that
`Φₚ` and `ΨSqₚ` have no common root, the full list of what is owed at a prime `p ≥ 5` is:

* `HasXCoordFormula W p` — ✅ **closed**: `hasXCoordFormula_of_two_ne_zero`
  (`EllipticCurves.Torsion.NsmulOrder`), at every index over any field with `(2 : F) ≠ 0`.
  ⚠️ This bullet used to read *"issue `#251`, through `#404`"*, and `#404` was neither a route to it
  nor a gate on it: `#404`'s on-curve identity is closed (`EllipticCurves.Torsion.OmegaCrux`,
  PR #557) and says nothing about `p • P`, which is the whole content of `HasXCoordFormula`;
* `∀ x, (W.ΨSq p).eval x = 0 → (W.Φ p).eval x ≠ 0` — ✅ **closed** on an elliptic curve over an
  algebraically closed field with `(2 : F) ≠ 0`: `eval_Φ_ne_zero_of_eval_ΨSq_eq_zero`
  (`EllipticCurves.Torsion.TwoTorsionOrder`).  ⚠️ It is **not** `#1184`, of which this bullet used
  to be called a weakening: `#1184` is an `IsCoprime` statement over an arbitrary base, and what is
  proved is its pointwise shadow, obtained from the order dictionary rather than from a Bézout
  certificate.  ⚠️ This clause used to end *"which does not descend"*, and that was wrong: over a
  **field** the shadow does descend, and `EllipticCurves.Torsion.CoprimeAdjacent` descends it.
  What stays out of reach is the arbitrary-**ring** statement, which is what `#1184` asks for;
* `#E[p] = p²` — ✅ **closed at every odd `p`** with `(p : F) ≠ 0`, on an elliptic curve over an
  algebraically closed field with `(2 : F) ≠ 0`: `card_torsion_eq_sq_of_odd`
  (`EllipticCurves.Torsion.OmegaChordSum`).  Every prime `p ≥ 5` is odd, so **the gate list is
  empty** at exactly the primes it was written for, and
  `EllipticCurves.Torsion.PrimaryTowerOdd` supplies every statement below with `hcard` discharged.
  ⚠️ This bullet used to read *"❌ **the one gate left** … the `≥` half is in this tree at no
  `p ∉ {2, 3}`"*, and both clauses are now false.  ⚠️ What is **still** true, and is why this
  remains a *third and separate* item rather than a consequence of the two above, is that
  `#E[p] = p²` does *not* follow from surjectivity of `[p]`: that is why it is a hypothesis below
  and not a conclusion, and it is why the discharge lives in a separate file.  ⚠️ Nothing here is
  claimed at **even** `p`: `card_torsion_eq_sq_of_odd` is odd-index only, and at `p = 2` the
  witness is still `card_torsion_two` (`EllipticCurves.Torsion.TwoTorsion`).

⚠️ The two closed bullets are exactly the two inputs of `nsmul_surjective_of_hasXCoordFormula`, so
their composite **is** hypothesis (1), packaged as `nsmul_surjective_of_two_ne_zero`
(`EllipticCurves.Torsion.TwoTorsionOrder`) — whose conclusion is verbatim the `hsurj` of every
statement below.  `EllipticCurves.Torsion.PrimaryTowerAlgClosed` substitutes it, leaving `hcard`
as the only hypothesis that is not about the field or the index, and
`EllipticCurves.Torsion.PrimaryTowerOdd` substitutes that in turn at every odd `p`.

Every statement below therefore holds at every odd `p` with `(p : F) ≠ 0` with no hypothesis left,
and with it the `p`-primary half of `E[n] ≅ (ℤ/nℤ)²`.  ⚠️ The statements in *this* file stay
conditional on purpose: they are the uniform half, and their hypotheses are what makes it visible
that the tower needs exactly two things.

## Two economies of the `p = 2` and `p = 3` arguments are preserved deliberately

* **No hypothesis on the field.**  `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0` and
  `(3 : F) ≠ 0` all appear in the two merged files and **none of them appears here**: they are
  consumed entirely by the two inputs, `IsAlgClosed` and `IsElliptic` by the surjectivity, the
  characteristic hypotheses by `card_torsion_two` and `card_torsion_three`.  What is left is a
  statement about an abelian group on which `[p]` is surjective.
* **No primality, except where it is genuinely used.**  `card_torsion_mul_of_surjective`,
  `card_torsion_pow_of_surjective`, `card_torsion_pow`, `finite_torsion_pow` and
  `card_torsion_pow_mul_self` hold for an **arbitrary** `p : ℕ`.  ⚠️ Only
  `nonempty_torsionPow_addEquiv` needs `p.Prime`, and the reason is sharp: its rank check runs over
  all primes `q`, and the branch `q ≠ p` needs `Nat.Coprime q (p ^ k)`, which fails at a composite
  `p` (take `p = 4`, `q = 2`).  The counting tower is not a prime-power phenomenon; the structure
  theorem is.

## Main statements

* `WeierstrassCurve.Affine.card_torsion_mul_of_surjective`: `#E[np] = #E[p] · #E[n]`.
* `WeierstrassCurve.Affine.card_torsion_pow_of_surjective`: `#E[pᵏ] = #E[p]ᵏ`, and
  `WeierstrassCurve.Affine.card_torsion_pow`, the same count once `#E[p] = p²` is supplied.
* `WeierstrassCurve.Affine.finite_torsion_pow`: `E[pᵏ]` is finite, read off that count.
* `WeierstrassCurve.Affine.card_torsion_pow_mul_self`: `#E[pᵏ] = pᵏ · pᵏ`, the shape the
  `PrimaryBasis` consumers take their cardinality hypothesis in.
* **`WeierstrassCurve.Affine.nonempty_torsionPow_addEquiv`**: the headline,
  `E[pᵏ] ≃+ (ℤ/pᵏℤ)²` at a prime `p`.

Every public declaration of this file is listed above.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-! ## The counting tower -/

/-- Multiplication by `p` on `W.Point`, with the integer scalar `(p : ℤ)` that
`AddSubgroup.torsionBy` uses, transported from the `ℕ`-scalar form along `natCast_zsmul`.  This is
the only bridge needed between a surjectivity statement and the divisibility engine of
`EllipticCurves.Torsion.Divisible`. -/
private lemma zsmul_surjective_of_nsmul {p : ℕ}
    (hsurj : Function.Surjective fun P : W.Point => p • P) :
    Function.Surjective fun P : W.Point => (p : ℤ) • P := by
  intro Q
  obtain ⟨P, hP⟩ := hsurj Q
  exact ⟨P, by change ((p : ℕ) : ℤ) • P = Q; rw [natCast_zsmul]; exact hP⟩

/-- **`#E[np] = #E[p] · #E[n]`.**  Multiplication by `p` is a surjection `E[np] → E[n]` with kernel
`E[p]`.

Note that **no coprimality is assumed**, and that is the point: the tower's own step has `n = pᵏ`,
which is never coprime to `p`, so the coprime multiplicativity of `EllipticCurves.Torsion.Coprime`
cannot be used for it.  **No hypothesis on `p` either** — not primality, not `p ≠ 0`. -/
theorem card_torsion_mul_of_surjective {p : ℕ}
    (hsurj : Function.Surjective fun P : W.Point => p • P) (n : ℕ) :
    Nat.card (W.torsion (n * p)) = Nat.card (W.torsion p) * Nat.card (W.torsion n) := by
  have hcast : W.torsion (n * p) = W.Point[(n : ℤ) * (p : ℤ)] :=
    congrArg (fun k : ℤ => W.Point[k]) (by push_cast; ring)
  rw [hcast,
    AddSubgroup.card_torsionBy_mul_of_surjective (n : ℤ) (zsmul_surjective_of_nsmul hsurj),
    show W.Point[(p : ℤ)] = W.torsion p from rfl, mul_comm]

/-- **The `p`-primary tower: `#E[pᵏ] = #E[p]ᵏ`.**  By induction from `#E[1] = 1`, each step
multiplying by `#E[p]`.  Still no hypothesis on `p`. -/
theorem card_torsion_pow_of_surjective {p : ℕ}
    (hsurj : Function.Surjective fun P : W.Point => p • P) (k : ℕ) :
    Nat.card (W.torsion (p ^ k)) = Nat.card (W.torsion p) ^ k := by
  induction k with
  | zero => simp [torsion_one]
  | succ k ih => rw [pow_succ, card_torsion_mul_of_surjective hsurj, ih, pow_succ, mul_comm]

/-- **`#E[pᵏ] = (pᵏ)²`**, the previous count with `#E[p] = p²` supplied.  This says `E[pᵏ]` attains
the bound `#E[n] ≤ n²`. -/
theorem card_torsion_pow {p : ℕ}
    (hsurj : Function.Surjective fun P : W.Point => p • P)
    (hcard : Nat.card (W.torsion p) = p ^ 2) (k : ℕ) :
    Nat.card (W.torsion (p ^ k)) = (p ^ k) ^ 2 := by
  rw [card_torsion_pow_of_surjective hsurj, hcard, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- `E[pᵏ]` is finite, read off the count `#E[pᵏ] = (pᵏ)² ≠ 0` rather than from any smoothness
hypothesis, which would drag in constraints the count already carries. -/
theorem finite_torsion_pow {p : ℕ} (hp : p ≠ 0)
    (hsurj : Function.Surjective fun P : W.Point => p • P)
    (hcard : Nat.card (W.torsion p) = p ^ 2) (k : ℕ) : Finite (W.torsion (p ^ k)) := by
  have h : Nat.card (W.torsion (p ^ k)) ≠ 0 := by
    rw [card_torsion_pow hsurj hcard]
    exact pow_ne_zero 2 (pow_ne_zero k hp)
  exact (Nat.card_ne_zero.mp h).2

/-- **`#E[pᵏ] = pᵏ · pᵏ`**, the same count as `card_torsion_pow` in the shape every consumer that
compares `E[pᵏ]` with `(ZMod (pᵏ))²` needs it: as a product of two copies of the modulus rather than
as a square.

⚠️ The conversion is a real rewrite and not a `rfl`.  It is stated once here rather than repeated at
each call site; `EllipticCurves.Torsion.PrimaryBasis.torsionPairHom_bijective_of_card`,
`EllipticCurves.TateModule.LevelStructure.infinite_tateModule_of_card` and
`EllipticCurves.TateModule.PrimaryFree.padicPairHom_injective` all take their cardinality hypothesis
in exactly this form. -/
theorem card_torsion_pow_mul_self {p : ℕ}
    (hsurj : Function.Surjective fun P : W.Point => p • P)
    (hcard : Nat.card (W.torsion p) = p ^ 2) (k : ℕ) :
    Nat.card (W.torsion (p ^ k)) = p ^ k * p ^ k := by
  rw [card_torsion_pow hsurj hcard, sq]

/-! ## The structure of `E[pᵏ]` -/

/-- **The structure theorem for `E[pᵏ]` at a prime `p`**: given surjectivity of `[p]` and the count
`#E[p] = p²`, the `pᵏ`-torsion subgroup is isomorphic to `ℤ/pᵏℤ × ℤ/pᵏℤ`.

The count `#E[pᵏ] = (pᵏ)²` goes into the classification core
`AddCommGroup.equiv_zmod_sq_of_card_sq`, whose rank hypothesis is checked prime by prime: at `q = p`
by injecting the `p`-torsion of `E[pᵏ]` into `E[p]` and quoting `hcard`, and at every `q ≠ p` by
coprimality, an element killed by both `q` and `pᵏ` being killed by `1`.

⚠️ **This is the only statement in the file that needs `p.Prime`**, and it needs it precisely for
the second branch: `Nat.Coprime q (p ^ k)` for every prime `q ≠ p` is false at a composite `p`. -/
theorem nonempty_torsionPow_addEquiv {p : ℕ} (hp : p.Prime)
    (hsurj : Function.Surjective fun P : W.Point => p • P)
    (hcard : Nat.card (W.torsion p) = p ^ 2) (k : ℕ) :
    Nonempty (W.torsion (p ^ k) ≃+ ZMod (p ^ k) × ZMod (p ^ k)) := by
  haveI := finite_torsion_pow hp.pos.ne' hsurj hcard k
  haveI : Finite (W.torsion p) := by
    have h : Nat.card (W.torsion p) ≠ 0 := by rw [hcard]; exact pow_ne_zero 2 hp.pos.ne'
    exact (Nat.card_ne_zero.mp h).2
  refine AddCommGroup.equiv_zmod_sq_of_card_sq (pow_pos hp.pos k)
    (fun a => nsmul_mem_torsion a) (card_torsion_pow hsurj hcard k) ?_
  intro q hq
  rcases eq_or_ne q p with rfl | hqp
  · -- an element of `E[qᵏ]` killed by `q` is a point of `E[q]`, and `#E[q] = q²`
    have hinj : Function.Injective
        fun a : {a : W.torsion (q ^ k) // (q : ℕ) • a = 0} => (⟨(a.1 : W.Point), by
          rw [mem_torsion_iff]
          exact congrArg Subtype.val a.2⟩ : W.torsion q) := by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext hab)
    calc Nat.card {a : W.torsion (q ^ k) // (q : ℕ) • a = 0}
        ≤ Nat.card (W.torsion q) := Nat.card_le_card_of_injective _ hinj
      _ = q ^ 2 := hcard
  · -- for a prime `q ≠ p`, an element of `E[pᵏ]` killed by `q` is killed by `1`
    have hcop : IsCoprime (q : ℤ) ((p : ℤ) ^ k) := by
      have hnat : Nat.Coprime q (p ^ k) :=
        Nat.Coprime.pow_right k ((Nat.coprime_primes hq hp).mpr hqp)
      simpa using Nat.isCoprime_iff_coprime.mpr hnat
    obtain ⟨u, v, huv⟩ := hcop
    have hzero : ∀ a : W.torsion (p ^ k), (q : ℕ) • a = 0 → a = 0 := by
      intro a ha
      have hqa : (q : ℤ) • a = 0 := by
        rw [show (q : ℤ) = ((q : ℕ) : ℤ) from rfl, natCast_zsmul, ha]
      have hka : ((p : ℤ) ^ k) • a = 0 := by
        rw [show ((p : ℤ) ^ k) = (((p ^ k : ℕ)) : ℤ) by push_cast; ring, natCast_zsmul]
        exact nsmul_mem_torsion a
      have h1 : ((1 : ℤ)) • a = 0 := by
        rw [← huv, add_smul, mul_smul, mul_smul, hqa, hka, smul_zero, smul_zero, add_zero]
      simpa using h1
    have hcard1 : Nat.card {a : W.torsion (p ^ k) // (q : ℕ) • a = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hzero a.1 a.2).trans (hzero b.1 b.2).symm)⟩, ⟨⟨0, by simp⟩⟩⟩
    rw [hcard1]
    exact Nat.one_le_pow 2 q hq.pos

end WeierstrassCurve.Affine
