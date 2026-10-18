/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.ThreeTorsion
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.TwoTorsion
import Tengoku.Seed.GroupTheory.Index

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Multiplicativity of the torsion bound

The bound `#E[n] ≤ n²` (Silverman, *AEC*, III.6, Corollary 6.4) is *multiplicative*: it suffices to
know it one prime at a time. This file proves the underlying group-theoretic statement, for an
arbitrary abelian group `A` and its `n`-torsion subgroups `A[n]`,

```
Nat.card A[m * n] ≤ Nat.card A[m] * Nat.card A[n],
```

together with the companion `Finite A[m] → Finite A[n] → Finite A[m * n]`, and specialises both to
the torsion subgroups `E[n]` of a Weierstrass curve.

Combining this with the two unconditional computations already available — `#E[2] ≤ 4` away from
characteristic `2` (`EllipticCurves.Torsion.TwoTorsion`) and `#E[3] ≤ 9` away from characteristic
`3` (`EllipticCurves.Torsion.ThreeTorsion`) — yields

```
Finite (W.torsion n)   and   Nat.card (W.torsion n) ≤ n ^ 2
```

for **every** nonzero `n` whose prime factors are all `2` or `3`, in particular for
`n = 4, 6, 8, 9, 12, …`. Like its two inputs this is entirely **independent of Ward's theorem, of
the elliptic-net recurrence and of the multiplication-by-`n` coordinate formula
`x(nP) = Φₙ(x)/ΨSqₙ(x)`**.  ⚠️ The independence claim is unchanged and is the point of this
sentence; its trailing *"which gate the general case"* was dropped, because the coordinate formula
is now proved at every index with `(2 : F) ≠ 0` (`hasXCoordFormula_of_two_ne_zero`,
`EllipticCurves.Torsion.NsmulOrder`) and gates nothing.

## The mechanism

If `m • (n • P) = (mn) • P = 0` for `P ∈ A[mn]`, then `n • P ∈ A[m]`, so multiplication by `n` is a
homomorphism

```
f : A[m * n] →+ A[m],      f P = n • P      (`AddSubgroup.torsionSmulHom`).
```

Its kernel consists of the points of `A[mn]` killed by `n`, hence injects into `A[n]`, and its range
sits inside `A[m]`. Mathlib's `AddSubgroup.card_mul_index` and `AddSubgroup.index_ker` give the
first-isomorphism-theorem count

```
Nat.card (ker f) * Nat.card (range f) = Nat.card A[m * n]
```

*unconditionally* (with the convention `Nat.card = 0` for infinite types), and
`AddMonoidHom.finite_iff_finite_ker_range` transfers finiteness. Both conclusions follow at once.

## What this does not do

It reduces `#E[n] ≤ n²` to the case of a prime `n`; for a prime `p ≥ 5` that case needs the
multiplication-by-`n` characterisation of torsion by division polynomials.  ⚠️ That clause used to
end *"which is not available"*, and it is: `card_torsion_le_sq`
(`EllipticCurves.Torsion.XSupport`) proves `#E[n] ≤ n²` at every index over a field with
`(2 : F) ≠ 0` and `(n : F) ≠ 0`, and the sharp equality at odd `n` is `card_torsion_eq_sq_of_odd`
(`EllipticCurves.Torsion.OmegaChordSum`).  Neither is proved here, which is what this section is
about.
Nor does it give *sharp* counts: `#E[4] = 16` would need surjectivity of `[2]` on `E(F̄)`.

## Main definitions

* `AddSubgroup.torsionSmulHom`: the homomorphism `A[m * n] →+ A[m]`, `P ↦ n • P`.

## Main statements

* `AddSubgroup.finite_torsionBy_mul`, `AddSubgroup.card_torsionBy_mul_le`: the two group-theoretic
  statements above, for an arbitrary abelian group.
* `WeierstrassCurve.Affine.finite_torsion_mul`, `WeierstrassCurve.Affine.card_torsion_mul_le`: their
  specialisations to `E[n]`.
* `WeierstrassCurve.Affine.finite_torsion_of_smooth`,
  `WeierstrassCurve.Affine.card_torsion_le_sq_of_smooth`: `E[n]` is finite of order at most `n²`
  whenever `n ≠ 0` has no prime factor other than `2` and `3` (and `(2 : F) ≠ 0`, `(3 : F) ≠ 0`).
* `WeierstrassCurve.Affine.finite_torsion_two_pow_mul_three_pow`,
  `WeierstrassCurve.Affine.card_torsion_two_pow_mul_three_pow_le`: the directly applicable explicit
  forms, `E[2^a · 3^b]` is finite of order at most `(2^a · 3^b)²`.
* `WeierstrassCurve.Affine.card_torsion_four_le`, `…_six_le`, `…_eight_le`, `…_nine_le`: the first
  named instances, `#E[4] ≤ 16`, `#E[6] ≤ 36`, `#E[8] ≤ 64`, `#E[9] ≤ 81`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

open scoped AddSubgroup

namespace AddSubgroup

variable (A : Type*) [AddCommGroup A] (m n : ℤ)

/-- **Multiplication by `n` maps `A[m * n]` into `A[m]`.** Indeed `m • (n • P) = (mn) • P = 0` for
`P ∈ A[m * n]`. This is the homomorphism whose kernel is `A[n]` and whose range measures the index,
and which therefore makes the torsion bound multiplicative. -/
def torsionSmulHom : A[m * n] →+ A[m] where
  toFun P := ⟨n • (P : A), by
    rw [torsionBy.zsmul_iff, smul_smul]
    exact torsionBy.zsmul_iff.mp P.2⟩
  map_zero' := by ext; simp
  map_add' P Q := by ext; simp [smul_add]

@[simp]
lemma torsionSmulHom_apply_coe (P : A[m * n]) :
    ((torsionSmulHom A m n P : A[m]) : A) = n • (P : A) :=
  rfl

/-- The kernel of `torsionSmulHom A m n` consists of elements of `A[m * n]` killed by `n`, so it
maps into `A[n]`. -/
def kerTorsionSmulHom : (torsionSmulHom A m n).ker → A[n] :=
  fun P => ⟨((P : A[m * n]) : A), by
    rw [torsionBy.zsmul_iff, ← torsionSmulHom_apply_coe A m n]
    exact congrArg Subtype.val (AddMonoidHom.mem_ker.mp P.2)⟩

lemma kerTorsionSmulHom_injective : Function.Injective (kerTorsionSmulHom A m n) := by
  intro P Q h
  have h' := Subtype.ext_iff.mp h
  exact Subtype.ext (Subtype.ext h')

lemma rangeTorsionSmulHom_injective :
    Function.Injective fun P : (torsionSmulHom A m n).range => (P : A[m]) :=
  fun _ _ h => Subtype.ext h

/-- **Finiteness of torsion is multiplicative.** -/
theorem finite_torsionBy_mul [Finite A[m]] [Finite A[n]] : Finite A[m * n] := by
  rw [(torsionSmulHom A m n).finite_iff_finite_ker_range]
  exact ⟨Finite.of_injective _ (kerTorsionSmulHom_injective A m n),
    Finite.of_injective _ (rangeTorsionSmulHom_injective A m n)⟩

/-- **The torsion bound is multiplicative**: `#A[m * n] ≤ #A[m] * #A[n]`, since `A[m * n]` is an
extension of a subgroup of `A[m]` by a subgroup of `A[n]`. -/
theorem card_torsionBy_mul_le [Finite A[m]] [Finite A[n]] :
    Nat.card A[m * n] ≤ Nat.card A[m] * Nat.card A[n] := by
  have h := (torsionSmulHom A m n).ker.card_mul_index
  rw [AddSubgroup.index_ker] at h
  calc Nat.card A[m * n]
      = Nat.card (torsionSmulHom A m n).ker * Nat.card (torsionSmulHom A m n).range := h.symm
    _ ≤ Nat.card A[n] * Nat.card A[m] :=
        Nat.mul_le_mul (Nat.card_le_card_of_injective _ (kerTorsionSmulHom_injective A m n))
          (Nat.card_le_card_of_injective _ (rangeTorsionSmulHom_injective A m n))
    _ = Nat.card A[m] * Nat.card A[n] := mul_comm _ _

end AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-! ## The specialisation to `E[n]` -/

private lemma torsion_mul_eq (m n : ℕ) : W.torsion (m * n) = W.Point[(m : ℤ) * (n : ℤ)] :=
  congrArg (fun k : ℤ => W.Point[k]) (Nat.cast_mul m n)

/-- **Finiteness of `E[n]` is multiplicative**: if `E[m]` and `E[n]` are finite, so is `E[mn]`. -/
theorem finite_torsion_mul {m n : ℕ} (hm : Finite (W.torsion m)) (hn : Finite (W.torsion n)) :
    Finite (W.torsion (m * n)) := by
  haveI := hm
  haveI := hn
  rw [torsion_mul_eq]
  exact AddSubgroup.finite_torsionBy_mul W.Point _ _

/-- **The torsion bound is multiplicative**: `#E[mn] ≤ #E[m] * #E[n]`.

This reduces the bound `#E[n] ≤ n²` to the case of a prime `n`, since `#E[m] ≤ m²` and
`#E[n] ≤ n²` then give `#E[mn] ≤ (mn)²`. -/
theorem card_torsion_mul_le {m n : ℕ} (hm : Finite (W.torsion m)) (hn : Finite (W.torsion n)) :
    Nat.card (W.torsion (m * n)) ≤ Nat.card (W.torsion m) * Nat.card (W.torsion n) := by
  haveI := hm
  haveI := hn
  rw [torsion_mul_eq]
  exact AddSubgroup.card_torsionBy_mul_le W.Point _ _

/-! ## The bound `#E[n] ≤ n²` for `3`-smooth `n` -/

/-- Every prime factor of `2^a * 3^b` is `2` or `3`. -/
private lemma primeFactors_two_pow_mul_three_pow (a b : ℕ) :
    ∀ p ∈ (2 ^ a * 3 ^ b).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp (hpp.dvd_of_dvd_pow h))

section Smooth

variable [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)

include h2 h3 in
/-- The two available base cases, `p = 2` and `p = 3`, in the shape consumed by the induction. -/
private lemma finite_and_card_torsion_le_sq_of_eq_two_or_three {p : ℕ} (hp : p = 2 ∨ p = 3) :
    Finite (W.torsion p) ∧ Nat.card (W.torsion p) ≤ p ^ 2 := by
  rcases hp with rfl | rfl
  · exact ⟨W.finite_torsion_two h2, by simpa using W.card_torsion_two_le h2⟩
  · exact ⟨W.finite_torsion_three h3, by simpa using W.card_torsion_three_le h3⟩

include h2 h3 in
/-- The induction behind `finite_torsion_of_smooth` and `card_torsion_le_sq_of_smooth`: strong
induction on `n`, splitting off the smallest prime factor and applying multiplicativity. The two
conclusions are carried together because the cardinality bound needs the finiteness of both
factors. -/
private lemma finite_and_card_torsion_le_sq_of_smooth :
    ∀ n : ℕ, n ≠ 0 → (∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) →
      Finite (W.torsion n) ∧ Nat.card (W.torsion n) ≤ n ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hfac
    by_cases h1 : n = 1
    · subst h1
      refine ⟨?_, ?_⟩
      · rw [torsion_one]
        infer_instance
      · rw [torsion_one]
        simp
    · have hprime : n.minFac.Prime := Nat.minFac_prime h1
      have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
      have hmem : n.minFac ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hn⟩
      have hsplit : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hdvd
      have hklt : n / n.minFac < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hprime.one_lt
      have hk0 : n / n.minFac ≠ 0 := fun h => hn (by rw [← hsplit, h, mul_zero])
      have hkfac : ∀ q ∈ (n / n.minFac).primeFactors, q = 2 ∨ q = 3 := fun q hq =>
        hfac q (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hdvd) hn hq)
      obtain ⟨hkfin, hkcard⟩ := ih _ hklt hk0 hkfac
      obtain ⟨hpfin, hpcard⟩ :=
        finite_and_card_torsion_le_sq_of_eq_two_or_three (W := W) h2 h3 (hfac _ hmem)
      refine ⟨?_, ?_⟩
      · rw [← hsplit]
        exact finite_torsion_mul hpfin hkfin
      · calc Nat.card (W.torsion n)
            = Nat.card (W.torsion (n.minFac * (n / n.minFac))) := by rw [hsplit]
          _ ≤ Nat.card (W.torsion n.minFac) * Nat.card (W.torsion (n / n.minFac)) :=
              card_torsion_mul_le hpfin hkfin
          _ ≤ n.minFac ^ 2 * (n / n.minFac) ^ 2 := Nat.mul_le_mul hpcard hkcard
          _ = (n.minFac * (n / n.minFac)) ^ 2 := (mul_pow _ _ 2).symm
          _ = n ^ 2 := by rw [hsplit]

include h2 h3 in
/-- **`E[n]` is finite for every `3`-smooth `n ≠ 0`**, over a field in which `2` and `3` are
invertible. -/
theorem finite_torsion_of_smooth {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : Finite (W.torsion n) :=
  (finite_and_card_torsion_le_sq_of_smooth h2 h3 n hn hfac).1

include h2 h3 in
/-- **`#E[n] ≤ n²` for every `3`-smooth `n ≠ 0`**, over a field in which `2` and `3` are invertible.

This is the `n = 2^a·3^b` case of Silverman, *AEC*, III.6, Corollary 6.4, obtained from the two
unconditional computations `#E[2] ≤ 4` and `#E[3] ≤ 9` purely by multiplicativity — no
multiplication-by-`n` coordinate formula and no elliptic-net recurrence are involved. -/
theorem card_torsion_le_sq_of_smooth {n : ℕ} (hn : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3) : Nat.card (W.torsion n) ≤ n ^ 2 :=
  (finite_and_card_torsion_le_sq_of_smooth h2 h3 n hn hfac).2

include h2 h3 in
/-- **`E[2^a · 3^b]` is finite**, the explicit form of the `3`-smooth finiteness. -/
theorem finite_torsion_two_pow_mul_three_pow (a b : ℕ) :
    Finite (W.torsion (2 ^ a * 3 ^ b)) :=
  finite_torsion_of_smooth h2 h3 (by positivity) (primeFactors_two_pow_mul_three_pow a b)

include h2 h3 in
/-- **`#E[2^a · 3^b] ≤ (2^a · 3^b)²`**, the explicit form of the `3`-smooth bound. -/
theorem card_torsion_two_pow_mul_three_pow_le (a b : ℕ) :
    Nat.card (W.torsion (2 ^ a * 3 ^ b)) ≤ (2 ^ a * 3 ^ b) ^ 2 :=
  card_torsion_le_sq_of_smooth h2 h3 (by positivity)
    (primeFactors_two_pow_mul_three_pow a b)

include h2 h3 in
/-- `#E[4] ≤ 16`. -/
theorem card_torsion_four_le : Nat.card (W.torsion 4) ≤ 16 := by
  have := card_torsion_two_pow_mul_three_pow_le (W := W) h2 h3 2 0
  norm_num at this
  exact this

include h2 h3 in
/-- `#E[6] ≤ 36`. -/
theorem card_torsion_six_le : Nat.card (W.torsion 6) ≤ 36 := by
  have := card_torsion_two_pow_mul_three_pow_le (W := W) h2 h3 1 1
  norm_num at this
  exact this

include h2 h3 in
/-- `#E[8] ≤ 64`. -/
theorem card_torsion_eight_le : Nat.card (W.torsion 8) ≤ 64 := by
  have := card_torsion_two_pow_mul_three_pow_le (W := W) h2 h3 3 0
  norm_num at this
  exact this

include h2 h3 in
/-- `#E[9] ≤ 81`. -/
theorem card_torsion_nine_le : Nat.card (W.torsion 9) ≤ 81 := by
  have := card_torsion_two_pow_mul_three_pow_le (W := W) h2 h3 0 2
  norm_num at this
  exact this

end Smooth

end WeierstrassCurve.Affine
