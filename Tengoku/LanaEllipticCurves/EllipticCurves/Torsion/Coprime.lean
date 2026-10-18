/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.TwoTorsion
import Tengoku.Seed.Data.Nat.Factorization.Induction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The coprime decomposition of torsion

`EllipticCurves.Torsion.Multiplicative` proves the *inequality* `#E[mn] ≤ #E[m] · #E[n]`, valid for
arbitrary `m` and `n`. When `m` and `n` are **coprime** that inequality is an **equality**, and in
fact holds already at the level of groups: for an arbitrary additive abelian group `A`,

```
A[m * n] ≃+ A[m] × A[n]                    whenever `IsCoprime m n` in `ℤ`.
```

This is the Chinese remainder theorem for `ℤ`-modules. Specialised to the torsion subgroups `E[n]`
of a Weierstrass curve it gives `#E[mn] = #E[m] · #E[n]` for coprime `m, n` — with *no* finiteness
hypothesis, since `Nat.card_prod` is unconditional — and, by induction over the prime factorisation,
the **primary decomposition**

```
#E[n] = ∏_{p ∈ n.primeFactors} #E[p ^ (n.factorization p)]                        (n ≠ 0),
```

which reduces the computation of `#E[n]` entirely to prime powers, complementing
`EllipticCurves.Torsion.Multiplicative`'s reduction of the *bound* to primes. Like its inputs, this
file is independent of Ward's theorem, of the elliptic-net recurrence, and of the
multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`.

## The mechanism

Write `h : IsCoprime m n` as a Bézout identity `u * m + v * n = 1`.

* Adding is well defined `A[m] × A[n] → A[m * n]` with no coprimality at all, since
  `(mn) • (a + b) = n • (m • a) + m • (n • b) = 0`.
* Its inverse is `P ↦ (v • n • P, u • m • P)`: the first component lies in `A[m]` because
  `m • (v • n • P) = v • ((m * n) • P) = 0`, and symmetrically for the second.
* The two are mutually inverse: `(v • n • P) + (u • m • P) = (v * n + u * m) • P = P`, while for
  `a ∈ A[m]` and `b ∈ A[n]` one has `v • n • (a + b) = v • n • a = (1 - u * m) • a = a` and
  `u • m • (a + b) = u • m • b = (1 - v * n) • b = b`.

Coprimality is genuinely needed for the *equality*: at `A = ZMod 2` and `m = n = 2` one has
`A[4] = A[2] = A`, so `#A[4] = 2` while `#A[2] · #A[2] = 4`.

## Main definitions

* `AddSubgroup.torsionByProdHom`: the addition homomorphism `A[m] × A[n] →+ A[m * n]`.
* `AddSubgroup.torsionByMulAddEquiv`: the isomorphism `A[m * n] ≃+ A[m] × A[n]` for coprime `m, n`.
* `WeierstrassCurve.Affine.torsionMulAddEquiv`: its specialisation `E[mn] ≃+ E[m] × E[n]`.

## Main statements

* `AddSubgroup.card_torsionBy_mul_of_isCoprime`, `AddSubgroup.finite_torsionBy_mul_iff`: the
  cardinality and finiteness consequences for an arbitrary abelian group.
* `WeierstrassCurve.Affine.card_torsion_mul`, `WeierstrassCurve.Affine.finite_torsion_mul_iff`:
  their specialisations to `E[n]`.
* `WeierstrassCurve.Affine.card_torsion_eq_prod_factorization`: the primary decomposition
  `#E[n] = ∏_p #E[p ^ (n.factorization p)]`.
* `WeierstrassCurve.Affine.card_torsion_two_mul`,
  `WeierstrassCurve.Affine.nonempty_torsion_two_mul_addEquiv`: `#E[2n] = 4 · #E[n]` and
  `E[2n] ≃+ (ℤ/2ℤ)² × E[n]` for odd `n`, over an algebraically closed field of characteristic `≠ 2`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, Corollary 6.4.
-/

open scoped AddSubgroup

namespace AddSubgroup

variable (A : Type*) [AddCommGroup A] (m n : ℤ)

/-- **Adding maps `A[m] × A[n]` into `A[m * n]`.** Indeed
`(mn) • (a + b) = n • (m • a) + m • (n • b)` vanishes as soon as `m • a = 0` and `n • b = 0`; no
coprimality is needed here. -/
def torsionByProdHom : A[m] × A[n] →+ A[m * n] where
  toFun P := ⟨(P.1 : A) + (P.2 : A), by
    rw [torsionBy.zsmul_iff, smul_add]
    have h₁ : (m * n) • (P.1 : A) = 0 := by
      rw [mul_comm, mul_smul, torsionBy.zsmul_iff.mp P.1.2, smul_zero]
    have h₂ : (m * n) • (P.2 : A) = 0 := by
      rw [mul_smul, torsionBy.zsmul_iff.mp P.2.2, smul_zero]
    rw [h₁, h₂, add_zero]⟩
  map_zero' := by ext; simp
  map_add' P Q := by
    ext
    simp only [AddSubgroup.coe_add, Prod.fst_add, Prod.snd_add]
    abel

@[simp]
lemma torsionByProdHom_apply_coe (P : A[m] × A[n]) :
    ((torsionByProdHom A m n P : A[m * n]) : A) = (P.1 : A) + (P.2 : A) :=
  rfl

variable {A m n}

/-- **Adding is bijective on coprime torsion.** Injectivity: if `a + b = 0` with `m • a = 0` and
`n • b = 0`, then `n • a = -n • b = 0`, so `a = (u * m + v * n) • a = 0`. Surjectivity:
`P = (v • n • P) + (u • m • P)` by the Bézout identity. -/
lemma torsionByProdHom_bijective (h : IsCoprime m n) :
    Function.Bijective (torsionByProdHom A m n) := by
  obtain ⟨u, v, huv⟩ := h
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hab
    rw [torsionBy.zsmul_iff] at ha hb
    have hab' : a + b = 0 := congrArg Subtype.val hab
    have hb' : b = -a := (neg_eq_of_add_eq_zero_right hab').symm
    have hna : n • a = 0 := by
      have : n • b = 0 := hb
      rw [hb', smul_neg, neg_eq_zero] at this
      exact this
    have ha0 : a = 0 := by
      have h1 : (u * m + v * n) • a = a := by rw [huv, one_smul]
      rw [← h1, add_smul, mul_smul, ha, smul_zero, zero_add, mul_smul, hna, smul_zero]
    have hb0 : b = 0 := by rw [hb', ha0, neg_zero]
    exact Prod.ext (Subtype.ext ha0) (Subtype.ext hb0)
  · intro P
    have hP : (m * n) • (P : A) = 0 := torsionBy.zsmul_iff.mp P.2
    refine ⟨(⟨v • n • (P : A), ?_⟩, ⟨u • m • (P : A), ?_⟩), ?_⟩
    · rw [torsionBy.zsmul_iff, ← mul_smul, ← mul_smul,
        show m * v * n = v * (m * n) by ring, mul_smul, hP, smul_zero]
    · rw [torsionBy.zsmul_iff, ← mul_smul, ← mul_smul,
        show n * u * m = u * (m * n) by ring, mul_smul, hP, smul_zero]
    · refine Subtype.ext ?_
      rw [torsionByProdHom_apply_coe]
      calc v • n • (P : A) + u • m • (P : A)
          = (v * n + u * m) • (P : A) := by rw [add_smul, mul_smul, mul_smul]
        _ = (P : A) := by rw [add_comm (v * n), huv, one_smul]

/-- **The Chinese remainder theorem for torsion subgroups**: for coprime `m` and `n`, adding is an
isomorphism `A[m] × A[n] ≃+ A[m * n]`, with inverse `P ↦ (v • n • P, u • m • P)` read off from a
Bézout identity `u * m + v * n = 1`. -/
noncomputable def torsionByMulAddEquiv (h : IsCoprime m n) : A[m * n] ≃+ A[m] × A[n] :=
  (AddEquiv.ofBijective (torsionByProdHom A m n) (torsionByProdHom_bijective h)).symm

/-- **The torsion count is multiplicative on coprime arguments.** This needs no finiteness
hypothesis: `Nat.card_prod` holds unconditionally, and both sides are `0` when either factor is
infinite. -/
theorem card_torsionBy_mul_of_isCoprime (h : IsCoprime m n) :
    Nat.card A[m * n] = Nat.card A[m] * Nat.card A[n] := by
  rw [Nat.card_congr (torsionByMulAddEquiv h).toEquiv, Nat.card_prod]

/-- **Finiteness of coprime torsion is an iff**, the sharp form of `finite_torsionBy_mul`. -/
theorem finite_torsionBy_mul_iff (h : IsCoprime m n) :
    Finite A[m * n] ↔ Finite A[m] ∧ Finite A[n] := by
  rw [(torsionByMulAddEquiv h).toEquiv.finite_iff, Prod.finite_iff]

end AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {m n : ℕ}

private lemma torsion_mul_eq' (m n : ℕ) : W.torsion (m * n) = W.Point[(m : ℤ) * (n : ℤ)] :=
  congrArg (fun k : ℤ => W.Point[k]) (Nat.cast_mul m n)

/-- **`E[mn] ≃+ E[m] × E[n]` for coprime `m` and `n`** — the Chinese remainder decomposition of the
torsion subgroups of a Weierstrass curve. -/
noncomputable def torsionMulAddEquiv (h : Nat.Coprime m n) :
    W.torsion (m * n) ≃+ W.torsion m × W.torsion n :=
  (AddEquiv.addSubgroupCongr (torsion_mul_eq' (W := W) m n)).trans
    (AddSubgroup.torsionByMulAddEquiv (Nat.isCoprime_iff_coprime.mpr h))

/-- **`#E[mn] = #E[m] · #E[n]` for coprime `m` and `n`**, the sharp companion of the general
inequality `card_torsion_mul_le`. No finiteness hypothesis is required. -/
theorem card_torsion_mul (h : Nat.Coprime m n) :
    Nat.card (W.torsion (m * n)) = Nat.card (W.torsion m) * Nat.card (W.torsion n) := by
  rw [torsion_mul_eq', AddSubgroup.card_torsionBy_mul_of_isCoprime
    (Nat.isCoprime_iff_coprime.mpr h)]

/-- **`E[mn]` is finite exactly when both `E[m]` and `E[n]` are**, for coprime `m` and `n`. -/
theorem finite_torsion_mul_iff (h : Nat.Coprime m n) :
    Finite (W.torsion (m * n)) ↔ Finite (W.torsion m) ∧ Finite (W.torsion n) := by
  rw [torsion_mul_eq', AddSubgroup.finite_torsionBy_mul_iff (Nat.isCoprime_iff_coprime.mpr h)]

/-- **The primary decomposition of the torsion count**: `#E[n]` is the product of `#E[p^k]` over the
prime powers `p^k` exactly dividing `n`. Together with `card_torsion_le_sq_of_smooth` this reduces
the computation of `#E[n]` entirely to prime powers. -/
theorem card_torsion_eq_prod_factorization (hn : n ≠ 0) :
    Nat.card (W.torsion n) = n.factorization.prod fun p k => Nat.card (W.torsion (p ^ k)) :=
  Nat.multiplicative_factorization (fun k => Nat.card (W.torsion k))
    (fun _ _ h => card_torsion_mul h) (by rw [torsion_one]; simp) hn

/-! ## The `2`-torsion instance

Over an algebraically closed field of characteristic `≠ 2` the merged computation `#E[2] = 4` splits
off from every odd-index torsion subgroup. -/

/-- **`#E[2n] = 4 · #E[n]` for odd `n`** over an algebraically closed field of characteristic
`≠ 2`. -/
theorem card_torsion_two_mul [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hn : Odd n) :
    Nat.card (W.torsion (2 * n)) = 4 * Nat.card (W.torsion n) := by
  rw [card_torsion_mul (Nat.coprime_two_left.mpr hn), card_torsion_two h2]

/-- **`E[2n] ≃+ (ℤ/2ℤ)² × E[n]` for odd `n`** over an algebraically closed field of characteristic
`≠ 2`. -/
theorem nonempty_torsion_two_mul_addEquiv [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (hn : Odd n) : Nonempty (W.torsion (2 * n) ≃+ (ZMod 2 × ZMod 2) × W.torsion n) := by
  obtain ⟨e⟩ := nonempty_torsionTwo_addEquiv (W := W) h2
  exact ⟨(torsionMulAddEquiv (Nat.coprime_two_left.mpr hn)).trans (e.prodCongr (AddEquiv.refl _))⟩

end WeierstrassCurve.Affine
