/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.Slope

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Twisted Chern characters

For a numerical divisor class `B`, the twisted Chern character is
`ch^B = e^{−B}·ch`, component by component.  A rational scalar `β` and a
polarisation `H` give the familiar specialization `B = βH`:

```
ch^β_i(E) = ∑_{j ≤ i} ((−β)^(i−j) / (i−j)!) · ch_j(E) · H^(i−j)
```

Nothing of the sort existed in the numerical layer, so the tilt slope `ν_{α,β}`
and the BMT quantity `Q_{α,β}` could not previously be written down at all.

## What makes the name honest

The exponential notation is a claim, and `twist_add_beta` is the theorem that
earns it: twisting by `β₁ + β₂` is twisting by `β₂` and then by `β₁`. That is
`e^{−(β₁+β₂)H} = e^{−β₁H}·e^{−β₂H}` read off the graded components, and it is
the only real proof in this file.

It reduces to the scalar identity `twistCoeff_add`,

```
(x + y)^m / m! = ∑_{a ≤ m} (x^a / a!) · (y^(m−a) / (m−a)!)
```

— the binomial theorem divided through by `m!` — plus a triangular reindexing of
the double sum. The reindexing is where the work is: the two sums run in
opposite directions, so a reflection (`Finset.sum_range_reflect`) sits between
them.

## Stated on a bare graded ring first

`twistCoeff` and `twist` mention no variety, no polarisation and no Chern
character: `twist` convolves an arbitrary family `c : ℕ → A` against the
exponential coefficients of an arbitrary ring element `H`. The group law is a
fact about that convolution and is proved there. `chBetaComp` is then the
specialisation at `H = P.cls` and `c = V.chComp E`, and inherits it.

This is deliberate. The group law has nothing to do with geometry, and proving
it against `NumericalVarietyData` would have hidden that behind hypotheses it
never uses.

## Main results

* `twistCoeff`, `twistCoeff_add` — the scalar exponential coefficients.
* `twist`, `twist_add_beta` — the convolution and **the group law**.
* `BField` and `chBComp` — an arbitrary rational numerical `B`-field and
  `ch^B_i(E)`;
* `chBetaComp` — the Picard-rank-one notation `ch^(βH)_i(E)`, with
  `chBComp_along_eq_chBetaComp` proving that the two notations agree.
-/

open Finset

universe u v

namespace AlgebraicGeometry.Numerical

/-! ### The scalar coefficients -/

/-- The coefficient of `H^m` in `e^{−βH}`.-/
noncomputable def twistCoeff (β : ℚ) (m : ℕ) : ℚ := (-β) ^ m / m.factorial

/--
@isnad1 id=eq.0h1v.s5.f92cb70d4ab1 from=translated src=- shape=73f1f31b vocab=735ac624
-/
@[simp]
theorem twistCoeff_zero_beta (m : ℕ) : twistCoeff 0 m = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [twistCoeff, hm]
  · simp [twistCoeff, hm, zero_pow hm]

/-- **The exponential functional equation, at the level of coefficients.** The
binomial theorem divided through by `m!`.
@isnad1 id=eq.0h3v.s5.365c14c46121 from=translated src=- shape=9c851489 vocab=24834971
-/
theorem twistCoeff_add (β₁ β₂ : ℚ) (m : ℕ) :
    twistCoeff (β₁ + β₂) m
      = ∑ a ∈ range (m + 1), twistCoeff β₁ a * twistCoeff β₂ (m - a) := by
  simp only [twistCoeff]
  have hneg : -(β₁ + β₂) = (-β₁) + (-β₂) := by ring
  rw [hneg, add_pow, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ham : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have key : (m.choose a : ℚ) * ((a.factorial : ℚ) * ((m - a).factorial : ℚ))
      = (m.factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial ham
    push_cast [← h]; ring
  have h1 : (a.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((m - a).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linear_combination ((-β₁) ^ a * (-β₂) ^ (m - a)) * key

/-! ### The twist on a bare graded ring -/

variable {A : Type u} [CommRing A] [Algebra ℚ A]

/-- **Convolution against `e^{−βH}`**, for an arbitrary family `c : ℕ → A` and
an arbitrary `H : A`. No variety and no polarisation appear.-/
noncomputable def twist (H : A) (β : ℚ) (c : ℕ → A) (i : ℕ) : A :=
  ∑ j ∈ range (i + 1), algebraMap ℚ A (twistCoeff β (i - j)) * c j * H ^ (i - j)

/-- **The group law**: `e^{−(β₁+β₂)H} = e^{−β₁H}·e^{−β₂H}`, read on components.

This is what makes the exponential notation honest rather than decorative.
@isnad1 id=eq.0h6v.s5.df029b881000 from=translated src=- shape=9b9e96b5 vocab=4790ba03
-/
theorem twist_add_beta (H : A) (β₁ β₂ : ℚ) (c : ℕ → A) (i : ℕ) :
    twist H (β₁ + β₂) c i = twist H β₁ (twist H β₂ c) i := by
  simp only [twist]
  have expand : ∀ k ∈ range (i + 1),
      algebraMap ℚ A (twistCoeff β₁ (i - k)) * (∑ j ∈ range (k + 1),
          algebraMap ℚ A (twistCoeff β₂ (k - j)) * c j * H ^ (k - j)) * H ^ (i - k)
        = ∑ j ∈ range (k + 1),
          algebraMap ℚ A (twistCoeff β₁ (i - k) * twistCoeff β₂ (k - j))
            * c j * H ^ (i - j) := by
    intro k hk
    have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : H ^ (k - j) * H ^ (i - k) = H ^ (i - j) := by
      rw [← pow_add]; congr 1; omega
    rw [map_mul]
    calc algebraMap ℚ A (twistCoeff β₁ (i - k))
          * (algebraMap ℚ A (twistCoeff β₂ (k - j)) * c j * H ^ (k - j)) * H ^ (i - k)
        = algebraMap ℚ A (twistCoeff β₁ (i - k)) * algebraMap ℚ A (twistCoeff β₂ (k - j))
            * c j * (H ^ (k - j) * H ^ (i - k)) := by ring
      _ = _ := by rw [hpow]
  rw [Finset.sum_congr rfl expand]
  rw [Finset.sum_comm' (t' := range (i + 1)) (s' := fun j => Finset.Ico j (i + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  -- The two inner sums run in opposite directions; this is the reflection between them.
  have hrefl : ∑ a ∈ range (i - j + 1), twistCoeff β₁ (i - j - a) * twistCoeff β₂ a
      = ∑ a ∈ range (i - j + 1), twistCoeff β₁ a * twistCoeff β₂ (i - j - a) :=
    calc ∑ a ∈ range (i - j + 1), twistCoeff β₁ (i - j - a) * twistCoeff β₂ a
        = ∑ a ∈ range (i - j + 1),
            (fun b : ℕ => twistCoeff β₁ b * twistCoeff β₂ (i - j - b))
              (i - j + 1 - 1 - a) := by
          refine Finset.sum_congr rfl fun a ha => ?_
          have hai : a < i - j + 1 := Finset.mem_range.mp ha
          simp only
          congr 2
          omega
      _ = ∑ a ∈ range (i - j + 1), twistCoeff β₁ a * twistCoeff β₂ (i - j - a) :=
          Finset.sum_range_reflect
            (fun b : ℕ => twistCoeff β₁ b * twistCoeff β₂ (i - j - b)) (i - j + 1)
  have hscalar : ∑ k ∈ Finset.Ico j (i + 1), twistCoeff β₁ (i - k) * twistCoeff β₂ (k - j)
      = twistCoeff (β₁ + β₂) (i - j) := by
    rw [twistCoeff_add β₁ β₂ (i - j), Finset.sum_Ico_eq_sum_range]
    have hlen : i + 1 - j = i - j + 1 := by omega
    rw [hlen]
    refine Eq.trans ?_ hrefl
    refine Finset.sum_congr rfl fun a ha => ?_
    have hai : a < i - j + 1 := Finset.mem_range.mp ha
    congr 2 <;> omega
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← map_sum, hscalar]

/-- Absorbing a scalar into the twisting class does not change the twist:
`e^{-(βH)} = e^{-βH}`.
@isnad1 id=eq.0h5v.s6.e60648344c90 from=translated src=- shape=d9c82360 vocab=3716a48a
-/
theorem twist_algebraMap_mul (H : A) (β : ℚ) (c : ℕ → A) (i : ℕ) :
    twist (algebraMap ℚ A β * H) 1 c i = twist H β c i := by
  simp only [twist]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcoeff : twistCoeff 1 (i - j) * β ^ (i - j) = twistCoeff β (i - j) := by
    unfold twistCoeff
    have hfactorial : ((i - j).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    rw [← mul_pow]
    ring
  rw [mul_pow, ← map_pow]
  calc
    algebraMap ℚ A (twistCoeff 1 (i - j)) * c j *
          (algebraMap ℚ A (β ^ (i - j)) * H ^ (i - j)) =
        algebraMap ℚ A (twistCoeff 1 (i - j) * β ^ (i - j)) * c j * H ^ (i - j) := by
          rw [map_mul]
          ring
    _ = _ := by rw [hcoeff]

/-! ### The twisted Chern character -/

variable {N : Type v} [AddCommGroup N] {n : ℕ}
variable (V : NumericalVarietyData n A N)

/-- A numerical `B`-field: an arbitrary rational codimension-one class.

No positivity is required.  The rational scalar restriction comes from the
current `NumericalRingData`, whose intersection ring and degree map are over
`ℚ`; it is not a mathematical restriction on the usual real `B`-field.-/
structure BField (R : NumericalRingData n A) where
  /-- The numerical divisor class `B`.-/
  cls : A
  /-- The class lies in codimension one.-/
  cls_mem : cls ∈ R.piece 1

namespace BField

variable {R : NumericalRingData n A}

/-- Powers of a `B`-field have their expected codimension.
@isnad1 id=mem.0h5v.s7.966f2e480db5 from=translated src=- shape=9f9b4d7a vocab=93ed5e59
-/
theorem pow_mem (B : BField R) (i : ℕ) : B.cls ^ i ∈ R.piece i := by
  induction i with
  | zero => simpa using R.one_mem_piece_zero
  | succ i ih => simpa [pow_succ] using R.mul_mem_piece ih B.cls_mem

/-- The `B`-field `βH` determined by a polarisation and a rational scalar.-/
noncomputable def along (P : Polarization R) (β : ℚ) : BField R where
  cls := algebraMap ℚ A β * P.cls
  cls_mem := by
    simpa using R.mul_mem_piece (R.algebraMap_mem_piece_zero β) P.cls_mem

/-- The class underlying the scalar `B`-field is literally `βH`.
@isnad1 id=eq.0h5v.s6.09dcc2654579 from=translated src=- shape=2aed821d vocab=e22be429
-/
@[simp]
theorem along_cls (P : Polarization R) (β : ℚ) :
    (along P β).cls = algebraMap ℚ A β * P.cls := rfl

end BField

/-- The `B`-twisted Chern-character component `ch^B_i(E)`.-/
noncomputable def chBComp (B : BField V.ring) (E : N) (i : ℕ) : A :=
  twist B.cls 1 (V.chComp E) i

/-- The component formula obtained by expanding the truncated exponential `e^{-B}`.
@isnad1 id=eq.0h7v.s7.245476b53800 from=translated src=- shape=c410e702 vocab=26e99ddb
-/
theorem chBComp_eq (B : BField V.ring) (E : N) (i : ℕ) :
    chBComp V B E i =
      ∑ j ∈ range (i + 1),
        algebraMap ℚ A (twistCoeff 1 (i - j)) * V.chComp E j * B.cls ^ (i - j) := rfl

/-- `ch^B_i(E)` remains in codimension `i`.
@isnad1 id=mem.0h7v.s7.a6b0b778054e from=translated src=- shape=94f36fa4 vocab=2b799155
-/
theorem chBComp_mem (B : BField V.ring) (E : N) (i : ℕ) :
    chBComp V B E i ∈ V.ring.piece i := by
  rw [chBComp_eq]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h0 : algebraMap ℚ A (twistCoeff 1 (i - j)) * V.chComp E j ∈ V.ring.piece j := by
    have := V.ring.mul_mem_piece (V.ring.algebraMap_mem_piece_zero (twistCoeff 1 (i - j)))
      (V.chComp_mem E j)
    simpa using this
  have := V.ring.mul_mem_piece h0 (B.pow_mem (i - j))
  rwa [Nat.add_sub_cancel' hji] at this

/-- The `B`-twisted Chern character is additive in the numerical class.
@isnad1 id=eq.0h8v.s6.37dee591e01b from=translated src=- shape=bfa19ab3 vocab=f6619926
-/
theorem chBComp_add (B : BField V.ring) (E F : N) (i : ℕ) :
    chBComp V B (E + F) i = chBComp V B E i + chBComp V B F i := by
  simp only [chBComp_eq, V.chComp_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The codimension-zero component is unchanged by a `B`-field twist.
@isnad1 id=eq.0h6v.s6.cc4eaba75296 from=translated src=- shape=49048116 vocab=70a81e68
-/
theorem chBComp_zero (B : BField V.ring) (E : N) :
    chBComp V B E 0 = V.chComp E 0 := by
  simp [chBComp, twist, twistCoeff]

/-- The first twisted component is `ch₁^B = ch₁ - B ch₀`.
@isnad1 id=eq.0h6v.s7.3db405343562 from=translated src=- shape=0c31adb7 vocab=c26d441a
-/
theorem chBComp_one (B : BField V.ring) (E : N) :
    chBComp V B E 1 = V.chComp E 1 - V.chComp E 0 * B.cls := by
  norm_num [chBComp, twist, twistCoeff, Finset.sum_range_succ]
  ring

/-- The second twisted component is
`ch₂^B = ch₂ - B ch₁ + (B²/2) ch₀`.
@isnad1 id=eq.0h6v.s8.70f92a507fdd from=translated src=- shape=90c2c470 vocab=4cc5cd85
-/
theorem chBComp_two (B : BField V.ring) (E : N) :
    chBComp V B E 2 =
      V.chComp E 2 - V.chComp E 1 * B.cls
        + algebraMap ℚ A (1 / 2) * V.chComp E 0 * B.cls ^ 2 := by
  norm_num [chBComp, twist, twistCoeff, Finset.sum_range_succ]
  ring

variable (P : Polarization V.ring)

/-- **The `β`-twisted Chern character** `ch^β_i(E)`.-/
noncomputable def chBetaComp (β : ℚ) (E : N) (i : ℕ) : A :=
  twist P.cls β (V.chComp E) i

/--
@isnad1 id=eq.0h8v.s7.c6a0bc342256 from=translated src=- shape=78dda2c5 vocab=d5333c1e
-/
theorem chBetaComp_eq (β : ℚ) (E : N) (i : ℕ) :
    chBetaComp V P β E i
      = ∑ j ∈ range (i + 1),
        algebraMap ℚ A (twistCoeff β (i - j)) * V.chComp E j * P.cls ^ (i - j) := rfl

/-- `ch^β_i(E)` lives in codimension `i`, like `ch_i(E)`: each summand is
`piece 0 · piece j · piece (i−j)`, and `j + (i−j) = i` inside the sum's range.
@isnad1 id=mem.0h8v.s7.a74dc161dabd from=translated src=- shape=a38a064b vocab=92df142c
-/
theorem chBetaComp_mem (β : ℚ) (E : N) (i : ℕ) :
    chBetaComp V P β E i ∈ V.ring.piece i := by
  rw [chBetaComp_eq]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h0 : algebraMap ℚ A (twistCoeff β (i - j)) * V.chComp E j ∈ V.ring.piece j := by
    have := V.ring.mul_mem_piece (V.ring.algebraMap_mem_piece_zero (twistCoeff β (i - j)))
      (V.chComp_mem E j)
    simpa using this
  have := V.ring.mul_mem_piece h0 (P.pow_mem (i - j))
  rwa [Nat.add_sub_cancel' hji] at this

/-- The twisted Chern character is additive in the class, because `ch` is.
@isnad1 id=eq.0h9v.s6.95307f85e0f3 from=translated src=- shape=90faca75 vocab=24576603
-/
theorem chBetaComp_add (β : ℚ) (E F : N) (i : ℕ) :
    chBetaComp V P β (E + F) i = chBetaComp V P β E i + chBetaComp V P β F i := by
  simp only [chBetaComp_eq, V.chComp_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- At `β = 0` the twist is the identity: `ch^0 = ch`.
@isnad1 id=eq.0h7v.s6.9270947db605 from=translated src=- shape=eee4835b vocab=d72d8d16
-/
theorem chBetaComp_zero_beta (E : N) (i : ℕ) :
    chBetaComp V P 0 E i = V.chComp E i := by
  rw [chBetaComp_eq, Finset.sum_eq_single i]
  · simp
  · intro j hj hne
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have : i - j ≠ 0 := by omega
    simp [twistCoeff_zero_beta, this]
  · intro h
    exact absurd (Finset.self_mem_range_succ i) h

/-- **The group law on the twisted Chern character**, inherited from `twist`.
@isnad1 id=eq.0h9v.s6.ccdb7f46bd6d from=translated src=- shape=8f1b3186 vocab=a25fe15a
-/
theorem chBetaComp_add_beta (β₁ β₂ : ℚ) (E : N) (i : ℕ) :
    chBetaComp V P (β₁ + β₂) E i = twist P.cls β₁ (chBetaComp V P β₂ E) i :=
  twist_add_beta P.cls β₁ β₂ (V.chComp E) i

/-- The arbitrary-class notation and the scalar notation agree at `B = βH`.
@isnad1 id=eq.0h8v.s6.a0e93897e3fb from=translated src=- shape=3deb8c86 vocab=3e8c7317
-/
theorem chBComp_along_eq_chBetaComp (β : ℚ) (E : N) (i : ℕ) :
    chBComp V (BField.along P β) E i = chBetaComp V P β E i := by
  exact twist_algebraMap_mul P.cls β (V.chComp E) i

end AlgebraicGeometry.Numerical
