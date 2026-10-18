/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.CurveField.Rational

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The tripod `ℙ¹ ∖ {0, 1, ∞}`

Let `t` be a rational generator of `K` (`K = ℚ(t)`, `Belyi.CurveField.IsRationalGenerator`).
The *tripod* is the complement in `ℙ¹` of the three places `t = 0`, `t = 1`, `t = ∞`
(`Belyi.CurveField.tripodPlaces t`). Each of these places has degree one, and `t` (resp.
`t - 1`) has a simple zero at `t = 0` (resp. `t = 1`) and a simple pole at `∞`.

The algebraic points of the tripod correspond to `ℚ̄ ∖ {0, 1}` via `x ↦ t(x)`
(`Belyi.CurveField.QbarPoint.equivTripod`), and its coordinate ring, the ring of functions
regular away from the three places, is `ℚ[t, t⁻¹, (1 - t)⁻¹]`
(`Belyi.CurveField.forall_mem_iff_mem_adjoin_tripod`).

## Main definitions and results

* `Belyi.CurveField.zeroPlace t`, `Belyi.CurveField.onePlace t`: the places `t = 0`, `t = 1`
  (`Belyi.CurveField.eq_zeroPlace_iff`, `Belyi.CurveField.eq_onePlace_iff`).
* `Belyi.CurveField.tripodPlaces t : Finset (Place K)`, of cardinality `3`;
  `Belyi.CurveField.mem_tripodPlaces_iff_ord`: `P` is one of them iff
  `ord_P t ≠ 0 ∨ ord_P (t - 1) > 0`; `Belyi.CurveField.notMem_tripodPlaces_iff`: `P` is not
  one of them iff `t, t⁻¹, (1 - t)⁻¹ ∈ O_P`; `Belyi.CurveField.deg_of_mem_tripodPlaces`.
* `Belyi.CurveField.ord_self`: the divisor of `t` is `[0] - [∞]`.
* `Belyi.CurveField.QbarPoint.P_mem_tripodPlaces_iff`, `Belyi.CurveField.QbarPoint.equivTripod`.
* `Belyi.CurveField.setOf_forall_mem_eq_adjoin_tripod`: the coordinate ring of the tripod.
-/

open Polynomial
open scoped IntermediateField

local notation "Qbar" => AlgebraicClosure ℚ

namespace Belyi.CurveField

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- The place `t = 0`. -/
noncomputable def zeroPlace (t : K) : Place K := infPlace t⁻¹

/-- The place `t = 1`. -/
noncomputable def onePlace (t : K) : Place K := infPlace (t - 1)⁻¹

open Classical in
/-- The three places `t = 0`, `t = 1`, `t = ∞` removed from `ℙ¹` to form the tripod. -/
noncomputable def tripodPlaces (t : K) : Finset (Place K) :=
  {zeroPlace t, onePlace t, infPlace t}

theorem mem_tripodPlaces {t : K} {P : Place K} :
    P ∈ tripodPlaces t ↔ P = zeroPlace t ∨ P = onePlace t ∨ P = infPlace t := by
  simp [tripodPlaces]

variable {t : K} (ht : IsRationalGenerator t)
include ht

/-! ### The places `t = 0` and `t = 1` -/

omit ht in
/-- `t` and `t - 1` have no common zero. -/
theorem not_ord_pos_and_ord_sub_one_pos (P : Place K) :
    ¬ (0 < P.ord t ∧ 0 < P.ord (t - 1)) := by
  rintro ⟨h1, h2⟩
  have h : t + -(t - 1) = 1 := by ring
  have := P.min_le_ord_add (f := t) (g := -(t - 1)) (by rw [h]; exact one_ne_zero)
  rw [Place.ord_neg, h, Place.ord_one] at this
  omega

/-! ### The three places -/

/-! ### Points of the tripod -/

namespace QbarPoint

end QbarPoint

/-! ### The coordinate ring `ℚ[t, t⁻¹, (1 - t)⁻¹]` of the tripod -/

end Belyi.CurveField
