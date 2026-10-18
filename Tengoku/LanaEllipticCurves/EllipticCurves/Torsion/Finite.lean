/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A finiteness engine for point sets with bounded `x`-support

For a Weierstrass curve `W` over a field `F`, the Weierstrass equation `y² + a₁xy + a₃y = x³ + …`
is *quadratic in `y`*, so for each fixed `x` there are at most two points `(x, y)` on the curve:
any two solutions `y₁, y₂` satisfy `y₁ = y₂` or `y₁ = negY x y₂` (Mathlib's
`WeierstrassCurve.Affine.Y_eq_of_X_eq`). Consequently, **any set of affine points whose
`x`-coordinates lie in a finite set is itself finite**.

Counting the same fibres rather than merely bounding them gives the sharper statement that such a
set has at most `2 * S.ncard + 1` elements: at most two points above each `x ∈ S`, plus the point at
infinity. Since the `x`-coordinates of the nonzero `n`-torsion points are expected to be the
`≤ (n² − 1)/2` roots of `W.preΨ n` for odd `n`, and `2 * (n² − 1)/2 + 1 = n²`, this is exactly the
shape of the sharp bound `#E[n] ≤ n²`.

This is the purely geometric counting infrastructure behind the finiteness of `E[n]` (issue #252,
rung 3 of the `#E[n] ≤ n²` program, parent #246). It is deliberately **independent of the
division-polynomial / elliptic-net recurrence**: it takes the finite `x`-support as a *hypothesis*.
The remaining input — that every nonzero `n`-torsion point has an `x`-coordinate among the roots of
a suitable division polynomial — is supplied by the multiplication-by-`n` characterisation (#251),
which is **closed**: `mem_torsionXSupport_of_mem_torsion` (`EllipticCurves.Torsion.XSupport`) in
general, and unconditionally for `n = 3` by `EllipticCurves.Torsion.ThreeTorsion`.

## Main definitions

* `WeierstrassCurve.Affine.someY`: a classically chosen solution `y` of the Weierstrass equation
  above `x`, whenever there is one. It labels one of the (at most two) points of the `y`-fibre, so
  that the other is distinguished from it by a single `Bool`.

## Main statements

* `WeierstrassCurve.Affine.setOf_equation_subset_pair`: the `y`-fibre `{y | W.Equation x y}` is
  contained in the two-element set `{y₀, W.negY x y₀}` for any solution `y₀`.
* `WeierstrassCurve.Affine.setOf_equation_finite`: the `y`-fibre over a fixed `x` is finite.
* `WeierstrassCurve.Affine.finite_of_xCoords`: a set of points whose nonzero members have
  `x`-coordinate in a finite set `S` is finite.
* `WeierstrassCurve.Affine.ncard_le_of_xCoords`: the cardinality companion, `A.ncard ≤ 2 * S.ncard
  + 1`.
* `WeierstrassCurve.Affine.torsion_finite_of_xCoords`,
  `WeierstrassCurve.Affine.finite_torsion_of_xCoords`,
  `WeierstrassCurve.Affine.card_torsion_le_of_xCoords`: the specialisations to `E[n]`, the exact
  interface the `#E[n] ≤ n²` counting (#252) consumes; #251 supplies the finite `x`-support and is
  closed (`EllipticCurves.Torsion.XSupport`), so `card_torsion_le_sq` is merged there.

## References

Silverman, *The Arithmetic of Elliptic Curves*, III.4 and III.6 Cor 6.4 (the sharp count).
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : Affine F)

/-- The `y`-fibre of the Weierstrass equation over a fixed `x` is contained in the two-element set
`{y₀, W.negY x y₀}` cut out by any single solution `y₀`: the equation is quadratic in `y`, and
`Y_eq_of_X_eq` says any two solutions coincide up to the `negY` involution. -/
lemma setOf_equation_subset_pair {x y₀ : F} (h₀ : W.Equation x y₀) :
    {y : F | W.Equation x y} ⊆ {y₀, W.negY x y₀} := by
  intro y hy
  rcases Y_eq_of_X_eq hy h₀ rfl with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- For each fixed `x`, only finitely many `y` satisfy the Weierstrass equation `W.Equation x y`
(at most two). -/
lemma setOf_equation_finite (x : F) : {y : F | W.Equation x y}.Finite := by
  rcases Set.eq_empty_or_nonempty {y : F | W.Equation x y} with h | ⟨y₀, h₀⟩
  · rw [h]; exact Set.finite_empty
  · exact ((Set.finite_singleton _).insert _).subset
      (W.setOf_equation_subset_pair h₀)

/-- The `y`-fibre over a fixed `x` has at most two elements. -/
lemma setOf_equation_ncard_le_two (x : F) : {y : F | W.Equation x y}.ncard ≤ 2 := by
  rcases Set.eq_empty_or_nonempty {y : F | W.Equation x y} with h | ⟨y₀, h₀⟩
  · rw [h, Set.ncard_empty]; norm_num
  · calc {y : F | W.Equation x y}.ncard
        ≤ ({y₀, W.negY x y₀} : Set F).ncard :=
          Set.ncard_le_ncard (W.setOf_equation_subset_pair h₀) (Set.toFinite _)
      _ ≤ 2 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          rw [Set.ncard_singleton]

/-- The auxiliary "coordinate tag" map: the identity point goes to `none`, and a genuine point
`(x, y)` goes to `some (x, y)`. It is injective, and turns finiteness of a set of points into
finiteness of a set of tags. -/
private def coordTag : W.Point → Option (F × F)
  | 0 => none
  | .some x y _ => some (x, y)

private lemma coordTag_injective : Function.Injective W.coordTag := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h <;>
    simp only [coordTag, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  · rfl
  · obtain ⟨rfl, rfl⟩ := h; rfl

/-- **Finiteness engine.** A set `A` of affine points on `W` whose *nonzero* members all have
`x`-coordinate in a finite set `S` is itself finite.

This is the geometric heart of the `#E[n] ≤ n²` finiteness argument (#252): the Weierstrass
equation is quadratic in `y`, so each `x ∈ S` supports at most two points, and `A` embeds into the
finite set of such coordinate pairs (plus the identity). -/
theorem finite_of_xCoords {A : Set W.Point} {S : Set F} (hS : S.Finite)
    (hx : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄, (.some x y h : W.Point) ∈ A → x ∈ S) :
    A.Finite := by
  -- The set of coordinate pairs with `x`-coordinate in `S` that lie on the curve.
  set T : Set (F × F) := {p : F × F | p.1 ∈ S ∧ W.Equation p.1 p.2} with hT
  -- `T` is finite: it is the union over `x ∈ S` of the (finite) `y`-fibres.
  have hTfin : T.Finite := by
    apply Set.Finite.subset (hS.biUnion fun x _ => (W.setOf_equation_finite x).image (Prod.mk x))
    rintro ⟨x, y⟩ ⟨hxS, hxy⟩
    exact Set.mem_biUnion hxS ⟨y, hxy, rfl⟩
  -- `A` embeds into `insert none (some '' T)` via the injective coordinate tag.
  refine Set.Finite.of_finite_image (f := W.coordTag) ?_ (W.coordTag_injective.injOn)
  refine ((hTfin.image some).insert none).subset ?_
  rintro _ ⟨(_ | ⟨x, y, h⟩), hP, rfl⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨(x, y), ⟨hx hP, h.left⟩, rfl⟩

/-! ## The cardinality companion -/

open Classical in
/-- A classically chosen solution of the Weierstrass equation above `x`, when there is one (and the
junk value `0` otherwise).

Its only role is bookkeeping: the `y`-fibre over `x` has at most two elements, and `someY x` picks
one of them, so the other is distinguished from it by a single `Bool`. -/
noncomputable def someY (x : F) : F :=
  if h : ∃ y : F, W.Equation x y then h.choose else 0

/-- `someY x` does lie on `W` as soon as some point of `W` does. -/
lemma equation_someY {x y : F} (h : W.Equation x y) : W.Equation x (W.someY x) := by
  classical
  rw [someY, dite_eq_left ⟨y, h⟩]
  exact Exists.choose_spec (⟨y, h⟩ : ∃ y : F, W.Equation x y)

open Classical in
/-- The refined coordinate tag: the identity point goes to `none`, and a genuine point `(x, y)` goes
to `some (x, b)` where the `Bool` `b` records whether `y` is the designated solution `someY x` or
the other one. It is injective, which is exactly the statement that at most two points lie above
each `x`. -/
private noncomputable def fibreTag : W.Point → Option (F × Bool)
  | 0 => none
  | .some x y _ => some (x, decide (y = W.someY x))

private lemma fibreTag_injective : Function.Injective W.fibreTag := by
  classical
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h <;>
    simp only [fibreTag, reduceCtorEq, Option.some.injEq, Prod.mk.injEq, decide_eq_decide] at h
  · rfl
  · obtain ⟨rfl, hb⟩ := h
    have hy : y₁ = y₂ := by
      by_cases hy₁ : y₁ = W.someY x₁
      · exact hy₁.trans (hb.mp hy₁).symm
      · have hy₂ : y₂ ≠ W.someY x₁ := fun hc => hy₁ (hb.mpr hc)
        rcases Y_eq_of_X_eq h₁.left h₂.left rfl with h | h
        · exact h
        · exfalso
          rcases Y_eq_of_X_eq (W.equation_someY h₁.left) h₁.left rfl with h' | h'
          · exact hy₁ h'.symm
          · exact hy₂ (by rw [h', h, negY_negY])
    subst hy
    rfl

/-- **Counting engine.** A set `A` of affine points on `W` whose *nonzero* members all have
`x`-coordinate in a finite set `S` has at most `2 * S.ncard + 1` elements: at most two points above
each `x ∈ S`, plus the point at infinity.

This is the sharp companion of `WeierstrassCurve.Affine.finite_of_xCoords`, and the shape in which
the `#E[n] ≤ n²` bound (#252) is proved: for odd `n` the `x`-support has `≤ (n² − 1)/2` elements and
`2 * (n² − 1)/2 + 1 = n²`. -/
theorem ncard_le_of_xCoords {A : Set W.Point} {S : Set F} (hS : S.Finite)
    (hx : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄, (.some x y h : W.Point) ∈ A → x ∈ S) :
    A.ncard ≤ 2 * S.ncard + 1 := by
  classical
  have hT : (S ×ˢ (Set.univ : Set Bool)).Finite := hS.prod Set.finite_univ
  have hsub : W.fibreTag '' A ⊆ insert none (some '' (S ×ˢ (Set.univ : Set Bool))) := by
    rintro _ ⟨(_ | ⟨x, y, h⟩), hP, rfl⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨(x, _), ⟨hx hP, Set.mem_univ _⟩, rfl⟩
  calc A.ncard
      = (W.fibreTag '' A).ncard := (Set.ncard_image_of_injective A W.fibreTag_injective).symm
    _ ≤ (insert none (some '' (S ×ˢ (Set.univ : Set Bool)))).ncard :=
        Set.ncard_le_ncard hsub ((hT.image some).insert none)
    _ ≤ (some '' (S ×ˢ (Set.univ : Set Bool))).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 * S.ncard + 1 := by
        rw [Set.ncard_image_of_injective _ (Option.some_injective _), Set.ncard_prod]
        simp [mul_comm]

/-- **The refined counting engine.**  Same as `WeierstrassCurve.Affine.ncard_le_of_xCoords`, except
that the `x`-support is split into a part `S` counted with two points per fibre and a part `S₀` over
which every point of `A` is *its own negative* — and so is alone in its fibre.  The bound drops from
`2 * (S ∪ S₀).ncard + 1` to `2 * S.ncard + S₀.ncard + 1`.

⚠️ The hypothesis `hone` is stated geometrically, as `y = W.negY x y`, rather than in terms of the
bookkeeping value `W.someY x`: that is the form a consumer has, and the translation between the two
is the `Y_eq_of_X_eq` step inside the proof.

This is what turns the `2n² − 1` of `ncard_le_of_xCoords` into the sharp `#E[n] ≤ n²` at an **even**
index, where `S₀` is the three-element root set of `Ψ₂Sq` — see
`EllipticCurves.Torsion.XSupport`. -/
theorem ncard_le_of_xCoords_of_selfNeg {A : Set W.Point} {S S₀ : Set F} (hS : S.Finite)
    (hS₀ : S₀.Finite)
    (hx : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄, (.some x y h : W.Point) ∈ A → x ∈ S ∪ S₀)
    (hone : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄, (.some x y h : W.Point) ∈ A → x ∈ S₀ →
      y = W.negY x y) :
    A.ncard ≤ 2 * S.ncard + S₀.ncard + 1 := by
  classical
  set U : Set (F × Bool) := S ×ˢ Set.univ ∪ S₀ ×ˢ {true} with hU
  have hUfin : U.Finite := (hS.prod Set.finite_univ).union (hS₀.prod (Set.finite_singleton _))
  have hsub : W.fibreTag '' A ⊆ insert none (some '' U) := by
    rintro _ ⟨(_ | ⟨x, y, h⟩), hP, rfl⟩
    · exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ⟨(x, decide (y = W.someY x)), ?_, rfl⟩
      rcases hx hP with hxS | hxS₀
      · exact Or.inl ⟨hxS, Set.mem_univ _⟩
      -- Over `S₀` the fibre is a singleton, so the `Bool` tag is forced to `true`.
      · refine Or.inr ⟨hxS₀, ?_⟩
        have hy : y = W.someY x := by
          rcases Y_eq_of_X_eq (W.equation_someY h.left) h.left rfl with h' | h'
          · exact h'.symm
          · rw [h', ← hone hP hxS₀]
        simp [hy]
  calc A.ncard
      = (W.fibreTag '' A).ncard := (Set.ncard_image_of_injective A W.fibreTag_injective).symm
    _ ≤ (insert none (some '' U)).ncard :=
        Set.ncard_le_ncard hsub ((hUfin.image some).insert none)
    _ ≤ (some '' U).ncard + 1 := Set.ncard_insert_le _ _
    _ = U.ncard + 1 := by rw [Set.ncard_image_of_injective _ (Option.some_injective _)]
    _ ≤ 2 * S.ncard + S₀.ncard + 1 := by
        have h := Set.ncard_union_le (S ×ˢ (Set.univ : Set Bool)) (S₀ ×ˢ ({true} : Set Bool))
        rw [Set.ncard_prod, Set.ncard_prod] at h
        simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool,
          Set.ncard_singleton, mul_one] at h
        rw [hU]
        omega

variable [DecidableEq F]

/-- Specialisation of `finite_of_xCoords` to the `n`-torsion subgroup `E[n]`: if every nonzero
`n`-torsion point has `x`-coordinate in a finite set `S`, then `E[n]` is finite (as a set of
points). This is the exact interface the `#E[n] ≤ n²` counting (#252) consumes; #251 provides the
finite root set of `W.ΨSq n` as `S` and is closed (`EllipticCurves.Torsion.XSupport`). -/
theorem torsion_finite_of_xCoords {n : ℕ} {S : Set F} (hS : S.Finite)
    (hx : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄,
      (.some x y h : W.Point) ∈ W.torsion n → x ∈ S) :
    (W.torsion n : Set W.Point).Finite :=
  W.finite_of_xCoords hS hx

/-- The subtype form of `torsion_finite_of_xCoords`: `E[n]` is a `Finite` type once its nonzero
points have `x`-coordinates in a finite set. -/
theorem finite_torsion_of_xCoords {n : ℕ} {S : Set F} (hS : S.Finite)
    (hx : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄,
      (.some x y h : W.Point) ∈ W.torsion n → x ∈ S) :
    Finite (W.torsion n) :=
  Set.finite_coe_iff.mpr (W.torsion_finite_of_xCoords hS hx)

/-- Specialisation of `ncard_le_of_xCoords` to the `n`-torsion subgroup `E[n]`: if every nonzero
`n`-torsion point has `x`-coordinate in a finite set `S`, then `#E[n] ≤ 2 * S.ncard + 1`. -/
theorem card_torsion_le_of_xCoords {n : ℕ} {S : Set F} (hS : S.Finite)
    (hx : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄,
      (.some x y h : W.Point) ∈ W.torsion n → x ∈ S) :
    Nat.card (W.torsion n) ≤ 2 * S.ncard + 1 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  exact W.ncard_le_of_xCoords hS hx

/-- Specialisation of `ncard_le_of_xCoords_of_selfNeg` to `E[n]`: the `x`-support is split into a
part `S` counted with two points per fibre and a part `S₀` of `x`-coordinates of `2`-torsion points,
each of which carries a single point.  This is the shape in which the **sharp** `#E[n] ≤ n²` is
proved at an even index (`EllipticCurves.Torsion.XSupport`). -/
theorem card_torsion_le_of_xCoords_of_selfNeg {n : ℕ} {S S₀ : Set F} (hS : S.Finite)
    (hS₀ : S₀.Finite)
    (hx : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄,
      (.some x y h : W.Point) ∈ W.torsion n → x ∈ S ∪ S₀)
    (hone : ∀ ⦃x y : F⦄ ⦃h : W.Nonsingular x y⦄,
      (.some x y h : W.Point) ∈ W.torsion n → x ∈ S₀ → y = W.negY x y) :
    Nat.card (W.torsion n) ≤ 2 * S.ncard + S₀.ncard + 1 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  exact W.ncard_le_of_xCoords_of_selfNeg hS hS₀ hx hone

end WeierstrassCurve.Affine
