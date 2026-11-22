/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Tengoku.Seed.RingTheory.Ideal.Quotient.Basic
import Tengoku.LanaTateCurvesTheta.TateCurvesTheta.TateCurve.Discriminant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Split multiplicative reduction of the Tate curve

The Tate curve `E_q : y² + xy = x³ + a₄x + a₆` has integral coefficients
(`‖a₄‖, ‖a₆‖ ≤ ‖q‖ < 1`), so it defines a Weierstrass model `tateCurveInt` over the ring
of integers `𝒪 = {x : K | ‖x‖ ≤ 1}` of the ultrametric field `K`. Reducing modulo the
maximal ideal `𝔪 = {x | ‖x‖ < 1}` kills `a₄` and `a₆`, and the special fibre is the
standard **nodal cubic** `y² + xy = x³`: singular at the origin with tangent-cone
quadratic `T² + T = T(T + 1)` — two *distinct rational* tangent directions. This is
**split multiplicative reduction**, over an arbitrary residue field: the tangent
directions `0` and `-1` are always rational and always distinct.

This realizes the reduction-theoretic half of the characterization of the Tate parameter
(issue #37): `E_q` is the split multiplicative curve with parameter `q`; conversely the
`j`-invariant bijection (`QParameter/JParametrization.lean`) recovers `q` from any
prescribed non-integral `j`.

## Main definitions

* `TateCurvesTheta.integerRing K`: the closed unit ball as a subring of `K`.
* `TateCurvesTheta.integerIdeal K`: the open unit ball as a (maximal) ideal of it.
* `TateCurvesTheta.WeierstrassCurve.HasSplitNodeAtOrigin`,
  `TateCurvesTheta.WeierstrassCurve.IsSplitMultiplicative`: split multiplicative
  reduction for a Weierstrass curve in nodal-normalized position.
* `TateCurvesTheta.TateParameter.tateCurveInt`: the integral model of `E_q`.

## Main results

* `TateParameter.tateCurveInt_map_subtype`: the integral model recovers `E_q` over `K`.
* `TateParameter.tateCurveInt_reduction`: the special fibre is the nodal cubic
  `y² + xy = x³`.
* `TateParameter.isSplitMultiplicative_reduction`: **the Tate curve has split
  multiplicative reduction** — the special fibre is nodal (`Δ̄ = 0`, `c₄̄ = 1 ≠ 0`) with
  split tangent cone `T(T + 1)`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, §3, §5.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Ch. VII, §5.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- **The ring of integers** of an ultrametric normed field: the closed unit ball
`{x : K | ‖x‖ ≤ 1}`, a subring by the ultrametric inequality. -/
def integerRing : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' ha hb := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' ha := by simpa using ha
  mul_mem' ha hb := by
    rw [Set.mem_ofPred_eq, norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb

/--
@isnad1 id=iff.0h2v.s6.2b369601b996 from=translated src=- shape=f5463152 vocab=efd49e9d
-/
@[simp] lemma mem_integerRing_iff {x : K} : x ∈ integerRing K ↔ ‖x‖ ≤ 1 := Iff.rfl

/-- **The maximal ideal** of the ring of integers: the open unit ball `{x | ‖x‖ < 1}`. -/
def integerIdeal : Ideal (integerRing K) where
  carrier := {x | ‖(x : K)‖ < 1}
  zero_mem' := by simp
  add_mem' ha hb :=
    lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' r x hx := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, norm_mul]
    calc ‖(r : K)‖ * ‖(x : K)‖ ≤ 1 * ‖(x : K)‖ :=
          mul_le_mul_of_nonneg_right r.2 (norm_nonneg _)
      _ = ‖(x : K)‖ := one_mul _
      _ < 1 := hx

/--
@isnad1 id=iff.0h2v.s9.bfff490a87f7 from=translated src=- shape=72af5820 vocab=45ce77cd
-/
@[simp] lemma mem_integerIdeal_iff {x : integerRing K} :
    x ∈ integerIdeal K ↔ ‖(x : K)‖ < 1 := Iff.rfl

/-- Elements of the integer ring of norm one are units.
@isnad1 id=isunit.1h2v.s8.aa0ef0028746 from=translated src=- shape=68633449 vocab=a0f43dc6
-/
lemma isUnit_integerRing_of_norm_eq_one {x : integerRing K} (hx : ‖(x : K)‖ = 1) :
    IsUnit x := by
  have hx0 : (x : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact zero_ne_one hx
  have hmem : (x : K)⁻¹ ∈ integerRing K := by
    rw [mem_integerRing_iff, norm_inv, hx, inv_one]
  refine ⟨⟨x, ⟨(x : K)⁻¹, hmem⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

/-- The open unit ball is a **maximal ideal** of the integer ring: any strictly larger
ideal contains a norm-one element, hence a unit.
@isnad1 id=ismaxima.0h1v.s7.165d5300ee3c from=translated src=- shape=24bbaeff vocab=b72b87c8
-/
instance integerIdeal_isMaximal : (integerIdeal K).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · rw [mem_integerIdeal_iff]
    simp
  · intro J x hIJ hxI hxJ
    have hx1 : ‖(x : K)‖ = 1 := le_antisymm x.2 (by
      by_contra h
      rw [not_le] at h
      exact hxI ((mem_integerIdeal_iff K).mpr h))
    obtain ⟨u, hu⟩ := isUnit_integerRing_of_norm_eq_one K hx1
    have h1 : (1 : integerRing K) = (u⁻¹ : (integerRing K)ˣ) * x := by
      rw [← hu, Units.inv_mul]
    rw [h1]
    exact J.mul_mem_left _ hxJ

end TateCurvesTheta

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- A Weierstrass curve in **nodal-normalized position** (`a₃ = a₄ = a₆ = 0`, so the
curve passes through the origin and is singular there) has a **split node** when the
tangent-cone quadratic `T² + a₁T - a₂` splits into two *distinct* linear factors over the
base ring. -/
def HasSplitNodeAtOrigin (W : WeierstrassCurve R) : Prop :=
  W.a₃ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0 ∧
    ∃ α β : R, α ≠ β ∧
      Polynomial.X ^ 2 + Polynomial.C W.a₁ * Polynomial.X - Polynomial.C W.a₂ =
        (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)

/-- **Split multiplicative reduction data** for a Weierstrass curve (over the residue
field, in nodal-normalized position): the curve is singular (`Δ = 0`) of multiplicative
type (`c₄ ≠ 0`), with split tangent directions at the node. -/
structure IsSplitMultiplicative (W : WeierstrassCurve R) : Prop where
  Δ_eq_zero : W.Δ = 0
  c₄_ne_zero : W.c₄ ≠ 0
  hasSplitNodeAtOrigin : W.HasSplitNodeAtOrigin

/-- **The nodal cubic** `y² + xy = x³`, the special fibre of every Tate curve. -/
def nodalCubic : WeierstrassCurve R := ⟨1, 0, 0, 0, 0⟩

/--
@isnad1 id=eq.0h1v.s4.a56581e2bdc0 from=translated src=- shape=5f1ef773 vocab=e548780e
-/
@[simp] lemma nodalCubic_a₁ : (nodalCubic : WeierstrassCurve R).a₁ = 1 := rfl
/--
@isnad1 id=eq.0h1v.s4.67cc216cd0fb from=translated src=- shape=5f1ef773 vocab=5df939d9
-/
@[simp] lemma nodalCubic_a₂ : (nodalCubic : WeierstrassCurve R).a₂ = 0 := rfl

/-- The nodal cubic is singular: `Δ = 0`.
@isnad1 id=eq.0h1v.s4.ebaeedbca659 from=translated src=- shape=5f1ef773 vocab=f187bd6a
-/
lemma nodalCubic_Δ : (nodalCubic : WeierstrassCurve R).Δ = 0 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, nodalCubic]
  ring

/-- The nodal cubic has `c₄ = 1`.
@isnad1 id=eq.0h1v.s4.f6d9696b709d from=translated src=- shape=5f1ef773 vocab=fb6630ad
-/
lemma nodalCubic_c₄ : (nodalCubic : WeierstrassCurve R).c₄ = 1 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, nodalCubic]
  ring

/-- **The nodal cubic has a split node**: its tangent-cone quadratic is
`T² + T = T(T + 1)`, with the two distinct rational tangent directions `0` and `-1`.
@isnad1 id=hassplit.0h1v.s3.19cc3e057ab1 from=translated src=- shape=4c9b52a8 vocab=569873c1
-/
lemma nodalCubic_hasSplitNodeAtOrigin [Nontrivial R] :
    (nodalCubic : WeierstrassCurve R).HasSplitNodeAtOrigin := by
  refine ⟨rfl, rfl, rfl, 0, -1, ?_, ?_⟩
  · intro h
    exact one_ne_zero (neg_eq_zero.mp h.symm)
  · simp only [nodalCubic_a₁, nodalCubic_a₂, map_zero, map_one, map_neg]
    ring

/-- **The nodal cubic has split multiplicative type** over any nontrivial ring.
@isnad1 id=issplitm.0h1v.s3.18108eb8e6d8 from=translated src=- shape=4c9b52a8 vocab=54bceb6c
-/
lemma nodalCubic_isSplitMultiplicative [Nontrivial R] :
    (nodalCubic : WeierstrassCurve R).IsSplitMultiplicative :=
  ⟨nodalCubic_Δ, by rw [nodalCubic_c₄]; exact one_ne_zero,
    nodalCubic_hasSplitNodeAtOrigin⟩

end WeierstrassCurve

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (t : TateParameter K)

/-- **The integral model of the Tate curve**: the Weierstrass model
`y² + xy = x³ + a₄x + a₆` over the ring of integers of `K` (the coefficients satisfy
`‖a₄‖, ‖a₆‖ ≤ ‖q‖ < 1`). -/
def tateCurveInt (h12 : (12 : K) ≠ 0) : _root_.WeierstrassCurve (integerRing K) :=
  ⟨1, 0, 0,
    ⟨t.a₄, le_of_lt (lt_of_le_of_lt t.norm_a₄_le t.norm_lt_one)⟩,
    ⟨t.a₆, le_of_lt (lt_of_le_of_lt (t.norm_a₆_le h12) t.norm_lt_one)⟩⟩

/-- The integral model recovers the Tate curve over `K`.
@isnad1 id=eq.1h2v.s7.4cc1e30c2b8b from=translated src=- shape=ed1b3e82 vocab=41a11c01
-/
lemma tateCurveInt_map_subtype (h12 : (12 : K) ≠ 0) :
    (t.tateCurveInt h12).map (integerRing K).subtype = t.tateCurve := by
  simp only [_root_.WeierstrassCurve.map, tateCurveInt, tateCurve]
  rfl

/-- **The special fibre of the Tate curve is the nodal cubic** `y² + xy = x³`: reduction
modulo the maximal ideal kills `a₄` and `a₆`.
@isnad1 id=eq.1h2v.s9.6f6e3b506b45 from=translated src=- shape=cd682a77 vocab=1fd25bfe
-/
theorem tateCurveInt_reduction (h12 : (12 : K) ≠ 0) :
    (t.tateCurveInt h12).map (Ideal.Quotient.mk (integerIdeal K)) =
      WeierstrassCurve.nodalCubic := by
  have ha₄ : Ideal.Quotient.mk (integerIdeal K)
      ⟨t.a₄, le_of_lt (lt_of_le_of_lt t.norm_a₄_le t.norm_lt_one)⟩ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (lt_of_le_of_lt t.norm_a₄_le t.norm_lt_one)
  have ha₆ : Ideal.Quotient.mk (integerIdeal K)
      ⟨t.a₆, le_of_lt (lt_of_le_of_lt (t.norm_a₆_le h12) t.norm_lt_one)⟩ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (lt_of_le_of_lt (t.norm_a₆_le h12) t.norm_lt_one)
  simp only [_root_.WeierstrassCurve.map, tateCurveInt, WeierstrassCurve.nodalCubic,
    map_one, map_zero, ha₄, ha₆]

/-- **The Tate curve has split multiplicative reduction**: its special fibre is the nodal
cubic, which is singular (`Δ̄ = 0`) of multiplicative type (`c₄̄ = 1 ≠ 0`) with the two
distinct rational tangent directions `T` and `T + 1` at the node — over an arbitrary
residue field.
@isnad1 id=issplitm.1h2v.s9.6802ace4ad00 from=translated src=- shape=8f1078da vocab=6fa7a2fc
-/
theorem isSplitMultiplicative_reduction (h12 : (12 : K) ≠ 0) :
    ((t.tateCurveInt h12).map
        (Ideal.Quotient.mk (integerIdeal K))).IsSplitMultiplicative := by
  rw [t.tateCurveInt_reduction h12]
  exact WeierstrassCurve.nodalCubic_isSplitMultiplicative

end TateParameter

end TateCurvesTheta
