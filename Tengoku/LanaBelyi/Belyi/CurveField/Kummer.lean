/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.CurveField.KummerStep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kummer–Fermat coverings of curves

Let `K ⊆ L` be curve fields with `L` finite over `K`, let `φ ∈ K`, `N > 0`, and let
`u, v ∈ L` satisfy `u ^ N = φ`, `v ^ N = 1 - φ` and `L = K(u, v)`. This is the pull-back
along `φ : X → ℙ¹` of the Fermat curve `x ^ N + y ^ N = 1` over `ℙ¹` (the coordinate being
`x ^ N`).

The *cusps* of `φ` are the places `P` of `K` with `ord_P φ ≠ 0` or `ord_P (φ - 1) > 0`
(`Belyi.CurveField.Place.IsCuspOf`), i.e. the points over `0, 1, ∞`.

## Main results

* `Belyi.CurveField.Place.le_ramificationIdx_mul_abs_ord`,
  `Belyi.CurveField.Place.le_ramificationIdx_mul_ord_sub_one`: over the cusps, the
  ramification is large: `N ≤ e(Q|P) · |ord_P φ|`, resp. `N ≤ e(Q|P) · ord_P (φ - 1)`.
* `Belyi.CurveField.Place.ramificationIdx_eq_one_of_not_isCuspOf`: off the cusps, `L / K` is
  unramified.
* `Belyi.CurveField.QbarPoint.fieldOf_eq_adjoin_kummer`: off the cusps, the field of
  definition of an algebraic point `y` of `L` is generated over that of `x = y|_K` by the
  values `u(y)` and `v(y)`, which satisfy `u(y) ^ N = φ(x)` and `v(y) ^ N = 1 - φ(x)`
  (`Belyi.CurveField.QbarPoint.eval_u_pow`, `Belyi.CurveField.QbarPoint.eval_v_pow`).

The proofs go through the tower `K ⊆ K(u) ⊆ L` and apply the results of
`Belyi.CurveField.KummerStep` to each simple Kummer step.
-/

open IsLocalRing Module Polynomial
open scoped IntermediateField

namespace Belyi.CurveField

variable {K L : Type*} [Field K] [CharZero K] [IsCurveField K] [Field L] [CharZero L]
  [IsCurveField L] [Algebra K L] [FiniteDimensional K L]

namespace Place

/-- `P` is a cusp of `φ`: a zero or pole of `φ`, or a zero of `φ - 1`. -/
def IsCuspOf (φ : K) (P : Place K) : Prop := P.ord φ ≠ 0 ∨ 0 < P.ord (φ - 1)

/-- Off the cusps, `φ` and `1 - φ` have order `0`.
@isnad1 id=and.1h3v.s6.853870c83a32 from=translated src=- shape=ccf854dc vocab=be1ee12a
-/
theorem ord_eq_zero_of_not_isCuspOf {φ : K} {P : Place K} (h : ¬ P.IsCuspOf φ) :
    P.ord φ = 0 ∧ P.ord (1 - φ) = 0 := by
  simp only [IsCuspOf, not_or, not_not, not_lt] at h
  refine ⟨h.1, ?_⟩
  rw [← neg_sub, ord_neg]
  rcases eq_or_ne (φ - 1) 0 with h0 | h0
  · rw [h0, ord_zero]
  · have hφ : φ ∈ P.1 := by
      rcases eq_or_ne φ 0 with rfl | hφ0
      · exact P.1.zero_mem
      · exact P.mem_of_ord_nonneg h.1.ge
    have := P.ord_nonneg_of_mem (sub_mem hφ P.1.one_mem)
    omega

variable {φ : K} {N : ℕ} {u v : L}

/-- `N · ord_Q u = e(Q|P) · ord_P φ`.
@isnad1 id=eq.1h6v.s7.8400c31ed947 from=translated src=- shape=de1b2f17 vocab=bb27e3c9
-/
theorem mul_ord_eq_of_pow_eq {w : L} {a : K} (hw : w ^ N = algebraMap K L a) (Q : Place L) :
    N * Q.ord w = Q.ramificationIdx K * (Q.restrict K).ord a := by
  rw [← Q.ord_algebraMap_eq_mul, ← hw, ord_pow]

/-- If `w ^ N = a` with `ord_P a = 0`, then `w` is regular with `ord_Q w = 0` at `Q | P`.
@isnad1 id=and.3h6v.s8.df626fa8ba5f from=translated src=- shape=5fd13b55 vocab=1b2c6e69
-/
theorem mem_ord_eq_zero_aux {w : L} {a : K} (hN : 0 < N) (hw : w ^ N = algebraMap K L a)
    (Q : Place L) (ha : (Q.restrict K).ord a = 0) : w ∈ Q.1 ∧ Q.ord w = 0 := by
  refine ⟨(mem_of_pow_eq hN hw Q ha).1, ?_⟩
  have hm := mul_ord_eq_of_pow_eq hw Q
  rw [ha, mul_zero, mul_eq_zero] at hm
  exact hm.resolve_left (by exact_mod_cast hN.ne')

/-- **Ramification over the zeros and poles of `φ`**: `N ≤ e(Q|P) · |ord_P φ|`.
@isnad1 id=le.2h6v.s8.418c82d83718 from=translated src=- shape=5a36580e vocab=73697540
-/
theorem le_ramificationIdx_mul_abs_ord (hu : u ^ N = algebraMap K L φ) (Q : Place L)
    (h : (Q.restrict K).ord φ ≠ 0) :
    (N : ℤ) ≤ Q.ramificationIdx K * |(Q.restrict K).ord φ| := by
  have hm := mul_ord_eq_of_pow_eq hu Q
  have he : (0 : ℤ) < Q.ramificationIdx K := by exact_mod_cast Q.ramificationIdx_pos
  have hu0 : Q.ord u ≠ 0 := by
    intro h0
    rw [h0, mul_zero, eq_comm, mul_eq_zero] at hm
    exact hm.elim he.ne' h
  have h1 : 1 ≤ |Q.ord u| := Int.one_le_abs hu0
  have h2 := congrArg abs hm
  rw [abs_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg N), abs_of_pos he] at h2
  rw [← h2]
  nlinarith [Int.natCast_nonneg N]

/-- **Ramification over the zeros of `φ - 1`**: `N ≤ e(Q|P) · ord_P (φ - 1)`.
@isnad1 id=le.2h6v.s8.95c4ca14f8ea from=translated src=- shape=44757155 vocab=cef1356f
-/
theorem le_ramificationIdx_mul_ord_sub_one (hv : v ^ N = 1 - algebraMap K L φ) (Q : Place L)
    (h : 0 < (Q.restrict K).ord (φ - 1)) :
    (N : ℤ) ≤ Q.ramificationIdx K * (Q.restrict K).ord (φ - 1) := by
  have hv' : v ^ N = algebraMap K L (1 - φ) := by rw [hv, map_sub, map_one]
  have hm := mul_ord_eq_of_pow_eq hv' Q
  rw [← neg_sub, ord_neg] at hm
  have he : (0 : ℤ) < Q.ramificationIdx K := by exact_mod_cast Q.ramificationIdx_pos
  have hpos : 0 < (N : ℤ) * Q.ord v := by rw [hm]; positivity
  have hv0 : 0 < Q.ord v := pos_of_mul_pos_right hpos (Int.natCast_nonneg N)
  rw [← hm]
  nlinarith

section Tower

/-! ### The tower `K ⊆ K(u) ⊆ L` -/

omit [CharZero K] [IsCurveField K] [CharZero L] [IsCurveField L] [FiniteDimensional K L]

/-- The generator `u ∈ K(u)` satisfies `u ^ N = φ`.
@isnad1 id=eq.1h5v.s10.bcea150815dd from=translated src=- shape=758ab5fd vocab=1dac41f8
-/
theorem gen_pow_eq (hu : u ^ N = algebraMap K L φ) :
    (IntermediateField.AdjoinSimple.gen K u) ^ N = algebraMap K K⟮u⟯ φ :=
  (algebraMap K⟮u⟯ L).injective (by
    rw [map_pow, IntermediateField.AdjoinSimple.algebraMap_gen, hu,
      ← IsScalarTower.algebraMap_apply])

/-- `K(u)` is generated over `K` by its generator.
@isnad1 id=eq.0h3v.s11.ef14abfb8602 from=translated src=- shape=2f5541bf vocab=fa7ce4b0
-/
theorem adjoin_adjoinSimple_gen_eq_top (u : L) : K⟮IntermediateField.AdjoinSimple.gen K u⟯ = ⊤ := by
  apply IntermediateField.lift_injective
  rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
  rfl

/-- `v ^ N = 1 - φ` over `K(u)`.
@isnad1 id=eq.1h6v.s10.460830eddcae from=translated src=- shape=ff79c059 vocab=f6fb0640
-/
theorem pow_eq_algebraMap_sub (hv : v ^ N = 1 - algebraMap K L φ) :
    v ^ N = algebraMap K⟮u⟯ L (1 - algebraMap K K⟮u⟯ φ) := by
  rw [hv, map_sub, map_one, ← IsScalarTower.algebraMap_apply]

/-- `L = K(u)(v)`.
@isnad1 id=eq.1h4v.s10.ab7ce954f911 from=translated src=- shape=6f4e7a6c vocab=6dfc0998
-/
theorem adjoin_adjoin_eq_top (hgen : IntermediateField.adjoin K {u, v} = ⊤) :
    (K⟮u⟯)⟮v⟯ = ⊤ := by
  rw [← IntermediateField.restrictScalars_eq_top_iff (K := K),
    IntermediateField.adjoin_simple_adjoin_simple]
  exact hgen

end Tower

/-- Off the cusps, `u` is regular and has order `0` (it is a unit, or zero if `φ = 0`).
@isnad1 id=and.3h6v.s8.db18875ce023 from=translated src=- shape=e6052115 vocab=27a87dfd
-/
theorem mem_and_ord_eq_zero_u (hN : 0 < N) (hu : u ^ N = algebraMap K L φ) (Q : Place L)
    (hQ : ¬ (Q.restrict K).IsCuspOf φ) : u ∈ Q.1 ∧ Q.ord u = 0 :=
  mem_ord_eq_zero_aux hN hu Q (ord_eq_zero_of_not_isCuspOf hQ).1

/-- Off the cusps, `v` is regular and has order `0` (it is a unit, or zero if `φ = 1`).
@isnad1 id=and.3h6v.s8.95779d6896bf from=translated src=- shape=09a01e76 vocab=bb05f0ec
-/
theorem mem_and_ord_eq_zero_v (hN : 0 < N) (hv : v ^ N = 1 - algebraMap K L φ) (Q : Place L)
    (hQ : ¬ (Q.restrict K).IsCuspOf φ) : v ∈ Q.1 ∧ Q.ord v = 0 :=
  mem_ord_eq_zero_aux hN (by rw [hv, map_sub, map_one]) Q (ord_eq_zero_of_not_isCuspOf hQ).2

/-- An intermediate field of a finite extension of curve fields is a curve field.
@isnad1 id=iscurvef.0h3v.s6.2622fdd95fa1 from=translated src=- shape=2e52a75e vocab=245487bd
-/
instance _root_.Belyi.CurveField.isCurveField_intermediateField (E : IntermediateField K L) :
    IsCurveField E :=
  isCurveField_of_finite K E

/-- **Kummer–Fermat coverings are unramified off the cusps.**
@isnad1 id=eq.5h7v.s8.7d243571b262 from=translated src=- shape=9dc19866 vocab=8605215c
-/
theorem ramificationIdx_eq_one_of_not_isCuspOf (hN : 0 < N) (hu : u ^ N = algebraMap K L φ)
    (hv : v ^ N = 1 - algebraMap K L φ) (hgen : IntermediateField.adjoin K {u, v} = ⊤)
    (Q : Place L) (hQ : ¬ (Q.restrict K).IsCuspOf φ) : Q.ramificationIdx K = 1 := by
  obtain ⟨h1, h2⟩ := ord_eq_zero_of_not_isCuspOf hQ
  rw [ramificationIdx_tower (M := K⟮u⟯)]
  have e1 : (Q.restrict K⟮u⟯).ramificationIdx K = 1 :=
    ramificationIdx_eq_one_of_pow_eq hN (gen_pow_eq hu) (adjoin_adjoinSimple_gen_eq_top u) _
      (by rw [restrict_restrict]; exact h1)
  have e2 : Q.ramificationIdx K⟮u⟯ = 1 := by
    refine ramificationIdx_eq_one_of_pow_eq hN (pow_eq_algebraMap_sub hv)
      (adjoin_adjoin_eq_top hgen) Q ?_
    rw [← map_one (algebraMap K K⟮u⟯), ← map_sub, ord_algebraMap_eq_mul, restrict_restrict, h2,
      mul_zero]
  rw [e1, e2]

end Place

/-- If `F₁ = F₀(a)`, then `F₁(b) = F₀(a, b)`.
@isnad1 id=eq.1h6v.s9.cc1694657a11 from=translated src=- shape=2784709b vocab=695aa99b
-/
theorem restrictScalars_adjoin_adjoin_eq {F E : Type*} [Field F]
    [Field E] [Algebra F E] {F₀ F₁ : IntermediateField F E} {a b : E}
    (h : F₁ = (IntermediateField.adjoin F₀ {a}).restrictScalars F) :
    (IntermediateField.adjoin F₁ {b}).restrictScalars F =
      (IntermediateField.adjoin F₀ {a, b}).restrictScalars F := by
  have hmem : ∀ z, z ∈ F₁ ↔ z ∈ IntermediateField.adjoin F₀ {a} := fun z ↦ by
    rw [h, IntermediateField.mem_restrictScalars]
  have h01 : F₀ ≤ F₁ := fun z hz ↦ (hmem z).mpr
    (IntermediateField.algebraMap_mem (IntermediateField.adjoin F₀ {a}) ⟨z, hz⟩)
  have ha : a ∈ F₁ := (hmem a).mpr (IntermediateField.mem_adjoin_simple_self F₀ a)
  have h1 : F₁ ≤ (IntermediateField.adjoin F₀ {a, b}).restrictScalars F := fun z hz ↦
    (IntermediateField.mem_restrictScalars F).mpr (IntermediateField.adjoin.mono _ _ _
      (Set.singleton_subset_iff.mpr (Set.mem_insert a {b})) ((hmem z).mp hz))
  have h2 : F₀ ≤ (IntermediateField.adjoin F₁ {b}).restrictScalars F := fun z hz ↦
    (IntermediateField.mem_restrictScalars F).mpr
      (IntermediateField.algebraMap_mem (IntermediateField.adjoin F₁ {b}) ⟨z, h01 hz⟩)
  refine le_antisymm (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · have hle : IntermediateField.adjoin F₁ {b} ≤ IntermediateField.extendScalars h1 := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      change b ∈ (IntermediateField.adjoin F₀ {a, b}).restrictScalars F
      exact (IntermediateField.mem_restrictScalars F).mpr
        (IntermediateField.subset_adjoin F₀ _ (Set.mem_insert_of_mem a (Set.mem_singleton b)))
    exact hle hz
  · have hle : IntermediateField.adjoin F₀ {a, b} ≤ IntermediateField.extendScalars h2 := by
      rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
      constructor
      · change a ∈ (IntermediateField.adjoin F₁ {b}).restrictScalars F
        exact (IntermediateField.mem_restrictScalars F).mpr
          (IntermediateField.algebraMap_mem (IntermediateField.adjoin F₁ {b}) ⟨a, ha⟩)
      · change b ∈ (IntermediateField.adjoin F₁ {b}).restrictScalars F
        exact (IntermediateField.mem_restrictScalars F).mpr
          (IntermediateField.mem_adjoin_simple_self F₁ b)
    exact hle hz

namespace QbarPoint

variable {φ : K} {N : ℕ} {u v : L}

/-- Off the cusps, `u` is regular at `y`.
@isnad1 id=mem.3h6v.s8.8f1cab873d26 from=translated src=- shape=b43aa96c vocab=41dbd32e
-/
theorem mem_u (hN : 0 < N) (hu : u ^ N = algebraMap K L φ) (y : QbarPoint L)
    (hy : ¬ (y.restrict K).P.IsCuspOf φ) : u ∈ y.P.1 :=
  (Place.mem_and_ord_eq_zero_u hN hu y.P hy).1

/-- Off the cusps, `v` is regular at `y`.
@isnad1 id=mem.3h6v.s8.fb08464bf014 from=translated src=- shape=3949e60d vocab=22d16118
-/
theorem mem_v (hN : 0 < N) (hv : v ^ N = 1 - algebraMap K L φ) (y : QbarPoint L)
    (hy : ¬ (y.restrict K).P.IsCuspOf φ) : v ∈ y.P.1 :=
  (Place.mem_and_ord_eq_zero_v hN hv y.P hy).1

/-- Off the cusps, `φ` is regular at `x`.
@isnad1 id=mem.1h3v.s6.a2d75995691b from=translated src=- shape=fa8cf385 vocab=d5581d58
-/
theorem mem_φ (y : QbarPoint K) (hy : ¬ y.P.IsCuspOf φ) : φ ∈ y.P.1 := by
  rcases eq_or_ne φ 0 with rfl | h0
  · exact y.P.1.zero_mem
  · exact y.P.mem_of_ord_nonneg (Place.ord_eq_zero_of_not_isCuspOf hy).1.ge

/-- `u(y) ^ N = φ(y|_K)`.
@isnad1 id=eq.3h6v.s8.682bce6af080 from=translated src=- shape=bca29cee vocab=85902577
-/
theorem eval_u_pow (hN : 0 < N) (hu : u ^ N = algebraMap K L φ) (y : QbarPoint L)
    (hy : ¬ (y.restrict K).P.IsCuspOf φ) :
    y.eval u (mem_u hN hu y hy) ^ N = (y.restrict K).eval φ (mem_φ _ hy) := by
  rw [← y.eval_pow, y.eval_congr hu, eval_restrict]

/-- `v(y) ^ N = 1 - φ(y|_K)`.
@isnad1 id=eq.3h6v.s8.2a2a79ced490 from=translated src=- shape=31d59669 vocab=1f6ca38d
-/
theorem eval_v_pow (hN : 0 < N) (hv : v ^ N = 1 - algebraMap K L φ) (y : QbarPoint L)
    (hy : ¬ (y.restrict K).P.IsCuspOf φ) :
    y.eval v (mem_v hN hv y hy) ^ N = 1 - (y.restrict K).eval φ (mem_φ _ hy) := by
  rw [← y.eval_pow, y.eval_congr hv, y.eval_sub y.P.1.one_mem (mem_φ (y.restrict K) hy), eval_one,
    eval_restrict]

/-- **Lifting points.** Every algebraic point `x` of `K` off the cusps lifts to a point `y` of
`L` (of degree at most `[L : K] · deg x`), and `u(y) ^ N = φ(x)`, `v(y) ^ N = 1 - φ(x)`.
@isnad1 id=ex.4h7v.s9.567d9d690d34 from=translated src=- shape=23e6ad81 vocab=59cff16a
-/
theorem exists_restrict_eq_kummer (hN : 0 < N) (hu : u ^ N = algebraMap K L φ)
    (hv : v ^ N = 1 - algebraMap K L φ) (x : QbarPoint K) (hx : ¬ x.P.IsCuspOf φ) :
    ∃ (y : QbarPoint L) (hy : y.restrict K = x), y.deg ≤ finrank K L * x.deg ∧
      y.eval u (mem_u hN hu y (hy ▸ hx)) ^ N = x.eval φ (mem_φ x hx) ∧
      y.eval v (mem_v hN hv y (hy ▸ hx)) ^ N = 1 - x.eval φ (mem_φ x hx) := by
  obtain ⟨y, rfl, hdeg⟩ := exists_restrict_eq (L := L) x
  exact ⟨y, rfl, hdeg, eval_u_pow hN hu y hx, eval_v_pow hN hv y hx⟩

end QbarPoint

namespace Place

variable {φ : K} {N : ℕ} {u v : L}

end Place

end Belyi.CurveField
