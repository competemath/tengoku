/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Continuity
import Tengoku.LanaOka.Oka.Analysis.Complex.KummerCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite coverings of a product with an annulus

Let `B` be a convex open subset of a real normed space `E` and `0 ≤ r < R`. The finite coverings
of `B × {r < ‖w‖ < R}` are the finite disjoint unions of the Kummer coverings
`B × {r < ‖u‖ᵏ < R} → B × {r < ‖w‖ < R}, (b, u) ↦ (b, uᵏ)`
(`IsCoveringMap.exists_homeomorph_sigma_kummerAnnulus`).

This is reduced to the case of the punctured disc (`IsCoveringMap.exists_homeomorph_sigma_kummer`)
by the radial homeomorphisms `KummerAnnulus.toDisc k : B × {r < ‖u‖ᵏ < R} ≃ₜ B × Δ*`, which
multiply `u` by a positive real number and conjugate the Kummer covering of degree `k` of the
annulus to the Kummer covering of degree `k` of the punctured disc (`KummerAnnulus.toDisc_cover`).

## Main definitions

- `KummerAnnulus.annulus r R k`: the annulus `{r < ‖u‖ᵏ < R}`.
- `KummerAnnulus.base B r R k`: the set `B × {r < ‖u‖ᵏ < R}` inside `E × ℂ`.
- `KummerAnnulus.cover B r R k`: the Kummer covering `(b, u) ↦ (b, uᵏ)` of `B × {r < ‖w‖ < R}`.
- `KummerAnnulus.toDisc B k`: the radial homeomorphism `B × {r < ‖u‖ᵏ < R} ≃ₜ B × Δ*`.

## Main results

- `KummerAnnulus.toDisc_cover`: the radial homeomorphisms conjugate the Kummer coverings.
- `IsCoveringMap.exists_homeomorph_sigma_kummerAnnulus`: a covering of `B × {r < ‖w‖ < R}` with
  finite fibres is isomorphic to a finite disjoint union of Kummer coverings.
-/

open Set Topology

namespace KummerAnnulus

noncomputable section

variable {E : Type*} (B : Set E) (r R : ℝ)

/-- The annulus `{r < ‖u‖ᵏ < R}`, the source of the Kummer covering of degree `k` of the annulus
`{r < ‖w‖ < R}`. -/
def annulus (k : ℕ) : Set ℂ := {u | r < ‖u‖ ^ k ∧ ‖u‖ ^ k < R}

/-- The product `B × {r < ‖u‖ᵏ < R}`, as a subset of `E × ℂ`. -/
def base (k : ℕ) : Set (E × ℂ) := B ×ˢ annulus r R k

variable {B r R} in
lemma mem_base {k : ℕ} {x : E × ℂ} :
    x ∈ base B r R k ↔ x.1 ∈ B ∧ r < ‖x.2‖ ^ k ∧ ‖x.2‖ ^ k < R :=
  Iff.rfl

lemma isOpen_base [TopologicalSpace E] {B : Set E} (hB : IsOpen B) (k : ℕ) :
    IsOpen (base B r R k) :=
  hB.prod ((isOpen_lt continuous_const (continuous_norm.pow k)).inter
    (isOpen_lt (continuous_norm.pow k) continuous_const))

variable {r R} in
lemma pos_of_mem_base (hr : 0 ≤ r) {k : ℕ} (hk : k ≠ 0) {x : E × ℂ}
    (hx : x ∈ base B r R k) : 0 < ‖x.2‖ := by
  rcases (norm_nonneg x.2).lt_or_eq with h | h
  · exact h
  · have := hx.2.1
    rw [← h, zero_pow hk] at this
    linarith

/-- The **Kummer covering** `(b, u) ↦ (b, uᵏ)` of `B × {r < ‖w‖ < R}`. -/
def cover (k : ℕ+) (y : base B r R k) : base B r R 1 :=
  ⟨(y.1.1, y.1.2 ^ (k : ℕ)), y.2.1, by simpa [annulus, norm_pow] using y.2.2⟩

@[simp]
lemma cover_apply (k : ℕ+) (y : base B r R k) :
    (cover B r R k y : E × ℂ) = (y.1.1, y.1.2 ^ (k : ℕ)) :=
  rfl

/-! ### The radial homeomorphism with `B × Δ*` -/

/-- The radius `((sᵏ - r) / (R - r))^{1/k}` in `Δ*` corresponding to the radius `s`. -/
def rad (k : ℕ) (s : ℝ) : ℝ := ((s ^ k - r) / (R - r)) ^ ((k : ℝ)⁻¹)

/-- The radius `(r + (R - r) tᵏ)^{1/k}` corresponding to the radius `t` in `Δ*`. -/
def irad (k : ℕ) (t : ℝ) : ℝ := (r + (R - r) * t ^ k) ^ ((k : ℝ)⁻¹)

variable {r R}

lemma rad_pow {k : ℕ} (hk : k ≠ 0) {s : ℝ} (hs : r ≤ s ^ k) (hrR : r < R) :
    rad r R k s ^ k = (s ^ k - r) / (R - r) :=
  Real.rpow_inv_natCast_pow (div_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 hrR.le)) hk

lemma irad_pow {k : ℕ} (hk : k ≠ 0) (hr : 0 ≤ r) (hrR : r < R) {t : ℝ} (ht : 0 ≤ t) :
    irad r R k t ^ k = r + (R - r) * t ^ k :=
  Real.rpow_inv_natCast_pow (by have := sub_nonneg.2 hrR.le; positivity) hk

lemma rad_pos {k : ℕ} {s : ℝ} (hs : r < s ^ k) (hrR : r < R) : 0 < rad r R k s :=
  Real.rpow_pos_of_pos (div_pos (sub_pos.2 hs) (sub_pos.2 hrR)) _

lemma irad_pos {k : ℕ} (hr : 0 ≤ r) (hrR : r < R) {t : ℝ} (ht : 0 < t) :
    0 < irad r R k t := by
  refine Real.rpow_pos_of_pos ?_ _
  rcases hr.lt_or_eq with hr | rfl
  · have := sub_pos.2 hrR
    positivity
  · have := hrR
    rw [sub_zero, zero_add]
    positivity

lemma irad_rad {k : ℕ} (hk : k ≠ 0) (hrR : r < R) {s : ℝ} (hs0 : 0 ≤ s) (hs : r ≤ s ^ k) :
    irad r R k (rad r R k s) = s := by
  rw [irad, rad_pow hk hs hrR, mul_div_cancel₀ _ (sub_pos.2 hrR).ne', add_sub_cancel,
    Real.pow_rpow_inv_natCast hs0 hk]

lemma rad_irad {k : ℕ} (hk : k ≠ 0) (hr : 0 ≤ r) (hrR : r < R) {t : ℝ} (ht : 0 ≤ t) :
    rad r R k (irad r R k t) = t := by
  rw [rad, irad_pow hk hr hrR ht, add_sub_cancel_left, mul_div_cancel_left₀ _ (sub_pos.2 hrR).ne',
    Real.pow_rpow_inv_natCast ht hk]

/-- The radial map `B × {r < ‖u‖ᵏ < R} → B × Δ*`. -/
def toDiscFun (hr : 0 ≤ r) (hrR : r < R) (k : ℕ+) (y : base B r R k) : Kummer.base B :=
  ⟨(y.1.1, ((rad r R k ‖y.1.2‖ / ‖y.1.2‖ : ℝ) : ℂ) * y.1.2), y.2.1, by
    have hs := pos_of_mem_base B hr k.ne_zero y.2
    have hrad := rad_pos y.2.2.1 hrR
    refine ⟨mul_ne_zero (Complex.ofReal_ne_zero.2 (div_pos hrad hs).ne') (norm_pos_iff.1 hs), ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hrad hs).le,
      div_mul_cancel₀ _ hs.ne']
    refine lt_of_pow_lt_pow_left₀ k zero_le_one ?_
    rw [one_pow, rad_pow k.ne_zero y.2.2.1.le hrR, div_lt_one (sub_pos.2 hrR)]
    linarith [y.2.2.2]⟩

/-- The radial map `B × Δ* → B × {r < ‖u‖ᵏ < R}`. -/
def fromDiscFun (hr : 0 ≤ r) (hrR : r < R) (k : ℕ+) (y : Kummer.base B) : base B r R k :=
  ⟨(y.1.1, ((irad r R k ‖y.1.2‖ / ‖y.1.2‖ : ℝ) : ℂ) * y.1.2), y.2.1, by
    have ht := norm_pos_iff.2 y.2.2.1
    have hirad := irad_pos (k := k) hr hrR ht
    simp only [annulus, mem_ofPred_eq]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hirad ht).le,
      div_mul_cancel₀ _ ht.ne', irad_pow k.ne_zero hr hrR ht.le]
    have h1 : 0 < ‖y.1.2‖ ^ (k : ℕ) := pow_pos ht _
    have h2 : ‖y.1.2‖ ^ (k : ℕ) < 1 := pow_lt_one₀ ht.le y.2.2.2 k.ne_zero
    have h3 := sub_pos.2 hrR
    constructor <;> nlinarith⟩

lemma norm_toDiscFun (hr : 0 ≤ r) (hrR : r < R) (k : ℕ+) (y : base B r R k) :
    ‖(toDiscFun B hr hrR k y).1.2‖ = rad r R k ‖y.1.2‖ := by
  have hs := pos_of_mem_base B hr k.ne_zero y.2
  have hrad := rad_pos y.2.2.1 hrR
  change ‖((rad r R k ‖y.1.2‖ / ‖y.1.2‖ : ℝ) : ℂ) * y.1.2‖ = _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hrad hs).le,
    div_mul_cancel₀ _ hs.ne']

lemma norm_fromDiscFun (hr : 0 ≤ r) (hrR : r < R) (k : ℕ+) (y : Kummer.base B) :
    ‖(fromDiscFun B hr hrR k y).1.2‖ = irad r R k ‖y.1.2‖ := by
  have ht := norm_pos_iff.2 y.2.2.1
  have hirad := irad_pos (k := k) hr hrR ht
  change ‖((irad r R k ‖y.1.2‖ / ‖y.1.2‖ : ℝ) : ℂ) * y.1.2‖ = _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hirad ht).le,
    div_mul_cancel₀ _ ht.ne']

lemma continuous_rad (k : ℕ) : Continuous (rad r R k) :=
  (Real.continuous_rpow_const (inv_nonneg.2 k.cast_nonneg)).comp (by fun_prop)

lemma continuous_irad (k : ℕ) : Continuous (irad r R k) :=
  (Real.continuous_rpow_const (inv_nonneg.2 k.cast_nonneg)).comp (by fun_prop)

variable [TopologicalSpace E]

/-- The **radial homeomorphism** `B × {r < ‖u‖ᵏ < R} ≃ₜ B × Δ*`,
`(b, u) ↦ (b, ((‖u‖ᵏ - r) / (R - r))^{1/k} u / ‖u‖)`. -/
def toDisc (hr : 0 ≤ r) (hrR : r < R) (k : ℕ+) : base B r R k ≃ₜ Kummer.base B where
  toFun := toDiscFun B hr hrR k
  invFun := fromDiscFun B hr hrR k
  left_inv y := by
    have hs := pos_of_mem_base B hr k.ne_zero y.2
    have hrad := rad_pos y.2.2.1 hrR
    refine Subtype.ext (Prod.ext rfl ?_)
    change ((irad r R k ‖(toDiscFun B hr hrR k y).1.2‖ / ‖(toDiscFun B hr hrR k y).1.2‖ : ℝ) :
      ℂ) * (((rad r R k ‖y.1.2‖ / ‖y.1.2‖ : ℝ) : ℂ) * y.1.2) = y.1.2
    rw [norm_toDiscFun, irad_rad k.ne_zero hrR hs.le y.2.2.1.le, ← mul_assoc,
      ← Complex.ofReal_mul, div_mul_div_comm, mul_comm ‖y.1.2‖, div_self (by positivity),
      Complex.ofReal_one, one_mul]
  right_inv y := by
    have ht := norm_pos_iff.2 y.2.2.1
    have hirad := irad_pos (k := k) hr hrR ht
    refine Subtype.ext (Prod.ext rfl ?_)
    change ((rad r R k ‖(fromDiscFun B hr hrR k y).1.2‖ / ‖(fromDiscFun B hr hrR k y).1.2‖ : ℝ) :
      ℂ) * (((irad r R k ‖y.1.2‖ / ‖y.1.2‖ : ℝ) : ℂ) * y.1.2) = y.1.2
    rw [norm_fromDiscFun, rad_irad k.ne_zero hr hrR ht.le, ← mul_assoc,
      ← Complex.ofReal_mul, div_mul_div_comm, mul_comm ‖y.1.2‖, div_self (by positivity),
      Complex.ofReal_one, one_mul]
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk (by fun_prop) (Continuous.mul ?_
      (by fun_prop))) _
    refine Complex.continuous_ofReal.comp (Continuous.div ?_ (by fun_prop)
      fun y ↦ (pos_of_mem_base B hr k.ne_zero y.2).ne')
    exact (continuous_rad k).comp (by fun_prop)
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.prodMk (by fun_prop) (Continuous.mul ?_
      (by fun_prop))) _
    refine Complex.continuous_ofReal.comp (Continuous.div ?_ (by fun_prop)
      fun y ↦ (norm_pos_iff.2 y.2.2.1).ne')
    exact (continuous_irad k).comp (by fun_prop)

@[simp]
lemma toDisc_apply (hr : 0 ≤ r) (hrR : r < R) (k : ℕ+) (y : base B r R k) :
    (toDisc B hr hrR k y : E × ℂ) = (y.1.1, ((rad r R k ‖y.1.2‖ / ‖y.1.2‖ : ℝ) : ℂ) * y.1.2) :=
  rfl

/-- **The radial homeomorphisms conjugate the Kummer coverings** of the annulus and of the
punctured disc. -/
theorem toDisc_cover (hr : 0 ≤ r) (hrR : r < R) (k : ℕ+) (y : base B r R k) :
    toDisc B hr hrR 1 (cover B r R k y) = Kummer.cover B k (toDisc B hr hrR k y) := by
  have hs := pos_of_mem_base B hr k.ne_zero y.2
  refine Subtype.ext (Prod.ext rfl ?_)
  change ((rad r R (1 : ℕ+) ‖y.1.2 ^ (k : ℕ)‖ / ‖y.1.2 ^ (k : ℕ)‖ : ℝ) : ℂ) * y.1.2 ^ (k : ℕ) =
    (((rad r R k ‖y.1.2‖ / ‖y.1.2‖ : ℝ) : ℂ) * y.1.2) ^ (k : ℕ)
  have h1 : rad r R ((1 : ℕ+) : ℕ) (‖y.1.2‖ ^ (k : ℕ)) = (‖y.1.2‖ ^ (k : ℕ) - r) / (R - r) := by
    simp [rad]
  rw [mul_pow, ← Complex.ofReal_pow, div_pow, rad_pow k.ne_zero y.2.2.1.le hrR, norm_pow, h1]

end

end KummerAnnulus

open KummerAnnulus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} {r R : ℝ}
  {X : Type*} [TopologicalSpace X] {p : X → base B r R 1}
