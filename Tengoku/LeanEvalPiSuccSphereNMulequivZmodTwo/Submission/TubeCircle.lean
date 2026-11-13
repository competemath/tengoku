import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The standard twist-`k` framed circle and its tube

In `E := ℝ^{m+3}` (Euclidean) we study the unit circle
`circleAt θ = (cos θ, sin θ, 0, …, 0)` in the `(x₀, x₁)`-plane, together with the
twist-`k` orthonormal normal frame (`nuVec k θ`, indexed by `Fin (m+2)`):

* `nuVec k θ 0    = cos (kθ) • r̂(θ) + sin (kθ) • e_last`,
* `nuVec k θ i    = e_{i+1}` for middle indices `i` (constants),
* `nuVec k θ last = -sin (kθ) • r̂(θ) + cos (kθ) • e_last`,

where `r̂(θ) = circleAt θ` is the radial direction and `e_last` the last coordinate
vector.  The tube map is

* `tubeMap k θ w := circleAt θ + ∑ i, w i • nuVec k θ i`.

Main results:

* coordinate formulas `tubeMap_apply_zero/one/last/mid` in terms of the radial
  coefficient `tubeA` and vertical coefficient `tubeB`;
* the explicit smooth inverse data `wCoord k : E → ℝ^{m+2}` (defined via the
  Chebyshev pair `rotP` — no branch cuts, everything `2π`-periodic), with the round
  trips `wCoord_tubeMap` and `tubeMap_wCoord`;
* **injectivity** `tubeMap_inj` on `‖w‖ < 1/2`: the angle is recovered up to `2πℤ`
  and the normal coordinates on the nose;
* the distance-from-circle function `tubeDistSq` with
  `norm_wCoord_sq : ‖wCoord k v‖² = tubeDistSq v` and
  `norm_tubeMap_sub_circleAt : ‖tubeMap k θ w - circleAt θ‖² = ‖w‖²`;
* smoothness: `contDiff_tubeMap` (jointly in `(θ, w)`) and
  `contDiffOn_wCoord` on the open set `tubeGood = {0 < x₀² + x₁²}`;
* orthonormality of the frame (`inner_nuVec_nuVec`) and orthogonality to the
  tangent (`inner_nuVec_tangentAt`).
-/

noncomputable section

namespace Submission

open scoped RealInnerProductSpace ContDiff
open Real

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (m + 3))
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))

/-! ## Small helpers -/

lemma normSq_eq_sum_sq {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

lemma abs_coordinate_le_norm {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι)
    (i : ι) : |x i| ≤ ‖x‖ := by
  have h1 : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [normSq_eq_sum_sq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  calc |x i| = Real.sqrt ((x i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg x)

lemma inner_eq_sum (x y : E) : ⟪x, y⟫ = ∑ j, x j * y j := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => by
    simp [RCLike.inner_apply, mul_comm]

/-- A sum over `Fin (m+3)` supported on the first two indices.-/
lemma sum_split_pair01 (f : Fin (m + 3) → ℝ) (a b : ℝ)
    (h0 : f 0 = a) (h1 : f 1 = b)
    (hrest : ∀ j : Fin (m + 3), j ≠ 0 → j ≠ 1 → f j = 0) :
    ∑ j, f j = a + b := by
  have key : ∀ j, f j
      = (if j = 0 then a else 0) + (if j = 1 then b else 0) := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0
      rw [ite_eq_left rfl, ite_eq_right (Fin.zero_ne_one (n := m + 1)), add_zero, h0]
    · by_cases hj1 : j = 1
      · subst hj1
        rw [ite_eq_right (Fin.zero_ne_one (n := m + 1)).symm, ite_eq_left rfl, zero_add, h1]
      · rw [ite_eq_right hj0, ite_eq_right hj1, add_zero, hrest j hj0 hj1]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ (0 : Fin (m + 3)) (fun _ => a),
    Finset.sum_ite_eq' _ (1 : Fin (m + 3)) (fun _ => b),
    ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _)]

/-! Index bookkeeping. -/

lemma lastA_ne_zero : (Fin.last (m + 2) : Fin (m + 3)) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_last, Fin.val_zero] at h'
  omega

lemma lastA_ne_one : (Fin.last (m + 2) : Fin (m + 3)) ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_last, Fin.val_one] at h'
  omega

lemma lastW_ne_zero : (Fin.last (m + 1) : Fin (m + 2)) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_last, Fin.val_zero] at h'
  omega

/-! ## The Chebyshev rotation pair

`rotP k (c, s)` is the pair `(Re, Im)` of `(c + i s)^k`; on the unit circle it
computes `(cos kθ, sin kθ)` from `(cos θ, sin θ)` polynomially — this is how all
`kθ`-quantities stay smooth in the ambient point without choosing a branch of the
angle. -/

/-- The Chebyshev pair: `rotP k (c, s)` = real and imaginary part of `(c + is)^k`.-/
def rotP : ℕ → ℝ × ℝ → ℝ × ℝ
  | 0, _ => (1, 0)
  | k + 1, p =>
      (p.1 * (rotP k p).1 - p.2 * (rotP k p).2,
       p.2 * (rotP k p).1 + p.1 * (rotP k p).2)

@[simp] lemma rotP_zero (p : ℝ × ℝ) : rotP 0 p = (1, 0) := rfl

lemma rotP_succ (k : ℕ) (p : ℝ × ℝ) :
    rotP (k + 1) p
      = (p.1 * (rotP k p).1 - p.2 * (rotP k p).2,
         p.2 * (rotP k p).1 + p.1 * (rotP k p).2) := rfl

/-- On the unit circle the Chebyshev pair computes `(cos kθ, sin kθ)`.-/
lemma rotP_cos_sin (k : ℕ) (θ : ℝ) :
    rotP k (Real.cos θ, Real.sin θ) = (Real.cos (k * θ), Real.sin (k * θ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have harg : ((k : ℝ) + 1) * θ = θ + k * θ := by ring
    rw [rotP_succ, ih]
    push_cast
    rw [harg, Real.cos_add, Real.sin_add]

/-- The Chebyshev pair preserves the squared norm (raised to the `k`-th power).-/
lemma rotP_sq_add_sq (k : ℕ) (p : ℝ × ℝ) :
    (rotP k p).1 ^ 2 + (rotP k p).2 ^ 2 = (p.1 ^ 2 + p.2 ^ 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [rotP_succ]
    show (p.1 * (rotP k p).1 - p.2 * (rotP k p).2) ^ 2
        + (p.2 * (rotP k p).1 + p.1 * (rotP k p).2) ^ 2 = _
    rw [pow_succ (p.1 ^ 2 + p.2 ^ 2) k]
    linear_combination (p.1 ^ 2 + p.2 ^ 2) * ih

lemma contDiff_rotP (k : ℕ) : ContDiff ℝ ∞ (rotP k) := by
  induction k with
  | zero =>
    have h : rotP 0 = fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)) := rfl
    rw [h]
    exact contDiff_const
  | succ k ih =>
    have h1 : ContDiff ℝ ∞ fun p : ℝ × ℝ => (rotP k p).1 := contDiff_fst.comp ih
    have h2 : ContDiff ℝ ∞ fun p : ℝ × ℝ => (rotP k p).2 := contDiff_snd.comp ih
    have h : rotP (k + 1) = fun p : ℝ × ℝ =>
        (p.1 * (rotP k p).1 - p.2 * (rotP k p).2,
         p.2 * (rotP k p).1 + p.1 * (rotP k p).2) := rfl
    rw [h]
    exact ((contDiff_fst.mul h1).sub (contDiff_snd.mul h2)).prodMk
      ((contDiff_snd.mul h1).add (contDiff_fst.mul h2))

/-! ## The circle, the vertical direction, and the frame

All vectors are defined coordinatewise (as `WithLp.toLp` of explicit functions), so
that coordinate evaluation is definitional. -/

/-- The coordinate vector `e_{j₀}` of the ambient space.-/
def coordVec (j₀ : Fin (m + 3)) : E :=
  WithLp.toLp 2 fun j => if j = j₀ then (1 : ℝ) else 0

@[simp] lemma coordVec_apply (j₀ j : Fin (m + 3)) :
    coordVec j₀ j = if j = j₀ then (1 : ℝ) else 0 := rfl

/-- The unit circle in the `(x₀, x₁)`-plane; also the radial direction `r̂(θ)`.-/
def circleAt (θ : ℝ) : E :=
  WithLp.toLp 2 fun j =>
    if j = 0 then Real.cos θ else if j = 1 then Real.sin θ else 0

@[simp] lemma circleAt_apply (θ : ℝ) (j : Fin (m + 3)) :
    circleAt θ j = if j = 0 then Real.cos θ else if j = 1 then Real.sin θ else 0 :=
  rfl

/-- The tangent direction of the circle.-/
def tangentAt (θ : ℝ) : E :=
  WithLp.toLp 2 fun j =>
    if j = 0 then -Real.sin θ else if j = 1 then Real.cos θ else 0

@[simp] lemma tangentAt_apply (θ : ℝ) (j : Fin (m + 3)) :
    tangentAt θ j
      = if j = 0 then -Real.sin θ else if j = 1 then Real.cos θ else 0 := rfl

/-- The last coordinate vector (the direction "vertical to the circle plane" used by
the twisted frame).-/
def eVert : E := coordVec (Fin.last (m + 2))

lemma circleAt_apply_zero (θ : ℝ) : circleAt (m := m) θ 0 = Real.cos θ := by
  rw [circleAt_apply, ite_eq_left rfl]

lemma circleAt_apply_one (θ : ℝ) : circleAt (m := m) θ 1 = Real.sin θ := by
  rw [circleAt_apply, ite_eq_right (Fin.zero_ne_one (n := m + 1)).symm, ite_eq_left rfl]

lemma circleAt_apply_other (θ : ℝ) {j : Fin (m + 3)} (h0 : j ≠ 0) (h1 : j ≠ 1) :
    circleAt (m := m) θ j = 0 := by
  rw [circleAt_apply, ite_eq_right h0, ite_eq_right h1]

lemma eVert_apply_last : eVert (m := m) (Fin.last (m + 2)) = 1 := by
  show (if Fin.last (m + 2) = Fin.last (m + 2) then (1 : ℝ) else 0) = 1
  rw [ite_eq_left rfl]

lemma eVert_apply_ne {j : Fin (m + 3)} (h : j ≠ Fin.last (m + 2)) :
    eVert (m := m) j = 0 := by
  show (if j = Fin.last (m + 2) then (1 : ℝ) else 0) = 0
  rw [ite_eq_right h]

/-- Coordinate of a two-term smul combination (definitional).-/
lemma addSmul_coord (a b : ℝ) (x y : E) (j : Fin (m + 3)) :
    (a • x + b • y) j = a * x j + b * y j := rfl

/-- The twist-`k` normal frame along the circle.-/
def nuVec (k : ℕ) (θ : ℝ) (i : Fin (m + 2)) : E :=
  if i = 0 then Real.cos (k * θ) • circleAt θ + Real.sin (k * θ) • eVert
  else if i = Fin.last (m + 1) then
    (-Real.sin (k * θ)) • circleAt θ + Real.cos (k * θ) • eVert
  else coordVec i.succ

lemma nuVec_zero (k : ℕ) (θ : ℝ) :
    nuVec (m := m) k θ 0
      = Real.cos (k * θ) • circleAt θ + Real.sin (k * θ) • eVert := by
  rw [nuVec, ite_eq_left rfl]

lemma nuVec_last (k : ℕ) (θ : ℝ) :
    nuVec (m := m) k θ (Fin.last (m + 1))
      = (-Real.sin (k * θ)) • circleAt θ + Real.cos (k * θ) • eVert := by
  rw [nuVec, ite_eq_right lastW_ne_zero, ite_eq_left rfl]

lemma nuVec_mid (k : ℕ) (θ : ℝ) {i : Fin (m + 2)} (h0 : i ≠ 0)
    (hl : i ≠ Fin.last (m + 1)) :
    nuVec (m := m) k θ i = coordVec i.succ := by
  rw [nuVec, ite_eq_right h0, ite_eq_right hl]

/-- Middle indices have ambient successor different from `0`, `1` and the last
index.-/
lemma midSucc_ne {i : Fin (m + 2)} (h0 : i ≠ 0) (hl : i ≠ Fin.last (m + 1)) :
    (i.succ : Fin (m + 3)) ≠ 0 ∧ (i.succ : Fin (m + 3)) ≠ 1
      ∧ (i.succ : Fin (m + 3)) ≠ Fin.last (m + 2) := by
  have hv0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hvl : i.val ≠ m + 1 := fun h => hl (Fin.ext h)
  refine ⟨Fin.succ_ne_zero i, ?_, ?_⟩
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_one] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_last] at h'
    omega

/-! ## The tube map and its coordinates -/

/-- The radial coefficient of a tube point.-/
def tubeA (k : ℕ) (θ : ℝ) (w : F) : ℝ :=
  1 + w 0 * Real.cos (k * θ) - w (Fin.last (m + 1)) * Real.sin (k * θ)

/-- The vertical (last) coordinate of a tube point.-/
def tubeB (k : ℕ) (θ : ℝ) (w : F) : ℝ :=
  w 0 * Real.sin (k * θ) + w (Fin.last (m + 1)) * Real.cos (k * θ)

/-- The tube map: the circle point at angle `θ` displaced by `w` in the twist-`k`
frame.-/
def tubeMap (k : ℕ) (θ : ℝ) (w : F) : E :=
  circleAt θ + ∑ i, w i • nuVec k θ i

/-- Coordinate of a finite sum of Euclidean vectors.-/
lemma sum_coord {ι : Type*} [Fintype ι] (g : ι → E) (j : Fin (m + 3)) :
    (∑ i, g i) j = ∑ i, (g i) j :=
  map_sum (EuclideanSpace.proj j) g Finset.univ

/-- Sums over `Fin (m+2)` supported on the first and last index.-/
lemma sum_split_pair (f : Fin (m + 2) → ℝ) (a b : ℝ)
    (h0 : f 0 = a) (hl : f (Fin.last (m + 1)) = b)
    (hmid : ∀ i : Fin (m + 2), i ≠ 0 → i ≠ Fin.last (m + 1) → f i = 0) :
    ∑ i, f i = a + b := by
  have key : ∀ i, f i
      = (if i = 0 then a else 0) + (if i = Fin.last (m + 1) then b else 0) := by
    intro i
    by_cases h1 : i = 0
    · subst h1
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm lastW_ne_zero), add_zero, h0]
    · by_cases h2 : i = Fin.last (m + 1)
      · subst h2
        rw [ite_eq_right lastW_ne_zero, ite_eq_left rfl, zero_add, hl]
      · rw [ite_eq_right h1, ite_eq_right h2, add_zero, hmid i h1 h2]
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ (0 : Fin (m + 2)) (fun _ => a),
    Finset.sum_ite_eq' _ (Fin.last (m + 1)) (fun _ => b),
    ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _)]

lemma tubeMap_coord (k : ℕ) (θ : ℝ) (w : F) (j : Fin (m + 3)) :
    tubeMap k θ w j = circleAt θ j + ∑ i, w i * nuVec k θ i j := by
  have h1 : tubeMap k θ w j = circleAt θ j + (∑ i, w i • nuVec k θ i) j := rfl
  rw [h1, sum_coord]
  rfl

lemma tubeMap_apply_zero (k : ℕ) (θ : ℝ) (w : F) :
    tubeMap k θ w 0 = tubeA k θ w * Real.cos θ := by
  rw [tubeMap_coord, circleAt_apply_zero]
  have hsum : (∑ i, w i * nuVec k θ i 0)
      = w 0 * (Real.cos (k * θ) * Real.cos θ)
        + w (Fin.last (m + 1)) * (-Real.sin (k * θ) * Real.cos θ) := by
    apply sum_split_pair
    · rw [nuVec_zero, addSmul_coord, circleAt_apply_zero,
        eVert_apply_ne (Ne.symm lastA_ne_zero)]
      ring
    · rw [nuVec_last, addSmul_coord, circleAt_apply_zero,
        eVert_apply_ne (Ne.symm lastA_ne_zero)]
      ring
    · intro i h0 hl
      rw [nuVec_mid k θ h0 hl, coordVec_apply,
        ite_eq_right (Ne.symm (midSucc_ne h0 hl).1), mul_zero]
  rw [hsum, tubeA]
  ring

lemma tubeMap_apply_one (k : ℕ) (θ : ℝ) (w : F) :
    tubeMap k θ w 1 = tubeA k θ w * Real.sin θ := by
  rw [tubeMap_coord, circleAt_apply_one]
  have hsum : (∑ i, w i * nuVec k θ i 1)
      = w 0 * (Real.cos (k * θ) * Real.sin θ)
        + w (Fin.last (m + 1)) * (-Real.sin (k * θ) * Real.sin θ) := by
    apply sum_split_pair
    · rw [nuVec_zero, addSmul_coord, circleAt_apply_one,
        eVert_apply_ne (Ne.symm lastA_ne_one)]
      ring
    · rw [nuVec_last, addSmul_coord, circleAt_apply_one,
        eVert_apply_ne (Ne.symm lastA_ne_one)]
      ring
    · intro i h0 hl
      rw [nuVec_mid k θ h0 hl, coordVec_apply,
        ite_eq_right (Ne.symm (midSucc_ne h0 hl).2.1), mul_zero]
  rw [hsum, tubeA]
  ring

lemma tubeMap_apply_last (k : ℕ) (θ : ℝ) (w : F) :
    tubeMap k θ w (Fin.last (m + 2)) = tubeB k θ w := by
  rw [tubeMap_coord, circleAt_apply_other θ lastA_ne_zero lastA_ne_one]
  have hsum : (∑ i, w i * nuVec k θ i (Fin.last (m + 2)))
      = w 0 * Real.sin (k * θ) + w (Fin.last (m + 1)) * Real.cos (k * θ) := by
    apply sum_split_pair
    · rw [nuVec_zero, addSmul_coord,
        circleAt_apply_other θ lastA_ne_zero lastA_ne_one, eVert_apply_last]
      ring
    · rw [nuVec_last, addSmul_coord,
        circleAt_apply_other θ lastA_ne_zero lastA_ne_one, eVert_apply_last]
      ring
    · intro i h0 hl
      rw [nuVec_mid k θ h0 hl, coordVec_apply,
        ite_eq_right (Ne.symm (midSucc_ne h0 hl).2.2), mul_zero]
  rw [hsum, tubeB, zero_add]

lemma tubeMap_apply_mid (k : ℕ) (θ : ℝ) (w : F) {i : Fin (m + 2)}
    (h0 : i ≠ 0) (hl : i ≠ Fin.last (m + 1)) :
    tubeMap k θ w i.succ = w i := by
  obtain ⟨hs0, hs1, hsl⟩ := midSucc_ne h0 hl
  rw [tubeMap_coord, circleAt_apply_other θ hs0 hs1]
  have hzero : ∀ i' ∈ Finset.univ, i' ≠ i
      → w i' * nuVec (m := m) k θ i' (i.succ : Fin (m + 3)) = 0 := by
    intro i' _ hne
    by_cases h'0 : i' = 0
    · subst h'0
      rw [nuVec_zero, addSmul_coord, circleAt_apply_other θ hs0 hs1,
        eVert_apply_ne hsl]
      ring
    · by_cases h'l : i' = Fin.last (m + 1)
      · subst h'l
        rw [nuVec_last, addSmul_coord, circleAt_apply_other θ hs0 hs1,
          eVert_apply_ne hsl]
        ring
      · rw [nuVec_mid k θ h'0 h'l, coordVec_apply, ite_eq_right, mul_zero]
        intro hcontra
        exact hne (Fin.succ_injective _ hcontra.symm)
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hzero, nuVec_mid k θ h0 hl,
    coordVec_apply, ite_eq_left rfl, mul_one, zero_add]

/-! ## The inverse data -/

/-- Squared radius of the projection to the circle plane.-/
def radSq (v : E) : ℝ := v 0 ^ 2 + v 1 ^ 2

/-- Radius of the projection to the circle plane.-/
def rad (v : E) : ℝ := Real.sqrt (radSq v)

/-- Cosine of the angle of the circle-plane projection.-/
def uC (v : E) : ℝ := v 0 / rad v

/-- Sine of the angle of the circle-plane projection.-/
def uS (v : E) : ℝ := v 1 / rad v

/-- `cos (k · angle v)`, computed polynomially (Chebyshev).-/
def cosK (k : ℕ) (v : E) : ℝ := (rotP k (uC v, uS v)).1

/-- `sin (k · angle v)`, computed polynomially (Chebyshev).-/
def sinK (k : ℕ) (v : E) : ℝ := (rotP k (uC v, uS v)).2

/-- The open region where the tube coordinates are defined (and smooth).-/
def tubeGood : Set E := {v | 0 < radSq v}

/-- The normal coordinates of an ambient point with respect to the twist-`k` frame
at the angle of its circle-plane projection.-/
def wCoord (k : ℕ) (v : E) : F :=
  WithLp.toLp 2 fun i : Fin (m + 2) =>
    if i = 0 then cosK k v * (rad v - 1) + sinK k v * v (Fin.last (m + 2))
    else if i = Fin.last (m + 1) then
      cosK k v * v (Fin.last (m + 2)) - sinK k v * (rad v - 1)
    else v i.succ

@[simp] lemma wCoord_apply (k : ℕ) (v : E) (i : Fin (m + 2)) :
    wCoord k v i
      = if i = 0 then cosK k v * (rad v - 1) + sinK k v * v (Fin.last (m + 2))
        else if i = Fin.last (m + 1) then
          cosK k v * v (Fin.last (m + 2)) - sinK k v * (rad v - 1)
        else v i.succ := rfl

lemma wCoord_apply_zero (k : ℕ) (v : E) :
    wCoord k v 0 = cosK k v * (rad v - 1) + sinK k v * v (Fin.last (m + 2)) := by
  rw [wCoord_apply, ite_eq_left rfl]

lemma wCoord_apply_last (k : ℕ) (v : E) :
    wCoord k v (Fin.last (m + 1))
      = cosK k v * v (Fin.last (m + 2)) - sinK k v * (rad v - 1) := by
  rw [wCoord_apply, ite_eq_right lastW_ne_zero, ite_eq_left rfl]

lemma wCoord_apply_mid (k : ℕ) (v : E) {i : Fin (m + 2)} (h0 : i ≠ 0)
    (hl : i ≠ Fin.last (m + 1)) :
    wCoord k v i = v i.succ := by
  rw [wCoord_apply, ite_eq_right h0, ite_eq_right hl]

/-! ### Basic facts on the tube region -/

lemma radSq_nonneg (v : E) : 0 ≤ radSq v := add_nonneg (sq_nonneg _) (sq_nonneg _)

lemma rad_nonneg (v : E) : 0 ≤ rad v := Real.sqrt_nonneg _

lemma rad_pos {v : E} (h : 0 < radSq v) : 0 < rad v := Real.sqrt_pos.mpr h

lemma rad_sq (v : E) : rad v ^ 2 = radSq v := Real.sq_sqrt (radSq_nonneg v)

lemma uC_sq_add_uS_sq {v : E} (h : 0 < radSq v) : uC v ^ 2 + uS v ^ 2 = 1 := by
  rw [uC, uS, div_pow, div_pow, ← add_div, rad_sq]
  have hnum : v 0 ^ 2 + v 1 ^ 2 = radSq v := rfl
  rw [hnum]
  exact div_self h.ne'

lemma cosK_sq_add_sinK_sq {v : E} (h : 0 < radSq v) (k : ℕ) :
    cosK k v ^ 2 + sinK k v ^ 2 = 1 := by
  rw [cosK, sinK, rotP_sq_add_sq]
  show (uC v ^ 2 + uS v ^ 2) ^ k = 1
  rw [uC_sq_add_uS_sq h, one_pow]

/-- Existence of an angle realizing the circle-plane direction.-/
lemma exists_angle {v : E} (h : 0 < radSq v) :
    ∃ θ : ℝ, Real.cos θ = uC v ∧ Real.sin θ = uS v := by
  have hsum : uC v ^ 2 + uS v ^ 2 = 1 := uC_sq_add_uS_sq h
  have hC1 : -1 ≤ uC v ∧ uC v ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (uS v), sq_nonneg (uC v + 1), sq_nonneg (uC v - 1)]
  rcases le_or_gt 0 (uS v) with hs | hs
  · refine ⟨Real.arccos (uC v), Real.cos_arccos hC1.1 hC1.2, ?_⟩
    rw [Real.sin_arccos]
    have h1 : 1 - uC v ^ 2 = uS v ^ 2 := by linarith
    rw [h1, Real.sqrt_sq hs]
  · refine ⟨-Real.arccos (uC v), ?_, ?_⟩
    · rw [Real.cos_neg]
      exact Real.cos_arccos hC1.1 hC1.2
    · rw [Real.sin_neg, Real.sin_arccos]
      have h1 : 1 - uC v ^ 2 = uS v ^ 2 := by linarith
      rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonpos hs.le, neg_neg]

/-! ### Round trip 1: tube coordinates of a tube point -/

lemma radSq_tubeMap (k : ℕ) (θ : ℝ) (w : F) :
    radSq (tubeMap k θ w) = tubeA k θ w ^ 2 := by
  rw [radSq, tubeMap_apply_zero, tubeMap_apply_one]
  linear_combination (tubeA k θ w ^ 2) * Real.sin_sq_add_cos_sq θ

lemma rad_tubeMap (k : ℕ) (θ : ℝ) {w : F} (h : 0 ≤ tubeA k θ w) :
    rad (tubeMap k θ w) = tubeA k θ w := by
  rw [rad, radSq_tubeMap, Real.sqrt_sq h]

lemma radSq_tubeMap_pos (k : ℕ) (θ : ℝ) {w : F} (h : 0 < tubeA k θ w) :
    0 < radSq (tubeMap k θ w) := by
  rw [radSq_tubeMap]
  positivity

lemma uC_tubeMap (k : ℕ) (θ : ℝ) {w : F} (h : 0 < tubeA k θ w) :
    uC (tubeMap k θ w) = Real.cos θ := by
  rw [uC, rad_tubeMap k θ h.le, tubeMap_apply_zero, mul_comm, mul_div_assoc,
    div_self h.ne', mul_one]

lemma uS_tubeMap (k : ℕ) (θ : ℝ) {w : F} (h : 0 < tubeA k θ w) :
    uS (tubeMap k θ w) = Real.sin θ := by
  rw [uS, rad_tubeMap k θ h.le, tubeMap_apply_one, mul_comm, mul_div_assoc,
    div_self h.ne', mul_one]

lemma cosK_tubeMap (k k' : ℕ) (θ : ℝ) {w : F} (h : 0 < tubeA k θ w) :
    cosK k' (tubeMap k θ w) = Real.cos (k' * θ) := by
  rw [cosK, uC_tubeMap k θ h, uS_tubeMap k θ h, rotP_cos_sin]

lemma sinK_tubeMap (k k' : ℕ) (θ : ℝ) {w : F} (h : 0 < tubeA k θ w) :
    sinK k' (tubeMap k θ w) = Real.sin (k' * θ) := by
  rw [sinK, uC_tubeMap k θ h, uS_tubeMap k θ h, rotP_cos_sin]

/-- **Round trip 1**: on the injectivity radius, the tube coordinates recover the
normal displacement.-/
theorem wCoord_tubeMap (k : ℕ) (θ : ℝ) {w : F} (h : 0 < tubeA k θ w) :
    wCoord k (tubeMap k θ w) = w := by
  apply (WithLp.equiv 2 _).injective
  funext i
  show wCoord k (tubeMap k θ w) i = w i
  have hcs : Real.cos (k * θ) ^ 2 + Real.sin (k * θ) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  by_cases h0 : i = 0
  · subst h0
    rw [wCoord_apply_zero, cosK_tubeMap k k θ h, sinK_tubeMap k k θ h,
      rad_tubeMap k θ h.le, tubeMap_apply_last, tubeA, tubeB]
    linear_combination (w 0) * hcs
  · by_cases hl : i = Fin.last (m + 1)
    · subst hl
      rw [wCoord_apply_last, cosK_tubeMap k k θ h, sinK_tubeMap k k θ h,
        rad_tubeMap k θ h.le, tubeMap_apply_last, tubeA, tubeB]
      linear_combination (w (Fin.last (m + 1))) * hcs
    · rw [wCoord_apply_mid k _ h0 hl, tubeMap_apply_mid k θ w h0 hl]

/-! ### Round trip 2: reconstruction of an ambient point -/

/-- **Round trip 2**: every point with nonzero circle-plane projection is the tube
image of its coordinates, at any angle realizing its projection direction.-/
theorem tubeMap_wCoord (k : ℕ) {v : E} (h : 0 < radSq v) {θ : ℝ}
    (hc : Real.cos θ = uC v) (hs : Real.sin θ = uS v) :
    tubeMap k θ (wCoord k v) = v := by
  have hrad : 0 < rad v := rad_pos h
  have hK : rotP k (Real.cos θ, Real.sin θ) = (cosK k v, sinK k v) := by
    rw [hc, hs]; rfl
  have hcos : Real.cos (k * θ) = cosK k v := by
    have h' := rotP_cos_sin k θ
    rw [hK] at h'
    exact (congrArg Prod.fst h').symm
  have hsin : Real.sin (k * θ) = sinK k v := by
    have h' := rotP_cos_sin k θ
    rw [hK] at h'
    exact (congrArg Prod.snd h').symm
  have hcs : cosK k v ^ 2 + sinK k v ^ 2 = 1 := cosK_sq_add_sinK_sq h k
  -- the radial coefficient of the reconstructed point is the radius
  have hA : tubeA k θ (wCoord k v) = rad v := by
    rw [tubeA, hcos, hsin, wCoord_apply_zero, wCoord_apply_last]
    linear_combination (rad v - 1) * hcs
  apply (WithLp.equiv 2 _).injective
  funext j
  show tubeMap k θ (wCoord k v) j = v j
  rcases Nat.lt_or_ge j.val 2 with hj2 | hj2
  · rcases Nat.lt_or_ge j.val 1 with hj1 | hj1
    · have hj : j = 0 := by
        apply Fin.ext
        rw [Fin.val_zero]
        omega
      subst hj
      rw [tubeMap_apply_zero, hA, hc, uC, mul_div_cancel₀ _ hrad.ne']
    · have hj : j = 1 := by
        apply Fin.ext
        rw [Fin.val_one]
        omega
      subst hj
      rw [tubeMap_apply_one, hA, hs, uS, mul_div_cancel₀ _ hrad.ne']
  · rcases Nat.lt_or_ge j.val (m + 2) with hjm | hjm
    · -- middle ambient coordinate
      set i : Fin (m + 2) := ⟨j.val - 1, by omega⟩ with hi
      have hi0 : i ≠ 0 := by
        intro hcon
        have h' := congrArg Fin.val hcon
        simp only [hi, Fin.val_zero] at h'
        omega
      have hil : i ≠ Fin.last (m + 1) := by
        intro hcon
        have h' := congrArg Fin.val hcon
        simp only [hi, Fin.val_last] at h'
        omega
      have hjsucc : (i.succ : Fin (m + 3)) = j := by
        apply Fin.ext
        rw [Fin.val_succ]
        simp only [hi]
        omega
      rw [← hjsucc, tubeMap_apply_mid k θ _ hi0 hil, wCoord_apply_mid k v hi0 hil,
        hjsucc]
    · -- last ambient coordinate
      have hj : j = Fin.last (m + 2) := by
        apply Fin.ext
        rw [Fin.val_last]
        have := j.isLt
        omega
      subst hj
      rw [tubeMap_apply_last, tubeB, hcos, hsin, wCoord_apply_zero,
        wCoord_apply_last]
      linear_combination (v (Fin.last (m + 2))) * hcs

/-! ## Injectivity -/

lemma tubeA_pos (k : ℕ) (θ : ℝ) {w : F} (hw : ‖w‖ < 1 / 2) :
    0 < tubeA k θ w := by
  have h0 : |w 0| ≤ ‖w‖ := abs_coordinate_le_norm w 0
  have hl : |w (Fin.last (m + 1))| ≤ ‖w‖ := abs_coordinate_le_norm w _
  have hc : |Real.cos (k * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hs : |Real.sin (k * θ)| ≤ 1 := Real.abs_sin_le_one _
  have h1 : |w 0 * Real.cos (k * θ)| ≤ ‖w‖ := by
    rw [abs_mul]
    calc |w 0| * |Real.cos (k * θ)| ≤ ‖w‖ * 1 :=
          mul_le_mul h0 hc (abs_nonneg _) (norm_nonneg w)
      _ = ‖w‖ := mul_one _
  have h2 : |w (Fin.last (m + 1)) * Real.sin (k * θ)| ≤ ‖w‖ := by
    rw [abs_mul]
    calc |w _| * |Real.sin (k * θ)| ≤ ‖w‖ * 1 :=
          mul_le_mul hl hs (abs_nonneg _) (norm_nonneg w)
      _ = ‖w‖ := mul_one _
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  rw [tubeA]
  linarith [h1'.1, h2'.2]

/-- The frame (hence the tube map) is `2π`-periodic in the angle.-/
lemma tubeMap_periodic (k : ℕ) (w : F) :
    Function.Periodic (fun θ => tubeMap (m := m) k θ w) (2 * π) := by
  intro θ
  have hc : Real.cos (θ + 2 * π) = Real.cos θ := Real.cos_add_two_pi θ
  have hs : Real.sin (θ + 2 * π) = Real.sin θ := Real.sin_add_two_pi θ
  have hck : Real.cos (k * (θ + 2 * π)) = Real.cos (k * θ) := by
    have harg : (k : ℝ) * (θ + 2 * π) = k * θ + (k : ℤ) * (2 * π) := by
      push_cast; ring
    rw [harg, Real.cos_add_int_mul_two_pi]
  have hsk : Real.sin (k * (θ + 2 * π)) = Real.sin (k * θ) := by
    have harg : (k : ℝ) * (θ + 2 * π) = k * θ + (k : ℤ) * (2 * π) := by
      push_cast; ring
    rw [harg, Real.sin_add_int_mul_two_pi]
  have hcircle : circleAt (m := m) (θ + 2 * π) = circleAt θ := by
    rw [circleAt, circleAt, hc, hs]
  show tubeMap k (θ + 2 * π) w = tubeMap k θ w
  rw [tubeMap, tubeMap, hcircle]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  by_cases h0 : i = 0
  · subst h0
    rw [nuVec_zero, nuVec_zero, hck, hsk, hcircle]
  · by_cases hl : i = Fin.last (m + 1)
    · subst hl
      rw [nuVec_last, nuVec_last, hck, hsk, hcircle]
    · rw [nuVec_mid k _ h0 hl, nuVec_mid k _ h0 hl]

/-! ## Distance from the circle -/

/-- Squared distance from the unit circle in the `(x₀,x₁)`-plane
(valid globally; smooth on `tubeGood`).-/
def tubeDistSq (v : E) : ℝ := ‖v‖ ^ 2 + 1 - 2 * rad v

lemma radSq_le_normSq (v : E) : radSq v ≤ ‖v‖ ^ 2 := by
  rw [normSq_eq_sum_sq]
  have hsub : ({0, 1} : Finset (Fin (m + 3))) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hpair : ∑ j ∈ ({0, 1} : Finset (Fin (m + 3))), (v j) ^ 2 = radSq v := by
    rw [Finset.sum_pair (Fin.zero_ne_one (n := m + 1))]
    rfl
  calc radSq v = ∑ j ∈ ({0, 1} : Finset (Fin (m + 3))), (v j) ^ 2 := hpair.symm
    _ ≤ ∑ j, (v j) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg _

lemma rad_le_norm (v : E) : rad v ≤ ‖v‖ := by
  calc rad v ≤ Real.sqrt (‖v‖ ^ 2) := Real.sqrt_le_sqrt (radSq_le_normSq v)
    _ = ‖v‖ := Real.sqrt_sq (norm_nonneg v)

lemma sq_rad_le_tubeDistSq (v : E) : (rad v - 1) ^ 2 ≤ tubeDistSq v := by
  have h1 := radSq_le_normSq v
  have h2 := rad_sq v
  rw [tubeDistSq]
  nlinarith

/-! Sum decompositions over the normal and ambient index sets. -/

lemma midW_ne (i : Fin m) :
    ((i.castSucc).succ : Fin (m + 2)) ≠ 0
      ∧ ((i.castSucc).succ : Fin (m + 2)) ≠ Fin.last (m + 1) := by
  constructor
  · exact Fin.succ_ne_zero _
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at h'
    omega

lemma sum_decomp_w (f : Fin (m + 2) → ℝ) :
    ∑ i, f i
      = f 0 + (∑ i : Fin m, f ((i.castSucc).succ)) + f (Fin.last (m + 1)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hlast : ((Fin.last m).succ : Fin (m + 2)) = Fin.last (m + 1) := by
    apply Fin.ext
    simp [Fin.val_succ, Fin.val_last]
  rw [hlast]
  ring

lemma sum_decomp_a (f : Fin (m + 3) → ℝ) :
    ∑ j, f j
      = f 0 + f 1 + (∑ i : Fin m, f (((i.castSucc).succ).succ))
        + f (Fin.last (m + 2)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have h1 : ((0 : Fin (m + 2)).succ : Fin (m + 3)) = 1 := by
    apply Fin.ext
    simp [Fin.val_succ]
  have hlast : (((Fin.last m).succ).succ : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_succ, Fin.val_last]
  rw [h1, hlast]
  ring

/-- **Norm of the tube coordinates**: on the region `radSq > 0` the tube
coordinates have squared norm the squared distance from the circle
(independently of the twist `k`).-/
theorem norm_wCoord_sq (k : ℕ) {v : E} (h : 0 < radSq v) :
    ‖wCoord k v‖ ^ 2 = tubeDistSq v := by
  have hcs := cosK_sq_add_sinK_sq h k
  have hradsq := rad_sq v
  rw [normSq_eq_sum_sq, sum_decomp_w, wCoord_apply_zero, wCoord_apply_last]
  have hmid : ∀ i : Fin m,
      (wCoord k v ((i.castSucc).succ)) ^ 2 = (v (((i.castSucc).succ).succ)) ^ 2 :=
    fun i => congrArg (· ^ 2) (wCoord_apply_mid k v (midW_ne i).1 (midW_ne i).2)
  rw [Finset.sum_congr rfl fun i _ => hmid i, tubeDistSq,
    normSq_eq_sum_sq (x := v), sum_decomp_a]
  have hrad : v 0 ^ 2 + v 1 ^ 2 = rad v ^ 2 := by rw [hradsq]; rfl
  linear_combination ((rad v - 1) ^ 2 + (v (Fin.last (m + 2))) ^ 2) * hcs
    - (1 : ℝ) * hrad

/-- On the injectivity region the squared distance from the circle of a tube point
is exactly `‖w‖²`.-/
lemma tubeDistSq_tubeMap (k : ℕ) (θ : ℝ) {w : F} (h : 0 < tubeA k θ w) :
    tubeDistSq (tubeMap k θ w) = ‖w‖ ^ 2 := by
  rw [← norm_wCoord_sq k (radSq_tubeMap_pos k θ h), wCoord_tubeMap k θ h]

/-! ## Smoothness -/

lemma contDiff_coordA (j : Fin (m + 3)) : ContDiff ℝ ∞ fun v : E => v j :=
  (EuclideanSpace.proj j : E →L[ℝ] ℝ).contDiff

lemma contDiff_circleAt : ContDiff ℝ ∞ (circleAt (m := m)) := by
  have h : circleAt (m := m) = fun θ =>
      (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm
        (fun j => if j = 0 then Real.cos θ else if j = 1 then Real.sin θ else 0) :=
    rfl
  rw [h]
  apply (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm.contDiff.comp
  rw [contDiff_pi]
  intro j
  by_cases h0 : j = 0
  · have heq : (fun θ : ℝ => if j = 0 then Real.cos θ
        else if j = 1 then Real.sin θ else 0) = Real.cos := by
      funext θ
      rw [ite_eq_left h0]
    rw [heq]
    exact Real.contDiff_cos
  · by_cases h1 : j = 1
    · have heq : (fun θ : ℝ => if j = 0 then Real.cos θ
          else if j = 1 then Real.sin θ else 0) = Real.sin := by
        funext θ
        rw [ite_eq_right h0, ite_eq_left h1]
      rw [heq]
      exact Real.contDiff_sin
    · have heq : (fun θ : ℝ => if j = 0 then Real.cos θ
          else if j = 1 then Real.sin θ else 0) = fun _ => (0 : ℝ) := by
        funext θ
        rw [ite_eq_right h0, ite_eq_right h1]
      rw [heq]
      exact contDiff_const

lemma contDiff_cos_k (k : ℕ) : ContDiff ℝ ∞ fun θ : ℝ => Real.cos (k * θ) :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

lemma contDiff_sin_k (k : ℕ) : ContDiff ℝ ∞ fun θ : ℝ => Real.sin (k * θ) :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

lemma contDiff_nuVec (k : ℕ) (i : Fin (m + 2)) :
    ContDiff ℝ ∞ fun θ => nuVec (m := m) k θ i := by
  by_cases h0 : i = 0
  · subst h0
    have heq : (fun θ => nuVec (m := m) k θ 0)
        = fun θ => Real.cos (k * θ) • circleAt θ + Real.sin (k * θ) • eVert := by
      funext θ
      exact nuVec_zero k θ
    rw [heq]
    exact ((contDiff_cos_k k).smul contDiff_circleAt).add
      ((contDiff_sin_k k).smul contDiff_const)
  · by_cases hl : i = Fin.last (m + 1)
    · subst hl
      have heq : (fun θ => nuVec (m := m) k θ (Fin.last (m + 1)))
          = fun θ => (-Real.sin (k * θ)) • circleAt θ + Real.cos (k * θ) • eVert := by
        funext θ
        exact nuVec_last k θ
      rw [heq]
      exact (((contDiff_sin_k k).neg).smul contDiff_circleAt).add
        ((contDiff_cos_k k).smul contDiff_const)
    · have heq : (fun θ => nuVec (m := m) k θ i) = fun _ => coordVec i.succ := by
        funext θ
        exact nuVec_mid k θ h0 hl
      rw [heq]
      exact contDiff_const

/-- **Smoothness of the tube map**, jointly in `(θ, w)`.-/
theorem contDiff_tubeMap (k : ℕ) :
    ContDiff ℝ ∞ fun p : ℝ × F => tubeMap k p.1 p.2 := by
  have h : (fun p : ℝ × F => tubeMap k p.1 p.2)
      = fun p : ℝ × F => circleAt p.1 + ∑ i, p.2 i • nuVec k p.1 i := rfl
  rw [h]
  apply ContDiff.add
  · exact contDiff_circleAt.comp contDiff_fst
  · apply ContDiff.sum
    intro i _
    exact ((EuclideanSpace.proj i).contDiff.comp contDiff_snd).smul
      ((contDiff_nuVec k i).comp contDiff_fst)

lemma contDiff_radSq : ContDiff ℝ ∞ (radSq (m := m)) := by
  have h : radSq (m := m) = fun v => v 0 ^ 2 + v 1 ^ 2 := rfl
  rw [h]
  exact ((contDiff_coordA 0).pow 2).add ((contDiff_coordA 1).pow 2)

lemma isOpen_tubeGood : IsOpen (tubeGood (m := m)) :=
  isOpen_lt continuous_const contDiff_radSq.continuous

lemma contDiffOn_rad : ContDiffOn ℝ ∞ (rad (m := m)) tubeGood := by
  intro v hv
  have h1 : ContDiffAt ℝ ∞ Real.sqrt (radSq v) :=
    Real.contDiffAt_sqrt (ne_of_gt hv)
  exact (h1.comp v contDiff_radSq.contDiffAt).contDiffWithinAt

lemma contDiffOn_uC : ContDiffOn ℝ ∞ (uC (m := m)) tubeGood := by
  apply ContDiffOn.div ((contDiff_coordA 0).contDiffOn) contDiffOn_rad
  intro v hv
  exact (rad_pos hv).ne'

lemma contDiffOn_uS : ContDiffOn ℝ ∞ (uS (m := m)) tubeGood := by
  apply ContDiffOn.div ((contDiff_coordA 1).contDiffOn) contDiffOn_rad
  intro v hv
  exact (rad_pos hv).ne'

lemma contDiffOn_cosK (k : ℕ) : ContDiffOn ℝ ∞ (cosK (m := m) k) tubeGood := by
  have h : cosK (m := m) k = fun v => (rotP k (uC v, uS v)).1 := rfl
  rw [h]
  exact (contDiff_fst.comp (contDiff_rotP k)).comp_contDiffOn
    (contDiffOn_uC.prodMk contDiffOn_uS)

lemma contDiffOn_sinK (k : ℕ) : ContDiffOn ℝ ∞ (sinK (m := m) k) tubeGood := by
  have h : sinK (m := m) k = fun v => (rotP k (uC v, uS v)).2 := rfl
  rw [h]
  exact (contDiff_snd.comp (contDiff_rotP k)).comp_contDiffOn
    (contDiffOn_uC.prodMk contDiffOn_uS)

/-- **Smoothness of the tube coordinates** on the region `radSq > 0`.-/
theorem contDiffOn_wCoord (k : ℕ) :
    ContDiffOn ℝ ∞ (wCoord (m := m) k) tubeGood := by
  have h : wCoord (m := m) k = fun v =>
      (EuclideanSpace.equiv (Fin (m + 2)) ℝ).symm
        (fun i => if i = 0 then
            cosK k v * (rad v - 1) + sinK k v * v (Fin.last (m + 2))
          else if i = Fin.last (m + 1) then
            cosK k v * v (Fin.last (m + 2)) - sinK k v * (rad v - 1)
          else v i.succ) := rfl
  rw [h]
  apply (EuclideanSpace.equiv (Fin (m + 2)) ℝ).symm.contDiff.comp_contDiffOn
  rw [contDiffOn_pi]
  intro i
  by_cases h0 : i = 0
  · have heq : (fun v : E => if i = 0 then
        cosK k v * (rad v - 1) + sinK k v * v (Fin.last (m + 2))
      else if i = Fin.last (m + 1) then
        cosK k v * v (Fin.last (m + 2)) - sinK k v * (rad v - 1)
      else v i.succ)
        = fun v => cosK k v * (rad v - 1) + sinK k v * v (Fin.last (m + 2)) := by
      funext v
      rw [ite_eq_left h0]
    rw [heq]
    exact ((contDiffOn_cosK k).mul (contDiffOn_rad.sub contDiffOn_const)).add
      ((contDiffOn_sinK k).mul ((contDiff_coordA (Fin.last (m + 2))).contDiffOn))
  · by_cases hl : i = Fin.last (m + 1)
    · have heq : (fun v : E => if i = 0 then
          cosK k v * (rad v - 1) + sinK k v * v (Fin.last (m + 2))
        else if i = Fin.last (m + 1) then
          cosK k v * v (Fin.last (m + 2)) - sinK k v * (rad v - 1)
        else v i.succ)
          = fun v => cosK k v * v (Fin.last (m + 2)) - sinK k v * (rad v - 1) := by
        funext v
        rw [ite_eq_right h0, ite_eq_left hl]
      rw [heq]
      exact ((contDiffOn_cosK k).mul
          ((contDiff_coordA (Fin.last (m + 2))).contDiffOn)).sub
        ((contDiffOn_sinK k).mul (contDiffOn_rad.sub contDiffOn_const))
    · have heq : (fun v : E => if i = 0 then
          cosK k v * (rad v - 1) + sinK k v * v (Fin.last (m + 2))
        else if i = Fin.last (m + 1) then
          cosK k v * v (Fin.last (m + 2)) - sinK k v * (rad v - 1)
        else v i.succ) = fun v => v i.succ := by
        funext v
        rw [ite_eq_right h0, ite_eq_right hl]
      rw [heq]
      exact (contDiff_coordA i.succ).contDiffOn

/-- `tubeDistSq` is smooth on the region `radSq > 0`.-/
lemma contDiffOn_tubeDistSq : ContDiffOn ℝ ∞ (tubeDistSq (m := m)) tubeGood := by
  have h : tubeDistSq (m := m) = fun v => ‖v‖ ^ 2 + 1 - 2 * rad v := rfl
  rw [h]
  apply ContDiffOn.sub
  · apply ContDiffOn.add _ contDiffOn_const
    have hnormsq : ContDiff ℝ ∞ fun v : E => ‖v‖ ^ 2 := by
      have h2 : (fun v : E => ‖v‖ ^ 2) = fun v : E => ⟪v, v⟫ := by
        funext v
        rw [real_inner_self_eq_norm_sq]
      rw [h2]
      exact ContDiff.inner ℝ contDiff_id contDiff_id
    exact hnormsq.contDiffOn
  · exact contDiffOn_const.mul contDiffOn_rad

/-! ## Orthonormality of the frame -/

lemma inner_coordVec_left (a : Fin (m + 3)) (y : E) : ⟪coordVec a, y⟫ = y a := by
  rw [inner_eq_sum]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · rw [coordVec_apply, ite_eq_left rfl, one_mul]
  · intro j _ hj
    rw [coordVec_apply, ite_eq_right hj, zero_mul]

lemma inner_coordVec_right (x : E) (a : Fin (m + 3)) : ⟪x, coordVec a⟫ = x a := by
  rw [real_inner_comm, inner_coordVec_left]

lemma inner_circleAt_circleAt (θ θ' : ℝ) :
    ⟪circleAt (m := m) θ, circleAt θ'⟫
      = Real.cos θ * Real.cos θ' + Real.sin θ * Real.sin θ' := by
  rw [inner_eq_sum]
  apply sum_split_pair01
  · rw [circleAt_apply_zero, circleAt_apply_zero]
  · rw [circleAt_apply_one, circleAt_apply_one]
  · intro j h0 h1
    rw [circleAt_apply_other θ h0 h1, zero_mul]

lemma inner_circleAt_self (θ : ℝ) : ⟪circleAt (m := m) θ, circleAt θ⟫ = 1 := by
  rw [inner_circleAt_circleAt]
  linear_combination Real.sin_sq_add_cos_sq θ

lemma inner_circleAt_eVert (θ : ℝ) : ⟪circleAt (m := m) θ, eVert⟫ = 0 := by
  rw [eVert, inner_coordVec_right]
  exact circleAt_apply_other θ lastA_ne_zero lastA_ne_one

lemma inner_eVert_self : ⟪eVert (m := m), eVert⟫ = 1 := by
  rw [eVert, inner_coordVec_right]
  exact eVert_apply_last

lemma inner_circleAt_tangentAt (θ : ℝ) :
    ⟪circleAt (m := m) θ, tangentAt θ⟫ = 0 := by
  have h : ⟪circleAt (m := m) θ, tangentAt θ⟫
      = Real.cos θ * -Real.sin θ + Real.sin θ * Real.cos θ := by
    rw [inner_eq_sum]
    apply sum_split_pair01
    · rw [circleAt_apply_zero, tangentAt_apply, ite_eq_left rfl]
    · rw [circleAt_apply_one, tangentAt_apply,
        ite_eq_right (Fin.zero_ne_one (n := m + 1)).symm, ite_eq_left rfl]
    · intro j h0 h1
      rw [circleAt_apply_other θ h0 h1, zero_mul]
  rw [h]
  ring

lemma inner_eVert_tangentAt (θ : ℝ) : ⟪eVert (m := m), tangentAt θ⟫ = 0 := by
  rw [eVert, inner_coordVec_left, tangentAt_apply, ite_eq_right lastA_ne_zero,
    ite_eq_right lastA_ne_one]

/-- **Orthonormality of the twist-`k` frame.**-/
theorem inner_nuVec_nuVec (k : ℕ) (θ : ℝ) (i j : Fin (m + 2)) :
    ⟪nuVec (m := m) k θ i, nuVec k θ j⟫ = if i = j then 1 else 0 := by
  have hC := inner_circleAt_self (m := m) θ
  have hV := inner_eVert_self (m := m)
  have hCV := inner_circleAt_eVert (m := m) θ
  have hVC : ⟪eVert (m := m), circleAt θ⟫ = 0 := by
    rw [real_inner_comm]; exact hCV
  have expand : ∀ a b c d : ℝ,
      ⟪a • circleAt (m := m) θ + b • eVert, c • circleAt θ + d • eVert⟫
        = a * c + b * d := by
    intro a b c d
    rw [inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, hC, hV, hCV, hVC]
    ring
  have expandMixL : ∀ (a b : ℝ) (s : Fin (m + 3)), s ≠ 0 → s ≠ 1
      → s ≠ Fin.last (m + 2)
      → ⟪a • circleAt (m := m) θ + b • eVert, coordVec s⟫ = 0 := by
    intro a b s h0 h1 hlast
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_coordVec_right, inner_coordVec_right,
      circleAt_apply_other θ h0 h1, eVert_apply_ne hlast]
    ring
  have expandMixR : ∀ (a b : ℝ) (s : Fin (m + 3)), s ≠ 0 → s ≠ 1
      → s ≠ Fin.last (m + 2)
      → ⟪coordVec s, a • circleAt (m := m) θ + b • eVert⟫ = 0 := by
    intro a b s h0 h1 hlast
    rw [real_inner_comm]
    exact expandMixL a b s h0 h1 hlast
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0
      rw [ite_eq_left rfl, nuVec_zero, expand]
      linear_combination Real.cos_sq_add_sin_sq (k * θ)
    · by_cases hjl : j = Fin.last (m + 1)
      · subst hjl
        rw [ite_eq_right (Ne.symm lastW_ne_zero), nuVec_zero, nuVec_last, expand]
        ring
      · obtain ⟨hs0, hs1, hsl⟩ := midSucc_ne hj0 hjl
        rw [ite_eq_right (Ne.symm hj0), nuVec_zero, nuVec_mid k θ hj0 hjl,
          expandMixL _ _ _ hs0 hs1 hsl]
  · by_cases hil : i = Fin.last (m + 1)
    · subst hil
      by_cases hj0 : j = 0
      · subst hj0
        rw [ite_eq_right lastW_ne_zero, nuVec_last, nuVec_zero, expand]
        ring
      · by_cases hjl : j = Fin.last (m + 1)
        · subst hjl
          rw [ite_eq_left rfl, nuVec_last, expand]
          linear_combination Real.cos_sq_add_sin_sq (k * θ)
        · obtain ⟨hs0, hs1, hsl⟩ := midSucc_ne hj0 hjl
          rw [ite_eq_right (fun hcon => hjl hcon.symm), nuVec_last,
            nuVec_mid k θ hj0 hjl, expandMixL _ _ _ hs0 hs1 hsl]
    · obtain ⟨hs0, hs1, hsl⟩ := midSucc_ne hi0 hil
      by_cases hj0 : j = 0
      · subst hj0
        rw [ite_eq_right hi0, nuVec_mid k θ hi0 hil, nuVec_zero,
          expandMixR _ _ _ hs0 hs1 hsl]
      · by_cases hjl : j = Fin.last (m + 1)
        · subst hjl
          rw [ite_eq_right hil, nuVec_mid k θ hi0 hil, nuVec_last,
            expandMixR _ _ _ hs0 hs1 hsl]
        · rw [nuVec_mid k θ hi0 hil, nuVec_mid k θ hj0 hjl, inner_coordVec_left,
            coordVec_apply]
          by_cases hij : i = j
          · subst hij
            rw [ite_eq_left rfl, ite_eq_left rfl]
          · rw [ite_eq_right (fun hcon => hij (Fin.succ_injective _ hcon)), ite_eq_right hij]

/-- The frame is orthogonal to the tangent direction of the circle.-/
theorem inner_nuVec_tangentAt (k : ℕ) (θ : ℝ) (i : Fin (m + 2)) :
    ⟪nuVec (m := m) k θ i, tangentAt θ⟫ = 0 := by
  by_cases hi0 : i = 0
  · subst hi0
    rw [nuVec_zero, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_circleAt_tangentAt, inner_eVert_tangentAt]
    ring
  · by_cases hil : i = Fin.last (m + 1)
    · subst hil
      rw [nuVec_last, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        inner_circleAt_tangentAt, inner_eVert_tangentAt]
      ring
    · obtain ⟨hs0, hs1, _⟩ := midSucc_ne hi0 hil
      rw [nuVec_mid k θ hi0 hil, inner_coordVec_left, tangentAt_apply,
        ite_eq_right hs0, ite_eq_right hs1]

end Submission
