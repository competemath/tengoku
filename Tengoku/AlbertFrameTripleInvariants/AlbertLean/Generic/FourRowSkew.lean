import Tengoku.Seed.LinearAlgebra.Matrix.Notation
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms common_kernel_proportional` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mul_eq_zero_right` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms inverse_scale_of_product` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Elementary three-by-three skew-matrix lemmas

This file isolates the finite-coordinate algebra used by the proposed
quaternionic four-row reconstruction.  It does not define quaternionic
projectors, prove the rank/image hypotheses that lead to these lemmas, or make
any generic-coverage or invariant-field claim.

The two main facts are:

* two skew `3 x 3` matrices that kill the same nonzero vector are proportional,
  provided the first matrix is nonzero;
* if `B` and `C` are skew `3 x 3` matrices, `B` is nonzero, and `B * C = 0`,
  then `C = 0`.

Both proofs use the three independent skew coefficients.  The arbitrary-matrix
wrappers need `2 != 0` only to show that a matrix satisfying `M.transpose = -M`
has zero diagonal.  The coordinate cancellation lemma itself works over every
field.
-/

namespace AlbertLean.Generic.FourRowSkew

open Matrix

universe u

abbrev Vec3 (K : Type u) := Fin 3 -> K
abbrev Mat3 (K : Type u) := Matrix (Fin 3) (Fin 3) K

/-- A vector in the fixed three-coordinate order.-/
def vec3 {K : Type u} (x y z : K) : Vec3 K := ![x, y, z]

/-- The skew matrix with independent entries `(a,b,c)` in positions
`(0,1)`, `(0,2)`, and `(1,2)`.-/
def skew3 {K : Type u} [Neg K] [OfNat K 0] (a b c : K) : Mat3 K :=
  !![0, a, b;
     -a, 0, c;
     -b, -c, 0]

section Coordinates

variable {K : Type u} [Field K]

@[simp] theorem skew3_mulVec (a b c x y z : K) :
    skew3 a b c *ᵥ vec3 x y z =
      vec3 (a * y + b * z) (-a * x + c * z) (-b * x - c * y) := by
  funext i
  fin_cases i <;>
    simp [skew3, vec3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

@[simp] theorem skew3_zero_iff (a b c : K) :
    skew3 a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have h01 := congrArg (fun M : Mat3 K => M 0 1) h
    have h02 := congrArg (fun M : Mat3 K => M 0 2) h
    have h12 := congrArg (fun M : Mat3 K => M 1 2) h
    simpa [skew3] using And.intro h01 (And.intro h02 h12)
  · rintro ⟨rfl, rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skew3]

theorem skew3_ne_zero_coefficients {a b c : K} (h : skew3 a b c ≠ 0) :
    a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · exact Or.inr (Or.inr (fun hc => h (skew3_zero_iff a b c |>.2 ⟨ha, hb, hc⟩)))
    · exact Or.inr (Or.inl hb)
  · exact Or.inl ha

theorem vec3_ne_zero_coordinates {x y z : K} (h : vec3 x y z ≠ 0) :
    x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := by
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · exact Or.inr (Or.inr (fun hz => h (by
        funext i
        fin_cases i <;> simp [vec3, hx, hy, hz])))
    · exact Or.inr (Or.inl hy)
  · exact Or.inl hx

theorem skew3_smul (t a b c : K) :
    skew3 (t * a) (t * b) (t * c) = t • skew3 a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew3] <;> ring

theorem skew3_smul_sub (t p q r p' q' r' : K) :
    t • skew3 p' q' r' - skew3 p q r =
      skew3 (t * p' - p) (t * q' - q) (t * r' - r) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew3] <;> ring

/-- A nonzero skew `3 x 3` matrix is determined up to scale by any nonzero
vector in its kernel.  Both nonzero hypotheses are essential.-/
theorem skew3_common_kernel_proportional
    (a b c a' b' c' x y z : K)
    (hB : skew3 a b c ≠ 0)
    (hv : vec3 x y z ≠ 0)
    (hker : skew3 a b c *ᵥ vec3 x y z = 0)
    (hker' : skew3 a' b' c' *ᵥ vec3 x y z = 0) :
    ∃ t : K, skew3 a' b' c' = t • skew3 a b c := by
  rw [skew3_mulVec] at hker hker'
  have h0 : a * y + b * z = 0 := by
    simpa [vec3] using congrArg (fun v : Vec3 K => v 0) hker
  have h1 : -a * x + c * z = 0 := by
    simpa [vec3] using congrArg (fun v : Vec3 K => v 1) hker
  have h2 : -b * x - c * y = 0 := by
    simpa [vec3, Matrix.cons_val_two] using
      congrArg (fun v : Vec3 K => v 2) hker
  have h0' : a' * y + b' * z = 0 := by
    simpa [vec3] using congrArg (fun v : Vec3 K => v 0) hker'
  have h1' : -a' * x + c' * z = 0 := by
    simpa [vec3] using congrArg (fun v : Vec3 K => v 1) hker'
  have h2' : -b' * x - c' * y = 0 := by
    simpa [vec3, Matrix.cons_val_two] using
      congrArg (fun v : Vec3 K => v 2) hker'
  have hax : a * x = c * z := by linear_combination -h1
  have hbx : b * x = -(c * y) := by linear_combination -h2
  have hay : a * y = -(b * z) := by linear_combination h0
  have hcy : c * y = -(b * x) := by linear_combination -h2
  have hbz : b * z = -(a * y) := by linear_combination h0
  have hcz : c * z = a * x := by linear_combination h1
  have hax' : a' * x = c' * z := by linear_combination -h1'
  have hbx' : b' * x = -(c' * y) := by linear_combination -h2'
  have hay' : a' * y = -(b' * z) := by linear_combination h0'
  have hcy' : c' * y = -(b' * x) := by linear_combination -h2'
  have hbz' : b' * z = -(a' * y) := by linear_combination h0'
  have hcz' : c' * z = a' * x := by linear_combination h1'
  rcases vec3_ne_zero_coordinates hv with hx | hy | hz
  · have hc : c ≠ 0 := by
      intro hc
      have ha : a = 0 := by
        have hau : a * x = 0 := by simpa [hc] using hax
        exact (mul_eq_zero.mp hau).resolve_right hx
      have hb : b = 0 := by
        have hbu : b * x = 0 := by simpa [hc] using hbx
        exact (mul_eq_zero.mp hbu).resolve_right hx
      exact hB (skew3_zero_iff a b c |>.2 ⟨ha, hb, hc⟩)
    have ha : a = c * z / x := by
      apply (eq_div_iff hx).2
      exact hax
    have hb : b = -(c * y) / x := by
      apply (eq_div_iff hx).2
      exact hbx
    have ha' : a' = c' * z / x := by
      apply (eq_div_iff hx).2
      exact hax'
    have hb' : b' = -(c' * y) / x := by
      apply (eq_div_iff hx).2
      exact hbx'
    let t : K := c' / c
    have hta : a' = t * a := by
      rw [ha, ha']
      dsimp [t]
      field_simp [hc, hx]
    have htb : b' = t * b := by
      rw [hb, hb']
      dsimp [t]
      field_simp [hc, hx]
    have htc : c' = t * c := by
      dsimp [t]
      field_simp [hc]
    refine ⟨t, ?_⟩
    rw [hta, htb, htc]
    exact skew3_smul t a b c
  · have hb : b ≠ 0 := by
      intro hb
      have ha : a = 0 := by
        have hay0 : a * y = 0 := by simpa [hb] using hay
        exact (mul_eq_zero.mp hay0).resolve_right hy
      have hc : c = 0 := by
        have hcy0 : c * y = 0 := by simpa [hb] using hcy
        exact (mul_eq_zero.mp hcy0).resolve_right hy
      exact hB (skew3_zero_iff a b c |>.2 ⟨ha, hb, hc⟩)
    have ha : a = -(b * z) / y := by
      apply (eq_div_iff hy).2
      exact hay
    have hc : c = -(b * x) / y := by
      apply (eq_div_iff hy).2
      exact hcy
    have ha' : a' = -(b' * z) / y := by
      apply (eq_div_iff hy).2
      exact hay'
    have hc' : c' = -(b' * x) / y := by
      apply (eq_div_iff hy).2
      exact hcy'
    let t : K := b' / b
    have hta : a' = t * a := by
      rw [ha, ha']
      dsimp [t]
      field_simp [hb, hy]
    have htb : b' = t * b := by
      dsimp [t]
      field_simp [hb]
    have htc : c' = t * c := by
      rw [hc, hc']
      dsimp [t]
      field_simp [hb, hy]
    refine ⟨t, ?_⟩
    rw [hta, htb, htc]
    exact skew3_smul t a b c
  · have ha : a ≠ 0 := by
      intro ha
      have hb : b = 0 := by
        have hbw : b * z = 0 := by simpa [ha] using hbz
        exact (mul_eq_zero.mp hbw).resolve_right hz
      have hc : c = 0 := by
        have hcw : c * z = 0 := by simpa [ha] using hcz
        exact (mul_eq_zero.mp hcw).resolve_right hz
      exact hB (skew3_zero_iff a b c |>.2 ⟨ha, hb, hc⟩)
    have hb : b = -(a * y) / z := by
      apply (eq_div_iff hz).2
      exact hbz
    have hc : c = a * x / z := by
      apply (eq_div_iff hz).2
      exact hcz
    have hb' : b' = -(a' * y) / z := by
      apply (eq_div_iff hz).2
      exact hbz'
    have hc' : c' = a' * x / z := by
      apply (eq_div_iff hz).2
      exact hcz'
    let t : K := a' / a
    have hta : a' = t * a := by
      dsimp [t]
      field_simp [ha]
    have htb : b' = t * b := by
      rw [hb, hb']
      dsimp [t]
      field_simp [ha, hz]
    have htc : c' = t * c := by
      rw [hc, hc']
      dsimp [t]
      field_simp [ha, hz]
    refine ⟨t, ?_⟩
    rw [hta, htb, htc]
    exact skew3_smul t a b c

/-- The product of two skew matrices, exposed as nine scalar expressions.-/
theorem skew3_mul_skew3 (a b c p q r : K) :
    skew3 a b c * skew3 p q r =
      !![-a * p - b * q, -b * r, a * r;
         -c * q, -a * p - c * r, -a * q;
         c * p, -b * p, -b * q - c * r] := by
  simp only [skew3, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- A nonzero skew `3 x 3` matrix has no nonzero skew right factor whose
product with it vanishes.  This is the rank-free coordinate form of the
image/kernel argument.-/
theorem skew3_mul_eq_zero_right
    (a b c p q r : K)
    (hB : skew3 a b c ≠ 0)
    (hprod : skew3 a b c * skew3 p q r = 0) :
    skew3 p q r = 0 := by
  rw [skew3_mul_skew3] at hprod
  rcases skew3_ne_zero_coefficients hB with ha | hb | hc
  · have har : a * r = 0 := by
      have h : a * r = 0 := by
        simpa using congrArg (fun M : Mat3 K => M 0 2) hprod
      exact h
    have haq : a * q = 0 := by
      have h : -a * q = 0 := by
        simpa using congrArg (fun M : Mat3 K => M 1 2) hprod
      linear_combination -h
    have hr : r = 0 := (mul_eq_zero.mp har).resolve_left ha
    have hq : q = 0 := (mul_eq_zero.mp haq).resolve_left ha
    have hap : a * p = 0 := by
      have h : -a * p - c * r = 0 := by
        simpa using congrArg (fun M : Mat3 K => M 1 1) hprod
      have hneg : -(a * p) = 0 := by
        simpa only [hr, mul_zero, sub_zero, neg_mul] using h
      exact neg_eq_zero.mp hneg
    have hp : p = 0 := (mul_eq_zero.mp hap).resolve_left ha
    exact skew3_zero_iff p q r |>.2 ⟨hp, hq, hr⟩
  · have hbr : b * r = 0 := by
      have h : -b * r = 0 := by
        simpa using congrArg (fun M : Mat3 K => M 0 1) hprod
      linear_combination -h
    have hbp : b * p = 0 := by
      have h : -b * p = 0 := by
        simpa using congrArg (fun M : Mat3 K => M 2 1) hprod
      linear_combination -h
    have hr : r = 0 := (mul_eq_zero.mp hbr).resolve_left hb
    have hp : p = 0 := (mul_eq_zero.mp hbp).resolve_left hb
    have hbq : b * q = 0 := by
      have h : -b * q - c * r = 0 := by
        simpa using congrArg (fun M : Mat3 K => M 2 2) hprod
      have hneg : -(b * q) = 0 := by
        simpa only [hr, mul_zero, sub_zero, neg_mul] using h
      exact neg_eq_zero.mp hneg
    have hq : q = 0 := (mul_eq_zero.mp hbq).resolve_left hb
    exact skew3_zero_iff p q r |>.2 ⟨hp, hq, hr⟩
  · have hcq : c * q = 0 := by
      have h : -c * q = 0 := by
        simpa using congrArg (fun M : Mat3 K => M 1 0) hprod
      linear_combination -h
    have hcp : c * p = 0 := by
      have h : c * p = 0 := by
        simpa using congrArg (fun M : Mat3 K => M 2 0) hprod
      exact h
    have hq : q = 0 := (mul_eq_zero.mp hcq).resolve_left hc
    have hp : p = 0 := (mul_eq_zero.mp hcp).resolve_left hc
    have hcr : c * r = 0 := by
      have h : -a * p - c * r = 0 := by
        simpa using congrArg (fun M : Mat3 K => M 1 1) hprod
      have hneg : -(c * r) = 0 := by
        simpa only [hp, mul_zero, neg_zero, zero_sub, neg_mul] using h
      exact neg_eq_zero.mp hneg
    have hr : r = 0 := (mul_eq_zero.mp hcr).resolve_left hc
    exact skew3_zero_iff p q r |>.2 ⟨hp, hq, hr⟩

/-- The block consequence used after a same-`a` comparison has supplied
`B' = t B`: the displayed upper-left idempotency difference forces the lower
skew block to scale by `t⁻¹`.-/
theorem skew3_inverse_scale_of_product
    (a b c p q r p' q' r' t : K)
    (hB : skew3 a b c ≠ 0)
    (ht : t ≠ 0)
    (hprod :
      skew3 a b c * (t • skew3 p' q' r' - skew3 p q r) = 0) :
    skew3 p' q' r' = t⁻¹ • skew3 p q r := by
  have hzero :
      skew3 (t * p' - p) (t * q' - q) (t * r' - r) = 0 := by
    apply skew3_mul_eq_zero_right a b c
        (t * p' - p) (t * q' - q) (t * r' - r) hB
    rw [← skew3_smul_sub]
    exact hprod
  have hdiff : t • skew3 p' q' r' - skew3 p q r = 0 := by
    rw [skew3_smul_sub]
    exact hzero
  have hscale : t • skew3 p' q' r' = skew3 p q r := sub_eq_zero.mp hdiff
  calc
    skew3 p' q' r' = t⁻¹ • (t • skew3 p' q' r') := by
      simp [smul_smul, ht]
    _ = t⁻¹ • skew3 p q r := congrArg (fun M : Mat3 K => t⁻¹ • M) hscale

end Coordinates

section ArbitrarySkewMatrices

variable {K : Type u} [Field K]

/-- In characteristic other than two, every matrix satisfying
`M.transpose = -M` is one of the displayed three-coordinate skew matrices.-/
theorem eq_skew3_of_transpose_eq_neg
    (hchar : (2 : K) ≠ 0) (M : Mat3 K) (hM : M.transpose = -M) :
    M = skew3 (M 0 1) (M 0 2) (M 1 2) := by
  ext i j
  have hij := congrArg (fun N : Mat3 K => N i j) hM
  fin_cases i <;> fin_cases j
  · have hij' : M 0 0 = -M 0 0 := by
      simpa [Matrix.transpose_apply] using hij
    have hz : (2 : K) * M 0 0 = 0 := by
      linear_combination hij'
    exact (mul_eq_zero.mp hz).resolve_left hchar
  · rfl
  · rfl
  · have hij' : M 0 1 = -M 1 0 := by
      simpa [Matrix.transpose_apply] using hij
    change M 1 0 = -M 0 1
    linear_combination hij'
  · have hij' : M 1 1 = -M 1 1 := by
      simpa [Matrix.transpose_apply] using hij
    have hz : (2 : K) * M 1 1 = 0 := by
      linear_combination hij'
    exact (mul_eq_zero.mp hz).resolve_left hchar
  · rfl
  · have hij' : M 0 2 = -M 2 0 := by
      simpa [Matrix.transpose_apply] using hij
    change M 2 0 = -M 0 2
    linear_combination hij'
  · have hij' : M 1 2 = -M 2 1 := by
      simpa [Matrix.transpose_apply] using hij
    change M 2 1 = -M 1 2
    linear_combination hij'
  · have hij' : M 2 2 = -M 2 2 := by
      simpa [Matrix.transpose_apply] using hij
    have hz : (2 : K) * M 2 2 = 0 := by
      linear_combination hij'
    exact (mul_eq_zero.mp hz).resolve_left hchar

/-- Arbitrary skew matrices with a shared nonzero kernel vector are
proportional.  The first matrix is assumed nonzero to orient the scalar.-/
theorem common_kernel_proportional
    (hchar : (2 : K) ≠ 0) (B C : Mat3 K) (v : Vec3 K)
    (hBskew : B.transpose = -B) (hCskew : C.transpose = -C)
    (hB : B ≠ 0) (hv : v ≠ 0)
    (hBv : B *ᵥ v = 0) (hCv : C *ᵥ v = 0) :
    ∃ t : K, C = t • B := by
  have hBrep := eq_skew3_of_transpose_eq_neg hchar B hBskew
  have hCrep := eq_skew3_of_transpose_eq_neg hchar C hCskew
  have hvrep : v = vec3 (v 0) (v 1) (v 2) := by
    funext i
    fin_cases i <;> rfl
  rw [hBrep] at hB hBv ⊢
  rw [hCrep] at hCv ⊢
  rw [hvrep] at hBv hCv hv
  exact skew3_common_kernel_proportional
    (B 0 1) (B 0 2) (B 1 2)
    (C 0 1) (C 0 2) (C 1 2)
    (v 0) (v 1) (v 2) hB hv hBv hCv

/-- Product cancellation for arbitrary skew `3 x 3` matrices in
characteristic other than two.-/
theorem mul_eq_zero_right
    (hchar : (2 : K) ≠ 0) (B C : Mat3 K)
    (hBskew : B.transpose = -B) (hCskew : C.transpose = -C)
    (hB : B ≠ 0) (hprod : B * C = 0) : C = 0 := by
  have hBrep := eq_skew3_of_transpose_eq_neg hchar B hBskew
  have hCrep := eq_skew3_of_transpose_eq_neg hchar C hCskew
  rw [hBrep] at hB hprod
  rw [hCrep] at hprod ⊢
  exact skew3_mul_eq_zero_right
    (B 0 1) (B 0 2) (B 1 2)
    (C 0 1) (C 0 2) (C 1 2) hB hprod

/-- Same-`a` lower-block consequence for arbitrary skew blocks.  The premise
`B * (t • C' - C) = 0` is exactly the coordinate-free equation left after
substituting `B' = t B` in the upper-left idempotency equations.-/
theorem inverse_scale_of_product
    (hchar : (2 : K) ≠ 0) (B C C' : Mat3 K) (t : K)
    (hBskew : B.transpose = -B)
    (hCskew : C.transpose = -C)
    (hC'skew : C'.transpose = -C')
    (hB : B ≠ 0) (ht : t ≠ 0)
    (hprod : B * (t • C' - C) = 0) : C' = t⁻¹ • C := by
  have hBrep := eq_skew3_of_transpose_eq_neg hchar B hBskew
  have hCrep := eq_skew3_of_transpose_eq_neg hchar C hCskew
  have hC'rep := eq_skew3_of_transpose_eq_neg hchar C' hC'skew
  rw [hBrep] at hB hprod
  rw [hCrep] at hprod ⊢
  rw [hC'rep] at hprod ⊢
  exact skew3_inverse_scale_of_product
    (B 0 1) (B 0 2) (B 1 2)
    (C 0 1) (C 0 2) (C 1 2)
    (C' 0 1) (C' 0 2) (C' 1 2) t hB ht hprod

end ArbitrarySkewMatrices

end AlbertLean.Generic.FourRowSkew
