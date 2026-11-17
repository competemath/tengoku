/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.PBW.G2SquareCancellation
import Tengoku.Seed.FieldTheory.KummerExtension
import Tengoku.Seed.RingTheory.Polynomial.Cyclotomic.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The polynomial Newton operator for the G₂ square kernel

The operator used here is `(1 + z) F(xz)`, cubed. Its Newton factors have eigenvalues
`x^(3i)`. The proofs are reconstructed polynomial arguments; no specialization
inverts `x - 1` or a quantum integer.
-/

open Finset Polynomial

noncomputable section

namespace LieLean.QuantumGroup.G2Integral.SquareCancellation

variable {R : Type*} [CommRing R]

/-- The one-step dilation and multiplication operator. Its cube is the G₂ operator.-/
def shift (x : R) : Module.End R R[X] where
  toFun F := (1 + X) * F.comp (C x * X)
  map_add' F H := by simp [add_comp, mul_add]
  map_smul' c F := by simp [smul_eq_C_mul, mul_comp, mul_left_comm]

/--
@isnad1 id=eq.0h3v.s8.563d18321f21 from=translated src=- shape=c295c166 vocab=9f0fbbea
-/
lemma shift_apply (x : R) (F : R[X]) :
    shift x F = (1 + X) * F.comp (C x * X) := rfl

/-- The accumulated linear factors of the dilation operator.-/
def linearFactors (x : R) (n : ℕ) : R[X] :=
  ∏ i ∈ range n, (1 + C (x ^ i) * X)

/--
@isnad1 id=eq.0h4v.s9.c7834ec9e1da from=translated src=- shape=2c5d8e1d vocab=f57459b2
-/
lemma shift_pow_apply (x : R) (n : ℕ) (F : R[X]) :
    (shift x ^ n) F = linearFactors x n * F.comp (C (x ^ n) * X) := by
  induction n with
  | zero => simp [linearFactors]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, shift_apply, ih]
    simp only [mul_comp, comp_assoc, mul_comp, C_comp, X_comp]
    have hc : C (x ^ n) * (C x * X) = C (x ^ (n + 1)) * X := by
      rw [pow_succ, map_mul]
      ring
    rw [hc]
    have hp : (1 + X) * (linearFactors x n).comp (C x * X) =
        linearFactors x (n + 1) := by
      simp only [linearFactors, Polynomial.prod_comp, add_comp, one_comp, mul_comp, C_comp, X_comp]
      rw [prod_range_succ']
      simp only [pow_zero, map_one, one_mul]
      rw [mul_comm (1 + X)]
      congr 1
      apply prod_congr rfl
      intro i _
      rw [pow_succ, map_mul]
      ring
    rw [← mul_assoc, hp]

/-- The cube is precisely multiplication by the three G₂ linear factors followed by dilation.
@isnad1 id=eq.0h3v.s10.f93403a97d1a from=translated src=- shape=d97077f9 vocab=cae6a829
-/
lemma shift_cube_apply (x : R) (F : R[X]) :
    (shift x ^ 3) F = (1 + X) * (1 + C x * X) * (1 + C (x ^ 2) * X) *
      F.comp (C (x ^ 3) * X) := by
  rw [shift_pow_apply]
  simp [linearFactors, prod_range_succ]

/-- Polynomial Newton factors, before evaluation at the G₂ operator.-/
def newtonFactors (x : R) (j n : ℕ) : R[X] :=
  ∏ i ∈ range n, (X - C (x ^ (3 * (j + i))))

/-- An arbitrary consecutive interval of Newton factors, acting on polynomials.-/
def newtonOp (x : R) (j n : ℕ) : Module.End R R[X] :=
  aeval (shift x ^ 3) (newtonFactors x j n)

/--
@isnad1 id=eq.0h3v.s7.188649794d2e from=translated src=- shape=aa4c4db1 vocab=b3ddceff
-/
lemma newtonOp_zero (x : R) (j : ℕ) : newtonOp x j 0 = 1 := by
  simp [newtonOp, newtonFactors]

/--
@isnad1 id=eq.0h4v.s10.6225711a62b5 from=translated src=- shape=13d7af23 vocab=20e52849
-/
lemma newtonOp_succ (x : R) (j n : ℕ) :
    newtonOp x j (n + 1) =
      (shift x ^ 3 - x ^ (3 * (j + n)) • 1) * newtonOp x j n := by
  unfold newtonOp newtonFactors
  rw [prod_range_succ, mul_comm]
  simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

/--
@isnad1 id=eq.0h5v.s8.a5e309b46c55 from=translated src=- shape=8890f006 vocab=31119d81
-/
lemma newtonOp_add (x : R) (j n m : ℕ) :
    newtonOp x j (n + m) = newtonOp x (j + n) m * newtonOp x j n := by
  unfold newtonOp newtonFactors
  rw [prod_range_add, mul_comm, map_mul]
  congr 2
  apply prod_congr rfl
  intro i _
  congr 3
  omega

/--
@isnad1 id=eq.0h6v.s10.d79bf38209de from=translated src=- shape=2b414dd8 vocab=9b5cd74d
-/
lemma shift_pow_map {S : Type*} [CommRing S] (f : R →+* S) (x : R)
    (n : ℕ) (F : R[X]) :
    ((shift x ^ n) F).map f = (shift (f x) ^ n) (F.map f) := by
  rw [shift_pow_apply, shift_pow_apply]
  simp [linearFactors, Polynomial.map_comp, Polynomial.map_prod]

/--
@isnad1 id=eq.0h7v.s8.48895f1aa5a3 from=translated src=- shape=beda958c vocab=59c5c7ef
-/
lemma newtonOp_map {S : Type*} [CommRing S] (f : R →+* S) (x : R)
    (j n : ℕ) (F : R[X]) :
    (newtonOp x j n F).map f = newtonOp (f x) j n (F.map f) := by
  induction n with
  | zero => simp [newtonOp_zero]
  | succ n ih =>
    simp only [newtonOp_succ, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, smul_eq_C_mul, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, map_C, map_pow, shift_pow_map, ih]

/--
@isnad1 id=dvd.1h5v.s9.5f96bc32c987 from=translated src=- shape=dcd792f3 vocab=6b2df3a7
-/
lemma shift_pow_preserves_X_dvd (x : R) (n m : ℕ) (F : R[X])
    (hF : X ^ m ∣ F) : X ^ m ∣ (shift x ^ n) F := by
  obtain ⟨H, rfl⟩ := hF
  refine ⟨linearFactors x n * C (x ^ n) ^ m * H.comp (C (x ^ n) * X), ?_⟩
  simp only [shift_pow_apply, mul_comp, pow_comp, X_comp, mul_pow]
  ring

/--
@isnad1 id=dvd.1h6v.s8.0353313299f3 from=translated src=- shape=1d6dffb6 vocab=042d92ca
-/
lemma newtonOp_preserves_X_dvd (x : R) (j n m : ℕ) (F : R[X])
    (hF : X ^ m ∣ F) : X ^ m ∣ newtonOp x j n F := by
  induction n with
  | zero => simpa [newtonOp_zero] using hF
  | succ n ih =>
    simp only [newtonOp_succ, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, smul_eq_C_mul]
    exact dvd_sub (shift_pow_preserves_X_dvd x 3 m _ ih) (dvd_mul_of_dvd_right ih _)

section Domain

variable [IsDomain R]

/-- The root-of-unity product identity, without any inversion of the polynomial variable.
@isnad1 id=eq.2h3v.s7.b76bd7bb36ba from=translated src=- shape=2f69d619 vocab=1029243d
-/
theorem linearFactors_eq (x : R) (n : ℕ) (hn : 0 < n) (hx : IsPrimitiveRoot x n) :
    linearFactors x n = 1 - (-X) ^ n := by
  have hc : IsPrimitiveRoot (C x : R[X]) n :=
    hx.map_of_injective (Polynomial.C_injective)
  have hp := X_pow_sub_C_eq_prod hc hn (rfl : (-X : R[X]) ^ n = (-X) ^ n)
  have he := congrArg (Polynomial.eval (1 : R[X])) hp
  simpa [linearFactors, eval_prod, mul_neg, sub_neg_eq_add] using he.symm

omit [IsDomain R] in
/-- A primitive cubic multiple gives a primitive root for the Newton eigenvalues.
@isnad1 id=isprimit.1h3v.s5.393483524471 from=translated src=- shape=53dd36e4 vocab=061f7d55
-/
lemma primitive_cube {x : R} {h : ℕ} (hx : IsPrimitiveRoot x (3 * h)) :
    IsPrimitiveRoot (x ^ 3) h := by
  have hp := hx.pow_of_dvd (by decide : 3 ≠ 0) (dvd_mul_right 3 h)
  simpa using hp

/-- Each full block of Newton factors is `T^h - 1` at a primitive `3h`-th root.
@isnad1 id=eq.2h4v.s7.65ec670cee9c from=translated src=- shape=2ba2ab11 vocab=a6ce35e7
-/
theorem newtonFactors_block {x : R} {h : ℕ} (hh : 0 < h)
    (hx : IsPrimitiveRoot x (3 * h)) (j : ℕ) :
    newtonFactors x j h = X ^ h - 1 := by
  have hq := primitive_cube hx
  have ha : (x ^ (3 * j)) ^ h = 1 := by
    rw [← pow_mul, show 3 * j * h = 3 * h * j by ring, pow_mul, hx.pow_eq_one, one_pow]
  have hp := X_pow_sub_C_eq_prod hq hh ha
  rw [C_1] at hp
  rw [hp]
  apply prod_congr rfl
  intro i _
  congr 2
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

/-- Exact block cancellation on every polynomial at a primitive root.
This is not a statement only about the constant input polynomial.
@isnad1 id=eq.2h5v.s8.d80ebdd87f08 from=translated src=- shape=bc7ce950 vocab=e6e5e940
-/
theorem newtonOp_block {x : R} {h : ℕ} (hh : 0 < h)
    (hx : IsPrimitiveRoot x (3 * h)) (j : ℕ) (F : R[X]) :
    newtonOp x j h F = -((-X) ^ (3 * h)) * F := by
  rw [newtonOp, newtonFactors_block hh hx]
  simp only [map_sub, map_pow, aeval_X, map_one, ← pow_mul, LinearMap.sub_apply,
    Module.End.one_apply]
  rw [shift_pow_apply, linearFactors_eq x (3 * h) (by omega) hx, hx.pow_eq_one]
  simp only [map_one, one_mul, comp_X]
  ring

end Domain

/-- Integral coefficient divisibility for a single Newton block. The proof specializes at a
complex primitive root and uses its minimal polynomial over `ℤ`.
@isnad1 id=dvd.2h4v.s9.211bdfe6cce7 from=translated src=- shape=1cc0e7b4 vocab=afd2ac56
-/
theorem cyclotomic_dvd_newtonOp_coeff (h : ℕ) (hh : 0 < h) (j m n : ℕ)
    (hn : n < m + 3 * h) :
    cyclotomic (3 * h) ℤ ∣ (newtonOp (X : ℤ[X]) j h (X ^ m)).coeff n := by
  have hd : 0 < 3 * h := by omega
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (↑(3 * h) : ℂ))
  have hζ : IsPrimitiveRoot ζ (3 * h) := Complex.isPrimitiveRoot_exp (3 * h) hd.ne'
  rw [cyclotomic_eq_minpoly hζ hd]
  apply minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hd)
  have he := newtonOp_map (aeval ζ).toRingHom (X : ℤ[X]) j h (X ^ m)
  have he' := congrArg (fun P : ℂ[X] ↦ P.coeff n) he
  simp only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
    Polynomial.map_pow, map_X] at he'
  rw [he', newtonOp_block hh hζ]
  apply (X_pow_dvd_iff (n := m + 3 * h)).mp ?_ n hn
  refine ⟨-((-1 : ℂ[X]) ^ (3 * h)), ?_⟩
  rw [neg_pow, pow_add]
  ring

/-- A full Newton block over `ℤ[x]`, with its integral cyclotomic filtration.-/
def cyclotomicBlock (h : ℕ) (hh : 0 < h) (j : ℕ) :
    Block (cyclotomic (3 * h) ℤ) (3 * h) where
  toLinearMap := newtonOp (X : ℤ[X]) j h
  triangular m n hn := X_pow_dvd_iff.mp
    (newtonOp_preserves_X_dvd (X : ℤ[X]) j h m (X ^ m) dvd_rfl) n hn
  raises m n hn := cyclotomic_dvd_newtonOp_coeff h hh j m n hn

/--
@isnad1 id=eq.1h4v.s9.d2cd7693b28f from=translated src=- shape=81db661c vocab=b0a988ae
-/
lemma apply_cyclotomicBlocks (h : ℕ) (hh : 0 < h) (u r : ℕ) (F : ℤ[X][X]) :
    applyBlocks (fun j ↦ cyclotomicBlock h hh (u + j * h))
      (newtonOp (X : ℤ[X]) 0 u F) r =
        newtonOp (X : ℤ[X]) 0 (u + r * h) F := by
  induction r with
  | zero => simp [applyBlocks]
  | succ r ih =>
    rw [applyBlocks, ih]
    change newtonOp (X : ℤ[X]) (u + r * h) h
      (newtonOp (X : ℤ[X]) 0 (u + r * h) F) = _
    rw [show u + (r + 1) * h = (u + r * h) + h by ring,
      newtonOp_add _ 0 (u + r * h) h]
    simp only [zero_add, Module.End.mul_apply]

/-- Cyclotomic cancellation for every Newton coefficient, with no bounds on `n` or `t`.
This is the block valuation estimate in `ℤ[x]`; natural subtraction encodes the maximum
with zero. The input polynomial is arbitrary.
@isnad1 id=dvd.1h4v.s9.ec437761c324 from=translated src=- shape=52ac9732 vocab=60a23c47
-/
theorem cyclotomic_pow_dvd_newtonOp_coeff (h : ℕ) (hh : 0 < h) (t n : ℕ)
    (F : ℤ[X][X]) :
    cyclotomic (3 * h) ℤ ^ (t / h - n / (3 * h)) ∣
      (newtonOp (X : ℤ[X]) 0 t F).coeff n := by
  have hv := coeff_dvd_pow_of_blocks
    (fun j ↦ cyclotomicBlock h hh (t % h + j * h)) (by omega : 0 < 3 * h)
    (newtonOp (X : ℤ[X]) 0 (t % h) F) (t / h) n
  rw [apply_cyclotomicBlocks] at hv
  simpa only [Nat.mod_add_div', Nat.add_comm] using hv

/-- The polynomial `D_t(z)` of the integral Newton recurrence.-/
def newtonPolynomial (t : ℕ) : ℤ[X][X] := newtonOp (X : ℤ[X]) 0 t 1

/--
@isnad1 id=eq.0h0v.s5.efa6def4a2e1 from=translated src=- shape=eaff248d vocab=e94fc81f
-/
lemma newtonPolynomial_zero : newtonPolynomial 0 = 1 := by
  simp [newtonPolynomial, newtonOp_zero]

/-- The defining integral recurrence, in the original three-factor convention.
@isnad1 id=eq.0h1v.s9.3cc610f80d02 from=translated src=- shape=711d4588 vocab=7ab317f0
-/
lemma newtonPolynomial_succ (t : ℕ) :
    newtonPolynomial (t + 1) =
      (1 + X) * (1 + C (X : ℤ[X]) * X) * (1 + C ((X : ℤ[X]) ^ 2) * X) *
        (newtonPolynomial t).comp (C ((X : ℤ[X]) ^ 3) * X) -
          C ((X : ℤ[X]) ^ (3 * t)) * newtonPolynomial t := by
  simp only [newtonPolynomial, newtonOp_succ, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, smul_eq_C_mul, zero_add, shift_cube_apply]

/-- The integral coefficient `d(n,t;x)`, before the factorial prefactor.-/
def newtonCoeff (n t : ℕ) : ℤ[X] := (newtonPolynomial t).coeff n

/-- The unrestricted cyclotomic valuation estimate for the G₂ Newton coefficients.
@isnad1 id=dvd.1h3v.s7.7551d8f2d2d7 from=translated src=- shape=80028ad9 vocab=5f853144
-/
theorem cyclotomic_pow_dvd_newtonCoeff (h : ℕ) (hh : 0 < h) (n t : ℕ) :
    cyclotomic (3 * h) ℤ ^ (t / h - n / (3 * h)) ∣ newtonCoeff n t :=
  cyclotomic_pow_dvd_newtonOp_coeff h hh t n 1

end LieLean.QuantumGroup.G2Integral.SquareCancellation
