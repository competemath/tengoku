import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace PDT

open scoped Real
open Matrix

/-!
# The Tsirelson bound 2√2

We tie the PDT entanglement-bound claim to Mathlib's kernel-verified
`tsirelson_inequality` (in `Mathlib.Algebra.Star.CHSH`), and we construct
the explicit **real-Pauli** CHSH tuple that **saturates** the bound.

Mathlib states the upper bound as
  `A₀*B₀ + A₀*B₁ + A₁*B₀ − A₁*B₁ ≤ √2 ^ 3 • (1 : R)`,
and `√2 ^ 3 = 2 * √2`, the Tsirelson constant.
-/

/-! ## Part 0 : the scalar identity `√2 ^ 3 = 2 √2`. -/

/-- The scalar identity behind the bound: `√2 ^ 3 = 2 * √2`.
@isnad1 id=eq.0h0v.s5.1cb1685fdcb2 from=translated src=- shape=59a33cb9 vocab=9d82838a
-/
theorem sqrt_two_cubed_eq : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
  have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
    _ = 2 * Real.sqrt 2 := by rw [h]

/-! ## Part (a) : the bound, instantiated from Mathlib's verified theorem. -/

/-- **Tsirelson bound, PDT form (a):** for any CHSH tuple in a noncommutative
ordered real \*-algebra, the CHSH operator is bounded by `2 √2 • 1`.
This is a direct instantiation of Mathlib's `tsirelson_inequality`, with the
constant rewritten into the familiar `2√2` form.
@isnad1 id=le.1h5v.s8.b75d716dc69d from=translated src=- shape=4801ec61 vocab=af0eaa21
-/
theorem chsh_le_two_sqrt_two
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ (2 * Real.sqrt 2) • (1 : R) := by
  have h := tsirelson_inequality A₀ A₁ B₀ B₁ T
  rwa [sqrt_two_cubed_eq] at h

/-! ## Part (b) : the explicit real-Pauli tuple in `M₄(ℝ)` that saturates 2√2.

Working in `Matrix (Fin 4) (Fin 4) ℝ ≅ M₂(ℝ) ⊗ M₂(ℝ)` with computational basis
`|00⟩,|01⟩,|10⟩,|11⟩`. Real Paulis `X = !![0,1;1,0]`, `Z = !![1,0;0,-1]`.

  A₀ = X ⊗ I,   A₁ = Z ⊗ I,
  B₀ = I ⊗ (X+Z)/√2,   B₁ = I ⊗ (X−Z)/√2.

We factor the `√2` out:  `B₀ = (√2)⁻¹ • B₀i`, `B₁ = (√2)⁻¹ • B₁i`,
with `B₀i = I⊗(X+Z)`, `B₁i = I⊗(X−Z)` having integer entries and squaring to `2•1`.
-/

/-- `s = 1/√2`.-/
noncomputable def s : ℝ := (Real.sqrt 2)⁻¹

/--
@isnad1 id=eq.0h0v.s5.d54e002ec291 from=translated src=- shape=5228de3a vocab=e4782dad
-/
theorem s_sq : s * s = (1 : ℝ) / 2 := by
  unfold s
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

/-- `A₀ = X ⊗ I`.-/
def A₀ : Mat := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
/-- `A₁ = Z ⊗ I`.-/
def A₁ : Mat := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]
/-- integer part of `B₀`:  `I ⊗ (X+Z)`.-/
def B₀i : Mat := !![1,1,0,0; 1,-1,0,0; 0,0,1,1; 0,0,1,-1]
/-- integer part of `B₁`:  `I ⊗ (X−Z)`.-/
def B₁i : Mat := !![-1,1,0,0; 1,1,0,0; 0,0,-1,1; 0,0,1,1]
/-- `B₀ = (1/√2) • (I⊗(X+Z))`.-/
noncomputable def B₀ : Mat := s • B₀i
/-- `B₁ = (1/√2) • (I⊗(X−Z))`.-/
noncomputable def B₁ : Mat := s • B₁i

/-- Helper: every integer building block squares correctly.
@isnad1 id=eq.0h0v.s6.39f80f1d4220 from=translated src=- shape=5e8d215c vocab=79de8328
-/
theorem A₀_sq : A₀ * A₀ = (1 : Mat) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₀, Matrix.mul_apply, Fin.sum_univ_four]

/--
@isnad1 id=eq.0h0v.s6.4b936e9d54a4 from=translated src=- shape=5e8d215c vocab=1752ec80
-/
theorem A₁_sq : A₁ * A₁ = (1 : Mat) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₁, Matrix.mul_apply, Fin.sum_univ_four]

/--
@isnad1 id=eq.0h0v.s6.5dcb3b5fdb92 from=translated src=- shape=6ac889ba vocab=20a7b0be
-/
theorem B₀i_sq : B₀i * B₀i = (2 : ℝ) • (1 : Mat) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [B₀i, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/--
@isnad1 id=eq.0h0v.s6.5d395a4e168b from=translated src=- shape=6ac889ba vocab=69a72e69
-/
theorem B₁i_sq : B₁i * B₁i = (2 : ℝ) • (1 : Mat) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [B₁i, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- The four building blocks are symmetric, so (being real) self-adjoint.
@isnad1 id=eq.0h0v.s5.0fca676b7688 from=translated src=- shape=28fc0566 vocab=dfccb3c5
-/
theorem A₀_sa : star A₀ = A₀ := by
  rw [star_eq_conjTranspose]; ext i j; fin_cases i <;> fin_cases j <;> simp [A₀]
/--
@isnad1 id=eq.0h0v.s5.4dd4ea12f850 from=translated src=- shape=28fc0566 vocab=ac248864
-/
theorem A₁_sa : star A₁ = A₁ := by
  rw [star_eq_conjTranspose]; ext i j; fin_cases i <;> fin_cases j <;> simp [A₁]
/--
@isnad1 id=eq.0h0v.s5.2ab87199d547 from=translated src=- shape=28fc0566 vocab=e665a785
-/
theorem B₀i_sa : star B₀i = B₀i := by
  rw [star_eq_conjTranspose]; ext i j; fin_cases i <;> fin_cases j <;> simp [B₀i]
/--
@isnad1 id=eq.0h0v.s5.cfd881a05f39 from=translated src=- shape=28fc0566 vocab=d44b9a68
-/
theorem B₁i_sa : star B₁i = B₁i := by
  rw [star_eq_conjTranspose]; ext i j; fin_cases i <;> fin_cases j <;> simp [B₁i]

/-- Cross-party commutation (A on party 1, B on party 2).
@isnad1 id=eq.0h0v.s6.e3307a722063 from=translated src=- shape=10954431 vocab=43e1bde7
-/
theorem A₀B₀i_comm : A₀ * B₀i = B₀i * A₀ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₀, B₀i, Matrix.mul_apply, Fin.sum_univ_four]
/--
@isnad1 id=eq.0h0v.s6.9ecff392fbee from=translated src=- shape=10954431 vocab=52d97448
-/
theorem A₀B₁i_comm : A₀ * B₁i = B₁i * A₀ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₀, B₁i, Matrix.mul_apply, Fin.sum_univ_four]
/--
@isnad1 id=eq.0h0v.s6.66c8b5777d00 from=translated src=- shape=10954431 vocab=151713a0
-/
theorem A₁B₀i_comm : A₁ * B₀i = B₀i * A₁ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₁, B₀i, Matrix.mul_apply, Fin.sum_univ_four]
/--
@isnad1 id=eq.0h0v.s6.7619796c9943 from=translated src=- shape=10954431 vocab=80f721e9
-/
theorem A₁B₁i_comm : A₁ * B₁i = B₁i * A₁ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₁, B₁i, Matrix.mul_apply, Fin.sum_univ_four]

/-- **The real-Pauli quadruple is a genuine CHSH tuple.**
@isnad1 id=ischshtu.0h0v.s6.8b0af26cba70 from=translated src=- shape=8175f13d vocab=11813e66
-/
theorem isCHSH : IsCHSHTuple A₀ A₁ B₀ B₁ where
  A₀_inv := by rw [sq]; exact A₀_sq
  A₁_inv := by rw [sq]; exact A₁_sq
  B₀_inv := by
    rw [sq, B₀, smul_mul_smul_comm, B₀i_sq, smul_smul, s_sq]
    norm_num
  B₁_inv := by
    rw [sq, B₁, smul_mul_smul_comm, B₁i_sq, smul_smul, s_sq]
    norm_num
  A₀_sa := A₀_sa
  A₁_sa := A₁_sa
  B₀_sa := by rw [B₀, star_smul, B₀i_sa, star_trivial]
  B₁_sa := by rw [B₁, star_smul, B₁i_sa, star_trivial]
  A₀B₀_commutes := by rw [B₀, mul_smul_comm, smul_mul_assoc, A₀B₀i_comm]
  A₀B₁_commutes := by rw [B₁, mul_smul_comm, smul_mul_assoc, A₀B₁i_comm]
  A₁B₀_commutes := by rw [B₀, mul_smul_comm, smul_mul_assoc, A₁B₀i_comm]
  A₁B₁_commutes := by rw [B₁, mul_smul_comm, smul_mul_assoc, A₁B₁i_comm]

/-! ### Saturation: the CHSH operator achieves the eigenvalue `2√2`.

The CHSH operator `P = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ = (1/√2) • M`, where `M` is the
integer matrix `A₀B₀i + A₀B₁i + A₁B₀i − A₁B₁i`. `M` has the integer eigenvalue `4`
on the vector `v = (1,0,0,1)`, so `P` has eigenvalue `4/√2 = 2√2` on `v` — the
operator attains the Tsirelson value. -/

/-- The integer CHSH matrix `M = A₀B₀i + A₀B₁i + A₁B₀i − A₁B₁i`.-/
def Mchsh : Mat := A₀ * B₀i + A₀ * B₁i + A₁ * B₀i - A₁ * B₁i

/-- The eigenvector witnessing saturation.-/
def vsat : Fin 4 → ℝ := ![1,0,0,1]

/-- `M` evaluates to the explicit integer matrix `[[2,0,0,2],[0,-2,2,0],[0,2,-2,0],[2,0,0,2]]`.
@isnad1 id=eq.0h0v.s8.20a1c68590b9 from=translated src=- shape=d442889e vocab=672cb3f0
-/
theorem Mchsh_eq :
    Mchsh = !![2,0,0,2; 0,-2,2,0; 0,2,-2,0; 2,0,0,2] := by
  ext i j
  simp only [Mchsh, A₀, A₁, B₀i, B₁i, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- **`M` has integer eigenvalue 4 on `v=(1,0,0,1)`.**
@isnad1 id=eq.0h0v.s6.4a0b3597e3df from=translated src=- shape=c6cd107e vocab=f3735800
-/
theorem Mchsh_mulVec : Mchsh.mulVec vsat = (4 : ℝ) • vsat := by
  rw [Mchsh_eq]
  ext i; fin_cases i <;>
    simp [vsat, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- **Saturation of the Tsirelson bound (form b).**
The explicit real-Pauli CHSH operator `P = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁`
attains the eigenvalue `2√2` on the unit-direction `v = (1,0,0,1)`:
`P.mulVec v = (2√2) • v`. Since `‖v‖ ≠ 0`, the operator norm of `P` is ≥ `2√2`;
together with `chsh_le_two_sqrt_two` (≤ `2√2`), the bound is exactly attained.
@isnad1 id=eq.0h0v.s8.2f095480b243 from=translated src=- shape=84bb68b2 vocab=08490df3
-/
theorem chsh_saturates :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁).mulVec vsat
      = (2 * Real.sqrt 2) • vsat := by
  -- Rewrite the operator as `s • Mchsh`.
  have hop : A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ = s • Mchsh := by
    unfold Mchsh B₀ B₁
    rw [mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_smul_comm]
    rw [smul_sub, smul_add, smul_add]
  rw [hop]
  -- `(s • M).mulVec v = s • (M.mulVec v) = s • (4 • v) = (4s) • v`.
  rw [Matrix.smul_mulVec, Mchsh_mulVec, smul_smul]
  -- `4 * s = 2 √2`.
  have hcoef : (4 : ℝ) * s = 2 * Real.sqrt 2 := by
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    unfold s
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [show s * (4:ℝ) = (4:ℝ) * s by ring, hcoef]

/-- The witness direction is nonzero, so saturation is genuine (the operator
norm is bounded below by `2√2`).
@isnad1 id=ne.0h0v.s5.7116d0fa9894 from=translated src=- shape=435c0ea6 vocab=da5ade6a
-/
theorem vsat_ne_zero : vsat ≠ 0 := by
  intro h
  have : vsat 0 = (0 : Fin 4 → ℝ) 0 := by rw [h]
  simp [vsat] at this

end PDT
