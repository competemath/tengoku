import Tengoku.ClosureResidueP3Lean.P3.QDMR
import Tengoku.Seed.Analysis.Normed.Algebra.MatrixExponential
import Tengoku.Seed.Analysis.SpecialFunctions.Exponential
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.Combinatorics.SimpleGraph.Hasse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/Katsuya-Tagawa-research/closure-residue-p3-lean@21866e8f070e, `P3/Examples.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# P3 Examples

Finite examples for the closure–residue formalization.

This module formalizes:
* the two-dimensional linear–quadratic separation example;
* the delayed dynamic-depth phenomenon `H₁ ≠ 0`, `R₂ = 0`, `R₃ ≠ 0`;
* its exact unitary and matrix-exponential realization; and
* the finite graph-saturated long-path example.
-/

noncomputable section

open scoped BigOperators
open Matrix

namespace P3

section Examples

/-! ## J1: Theorem 9.1 — linear/quadratic separation in dimension two -/

abbrev Two := Fin 2

/-- The matrix unit `E₁₂`, using zero-based `Fin 2` coordinates `(0,1)`.
Defined directly by entries so the example does not depend on a matrix-unit
constructor whose name may vary across mathlib versions.-/
def E01 : A Two :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- The matrix unit `E₂₁`, using zero-based coordinates `(1,0)`.-/
def E10 : A Two :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- First diagonal matrix unit.-/
def E00 : A Two :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- Second diagonal matrix unit.-/
def E11 : A Two :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

@[simp]
theorem E01_apply (i j : Two) :
    E01 i j = if i = 0 ∧ j = 1 then 1 else 0 := by
  rfl

@[simp]
theorem E10_apply (i j : Two) :
    E10 i j = if i = 1 ∧ j = 0 then 1 else 0 := by
  rfl

@[simp]
theorem E00_apply (i j : Two) :
    E00 i j = if i = 0 ∧ j = 0 then 1 else 0 := by
  rfl

@[simp]
theorem E11_apply (i j : Two) :
    E11 i j = if i = 1 ∧ j = 1 then 1 else 0 := by
  rfl

theorem delta_E01 :
    delta (V := Two) E01 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [delta_apply, E01]

theorem delta_E10 :
    delta (V := Two) E10 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [delta_apply, E10]

theorem conjTranspose_E01 :
    E01.conjTranspose = E10 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, E01, E10]

theorem E01_mul_E10 :
    E01 * E10 = E00 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, E01, E10, E00]

theorem E10_mul_E01 :
    E10 * E01 = E11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, E01, E10, E11]

/-- Exact matrix commutator identity from Theorem 9.1.-/
theorem commutator_E01_E10 :
    E01 * E10 - E10 * E01 = E00 - E11 := by
  rw [E01_mul_E10, E10_mul_E01]

/-- The commutator is diagonal, hence fixed by the diagonal projection.-/
theorem delta_commutator_E01_E10 :
    delta (V := Two) (E01 * E10 - E10 * E01) =
      E00 - E11 := by
  rw [commutator_E01_E10]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [delta_apply, E00, E11]

theorem E00_sub_E11_ne_zero :
    E00 - E11 ≠ (0 : A Two) := by
  intro h
  have h00 := congrFun (congrFun h (0 : Two)) (0 : Two)
  norm_num [E00, E11] at h00

/-- Theorem 9.1, exact finite linear–quadratic separation.-/
theorem linearQuadraticSeparation_two :
    delta (V := Two) E01 = 0 ∧
    delta (V := Two) E10 = 0 ∧
    delta (V := Two) (E01 * E10 - E10 * E01) ≠ 0 := by
  refine ⟨delta_E01, delta_E10, ?_⟩
  rw [delta_commutator_E01_E10]
  exact E00_sub_E11_ne_zero

/-- `E01` viewed as an off-diagonal defect.-/
def offDiagE01 : OffDiag (V := Two) :=
  ⟨E01, by
    change delta (V := Two) E01 = 0
    exact delta_E01⟩

/-- `E10` viewed as an off-diagonal defect.-/
def offDiagE10 : OffDiag (V := Two) :=
  ⟨E10, by
    change delta (V := Two) E10 = 0
    exact delta_E10⟩

/-- The same separation expressed through the P3 quadratic-return API.
For `z = E01`, the return against `z* = E10` has first coordinate `1`,
so it is nonzero.-/
theorem quadraticReturn_E01_ne_zero :
    quadraticReturn (V := Two) offDiagE01 offDiagE01 ≠ 0 := by
  intro h
  have hentry :=
    quadraticReturn_self_entry
      (V := Two) offDiagE01 (0 : Two)
  rw [h] at hentry
  norm_num [offDiagE01, E01, Fin.sum_univ_two] at hentry

/-! ## J2a: algebraic core of the dynamic-depth example -/

/-- Complex square root of three, embedded from the reals.-/
def sqrtThreeC : ℂ := (Real.sqrt 3 : ℂ)

/-- The first off-diagonal coefficient in the dynamic-depth example.-/
def dynamicC1 (s : ℂ) : ℂ :=
  (1 + s) / 3 + Complex.I * ((1 - s) / 3)

/-- The second off-diagonal coefficient in the dynamic-depth example.-/
def dynamicC2 : ℂ :=
  2 / 3 + Complex.I * (2 / 3)

/-- The coefficient identity underlying the first nonzero delayed residue.
It is algebraic and only uses that `s` is real (`star s = s`).-/
theorem dynamicCoefficient_identity
    (s : ℂ) (hs : star s = s) :
    dynamicC1 s * star dynamicC2 -
        star (dynamicC1 s) * dynamicC2 =
      -(8 / 9 : ℂ) * Complex.I * s := by
  simp [dynamicC1, dynamicC2, hs]
  ring

@[simp]
theorem star_sqrtThreeC :
    star sqrtThreeC = sqrtThreeC := by
  simp [sqrtThreeC]

theorem dynamicCoefficient_identity_sqrtThree :
    dynamicC1 sqrtThreeC * star dynamicC2 -
        star (dynamicC1 sqrtThreeC) * dynamicC2 =
      -(8 / 9 : ℂ) * Complex.I * sqrtThreeC := by
  exact dynamicCoefficient_identity sqrtThreeC star_sqrtThreeC

theorem sqrtThreeC_ne_zero :
    sqrtThreeC ≠ 0 := by
  have hR : Real.sqrt (3 : ℝ) ≠ 0 := by
    positivity
  intro h
  have hre := congrArg Complex.re h
  change Real.sqrt (3 : ℝ) = 0 at hre
  exact hR hre

theorem dynamicCoefficient_nonzero :
    dynamicC1 sqrtThreeC * star dynamicC2 -
        star (dynamicC1 sqrtThreeC) * dynamicC2 ≠ 0 := by
  rw [dynamicCoefficient_identity_sqrtThree]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    sqrtThreeC_ne_zero

/-- Hermitian off-diagonal matrix with upper coefficient `c` and lower
coefficient `star c`.-/
def hermitianOffMatrix (c : ℂ) : A Two :=
  c • E01 + star c • E10

theorem delta_hermitianOffMatrix (c : ℂ) :
    delta (V := Two) (hermitianOffMatrix c) = 0 := by
  change delta (V := Two) (c • E01 + star c • E10) = 0
  rw [map_add, map_smul, map_smul, delta_E01, delta_E10]
  simp

theorem conjTranspose_hermitianOffMatrix (c : ℂ) :
    (hermitianOffMatrix c).conjTranspose = hermitianOffMatrix c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianOffMatrix, Matrix.conjTranspose_apply, E01, E10]

/-- Hermitian off-diagonal element as an element of `OffDiag`.-/
def hermitianOff (c : ℂ) : OffDiag (V := Two) :=
  ⟨hermitianOffMatrix c, delta_hermitianOffMatrix c⟩

/-- First primitive hidden direction from the paper's dynamic example.-/
def dynamicZ1 : OffDiag (V := Two) :=
  hermitianOff (dynamicC1 sqrtThreeC)

/-- Second primitive hidden direction from the paper's dynamic example.-/
def dynamicZ2 : OffDiag (V := Two) :=
  hermitianOff dynamicC2

theorem dynamicZ1_selfadjoint :
    dynamicZ1.1.conjTranspose = dynamicZ1.1 := by
  exact conjTranspose_hermitianOffMatrix (dynamicC1 sqrtThreeC)

theorem dynamicZ2_selfadjoint :
    dynamicZ2.1.conjTranspose = dynamicZ2.1 := by
  exact conjTranspose_hermitianOffMatrix dynamicC2

/-- The first hidden direction has zero self-return.  This is the algebraic
reason that a one-dimensional `H₁ = C z₁` can still have `R₂ = 0`.-/
theorem quadraticReturn_dynamicZ1_self_zero :
    quadraticReturn (V := Two) dynamicZ1 dynamicZ1 = 0 := by
  apply Subtype.ext
  apply (vertexEquiv (V := Two)).injective
  ext i
  change ((quadraticReturn (V := Two) dynamicZ1 dynamicZ1).1).ofLp i = 0
  rw [quadraticReturn_apply]
  rw [dynamicZ1_selfadjoint]
  simp

/-- The `(0,0)` coordinate of the mixed quadratic return is precisely the
coefficient appearing in the paper.-/
theorem quadraticReturn_dynamicZ1_dynamicZ2_entry :
    ((quadraticReturn (V := Two) dynamicZ1 dynamicZ2).1).ofLp (0 : Two) =
      dynamicC1 sqrtThreeC * star dynamicC2 -
        star (dynamicC1 sqrtThreeC) * dynamicC2 := by
  rw [quadraticReturn_apply]
  rw [dynamicZ2_selfadjoint]
  simp [dynamicZ1, dynamicZ2, hermitianOff, hermitianOffMatrix,
    Matrix.mul_apply, E01, E10]
  ring

/-- The mixed primitive defects have a nonzero quadratic diagonal return.-/
theorem quadraticReturn_dynamicZ1_dynamicZ2_ne_zero :
    quadraticReturn (V := Two) dynamicZ1 dynamicZ2 ≠ 0 := by
  intro h
  have h0 := congrArg
    (fun r : DiagZero (V := Two) => r.1.ofLp (0 : Two)) h
  rw [quadraticReturn_dynamicZ1_dynamicZ2_entry] at h0
  apply dynamicCoefficient_nonzero
  simpa using h0

/-! ## J2b1: coordinate dynamics for the paper's dynamic-depth orbit -/

/-- The diagonal Pauli direction `h = E00 - E11`, in coordinate form.-/
def dynamicHCoordinates : VertexSpace Two :=
  WithLp.toLp 2 (fun i => if i = (0 : Two) then 1 else -1)

/-- Matrix realization of the diagonal direction `h`.-/
def dynamicHMatrix : A Two :=
  diagonalEmbedding (V := Two) dynamicHCoordinates

/-- `h` packaged as an element of the diagonal observational algebra.-/
def dynamicHDiagonal : diagonalSubmodule (V := Two) :=
  ⟨dynamicHMatrix, ⟨dynamicHCoordinates, rfl⟩⟩

@[simp]
theorem delta_dynamicHMatrix :
    delta (V := Two) dynamicHMatrix = dynamicHMatrix := by
  simp [dynamicHMatrix]

/-- Coordinate formula for the two-dimensional conjugation dynamics used in
the paper's dynamic-depth example.  This is the finite matrix-coordinate
form; the separate bridge to the exponential/unitary presentation is kept
independent from the filtration proof.-/
def dynamicPhiCoreMatrix (M : A Two) : A Two :=
  fun i j =>
    if i = 0 ∧ j = 0 then
      (2 / 3 : ℂ) * M 0 0
        + (((1 - sqrtThreeC) - Complex.I * (sqrtThreeC + 1)) / 6) * M 0 1
        + (((1 - sqrtThreeC) + Complex.I * (sqrtThreeC + 1)) / 6) * M 1 0
        + (1 / 3 : ℂ) * M 1 1
    else if i = 0 ∧ j = 1 then
      (((1 + sqrtThreeC) + Complex.I * (1 - sqrtThreeC)) / 6)
          * (M 0 0 - M 1 1)
        + ((1 + Complex.I * sqrtThreeC) / 3) * M 0 1
        + (Complex.I / 3) * M 1 0
    else if i = 1 ∧ j = 0 then
      (((1 + sqrtThreeC) + Complex.I * (sqrtThreeC - 1)) / 6)
          * (M 0 0 - M 1 1)
        - (Complex.I / 3) * M 0 1
        + ((1 - Complex.I * sqrtThreeC) / 3) * M 1 0
    else
      (1 / 3 : ℂ) * M 0 0
        + (((sqrtThreeC - 1) + Complex.I * (sqrtThreeC + 1)) / 6) * M 0 1
        + (((sqrtThreeC - 1) - Complex.I * (sqrtThreeC + 1)) / 6) * M 1 0
        + (2 / 3 : ℂ) * M 1 1

/-- The coordinate dynamics as a complex-linear endomorphism of `M₂(C)`.-/
def dynamicPhiCore : Dynamics Two where
  toFun := dynamicPhiCoreMatrix
  map_add' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dynamicPhiCoreMatrix] <;> ring
  map_smul' c M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dynamicPhiCoreMatrix] <;> ring

/-- First orbit step from the paper:
`Phi(h) = (1/3) h + z₁`.-/
theorem dynamicPhiCore_h :
    dynamicPhiCore dynamicHMatrix =
      (1 / 3 : ℂ) • dynamicHMatrix + dynamicZ1.1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynamicPhiCore, dynamicPhiCoreMatrix,
      dynamicHMatrix, dynamicHCoordinates,
      diagonalEmbedding_apply, dynamicZ1, hermitianOff,
      hermitianOffMatrix, dynamicC1, star_sqrtThreeC] <;>
    ring

/-- At depth one, the primitive defect of `h` is exactly `z₁`.-/
theorem primitiveDefect_dynamicPhiCore_one :
    primitiveDefect (V := Two) dynamicPhiCore 1 dynamicHDiagonal =
      dynamicZ1 := by
  apply Subtype.ext
  rw [primitiveDefect_val]
  simp only [pow_one, dynamicHDiagonal]
  rw [dynamicPhiCore_h]
  rw [map_add, map_smul]
  have hh :
      offProjection (V := Two) dynamicHMatrix = 0 := by
    change dynamicHMatrix - delta (V := Two) dynamicHMatrix = 0
    rw [delta_dynamicHMatrix]
    simp
  have hz :
      offProjection (V := Two) dynamicZ1.1 = dynamicZ1.1 := by
    change dynamicZ1.1 - delta (V := Two) dynamicZ1.1 = dynamicZ1.1
    rw [dynamicZ1.2]
    simp
  rw [hh, hz]
  simp

/-! ## J2b2: second primitive defect and the nonzero depths H₁, R₃ -/

/-- The complex embedding of `sqrt 3` has square `3`.-/
theorem sqrtThreeC_sq :
    sqrtThreeC ^ 2 = (3 : ℂ) := by
  change ((Real.sqrt (3 : ℝ) : ℂ) ^ 2) = (3 : ℂ)
  norm_cast
  exact Real.sq_sqrt (by norm_num)

/-- The imaginary unit has square `-1`.-/
theorem complexI_sq :
    Complex.I ^ 2 = (-1 : ℂ) := by
  norm_num [pow_two]

/-- Second orbit step from the paper:
`Phi²(h) = -(1/3) h + z₂`.-/
theorem dynamicPhiCore_sq_h :
    (dynamicPhiCore ^ 2) dynamicHMatrix =
      -(1 / 3 : ℂ) • dynamicHMatrix + dynamicZ2.1 := by
  rw [pow_two]
  change dynamicPhiCore (dynamicPhiCore dynamicHMatrix) =
    -(1 / 3 : ℂ) • dynamicHMatrix + dynamicZ2.1
  rw [dynamicPhiCore_h]
  simp only [LinearMap.map_add, LinearMap.map_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynamicPhiCore, dynamicPhiCoreMatrix,
      dynamicHMatrix, dynamicHCoordinates,
      diagonalEmbedding_apply, dynamicZ1, dynamicZ2,
      hermitianOff, hermitianOffMatrix,
      dynamicC1, dynamicC2, star_sqrtThreeC] <;>
    ring_nf <;>
    simp only [sqrtThreeC_sq, complexI_sq] <;>
    ring

/-- At depth two, the primitive defect of `h` is exactly `z₂`.-/
theorem primitiveDefect_dynamicPhiCore_two :
    primitiveDefect (V := Two) dynamicPhiCore 2 dynamicHDiagonal =
      dynamicZ2 := by
  apply Subtype.ext
  rw [primitiveDefect_val]
  simp only [dynamicHDiagonal]
  rw [dynamicPhiCore_sq_h]
  have hh :
      offProjection (V := Two) dynamicHMatrix = 0 := by
    change dynamicHMatrix - delta (V := Two) dynamicHMatrix = 0
    rw [delta_dynamicHMatrix]
    simp
  have hz :
      offProjection (V := Two) dynamicZ2.1 = dynamicZ2.1 := by
    change dynamicZ2.1 - delta (V := Two) dynamicZ2.1 = dynamicZ2.1
    rw [dynamicZ2.2]
    simp
  rw [map_add, map_smul, hh, hz]
  simp

/-- The first dynamic coefficient is nonzero.-/
theorem dynamicC1_ne_zero :
    dynamicC1 sqrtThreeC ≠ 0 := by
  intro hc
  apply dynamicCoefficient_nonzero
  simp [hc]

/-- Hence the first primitive hidden matrix is nonzero.-/
theorem dynamicZ1_val_ne_zero :
    dynamicZ1.1 ≠ (0 : A Two) := by
  intro hz
  have h01 := congrFun (congrFun hz (0 : Two)) (1 : Two)
  apply dynamicC1_ne_zero
  simpa [dynamicZ1, hermitianOff, hermitianOffMatrix, E01, E10] using h01

/-- The hidden sector is already nonzero at depth one.-/
theorem hidden_dynamicPhiCore_one_ne_bot :
    hidden dynamicPhiCore 1 ≠ ⊥ := by
  intro hbot
  have hzmem :
      dynamicZ1.1 ∈ hidden dynamicPhiCore 1 := by
    rw [← primitiveDefect_dynamicPhiCore_one]
    exact primitiveDefect_mem_hidden
      (V := Two) dynamicPhiCore le_rfl dynamicHDiagonal
  rw [hbot] at hzmem
  have hz0 : dynamicZ1.1 = 0 := by
    simpa using hzmem
  exact dynamicZ1_val_ne_zero hz0

/-- The mixed depth-(1,2) primitive return belongs to `R₃`.-/
theorem dynamicMixedReturn_mem_residue_three :
    quadraticReturn (V := Two) dynamicZ1 dynamicZ2
      ∈ residue dynamicPhiCore 3 := by
  rw [residue_eq_span_primitive]
  rw [← primitiveDefect_dynamicPhiCore_one,
      ← primitiveDefect_dynamicPhiCore_two]
  exact primitiveReturn_mem_primitiveResidueSpan
    (V := Two) dynamicPhiCore (by norm_num)
      dynamicHDiagonal dynamicHDiagonal

/-- The quadratic residue sector is nonzero at depth three.-/
theorem residue_dynamicPhiCore_three_ne_bot :
    residue dynamicPhiCore 3 ≠ ⊥ := by
  intro hbot
  have hmem := dynamicMixedReturn_mem_residue_three
  rw [hbot] at hmem
  have hzero :
      quadraticReturn (V := Two) dynamicZ1 dynamicZ2 = 0 := by
    simpa using hmem
  exact quadraticReturn_dynamicZ1_dynamicZ2_ne_zero hzero

/-! ## J2b3: delayed residue, `R₂ = 0` -/

/-- Every depth-zero primitive defect of a diagonal observable vanishes.-/
theorem primitiveDefect_dynamicPhiCore_zero
    (d : diagonalSubmodule (V := Two)) :
    primitiveDefect (V := Two) dynamicPhiCore 0 d = 0 := by
  rcases d with ⟨M, ⟨x, rfl⟩⟩
  apply Subtype.ext
  rw [primitiveDefect_val]
  simp [offProjection, diagonalEmbedding_apply, delta_apply]

/-- For an arbitrary diagonal observable, the depth-one primitive defect is
a scalar multiple of the single hidden direction `z₁`.-/
theorem primitiveDefect_dynamicPhiCore_one_general
    (d : diagonalSubmodule (V := Two)) :
    primitiveDefect (V := Two) dynamicPhiCore 1 d =
      ((d.1 0 0 - d.1 1 1) / 2) • dynamicZ1 := by
  rcases d with ⟨M, ⟨x, rfl⟩⟩
  apply Subtype.ext
  rw [primitiveDefect_val]
  simp only [pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offProjection, delta_apply,
      dynamicPhiCore, dynamicPhiCoreMatrix,
      diagonalEmbedding_apply,
      dynamicZ1, hermitianOff, hermitianOffMatrix,
      dynamicC1, star_sqrtThreeC] <;>
    ring

/-- Any primitive quadratic return with total depth at most two vanishes.-/
theorem primitiveReturn_dynamicPhiCore_le_two_zero
    {m n : ℕ} (hmn : m + n ≤ 2)
    (d e : diagonalSubmodule (V := Two)) :
    quadraticReturn (V := Two)
        (primitiveDefect (V := Two) dynamicPhiCore m d)
        (primitiveDefect (V := Two) dynamicPhiCore n e) = 0 := by
  by_cases hm0 : m = 0
  · subst m
    rw [primitiveDefect_dynamicPhiCore_zero]
    simp
  by_cases hn0 : n = 0
  · subst n
    rw [primitiveDefect_dynamicPhiCore_zero]
    simp
  have hm1 : m = 1 := by omega
  have hn1 : n = 1 := by omega
  subst m
  subst n
  rw [primitiveDefect_dynamicPhiCore_one_general,
      primitiveDefect_dynamicPhiCore_one_general,
      quadraticReturn_smul_left,
      quadraticReturn_smul_right,
      quadraticReturn_dynamicZ1_self_zero]
  simp

/-- The primitive residue span is still zero at total depth two.-/
theorem primitiveResidueSpan_dynamicPhiCore_two_eq_bot :
    primitiveResidueSpan (V := Two) dynamicPhiCore 2 = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro r hr
    rcases hr with ⟨m, n, hmn, d, e, rfl⟩
    rw [primitiveReturn_dynamicPhiCore_le_two_zero hmn d e]
    exact Submodule.zero_mem _
  · exact bot_le

/-- The quadratic residue filtration has not yet returned at depth two.-/
theorem residue_dynamicPhiCore_two_eq_bot :
    residue dynamicPhiCore 2 = ⊥ := by
  rw [residue_eq_span_primitive,
      primitiveResidueSpan_dynamicPhiCore_two_eq_bot]

/-- Exact finite dynamic-depth phenomenon of Section 10:
a hidden defect appears at depth one, the quadratic residue is still absent
at depth two, and a nonzero residue appears at depth three.-/
theorem dynamicDepthPhenomenon :
    hidden dynamicPhiCore 1 ≠ ⊥ ∧
      residue dynamicPhiCore 2 = ⊥ ∧
      residue dynamicPhiCore 3 ≠ ⊥ := by
  exact ⟨hidden_dynamicPhiCore_one_ne_bot,
    residue_dynamicPhiCore_two_eq_bot,
    residue_dynamicPhiCore_three_ne_bot⟩

/-! ## J2c1: finite unitary implementing the dynamic-depth example -/

/-- Complex square root of two, embedded from the reals.-/
def sqrtTwoC : ℂ := (Real.sqrt 2 : ℂ)

@[simp]
theorem star_sqrtTwoC :
    star sqrtTwoC = sqrtTwoC := by
  simp [sqrtTwoC]

theorem sqrtTwoC_ne_zero :
    sqrtTwoC ≠ 0 := by
  have hR : Real.sqrt (2 : ℝ) ≠ 0 := by
    positivity
  intro h
  have hre := congrArg Complex.re h
  change Real.sqrt (2 : ℝ) = 0 at hre
  exact hR hre

theorem sqrtTwoC_sq :
    sqrtTwoC ^ 2 = (2 : ℂ) := by
  change ((Real.sqrt (2 : ℝ) : ℂ) ^ 2) = (2 : ℂ)
  norm_cast
  exact Real.sq_sqrt (by norm_num)

/-- The two real coefficients occurring in the finite matrix form of `U`.-/
def dynamicA : ℂ := 1 / sqrtTwoC

def dynamicB : ℂ := sqrtThreeC / (3 * sqrtTwoC)

@[simp]
theorem star_dynamicA :
    star dynamicA = dynamicA := by
  simp [dynamicA]

@[simp]
theorem star_dynamicB :
    star dynamicB = dynamicB := by
  simp [dynamicB]

/-- Printer-normalized versions used in explicit `conjTranspose` calculations.-/
@[simp]
theorem starRingEnd_dynamicA :
    (starRingEnd ℂ) dynamicA = dynamicA := by
  exact star_dynamicA

@[simp]
theorem starRingEnd_dynamicB :
    (starRingEnd ℂ) dynamicB = dynamicB := by
  exact star_dynamicB

theorem dynamicA_sq :
    dynamicA ^ 2 = (1 / 2 : ℂ) := by
  unfold dynamicA
  rw [div_pow, sqrtTwoC_sq]
  norm_num

theorem dynamicB_sq :
    dynamicB ^ 2 = (1 / 6 : ℂ) := by
  unfold dynamicB
  rw [div_pow, mul_pow, sqrtThreeC_sq, sqrtTwoC_sq]
  norm_num

theorem dynamicA_mul_dynamicB :
    dynamicA * dynamicB = sqrtThreeC / 6 := by
  unfold dynamicA dynamicB
  field_simp [sqrtTwoC_ne_zero]
  ring_nf
  rw [sqrtTwoC_sq]
  ring

theorem dynamicB_mul_dynamicA :
    dynamicB * dynamicA = sqrtThreeC / 6 := by
  rw [mul_comm]
  exact dynamicA_mul_dynamicB

/-- Cross-term normalization used in the explicit conjugation calculation.-/
theorem dynamicA_I_dynamicB_mul (x : ℂ) :
    dynamicA * Complex.I * dynamicB * x =
      Complex.I * x * (sqrtThreeC / 6) := by
  calc
    dynamicA * Complex.I * dynamicB * x =
        Complex.I * x * (dynamicA * dynamicB) := by ring
    _ = Complex.I * x * (sqrtThreeC / 6) := by
      rw [dynamicA_mul_dynamicB]

/-- The same cross coefficient in the ordering arising from the lower row.-/
theorem dynamicB_I_mul_dynamicA (x : ℂ) :
    dynamicB * Complex.I * x * dynamicA =
      Complex.I * x * (sqrtThreeC / 6) := by
  calc
    dynamicB * Complex.I * x * dynamicA =
        Complex.I * x * (dynamicB * dynamicA) := by ring
    _ = Complex.I * x * (sqrtThreeC / 6) := by
      rw [dynamicB_mul_dynamicA]

/-- Cross coefficient after `ring_nf` when the scalar sits on the left.-/
theorem mul_dynamicA_dynamicB (x : ℂ) :
    x * dynamicA * dynamicB = x * (sqrtThreeC / 6) := by
  calc
    x * dynamicA * dynamicB = x * (dynamicA * dynamicB) := by ring
    _ = x * (sqrtThreeC / 6) := by
      rw [dynamicA_mul_dynamicB]

/-- The same normalized cross coefficient with `b a`.-/
theorem mul_dynamicB_dynamicA (x : ℂ) :
    x * dynamicB * dynamicA = x * (sqrtThreeC / 6) := by
  calc
    x * dynamicB * dynamicA = x * (dynamicB * dynamicA) := by ring
    _ = x * (sqrtThreeC / 6) := by
      rw [dynamicB_mul_dynamicA]

/-- Normalized `b a` coefficient when a matrix entry sits on the right.-/
theorem dynamicB_dynamicA_mul (x : ℂ) :
    dynamicB * dynamicA * x = (sqrtThreeC / 6) * x := by
  calc
    dynamicB * dynamicA * x = (dynamicB * dynamicA) * x := rfl
    _ = (sqrtThreeC / 6) * x := by
      rw [dynamicB_mul_dynamicA]

/-- Normalized imaginary cross term in the ordering produced by `ring_nf`.-/
theorem dynamicB_I_dynamicA_mul (x : ℂ) :
    dynamicB * Complex.I * dynamicA * x =
      Complex.I * x * (sqrtThreeC / 6) := by
  calc
    dynamicB * Complex.I * dynamicA * x =
        Complex.I * x * (dynamicB * dynamicA) := by ring
    _ = Complex.I * x * (sqrtThreeC / 6) := by
      rw [dynamicB_mul_dynamicA]

/-- Cross coefficient with a matrix entry between `b` and `a`.-/
theorem dynamicB_mul_middle_dynamicA (x : ℂ) :
    dynamicB * x * dynamicA =
      x * (sqrtThreeC / 6) := by
  calc
    dynamicB * x * dynamicA = x * (dynamicB * dynamicA) := by ring
    _ = x * (sqrtThreeC / 6) := by
      rw [dynamicB_mul_dynamicA]

/-- Finite matrix form of the unitary in Section 10.  Writing
`a = 1/sqrt 2` and `b = sqrt 3/(3 sqrt 2) = 1/sqrt 6`, its entries are
`[[a - i b, b - i b], [-b - i b, a + i b]]`.-/
def dynamicUFinite : A Two :=
  fun i j =>
    if i = 0 ∧ j = 0 then
      dynamicA - Complex.I * dynamicB
    else if i = 0 ∧ j = 1 then
      dynamicB - Complex.I * dynamicB
    else if i = 1 ∧ j = 0 then
      -dynamicB - Complex.I * dynamicB
    else
      dynamicA + Complex.I * dynamicB

/-- The finite matrix is an isometry: `Uᴴ U = I`.-/
theorem dynamicUFinite_conjTranspose_mul_self :
    dynamicUFinite.conjTranspose * dynamicUFinite = (1 : A Two) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynamicUFinite, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, starRingEnd_dynamicA, starRingEnd_dynamicB] <;>
    ring_nf
  all_goals
    simp [dynamicA_sq, dynamicB_sq]
    norm_num

/-- The finite matrix is also coisometric: `U Uᴴ = I`.-/
theorem dynamicUFinite_mul_conjTranspose_self :
    dynamicUFinite * dynamicUFinite.conjTranspose = (1 : A Two) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynamicUFinite, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, starRingEnd_dynamicA, starRingEnd_dynamicB] <;>
    ring_nf
  all_goals
    simp [dynamicA_sq, dynamicB_sq]
    norm_num

/-- Two-sided unitary identity for the finite matrix implementing the example.-/
theorem dynamicUFinite_unitary :
    dynamicUFinite.conjTranspose * dynamicUFinite = (1 : A Two) ∧
      dynamicUFinite * dynamicUFinite.conjTranspose = (1 : A Two) := by
  exact ⟨dynamicUFinite_conjTranspose_mul_self,
    dynamicUFinite_mul_conjTranspose_self⟩

/-! ## J2c2: the finite unitary conjugation is exactly `dynamicPhiCore` -/

/-- Conjugation by the finite unitary matrix, regarded as a complex-linear
endomorphism of `M₂(C)`.-/
def dynamicPhiFinite : Dynamics Two where
  toFun := fun M => dynamicUFinite.conjTranspose * M * dynamicUFinite
  map_add' M N := by
    simp [mul_add, add_mul]
  map_smul' c M := by
    ext i j
    simp [Matrix.mul_apply]
    ring

/-- The coordinate dynamics used above is exactly conjugation by
`dynamicUFinite`.-/
theorem dynamicPhiFinite_apply (M : A Two) :
    dynamicPhiFinite M = dynamicPhiCore M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynamicPhiFinite, dynamicPhiCore, dynamicPhiCoreMatrix,
      dynamicUFinite, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, starRingEnd_dynamicA, starRingEnd_dynamicB] <;>
    ring_nf
  · simp only [dynamicA_I_dynamicB_mul, dynamicA_mul_dynamicB,
      dynamicA_sq, dynamicB_sq, complexI_sq]
    ring
  · simp only [dynamicA_I_dynamicB_mul, dynamicA_mul_dynamicB,
      dynamicA_sq, dynamicB_sq, complexI_sq]
    ring
  · simp only [dynamicB_I_mul_dynamicA,
      dynamicB_mul_middle_dynamicA, dynamicB_mul_dynamicA,
      dynamicA_sq, dynamicB_sq, complexI_sq]
    ring
  · simp only [dynamicB_I_dynamicA_mul, dynamicB_mul_dynamicA,
      dynamicA_sq, dynamicB_sq, complexI_sq]
    ring

/-- Equality of the two dynamics as linear endomorphisms.-/
theorem dynamicPhiFinite_eq_core :
    dynamicPhiFinite = dynamicPhiCore := by
  ext M i j
  exact congrArg (fun X : A Two => X i j) (dynamicPhiFinite_apply M)

/-- Therefore the exact dynamic-depth phenomenon is realized by unitary
conjugation with `dynamicUFinite`.-/
theorem dynamicDepthPhenomenon_unitaryFinite :
    hidden dynamicPhiFinite 1 ≠ ⊥ ∧
      residue dynamicPhiFinite 2 = ⊥ ∧
      residue dynamicPhiFinite 3 ≠ ⊥ := by
  rw [dynamicPhiFinite_eq_core]
  exact dynamicDepthPhenomenon

/-! ## J2c3: algebraic generator behind the exponential form -/

/-- `X = E₁₂ + E₂₁` from the paper.-/
def dynamicX : A Two :=
  E01 + E10

/-- `Y = i(E₁₂ - E₂₁)` from the paper.-/
def dynamicY : A Two :=
  Complex.I • (E01 - E10)

/-- `K = X + Y + h`, the Hermitian generator in the Section 10 example.-/
def dynamicK : A Two :=
  dynamicX + dynamicY + dynamicHMatrix

/-- The generator satisfies the exact quadratic relation `K² = 3 I`.-/
theorem dynamicK_sq :
    dynamicK ^ 2 = (3 : ℂ) • (1 : A Two) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, dynamicK, dynamicX, dynamicY,
      dynamicHMatrix, dynamicHCoordinates,
      diagonalEmbedding_apply,
      Matrix.mul_apply, E01, E10, Fin.sum_univ_two] <;>
    ring_nf
  all_goals
    rw [complexI_sq]
    norm_num

/-- Closed finite form of the unitary, using the already normalized
coefficients `a = 1/√2` and `b = 1/√6`.-/
def dynamicUClosed : A Two :=
  dynamicA • (1 : A Two) -
    (Complex.I * dynamicB) • dynamicK

/-- The entrywise finite unitary is exactly the closed polynomial form
`a I - i b K`.-/
theorem dynamicUFinite_eq_closed :
    dynamicUFinite = dynamicUClosed := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynamicUFinite, dynamicUClosed, dynamicK, dynamicX, dynamicY,
      dynamicHMatrix, dynamicHCoordinates,
      diagonalEmbedding_apply, E01, E10] <;>
    ring_nf
  all_goals
    rw [complexI_sq]
    ring

/-- The coefficient `b = 1/√6` is equivalently `a/√3`, matching the
paper's factor `(1/√2)(I - i K/√3)`.-/
theorem dynamicB_eq_dynamicA_div_sqrtThreeC :
    dynamicB = dynamicA / sqrtThreeC := by
  unfold dynamicA dynamicB
  field_simp [sqrtTwoC_ne_zero, sqrtThreeC_ne_zero]
  exact sqrtThreeC_sq

/-- The exact finite closed form written with the paper's `1/√3`
normalization.-/
def dynamicUPaperClosed : A Two :=
  dynamicA •
    ((1 : A Two) -
      (Complex.I / sqrtThreeC) • dynamicK)

/-- The current finite unitary equals the paper-normalized closed form.-/
theorem dynamicUFinite_eq_paperClosed :
    dynamicUFinite = dynamicUPaperClosed := by
  rw [dynamicUFinite_eq_closed]
  ext i j
  simp [dynamicUClosed, dynamicUPaperClosed,
    dynamicB_eq_dynamicA_div_sqrtThreeC]
  ring

/-! ## J2c4a: explicit diagonalizer and scalar exponential data -/

/-- The diagonalizer `V = K + √3 h`.  It is chosen so that
`K V = V (√3 h)`.-/
def dynamicV : A Two :=
  dynamicK + sqrtThreeC • dynamicHMatrix

/-- Scalar appearing in `V²`.-/
def dynamicVScale : ℂ :=
  6 + 2 * sqrtThreeC

/-- The explicit inverse candidate for `V`.-/
def dynamicVInv : A Two :=
  (1 / dynamicVScale) • dynamicV

theorem dynamicVScale_ne_zero :
    dynamicVScale ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  simp [dynamicVScale, sqrtThreeC] at hre
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  nlinarith

/-- The diagonalizer squares to a nonzero scalar multiple of the identity.-/
theorem dynamicV_sq :
    dynamicV ^ 2 = dynamicVScale • (1 : A Two) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, dynamicV, dynamicVScale,
      dynamicK, dynamicX, dynamicY,
      dynamicHMatrix, dynamicHCoordinates,
      diagonalEmbedding_apply,
      Matrix.mul_apply, E01, E10, Fin.sum_univ_two] <;>
    ring_nf
  all_goals
    rw [complexI_sq]
    simp only [sqrtThreeC_sq]
    ring

theorem dynamicV_mul_inv :
    dynamicV * dynamicVInv = (1 : A Two) := by
  calc
    dynamicV * dynamicVInv =
        (1 / dynamicVScale) • (dynamicV * dynamicV) := by
          ext i j
          simp [dynamicVInv, Matrix.mul_apply]
          ring
    _ = (1 / dynamicVScale) • (dynamicV ^ 2) := by
          rw [pow_two]
    _ = (1 / dynamicVScale) •
        (dynamicVScale • (1 : A Two)) := by
          rw [dynamicV_sq]
    _ = (1 : A Two) := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [dynamicVScale_ne_zero]

theorem dynamicVInv_mul :
    dynamicVInv * dynamicV = (1 : A Two) := by
  calc
    dynamicVInv * dynamicV =
        (1 / dynamicVScale) • (dynamicV * dynamicV) := by
          ext i j
          simp [dynamicVInv, Matrix.mul_apply]
          ring
    _ = (1 / dynamicVScale) • (dynamicV ^ 2) := by
          rw [pow_two]
    _ = (1 / dynamicVScale) •
        (dynamicVScale • (1 : A Two)) := by
          rw [dynamicV_sq]
    _ = (1 : A Two) := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [dynamicVScale_ne_zero]

/-- `V` as an actual unit of the matrix algebra.-/
def dynamicVUnit : (A Two)ˣ where
  val := dynamicV
  inv := dynamicVInv
  val_inv := dynamicV_mul_inv
  inv_val := dynamicVInv_mul

/-- The intertwining identity `K V = V (√3 h)`.-/
theorem dynamicK_mul_dynamicV :
    dynamicK * dynamicV =
      dynamicV * (sqrtThreeC • dynamicHMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynamicV, dynamicK, dynamicX, dynamicY,
      dynamicHMatrix, dynamicHCoordinates,
      diagonalEmbedding_apply,
      Matrix.mul_apply, E01, E10, Fin.sum_univ_two] <;>
    ring_nf
  all_goals
    rw [complexI_sq]
    simp only [sqrtThreeC_sq]
    ring

/-- Hence `K` is conjugate to the diagonal matrix `√3 h`.-/
theorem dynamicK_eq_conj_diagonal :
    dynamicK =
      dynamicV * (sqrtThreeC • dynamicHMatrix) * dynamicVInv := by
  calc
    dynamicK =
        dynamicK * (dynamicV * dynamicVInv) := by
          rw [dynamicV_mul_inv, mul_one]
    _ = (dynamicK * dynamicV) * dynamicVInv := by
          rw [mul_assoc]
    _ = dynamicV * (sqrtThreeC • dynamicHMatrix) * dynamicVInv := by
          rw [dynamicK_mul_dynamicV]

/-- Real angle used in the scalar diagonal exponential.-/
def dynamicTheta : ℝ :=
  -(Real.pi / 4)

/-- `α = - i π / 4`.-/
def dynamicAlpha : ℂ :=
  (dynamicTheta : ℂ) * Complex.I

/-- `√2 / 2 = 1 / √2` in the embedded complex coefficients.-/
theorem sqrtTwoC_div_two_eq_dynamicA :
    sqrtTwoC / 2 = dynamicA := by
  unfold dynamicA
  field_simp [sqrtTwoC_ne_zero]
  simpa [pow_two] using sqrtTwoC_sq

/-- Scalar exponential at `α = -iπ/4`.-/
theorem normedExp_dynamicAlpha :
    NormedSpace.exp dynamicAlpha =
      dynamicA - Complex.I * dynamicA := by
  rw [← Complex.exp_eq_exp_ℂ]
  rw [show dynamicAlpha =
      ((dynamicTheta : ℝ) : ℂ) * Complex.I by rfl]
  rw [Complex.exp_ofReal_mul_I]
  simp only [dynamicTheta, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hhalf :
      (((Real.sqrt 2 / 2 : ℝ) : ℂ)) = sqrtTwoC / 2 := by
    simp [sqrtTwoC]
  have hnegHalf :
      (((-(Real.sqrt 2 / 2) : ℝ) : ℂ)) = -(sqrtTwoC / 2) := by
    simp [sqrtTwoC]
  rw [hhalf, hnegHalf, sqrtTwoC_div_two_eq_dynamicA]
  ring

/-- Scalar exponential at `-α = +iπ/4`.-/
theorem normedExp_neg_dynamicAlpha :
    NormedSpace.exp (-dynamicAlpha) =
      dynamicA + Complex.I * dynamicA := by
  rw [← Complex.exp_eq_exp_ℂ]
  have harg :
      -dynamicAlpha =
        ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    simp [dynamicAlpha, dynamicTheta]
  rw [harg, Complex.exp_ofReal_mul_I]
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hhalf :
      (((Real.sqrt 2 / 2 : ℝ) : ℂ)) = sqrtTwoC / 2 := by
    simp [sqrtTwoC]
  rw [hhalf, sqrtTwoC_div_two_eq_dynamicA]
  ring

/-! ## J2c4b: exact matrix-exponential bridge -/

/-- The diagonal entries of `α h`.-/
def dynamicAlphaDiag : Two → ℂ :=
  fun i => if i = (0 : Two) then dynamicAlpha else -dynamicAlpha

/-- `α h` is literally the diagonal matrix with entries `α,-α`.-/
theorem dynamicAlpha_smul_h_eq_diagonal :
    dynamicAlpha • dynamicHMatrix =
      Matrix.diagonal dynamicAlphaDiag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynamicAlphaDiag, dynamicHMatrix, dynamicHCoordinates,
      diagonalEmbedding_apply]

/-- Exact exponential of the diagonal matrix `α h`.-/
theorem normedExp_dynamicAlpha_h :
    NormedSpace.exp (dynamicAlpha • dynamicHMatrix) =
      dynamicA • (1 : A Two) -
        (Complex.I * dynamicA) • dynamicHMatrix := by
  rw [dynamicAlpha_smul_h_eq_diagonal, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dynamicAlphaDiag, dynamicHMatrix, dynamicHCoordinates,
      diagonalEmbedding_apply,
      normedExp_dynamicAlpha, normedExp_neg_dynamicAlpha]

/-- Matrix appearing in the paper's exponential, temporarily written as
`(α/√3) K`.-/
def dynamicExponentMatrix : A Two :=
  (dynamicAlpha / sqrtThreeC) • dynamicK

/-- The exponent matrix is conjugate to the diagonal matrix `α h`.-/
theorem dynamicExponentMatrix_eq_conj :
    dynamicExponentMatrix =
      (↑dynamicVUnit : A Two) *
        (dynamicAlpha • dynamicHMatrix) *
        (↑(dynamicVUnit⁻¹) : A Two) := by
  change (dynamicAlpha / sqrtThreeC) • dynamicK =
    dynamicV * (dynamicAlpha • dynamicHMatrix) * dynamicVInv
  rw [dynamicK_eq_conj_diagonal]
  have hs :
      (dynamicAlpha / sqrtThreeC) * sqrtThreeC = dynamicAlpha := by
    field_simp [sqrtThreeC_ne_zero]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hs]

/-- Exponential respects the explicit similarity transform.-/
theorem normedExp_dynamicExponentMatrix :
    NormedSpace.exp dynamicExponentMatrix =
      dynamicV *
        NormedSpace.exp (dynamicAlpha • dynamicHMatrix) *
        dynamicVInv := by
  rw [dynamicExponentMatrix_eq_conj]
  simpa [dynamicVUnit] using
    (Matrix.exp_units_conj dynamicVUnit
      (dynamicAlpha • dynamicHMatrix))

/-- Conjugating `h` by `V` gives `K/√3`.-/
theorem dynamicV_conj_h :
    dynamicV * dynamicHMatrix * dynamicVInv =
      (1 / sqrtThreeC) • dynamicK := by
  rw [dynamicK_eq_conj_diagonal]
  have hs :
      (1 / sqrtThreeC) * sqrtThreeC = (1 : ℂ) := by
    field_simp [sqrtThreeC_ne_zero]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hs, one_smul]

/-- Conjugating the diagonal exponential gives exactly the paper-normalized
closed form of `U`.-/
theorem dynamicV_conj_exp_h_eq_paperClosed :
    dynamicV *
        NormedSpace.exp (dynamicAlpha • dynamicHMatrix) *
        dynamicVInv =
      dynamicUPaperClosed := by
  rw [normedExp_dynamicAlpha_h]
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hVone :
      dynamicV * (1 : A Two) * dynamicVInv = (1 : A Two) := by
    simpa using dynamicV_mul_inv
  rw [hVone, dynamicV_conj_h]
  rw [dynamicUPaperClosed]
  simp only [smul_sub, smul_smul]
  have hcoef :
      Complex.I * dynamicA * (1 / sqrtThreeC) =
        dynamicA * (Complex.I / sqrtThreeC) := by
    ring
  rw [hcoef]

/-- The exponential of `(α/√3)K` is the finite unitary already used in
the dynamic-depth proof.-/
theorem normedExp_dynamicExponentMatrix_eq_dynamicUFinite :
    NormedSpace.exp dynamicExponentMatrix = dynamicUFinite := by
  rw [normedExp_dynamicExponentMatrix,
      dynamicV_conj_exp_h_eq_paperClosed]
  exact dynamicUFinite_eq_paperClosed.symm

/-- The exponent exactly as written in the paper:
`- i π /(4√3) · K`.-/
def dynamicPaperExponent : A Two :=
  (-(Complex.I * ((Real.pi : ℂ) / (4 * sqrtThreeC)))) • dynamicK

/-- The paper coefficient is the same as `α/√3`.-/
theorem dynamicPaperExponent_eq_dynamicExponentMatrix :
    dynamicPaperExponent = dynamicExponentMatrix := by
  ext i j
  simp [dynamicPaperExponent, dynamicExponentMatrix,
    dynamicAlpha, dynamicTheta]
  ring

/-- Final exponential bridge for Section 10.-/
theorem normedExp_dynamicPaperExponent_eq_dynamicUFinite :
    NormedSpace.exp dynamicPaperExponent = dynamicUFinite := by
  rw [dynamicPaperExponent_eq_dynamicExponentMatrix]
  exact normedExp_dynamicExponentMatrix_eq_dynamicUFinite

/-! ## J3: Section 11 — finite long-path example -/

/-- The paper's path graph with `n+1` vertices.  We parameterize by `n`
so that the expected residue/incidence dimension is exactly `n`.-/
def longPathGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.pathGraph (n + 1)

/-- The finite path is connected.-/
theorem longPathGraph_connected (n : ℕ) :
    (longPathGraph n).Connected := by
  exact SimpleGraph.pathGraph_connected n

/-- A connected finite path has exactly one connected component.-/
theorem longPathGraph_componentCount (n : ℕ) :
    componentCount (V := Fin (n + 1)) (longPathGraph n) = 1 := by
  unfold componentCount
  letI : Subsingleton (longPathGraph n).ConnectedComponent :=
    (longPathGraph_connected n).preconnected.subsingleton_connectedComponent
  exact Nat.card_unique

/-- The incidence space of the path on `n+1` vertices has dimension `n`,
i.e. `N-1` in the paper's notation.-/
theorem longPathGraph_incidence_finrank (n : ℕ) :
    Module.finrank ℂ
        ↥(incidenceSpace (V := Fin (n + 1)) (longPathGraph n)) = n := by
  rw [incidence_rank, longPathGraph_componentCount]
  simp

/-- On a connected path, a traceless diagonal function that is constant
on connected components is necessarily zero.-/
theorem longPathGraph_componentConstant_eq_bot (n : ℕ) :
    componentConstant (V := Fin (n + 1)) (longPathGraph n) = ⊥ := by
  rw [← Submodule.finrank_eq_zero]
  rw [finrank_componentConstant, longPathGraph_componentCount]

/-- Section 11 at a finite graph-saturated depth:
if the support graph is the path, the silent stabilizer is zero.-/
theorem longPath_stabilizer_eq_bot_of_graphSaturated
    (n : ℕ) (φ : Dynamics (Fin (n + 1))) (k : ℕ)
    (hsat : graphSaturated (V := Fin (n + 1)) φ k)
    (hsupport :
      supportGraph (V := Fin (n + 1)) φ k = longPathGraph n) :
    stabilizer (V := Fin (n + 1)) φ k = ⊥ := by
  rw [stabilizer_eq_componentConstant_of_graphSaturated
      (V := Fin (n + 1)) φ k hsat,
    hsupport,
    longPathGraph_componentConstant_eq_bot]

/-- Section 11 at a finite graph-saturated depth:
the residue has the maximal traceless-diagonal dimension `n = N-1`.-/
theorem longPath_residue_finrank_of_graphSaturated
    (n : ℕ) (φ : Dynamics (Fin (n + 1))) (k : ℕ)
    (hsat : graphSaturated (V := Fin (n + 1)) φ k)
    (hsupport :
      supportGraph (V := Fin (n + 1)) φ k = longPathGraph n) :
    Module.finrank ℂ ↥(residue φ k) = n := by
  rw [residue_finrank_of_graphSaturated
      (V := Fin (n + 1)) φ k hsat,
    hsupport,
    longPathGraph_componentCount]
  simp

/-- Stabilized Section 11 statement:
under graph saturation at infinity and path support, QDMR is `n = N-1`.-/
theorem longPath_QDMR_eq
    (n : ℕ) (φ : Dynamics (Fin (n + 1)))
    (hsat : graphSaturatedAtInfinity (V := Fin (n + 1)) φ)
    (hsupport :
      stableSupportGraph (V := Fin (n + 1)) φ = longPathGraph n) :
    QDMR (V := Fin (n + 1)) φ = n := by
  rw [QDMR_eq_card_sub_components
      (V := Fin (n + 1)) φ hsat,
    hsupport,
    longPathGraph_componentCount]
  simp

/-- Compact finite long-path conclusion matching Section 11:
connected path support plus graph saturation eliminates the silent
traceless stabilizer and leaves `N-1` residue directions.-/
theorem finiteLongPathConclusion
    (n : ℕ) (φ : Dynamics (Fin (n + 1))) (k : ℕ)
    (hsat : graphSaturated (V := Fin (n + 1)) φ k)
    (hsupport :
      supportGraph (V := Fin (n + 1)) φ k = longPathGraph n) :
    stabilizer (V := Fin (n + 1)) φ k = ⊥ ∧
      Module.finrank ℂ ↥(residue φ k) = n := by
  exact ⟨
    longPath_stabilizer_eq_bot_of_graphSaturated n φ k hsat hsupport,
    longPath_residue_finrank_of_graphSaturated n φ k hsat hsupport
  ⟩

end Examples

end P3
