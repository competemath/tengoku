/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku

/-!
# Perron eigenvectors of finite nonnegative symmetric matrices

The finite matrix argument is shared by the binary, Johnson, spherical, and higher-hierarchy
bounds. It requires no coding-theory definitions. Positivity is propagated along the quiver of
positive matrix entries, allowing arbitrary finite index sets rather than just tridiagonal grids.
-/

@[expose] public section

noncomputable section

open Metric
open scoped BigOperators InnerProductSpace Matrix

namespace MetricCodes.Spherical.HigherHierarchyFinitePerron

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- Euclidean space on the matrix index set. -/
abbrev Space (I : Type*) := EuclideanSpace ℝ I

/-- A nonnegative matrix whose positive-entry quiver is strongly connected. -/
structure ConnectedNonnegativeMatrix (A : Matrix I I ℝ) : Prop where
  nonneg (i j : I) : 0 ≤ A i j
  connected : @Quiver.IsSStronglyConnected I
    ⟨fun i j => PLift (0 < A i j)⟩

/-- The linear operator associated to a real matrix. -/
def operator (A : Matrix I I ℝ) : Space I →ₗ[ℝ] Space I :=
  Matrix.toEuclideanLin A

/-- The continuous linear operator associated to a finite real matrix. -/
def continuousOperator (A : Matrix I I ℝ) : Space I →L[ℝ] Space I :=
  LinearMap.toContinuousLinearMap (operator A)

/-- The Rayleigh quotient of the matrix operator. -/
def rayleigh (A : Matrix I I ℝ) (x : Space I) : ℝ :=
  (continuousOperator A).rayleighQuotient x

omit [Nonempty I] in
/--
@isnad1 id=bddabove.0h2v.s7.cb52126a4d4c from=translated src=- shape=8c77253b vocab=8ac60260
-/
theorem rayleigh_bddAbove (A : Matrix I I ℝ) :
    BddAbove
      (Set.range (fun x : {x : Space I // x ≠ 0} => rayleigh A x)) := by
  refine ⟨‖continuousOperator A‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (le_abs_self _).trans
    ((continuousOperator A).rayleighQuotient_le_norm x)

/-- The supremum of the Rayleigh quotient over nonzero vectors. -/
def topEigenvalue (A : Matrix I I ℝ) : ℝ :=
  ⨆ x : {x : Space I // x ≠ 0}, rayleigh A x

omit [Nonempty I] in
/--
@isnad1 id=le.1h3v.s6.191eebf4716b from=translated src=- shape=d68e8b95 vocab=1e1e0d7a
-/
theorem rayleigh_le_top (A : Matrix I I ℝ)
    (x : Space I) (hx : x ≠ 0) :
    rayleigh A x ≤ topEigenvalue A := by
  exact le_ciSup (rayleigh_bddAbove A) ⟨x, hx⟩

omit [Nonempty I] in
/--
@isnad1 id=issymmet.1h2v.s6.c5be64bed025 from=translated src=- shape=94051cd2 vocab=498345f1
-/
theorem operator_isSymmetric (A : Matrix I I ℝ)
    (hA : Aᵀ = A) : (operator A).IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrArg (fun B : Matrix I I ℝ => B i j) hA
  simpa only [star_trivial, Matrix.transpose_apply] using h

/--
@isnad1 id=ex.1h2v.s8.bd426f7a6e31 from=translated src=- shape=fc76a544 vocab=f5da8696
-/
theorem exists_topEigenvector (A : Matrix I I ℝ)
    (hA : Aᵀ = A) :
    ∃ x : Space I, x ≠ 0 ∧
      operator A x = topEigenvalue A • x := by
  have h := (operator_isSymmetric A hA).hasEigenvalue_iSup_of_finiteDimensional
  have hvalue :
      Module.End.HasEigenvalue (operator A) (topEigenvalue A) := by
    simpa only [topEigenvalue, ne_eq, rayleigh, ContinuousLinearMap.rayleighQuotient,
      continuousOperator, ContinuousLinearMap.reApplyInnerSelf_apply,
      LinearMap.coe_toContinuousLinearMap', RCLike.re_to_real, Order.lt_one_iff,
      Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one, Real.ringHom_apply] using h
  obtain ⟨x, hx⟩ := hvalue.exists_hasEigenvector
  exact ⟨x, hx.2, hx.apply_eq_smul⟩

/-- Take the absolute value of each coordinate. -/
def coordinateAbs (x : Space I) : Space I :=
  WithLp.toLp 2 fun i : I => |x i|

omit [DecidableEq I] [Nonempty I] in
/--
@isnad1 id=eq.0h2v.s5.6ac7311a0964 from=translated src=- shape=c23d63b4 vocab=fba2b23f
-/
theorem coordinateAbs_norm (x : Space I) :
    ‖coordinateAbs x‖ = ‖x‖ := by
  have hsquare : ‖coordinateAbs x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [coordinateAbs, sq_abs]
  nlinarith [norm_nonneg (coordinateAbs x), norm_nonneg x]

omit [Fintype I] [DecidableEq I] [Nonempty I] in
/--
@isnad1 id=ne.1h2v.s6.fc74e1085756 from=translated src=- shape=231f0068 vocab=68f54273
-/
theorem coordinateAbs_ne_zero {x : Space I} (hx : x ≠ 0) :
    coordinateAbs x ≠ 0 := by
  intro habs
  apply hx
  apply PiLp.ext
  intro i
  have hi := congrArg (fun y : Space I => y i) habs
  simpa only [coordinateAbs, PiLp.zero_apply, abs_eq_zero] using hi

omit [Nonempty I] in
/--
@isnad1 id=le.1h3v.s9.75a6f3b25acc from=translated src=- shape=6064ff99 vocab=e4cc5081
-/
theorem inner_le_inner_coordinateAbs (A : Matrix I I ℝ)
    (hA : ∀ i j : I, 0 ≤ A i j) (x : Space I) :
    @inner ℝ (Space I) _ (operator A x) x ≤
      @inner ℝ (Space I) _ (operator A (coordinateAbs x))
        (coordinateAbs x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ i : I, (∑ j : I, A i j * x j) * x i) ≤
      ∑ i : I, (∑ j : I, A i j * |x j|) * |x i|
  simp_rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hproduct : x j * x i ≤ |x j| * |x i| := by
    calc
      x j * x i ≤ |x j * x i| := le_abs_self _
      _ = |x j| * |x i| := abs_mul _ _
  calc
    A i j * x j * x i = A i j * (x j * x i) := by ring
    _ ≤ A i j * (|x j| * |x i|) :=
      mul_le_mul_of_nonneg_left hproduct (hA i j)
    _ = A i j * |x j| * |x i| := by ring

omit [Nonempty I] in
/--
@isnad1 id=eq.2h4v.s8.be273d971f08 from=translated src=- shape=58bddd4c vocab=8632fd47
-/
theorem rayleigh_eq_of_eigenvector (A : Matrix I I ℝ)
    (x : Space I) (hx : x ≠ 0) (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x) :
    rayleigh A x = eigenvalue := by
  change @inner ℝ (Space I) _ (operator A x) x / ‖x‖ ^ 2 = eigenvalue
  rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnorm : ‖x‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  field_simp [hnorm]

omit [Nonempty I] in
/--
@isnad1 id=le.1h3v.s5.32b1aa3daeed from=translated src=- shape=d56fd04f vocab=b7a5ccbe
-/
theorem rayleigh_le_coordinateAbs (A : Matrix I I ℝ)
    (hA : ∀ i j : I, 0 ≤ A i j) (x : Space I) :
    rayleigh A x ≤ rayleigh A (coordinateAbs x) := by
  change
    @inner ℝ (Space I) _ (operator A x) x / ‖x‖ ^ 2 ≤
      @inner ℝ (Space I) _ (operator A (coordinateAbs x))
        (coordinateAbs x) / ‖coordinateAbs x‖ ^ 2
  rw [coordinateAbs_norm]
  gcongr
  exact inner_le_inner_coordinateAbs A hA x

/--
@isnad1 id=ex.2h2v.s9.96009690f6e5 from=translated src=- shape=30a21b6f vocab=c5749aa4
-/
theorem exists_nonnegative_topEigenvector (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hnonneg : ∀ i j : I, 0 ≤ A i j) :
    ∃ x : Space I, x ≠ 0 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 ≤ x i := by
  obtain ⟨x, hx, heig⟩ := exists_topEigenvector A hsymm
  let y : Space I := coordinateAbs x
  have hy : y ≠ 0 := coordinateAbs_ne_zero hx
  have hbelow := rayleigh_le_coordinateAbs A hnonneg x
  have habove := rayleigh_le_top A y hy
  have hxray := rayleigh_eq_of_eigenvector A x hx (topEigenvalue A) heig
  rw [hxray] at hbelow
  have hyray : rayleigh A y = topEigenvalue A :=
    le_antisymm habove hbelow
  have hself : IsSelfAdjoint (continuousOperator A) :=
    (operator_isSymmetric A hsymm).isSelfAdjoint
  have hmax :
      IsMaxOn (continuousOperator A).reApplyInnerSelf
        (sphere (0 : Space I) ‖y‖) y := by
    intro z hz
    have hnorm : ‖z‖ = ‖y‖ := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hznonzero : z ≠ 0 := by
      intro hzzero
      rw [hzzero, norm_zero] at hnorm
      exact hy (norm_eq_zero.mp hnorm.symm)
    have hray := rayleigh_le_top A z hznonzero
    rw [← hyray] at hray
    change
      (continuousOperator A).reApplyInnerSelf z / ‖z‖ ^ 2 ≤
        (continuousOperator A).reApplyInnerSelf y / ‖y‖ ^ 2 at hray
    rw [hnorm] at hray
    exact (div_le_div_iff_of_pos_right
      (sq_pos_of_pos (norm_pos_iff.mpr hy))).mp hray
  have heigy := hself.hasEigenvector_of_isMaxOn hy hmax
  refine ⟨y, hy, ?_, fun i => abs_nonneg (x i)⟩
  have happly := heigy.apply_eq_smul
  simpa only [topEigenvalue, ne_eq, rayleigh, continuousOperator,
    LinearMap.coe_toContinuousLinearMap, Real.ringHom_apply] using happly

/-- A finite nonnegative symmetric matrix has a unit nonnegative vector for its top eigenvalue.
@isnad1 id=ex.2h2v.s9.e7d4f7104514 from=translated src=- shape=98827439 vocab=3627e385
-/
theorem exists_nonnegative_unit_topEigenvector (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hnonneg : ∀ i j : I, 0 ≤ A i j) :
    ∃ x : Space I, ‖x‖ = 1 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 ≤ x i := by
  obtain ⟨x, hx, heig, hxnonneg⟩ := exists_nonnegative_topEigenvector A hsymm hnonneg
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖x‖⁻¹ • x, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
    exact inv_mul_cancel₀ hnorm.ne'
  · rw [map_smul, heig]
    exact smul_comm _ _ _
  · intro i
    exact mul_nonneg (inv_nonneg.mpr hnorm.le) (hxnonneg i)

omit [Nonempty I] in
/--
@isnad1 id=eq.5h6v.s9.793e190ea8c1 from=translated src=- shape=8b81c97b vocab=cfb84323
-/
theorem eigenvector_zero_of_positive_edge (A : Matrix I I ℝ)
    (hnonneg : ∀ i j : I, 0 ≤ A i j)
    (x : Space I) (hx : ∀ i : I, 0 ≤ x i)
    (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x)
    {i j : I} (hzero : x i = 0) (hedge : 0 < A i j) :
    x j = 0 := by
  have hrow := congrArg (fun z : Space I => z i) heig
  change (∑ k : I, A i k * x k) = eigenvalue * x i at hrow
  rw [hzero, mul_zero] at hrow
  have hsingle : A i j * x j ≤ ∑ k : I, A i k * x k := by
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (hnonneg i k) (hx k))
      (Finset.mem_univ j)
  rw [hrow] at hsingle
  have hterm : A i j * x j = 0 :=
    le_antisymm hsingle (mul_nonneg (hnonneg i j) (hx j))
  exact (mul_eq_zero.mp hterm).resolve_left hedge.ne'

omit [Nonempty I] in
/--
@isnad1 id=eq.4h7v.s9.bfa1f32fb757 from=translated src=- shape=92ca90c2 vocab=1d6db096
-/
theorem eigenvector_zero_of_positive_path (A : Matrix I I ℝ)
    (hnonneg : ∀ i j : I, 0 ≤ A i j)
    (x : Space I) (hx : ∀ i : I, 0 ≤ x i)
    (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x)
    {i j : I} (p : @Quiver.Path I ⟨fun u v => PLift (0 < A u v)⟩ i j)
    (hzero : x i = 0) : x j = 0 := by
  induction p with
  | nil => exact hzero
  | @cons j k p e ih =>
      exact eigenvector_zero_of_positive_edge A hnonneg x hx
        eigenvalue heig ih e.down

omit [Nonempty I] in
/--
@isnad1 id=lt.4h5v.s9.31e6d0c1ecad from=translated src=- shape=2cdbc9cd vocab=193055fe
-/
theorem eigenvector_pos_of_irreducible (A : Matrix I I ℝ)
    (hirreducible : ConnectedNonnegativeMatrix A)
    (x : Space I) (hxzero : x ≠ 0) (hx : ∀ i : I, 0 ≤ x i)
    (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x) :
    ∀ i : I, 0 < x i := by
  intro i
  by_contra hnot
  have hzero : x i = 0 :=
    le_antisymm (le_of_not_gt hnot) (hx i)
  apply hxzero
  apply PiLp.ext
  intro j
  obtain ⟨p, _⟩ := hirreducible.connected i j
  simpa only [PiLp.zero_apply] using
    eigenvector_zero_of_positive_path A hirreducible.nonneg x hx eigenvalue heig p hzero

/--
@isnad1 id=ex.2h2v.s9.adc3a0d76335 from=translated src=- shape=6e2ff674 vocab=c5a03ca4
-/
theorem exists_positive_topEigenvector (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hirreducible : ConnectedNonnegativeMatrix A) :
    ∃ x : Space I, x ≠ 0 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 < x i := by
  obtain ⟨x, hx, heig, hnonneg⟩ :=
    exists_nonnegative_topEigenvector A hsymm hirreducible.nonneg
  exact ⟨x, hx, heig,
    eigenvector_pos_of_irreducible A hirreducible x hx hnonneg
      (topEigenvalue A) heig⟩

/--
@isnad1 id=ex.2h2v.s8.ef15d0c988ed from=translated src=- shape=57dfbf52 vocab=28b60424
-/
theorem exists_positive_unit_topEigenvector (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hirreducible : ConnectedNonnegativeMatrix A) :
    ∃ x : Space I,
      ‖x‖ = 1 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 < x i := by
  obtain ⟨x, hx, heig, hpos⟩ :=
    exists_positive_topEigenvector A hsymm hirreducible
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖x‖⁻¹ • x, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
    exact inv_mul_cancel₀ hnorm.ne'
  · rw [map_smul, heig]
    exact smul_comm _ _ _
  · intro i
    change 0 < ‖x‖⁻¹ * x i
    exact mul_pos (inv_pos.mpr hnorm) (hpos i)

omit [DecidableEq I] [Nonempty I] in
/--
@isnad1 id=eq.1h2v.s6.0806c4108592 from=translated src=- shape=4f7757d8 vocab=fd5a33a9
-/
theorem unit_coordinate_sq_sum {x : Space I} (hx : ‖x‖ = 1) :
    (∑ i : I, x i ^ 2) = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, hx]
  norm_num

/--
@isnad1 id=ex.2h2v.s7.446b838261fc from=translated src=- shape=00763a2d vocab=1cb2218f
-/
theorem exists_positive_unit_topEigenpair (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hirreducible : ConnectedNonnegativeMatrix A) :
    ∃ x : I → ℝ,
      (∀ i : I, 0 < x i) ∧
      (∑ i : I, x i ^ 2) = 1 ∧
      (∀ i : I, ∑ j : I, A i j * x j = topEigenvalue A * x i) := by
  obtain ⟨x, hunit, heig, hpos⟩ :=
    exists_positive_unit_topEigenvector A hsymm hirreducible
  refine ⟨fun i => x i, hpos, unit_coordinate_sq_sum hunit, ?_⟩
  intro i
  have h := congrArg (fun z : Space I => z i) heig
  exact h

end MetricCodes.Spherical.HigherHierarchyFinitePerron
