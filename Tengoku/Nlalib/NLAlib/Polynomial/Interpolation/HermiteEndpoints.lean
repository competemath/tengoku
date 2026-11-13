import Tengoku.Nlalib.NLAlib.Polynomial.Interpolation.Hermite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Hermite interpolation with prescribed simple endpoints

A multiple of the squared interior nodal polynomial corrects one prescribed endpoint;
an affine multiple corrects two. Interior values and first derivatives are preserved.
These actual interpolants are used for Radau and Lobatto derivative remainders.
-/

noncomputable section
open Polynomial Finset Set

namespace Lagrange

/-- The double-node Hermite interpolant corrected to match the additional value `ya`
at the simple endpoint `a`. The denominator may vanish in the total definition;
the endpoint theorem excludes an endpoint that is also an interior node.-/
def hermiteEndpointInterpolate {q : ℕ} (a ya : ℝ) (v y d : Fin q → ℝ) : ℝ[X] :=
  hermiteInterpolate univ v y d +
    C ((ya - (hermiteInterpolate univ v y d).eval a) / (nodal univ v).eval a ^ 2) *
      nodal univ v ^ 2

/-- The double-node Hermite interpolant corrected by an affine multiple of the nodal
square to match the two simple endpoint values `ya` and `yb`. Coincident endpoints or
nodal endpoints use total division; the matching theorems exclude them.-/
def hermiteTwoEndpointInterpolate {q : ℕ} (a b ya yb : ℝ) (v y d : Fin q → ℝ) : ℝ[X] :=
  let H := hermiteInterpolate univ v y d
  let π := nodal univ v
  let ca := (ya - H.eval a) / π.eval a ^ 2
  let cb := (yb - H.eval b) / π.eval b ^ 2
  H + (C ca + C ((cb - ca) / (b - a)) * (X - C a)) * π ^ 2

private theorem nodal_eval_ne_zero_of_forall_ne {q : ℕ} (v : Fin q → ℝ) {a : ℝ}
    (ha : ∀ i, a ≠ v i) : (nodal univ v).eval a ≠ 0 := by
  classical
  rw [eval_nodal]
  exact prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (ha i)

private theorem natDegree_hermiteInterpolate_le {q : ℕ} {v : Fin q → ℝ}
    (hv : Function.Injective v) (y d : Fin q → ℝ) :
    (hermiteInterpolate univ v y d).natDegree ≤ 2 * q := by
  by_cases hq : 0 < q
  · have hd := degree_hermiteInterpolate_lt
      (show (univ : Finset (Fin q)).Nonempty from ⟨⟨0, hq⟩, mem_univ _⟩) hv.injOn y d
    apply natDegree_le_of_degree_le
    simpa only [card_univ, Fintype.card_fin] using hd.le
  · have hq0 : q = 0 := by omega
    subst q
    simp [hermiteInterpolate]

/-- The one-endpoint corrected interpolant has degree below `2q+1`, including `q=0`.
@isnad1 id=lt.1h6v.s6.6319a87d1ff6 from=translated src=- shape=415b0d01 vocab=7dceae7d
-/
theorem degree_hermiteEndpointInterpolate_lt {q : ℕ} (a ya : ℝ) {v : Fin q → ℝ}
    (hv : Function.Injective v) (y d : Fin q → ℝ) :
    (hermiteEndpointInterpolate a ya v y d).degree < (2 * q + 1 : ℕ) := by
  have hd : (hermiteEndpointInterpolate a ya v y d).natDegree ≤ 2 * q := by
    unfold hermiteEndpointInterpolate
    apply (natDegree_add_le _ _).trans
    apply max_le (natDegree_hermiteInterpolate_le hv y d)
    apply (natDegree_C_mul_le _ _).trans
    simp [natDegree_pow, natDegree_nodal, mul_comm]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast (Nat.lt_succ_of_le hd))

/-- The two-endpoint corrected interpolant has degree below `2q+2`, including `q=0`.
@isnad1 id=lt.1h8v.s6.a076f387ee3f from=translated src=- shape=e2cd599b vocab=cdb13417
-/
theorem degree_hermiteTwoEndpointInterpolate_lt {q : ℕ} (a b ya yb : ℝ) {v : Fin q → ℝ}
    (hv : Function.Injective v) (y d : Fin q → ℝ) :
    (hermiteTwoEndpointInterpolate a b ya yb v y d).degree < (2 * q + 2 : ℕ) := by
  have hd : (hermiteTwoEndpointInterpolate a b ya yb v y d).natDegree ≤ 2 * q + 1 := by
    dsimp only [hermiteTwoEndpointInterpolate]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_hermiteInterpolate_le hv y d).trans (by omega)
    · have hlin : (C ((ya - (hermiteInterpolate univ v y d).eval a) /
          (nodal univ v).eval a ^ 2) +
        C (((yb - (hermiteInterpolate univ v y d).eval b) / (nodal univ v).eval b ^ 2 -
          (ya - (hermiteInterpolate univ v y d).eval a) / (nodal univ v).eval a ^ 2) /
            (b - a)) * (X - C a)).natDegree ≤ 1 := by compute_degree
      apply (natDegree_mul_le.trans (Nat.add_le_add_right hlin _)).trans
      simp [natDegree_pow, natDegree_nodal]
      omega
  exact degree_le_natDegree.trans_lt (by exact_mod_cast (Nat.lt_succ_of_le hd))

/-- The one-endpoint correction retains the interior function values.
@isnad1 id=eq.1h7v.s5.dc453a6e7c95 from=translated src=- shape=3b63435e vocab=ef9033d8
-/
theorem eval_hermiteEndpointInterpolate_at_node {q : ℕ} (a ya : ℝ) {v : Fin q → ℝ}
    (hv : Function.Injective v) (y d : Fin q → ℝ) (i : Fin q) :
    (hermiteEndpointInterpolate a ya v y d).eval (v i) = y i := by
  simp only [hermiteEndpointInterpolate, eval_add, eval_mul, eval_C, eval_pow,
    eval_nodal_at_node (mem_univ i), eval_hermiteInterpolate_at_node hv.injOn y d (mem_univ i)]
  ring

/-- The one-endpoint correction retains the interior first derivatives.
@isnad1 id=eq.1h7v.s7.ec3d173c6af5 from=translated src=- shape=9bcd8ab3 vocab=b44424a0
-/
theorem eval_derivative_hermiteEndpointInterpolate_at_node {q : ℕ} (a ya : ℝ)
    {v : Fin q → ℝ} (hv : Function.Injective v) (y d : Fin q → ℝ) (i : Fin q) :
    (hermiteEndpointInterpolate a ya v y d).derivative.eval (v i) = d i := by
  simp [hermiteEndpointInterpolate, derivative_add, derivative_pow,
    eval_nodal_at_node (mem_univ i),
    eval_derivative_hermiteInterpolate_at_node hv.injOn y d (mem_univ i)]

/-- The one-endpoint correction matches its prescribed endpoint value.
@isnad1 id=eq.1h6v.s5.d77ccf4bd682 from=translated src=- shape=3fee2199 vocab=8c4abce0
-/
theorem eval_hermiteEndpointInterpolate_endpoint {q : ℕ} (a ya : ℝ) (v y d : Fin q → ℝ)
    (ha : ∀ i, a ≠ v i) : (hermiteEndpointInterpolate a ya v y d).eval a = ya := by
  have hπ := nodal_eval_ne_zero_of_forall_ne v ha
  simp only [hermiteEndpointInterpolate, eval_add, eval_mul, eval_C, eval_pow]
  field_simp
  ring

/-- The two-endpoint correction retains the interior function values.
@isnad1 id=eq.1h9v.s5.df365827842a from=translated src=- shape=7b608c47 vocab=9ea26af0
-/
theorem eval_hermiteTwoEndpointInterpolate_at_node {q : ℕ} (a b ya yb : ℝ)
    {v : Fin q → ℝ} (hv : Function.Injective v) (y d : Fin q → ℝ) (i : Fin q) :
    (hermiteTwoEndpointInterpolate a b ya yb v y d).eval (v i) = y i := by
  simp [hermiteTwoEndpointInterpolate, eval_nodal_at_node (mem_univ i),
    eval_hermiteInterpolate_at_node hv.injOn y d (mem_univ i)]

/-- The two-endpoint correction retains the interior first derivatives.
@isnad1 id=eq.1h9v.s7.297cd45ad961 from=translated src=- shape=1809a052 vocab=42f87012
-/
theorem eval_derivative_hermiteTwoEndpointInterpolate_at_node {q : ℕ} (a b ya yb : ℝ)
    {v : Fin q → ℝ} (hv : Function.Injective v) (y d : Fin q → ℝ) (i : Fin q) :
    (hermiteTwoEndpointInterpolate a b ya yb v y d).derivative.eval (v i) = d i := by
  simp [hermiteTwoEndpointInterpolate, derivative_add, derivative_mul,
    derivative_pow, eval_nodal_at_node (mem_univ i),
    eval_derivative_hermiteInterpolate_at_node hv.injOn y d (mem_univ i)]

/-- The two-endpoint correction matches its left prescribed value.
@isnad1 id=eq.1h8v.s5.b7b2ef0db9a1 from=translated src=- shape=36875158 vocab=dc8cea8b
-/
theorem eval_hermiteTwoEndpointInterpolate_left {q : ℕ} (a b ya yb : ℝ)
    (v y d : Fin q → ℝ) (ha : ∀ i, a ≠ v i) :
    (hermiteTwoEndpointInterpolate a b ya yb v y d).eval a = ya := by
  have hπ := nodal_eval_ne_zero_of_forall_ne v ha
  simp only [hermiteTwoEndpointInterpolate, eval_add, eval_mul, eval_C, eval_pow,
    eval_sub, eval_X, sub_self, mul_zero, add_zero]
  field_simp
  ring

/-- The two-endpoint correction matches its right prescribed value.
@isnad1 id=eq.3h8v.s6.b1a66244d63b from=translated src=- shape=c796f670 vocab=dc8cea8b
-/
theorem eval_hermiteTwoEndpointInterpolate_right {q : ℕ} (a b ya yb : ℝ)
    (v y d : Fin q → ℝ) (hab : a ≠ b) (ha : ∀ i, a ≠ v i) (hb : ∀ i, b ≠ v i) :
    (hermiteTwoEndpointInterpolate a b ya yb v y d).eval b = yb := by
  have hπa := nodal_eval_ne_zero_of_forall_ne v ha
  have hπb := nodal_eval_ne_zero_of_forall_ne v hb
  simp only [hermiteTwoEndpointInterpolate, eval_add, eval_mul, eval_C, eval_pow,
    eval_sub, eval_X]
  field_simp [sub_ne_zero.mpr hab.symm]
  ring

end Lagrange
