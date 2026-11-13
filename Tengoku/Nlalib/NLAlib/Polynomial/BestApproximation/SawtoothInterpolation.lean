import Tengoku.Nlalib.NLAlib.Polynomial.Chebyshev.ChebyshevAliasing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Odd trigonometric interpolation of the sawtooth

The odd interpolant is constructed as `sin(t) r(cos(t))`, where `r` is the Lagrange
interpolant of the divided sawtooth values at the interior canonical Chebyshev nodes.
This avoids an unproved trigonometric interpolation-existence premise in sharp Jackson.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real

namespace NLAlib

/-- The sine-divided Lagrange polynomial underlying the sharp Jackson sawtooth interpolant.
Source: Arnold, *Numerical Analysis* lecture notes, §1.2 (Jackson's theorem). Helper for `jackson-lipschitz`.
Atlas `jackson-lipschitz` (construction helper).-/
def sawtoothSineInterp (n : ℕ) : ℝ[X] :=
  Lagrange.interpolate (range n) (fun j => node (n + 1) (j + 1))
    (fun j => (Real.pi - (j + 1 : ℕ) * Real.pi / (n + 1)) / sin ((j + 1 : ℕ) * Real.pi / (n + 1)))

/-- The explicit odd trigonometric interpolant `τ_n(t)=sin(t) r_n(cos(t))`.
Source: Arnold, *Numerical Analysis* lecture notes, §1.2 (Jackson's theorem). Helper for `jackson-lipschitz`.
Atlas `jackson-lipschitz` (construction helper).-/
def sawtoothApprox (n : ℕ) (t : ℝ) : ℝ := sin t * (sawtoothSineInterp n).eval (cos t)

/-- Interior Chebyshev grid angles lie strictly between zero and Real.pi.
Source: canonical Chebyshev nodes; helper for sharp Jackson (`jackson-lipschitz`).
@isnad1 id=mem.1h2v.s6.0b93a37de39e from=translated src=- shape=6d9fa547 vocab=d0b85ecb
-/
theorem sawtooth_angle_mem_Ioo {n j : ℕ} (hj : j < n) :
    ((j + 1 : ℕ) : ℝ) * Real.pi / (n + 1) ∈ Set.Ioo (0 : ℝ) Real.pi := by
  constructor
  · positivity
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)]
    have hjs : ((j + 1 : ℕ) : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hj
    nlinarith [pi_pos]

/-- The sine at every interior interpolation angle is positive.
Source: canonical Chebyshev nodes; helper for sharp Jackson (`jackson-lipschitz`).
@isnad1 id=lt.1h2v.s6.3e16b04b6ee7 from=translated src=- shape=e46d864b vocab=4e6103e7
-/
theorem sin_sawtooth_angle_pos {n j : ℕ} (hj : j < n) :
    0 < sin (((j + 1 : ℕ) : ℝ) * Real.pi / (n + 1)) :=
  sin_pos_of_pos_of_lt_pi (sawtooth_angle_mem_Ioo hj).1 (sawtooth_angle_mem_Ioo hj).2

/-- The interior nodal map of the divided-sine interpolation is injective.
Source: Mathlib `strictAntiOn_node`; helper for sharp Jackson (`jackson-lipschitz`).
@isnad1 id=injon.0h1v.s5.ff81b2d12472 from=translated src=- shape=7ee54ffa vocab=0fe6d3ae
-/
theorem sawtooth_node_injOn (n : ℕ) :
    Set.InjOn (fun j => node (n + 1) (j + 1)) (range n : Set ℕ) := by
  intro i hi j hj hij
  have h := (strictAntiOn_node (n + 1)).injOn
    (mem_range.mpr (by have := mem_range.mp hi; omega))
    (mem_range.mpr (by have := mem_range.mp hj; omega)) hij
  omega

/-- The divided-sine interpolating polynomial has degree below `n`.
Source: Lagrange interpolation; helper for sharp Jackson (`jackson-lipschitz`).
@isnad1 id=lt.0h1v.s4.01ab1d3de9df from=translated src=- shape=95ba4981 vocab=e1ac72a5
-/
theorem degree_sawtoothSineInterp_lt (n : ℕ) : (sawtoothSineInterp n).degree < n := by
  have h := Lagrange.degree_interpolate_lt
    (fun j => (Real.pi - (j + 1 : ℕ) * Real.pi / (n + 1)) / sin ((j + 1 : ℕ) * Real.pi / (n + 1)))
    (sawtooth_node_injOn n)
  simpa only [card_range, sawtoothSineInterp] using h

/-- The explicit odd trigonometric polynomial takes the sawtooth value at every positive
interior half-period grid point.
Helper for `jackson-lipschitz`.
@isnad1 id=eq.1h2v.s6.31126cca708c from=translated src=- shape=0577affa vocab=7e714121
-/
theorem sawtoothApprox_grid_eq {n j : ℕ} (hj : j < n) :
    sawtoothApprox n (((j + 1 : ℕ) : ℝ) * Real.pi / (n + 1)) =
      Real.pi - ((j + 1 : ℕ) : ℝ) * Real.pi / (n + 1) := by
  have h := Lagrange.eval_interpolate_at_node
    (fun j => (Real.pi - (j + 1 : ℕ) * Real.pi / (n + 1)) / sin ((j + 1 : ℕ) * Real.pi / (n + 1)))
    (sawtooth_node_injOn n) (mem_range.mpr hj)
  change (sawtoothSineInterp n).eval (node (n + 1) (j + 1)) = _ at h
  unfold sawtoothApprox
  simp only [node, Nat.cast_add, Nat.cast_one] at h ⊢
  rw [h]
  exact mul_div_cancel₀ _ (by simpa only [Nat.cast_add, Nat.cast_one] using (sin_sawtooth_angle_pos hj).ne')

/-- The zero-degree sawtooth interpolant vanishes identically.
Helper for `jackson-lipschitz` (degenerate case).
@isnad1 id=eq.0h1v.s4.cbf2ed3cc367 from=translated src=- shape=a0dd47fb vocab=291bd936
-/
@[simp] theorem sawtoothApprox_zero (t : ℝ) : sawtoothApprox 0 t = 0 := by
  simp [sawtoothApprox, sawtoothSineInterp]

/-- The odd sawtooth interpolant vanishes at the origin.
Helper for `jackson-lipschitz` (Jackson's theorem through the sawtooth function).
@isnad1 id=eq.0h1v.s4.be6c5c3e1ec3 from=translated src=- shape=9b4d794a vocab=291bd936
-/
@[simp] theorem sawtoothApprox_at_zero (n : ℕ) : sawtoothApprox n 0 = 0 := by simp [sawtoothApprox]

/-- The odd sawtooth interpolant vanishes at Real.pi.
Helper for `jackson-lipschitz` (Jackson's theorem through the sawtooth function).
@isnad1 id=eq.0h1v.s3.360e6db51103 from=translated src=- shape=8d9dc71e vocab=b8f32fab
-/
@[simp] theorem sawtoothApprox_at_pi (n : ℕ) : sawtoothApprox n Real.pi = 0 := by simp [sawtoothApprox]

end NLAlib
