/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
module

public import Tengoku

/-!
# locating the roots of Lehmer's polynomial via its trace quintic.
`L` is reciprocal, so with `y = x + 1/x` it factors through a degree-5 polynomial:
  `L(x) = x⁵ · q(x + 1/x)`,  `q(y) = y⁵ + y⁴ − 5y³ − 5y² + 4y + 3`,
and a root of `L` lies on `|z| = 1` iff its trace `y = x + 1/x` lies in `[−2, 2]`
(`x = e^{iθ}`, `y = 2 cos θ`).  Salem's picture — 8 roots on the unit circle, one
reciprocal pair `{λ, 1/λ}` off it — therefore reduces to "`q` has 4 real roots in
`(−2, 2)` and one root in `(2, 21/10)`": five intermediate-value sign checks,
carried out here.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

@[expose] public section

namespace LehmerE10

/-- Lehmer's polynomial as a function on ℂ. -/
noncomputable def lehmerC (z : ℂ) : ℂ :=
  z ^ 10 + z ^ 9 - z ^ 7 - z ^ 6 - z ^ 5 - z ^ 4 - z ^ 3 + z + 1

/-- The degree-5 TRACE polynomial over ℝ (for root location). -/
def traceQ (y : ℝ) : ℝ := y ^ 5 + y ^ 4 - 5 * y ^ 3 - 5 * y ^ 2 + 4 * y + 3

/-- Trace polynomial over ℂ. -/
noncomputable def traceQC (y : ℂ) : ℂ := y ^ 5 + y ^ 4 - 5 * y ^ 3 - 5 * y ^ 2 + 4 * y + 3

/--
@isnad1 id=eq.0h1v.s3.6cae6ceafa9c from=translated src=- shape=c14c2a45 vocab=1b7bf53d
-/
@[simp] theorem traceQC_ofReal (y : ℝ) : traceQC (y : ℂ) = (traceQ y : ℂ) := by
  unfold traceQC traceQ; push_cast; ring

/-- **THE RECIPROCAL → TRACE REDUCTION: `L(x) = x⁵ · q(x + 1/x)`, PROVEN.**
@isnad1 id=eq.1h1v.s6.6b113cc278c0 from=translated src=- shape=6c84cb74 vocab=b126ab1b
-/
theorem lehmer_trace_reduction (z : ℂ) (hz : z ≠ 0) :
    lehmerC z = z ^ 5 * traceQC (z + 1 / z) := by
  unfold lehmerC traceQC
  field_simp
  ring

/-! ### The five real roots of the trace polynomial (IVT). -/

private theorem traceQ_cont : Continuous traceQ := by unfold traceQ; fun_prop

/-- A trace root in `(−2, −3/2)` (endpoints: q(−2)=−1 < 0 < 3/32 = q(−3/2)).
@isnad1 id=ex.0h0v.s6.07c6d894adb1 from=translated src=- shape=ebbecc40 vocab=abd56835
-/
theorem traceQ_root_1 : ∃ y ∈ Set.Ioo (-2 : ℝ) (-3/2), traceQ y = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (traceQ (-2)) (traceQ (-3/2)) := by
    rw [Set.mem_Ioo]; unfold traceQ; norm_num
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo (by norm_num : (-2:ℝ) ≤ -3/2)
    traceQ_cont.continuousOn h
  exact ⟨y, hy, hy0⟩

/-- A trace root in `(−3/2, −1)`.
@isnad1 id=ex.0h0v.s5.7d67ad1b2240 from=translated src=- shape=82e69b8d vocab=abd56835
-/
theorem traceQ_root_2 : ∃ y ∈ Set.Ioo (-3/2 : ℝ) (-1), traceQ y = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (traceQ (-1)) (traceQ (-3/2)) := by
    rw [Set.mem_Ioo]; unfold traceQ; norm_num
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo' (by norm_num : (-3/2:ℝ) ≤ -1)
    traceQ_cont.continuousOn h
  exact ⟨y, hy, hy0⟩

/-- A trace root in `(−1, 0)`.
@isnad1 id=ex.0h0v.s5.40781fb539b0 from=translated src=- shape=91876fed vocab=e3107dbf
-/
theorem traceQ_root_3 : ∃ y ∈ Set.Ioo (-1 : ℝ) 0, traceQ y = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (traceQ (-1)) (traceQ 0) := by
    rw [Set.mem_Ioo]; unfold traceQ; norm_num
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo (by norm_num : (-1:ℝ) ≤ 0)
    traceQ_cont.continuousOn h
  exact ⟨y, hy, hy0⟩

/-- A trace root in `(0, 1)`.
@isnad1 id=ex.0h0v.s5.daa6499d5e8d from=translated src=- shape=57cd9b24 vocab=41245c08
-/
theorem traceQ_root_4 : ∃ y ∈ Set.Ioo (0 : ℝ) 1, traceQ y = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (traceQ 1) (traceQ 0) := by
    rw [Set.mem_Ioo]; unfold traceQ; norm_num
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo' (by norm_num : (0:ℝ) ≤ 1)
    traceQ_cont.continuousOn h
  exact ⟨y, hy, hy0⟩

/-- The Salem trace root in `(2, 21/10)` — `y_L = λ_L + 1/λ_L > 2`, the off-circle
reciprocal pair.
@isnad1 id=ex.0h0v.s5.102714fe3946 from=translated src=- shape=779eb4e0 vocab=aa2b15c7
-/
theorem traceQ_root_salem : ∃ y ∈ Set.Ioo (2 : ℝ) (21/10), traceQ y = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (traceQ 2) (traceQ (21/10)) := by
    rw [Set.mem_Ioo]; unfold traceQ; norm_num
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo (by norm_num : (2:ℝ) ≤ 21/10)
    traceQ_cont.continuousOn h
  exact ⟨y, hy, hy0⟩

/-! ### On-circle Lehmer roots from trace roots in `(−2,2)`. -/

/-- Each trace root in `(−2,2)` gives a root of `L` on `|z| = 1`: for `y₀ ∈ (−2,2)`
    with `q(y₀) = 0`, the explicit `z = (y₀ + i√(4−y₀²))/2` has `‖z‖ = 1` and
    `z + 1/z = y₀`, so by the trace reduction `L(z) = z⁵ · q(y₀) = 0`.
@isnad1 id=ex.2h1v.s6.8993933afd10 from=translated src=- shape=a50b1ea3 vocab=ddd224ad
-/
theorem lehmer_root_on_circle (y₀ : ℝ) (h0 : traceQ y₀ = 0) (hmem : y₀ ∈ Set.Ioo (-2 : ℝ) 2) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ lehmerC z = 0 := by
  obtain ⟨hlo, hhi⟩ := hmem
  have h4 : (0:ℝ) ≤ 4 - y₀ ^ 2 := by nlinarith
  set r : ℝ := Real.sqrt (4 - y₀ ^ 2) with hrdef
  have hrr : r * r = 4 - y₀ ^ 2 := Real.mul_self_sqrt h4
  set z : ℂ := ⟨y₀ / 2, r / 2⟩ with hzdef
  have hns : Complex.normSq z = 1 := by rw [hzdef, Complex.normSq_mk]; nlinarith [hrr]
  have hznorm : ‖z‖ = 1 := by rw [Complex.norm_def, hns, Real.sqrt_one]
  have hz0 : z ≠ 0 := Complex.normSq_pos.mp (by rw [hns]; norm_num)
  have hzre : z.re = y₀ / 2 := by rw [hzdef]
  have h1z : 1 / z = (starRingEnd ℂ) z := by
    rw [one_div, Complex.inv_def, hns]; simp
  have hsum : z + 1 / z = (y₀ : ℂ) := by
    rw [h1z, Complex.add_conj, hzre]; push_cast; ring
  refine ⟨z, hznorm, ?_⟩
  rw [lehmer_trace_reduction z hz0, hsum, traceQC_ofReal, h0, Complex.ofReal_zero, mul_zero]

/-- `L` has a root on the unit circle (combining the trace root in `(−1,0)` with
    `lehmer_root_on_circle`).
@isnad1 id=ex.0h0v.s4.5798b46e667b from=translated src=- shape=db1b1ff3 vocab=5ff56a6d
-/
theorem elliptic_root_on_circle : ∃ z : ℂ, ‖z‖ = 1 ∧ lehmerC z = 0 := by
  obtain ⟨y, hy, hy0⟩ := traceQ_root_3
  exact lehmer_root_on_circle y hy0 ⟨by linarith [hy.1], by linarith [hy.2]⟩

end LehmerE10
