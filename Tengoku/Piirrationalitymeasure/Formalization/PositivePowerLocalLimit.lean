import Tengoku.Piirrationalitymeasure.Formalization.PositivePowerCharacteristic
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientLocalLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The local Gaussian limit for all positive-power generating functions. -/

namespace PiIrrationality.PositivePower

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

variable (u v : ℕ) {d : ℕ} (hd : 0 < d)

theorem law_memLp_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    MemLp (fun k : ℕ => (k : ℝ)) 2 (law u v hd x hx0 hx1 1).toMeasure := by
  apply memLp_of_mem_interior_integrableExpSet _ 2
  exact law_interior_integrableExpSet u v hd hx0 hx1 (by simpa using hx1)

theorem centered_memLp_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    MemLp (fun k : ℕ => (k : ℝ) - mean u v d x) 2
      (law u v hd x hx0 hx1 1).toMeasure :=
  (law_memLp_two u v hd hx0 hx1).sub (memLp_const _)

include hd in
theorem centered_integral {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (q : ℕ) (hm : mean u v d x = (q : ℝ)) (n : ℕ) :
    (∫ t in -Real.pi..Real.pi, centeredCharacteristic u v d x t ^ n) =
      (2 * Real.pi : ℂ) * (probability u v d x n (q * n) : ℂ) := by
  have h := lattice_fourier_inversion (law u v hd x hx0 hx1 n) (q * n)
  simp_rw [law_charFun u v hd hx0 hx1, law_toReal] at h
  have he (t : ℝ) : centeredCharacteristic u v d x t ^ n =
      characteristic u v d x t ^ n *
        Complex.exp (-((q * n : ℕ) : ℂ) * (t : ℂ) * Complex.I) := by
    simp only [centeredCharacteristic, mul_pow, ← Complex.exp_nat_mul, hm,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_natCast, Nat.cast_mul]
    congr 1
    congr 1
    ring
  simpa only [← he] using h

end PiIrrationality.PositivePower
