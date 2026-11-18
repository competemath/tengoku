import Tengoku.WasowAsymptoticsLean.WasowPencilCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms scaleEquiv_apply` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms natDegree_scaleEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms degreeMass_scaleEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms minorGCD_smul_C` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms degreeMass_smul_C` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pencil_smul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms degreeMass_smul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms isNilpotent_unscale` (it only prints; the queue checks the axioms of every declaration). -/

/-! Nonzero scalar factors produced by actual ramification preserve the full
characteristic-pencil degree invariant. The eigenvalue and nilpotence scaling
are handled explicitly, so the ramification factor is never silently removed. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace WasowPencilScaling
open WasowPencilReduction WasowReductionDescent WasowPencilDescent

/-- Invertible substitution of the polynomial variable by `X/c`.-/
def scaleEquiv (c : ℂ) (hc : c ≠ 0) : ℂ[X] ≃ₐ[ℂ] ℂ[X] :=
  Polynomial.algEquivOfCompEqX (Polynomial.C c⁻¹ * X) (Polynomial.C c * X)
    (by simp [← mul_assoc, ← Polynomial.C_mul, hc])
    (by simp [← mul_assoc, ← Polynomial.C_mul, hc])

/--
@isnad1 id=eq.1h2v.s7.7385a9d5714d from=translated src=- shape=1fa884f9 vocab=1c5912cd
-/
theorem scaleEquiv_apply (c : ℂ) (hc : c ≠ 0) (p : ℂ[X]) :
    scaleEquiv c hc p = p.comp (Polynomial.C c⁻¹ * X) := by
  simp [scaleEquiv, ← Polynomial.comp_eq_aeval]

/--
@isnad1 id=eq.1h2v.s6.b3ebc115d027 from=translated src=- shape=1002c8e8 vocab=13bd79a2
-/
theorem natDegree_scaleEquiv (c : ℂ) (hc : c ≠ 0) (p : ℂ[X]) :
    (scaleEquiv c hc p).natDegree = p.natDegree := by
  rw [scaleEquiv_apply, Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul_X _ (inv_ne_zero hc), mul_one]

variable {ι : Type*} [Fintype ι]

/--
@isnad1 id=eq.1h3v.s6.2012158ff1e2 from=translated src=- shape=0f64b4b7 vocab=0f3f126b
-/
theorem degreeMass_scaleEquiv (T : Matrix ι ι ℂ[X]) (c : ℂ) (hc : c ≠ 0) :
    WasowPencilDescent.degreeMass (T.map (scaleEquiv c hc)) =
      WasowPencilDescent.degreeMass T := by
  unfold WasowPencilDescent.degreeMass
  apply Finset.sum_congr rfl
  intro k _
  have hh := Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated
      (WasowPencilSimilarity.minorGCD_map_associated T (scaleEquiv c hc).toRingEquiv k))
  exact hh.symm.trans (natDegree_scaleEquiv c hc _)

/-- Multiplication by a nonzero constant polynomial is an actual invertible
row transformation, hence leaves every normalized determinantal divisor fixed.
@isnad1 id=eq.1h4v.s6.b42cac83a27a from=translated src=- shape=de53cfcc vocab=97cad45f
-/
theorem minorGCD_smul_C [DecidableEq ι] (T : Matrix ι ι ℂ[X])
    (c : ℂ) (hc : c ≠ 0) (k : ℕ) :
    minorGCD (Polynomial.C c • T) k = minorGCD T k := by
  have hi : (Polynomial.C c⁻¹ • (1 : Matrix ι ι ℂ[X])) * (Polynomial.C c • 1) = 1 := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_smul]
  simpa only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one] using
    WasowMinorEquivalence.minorGCD_equivalent
      (Polynomial.C c • (1 : Matrix ι ι ℂ[X])) (Polynomial.C c⁻¹ • 1)
      T 1 1 hi (Matrix.one_mul 1) k

/--
@isnad1 id=eq.1h3v.s6.a87e54165602 from=translated src=- shape=aa77cdcb vocab=27deee44
-/
theorem degreeMass_smul_C [DecidableEq ι] (T : Matrix ι ι ℂ[X])
    (c : ℂ) (hc : c ≠ 0) :
    WasowPencilDescent.degreeMass (Polynomial.C c • T) = WasowPencilDescent.degreeMass T := by
  unfold WasowPencilDescent.degreeMass
  simp_rw [minorGCD_smul_C T c hc]

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {h : σ → ℕ}

omit [Fintype σ] in
/-- Exact polynomial identity for the characteristic pencil of the scaled matrix.
@isnad1 id=eq.1h4v.s8.c8d89f41780c from=translated src=- shape=4b0aac99 vocab=5cdfe385
-/
theorem pencil_smul (C : Matrix (OldIndex h) (OldIndex h) ℂ) (c : ℂ) (hc : c ≠ 0) :
    pencil (c • C) = Polynomial.C c • ((pencil C).map (scaleEquiv c hc)) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    have hi : Polynomial.C c * Polynomial.C c⁻¹ = (1 : ℂ[X]) := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1]
    simp [pencil, scaleEquiv_apply, smul_eq_mul, mul_sub, ← mul_assoc, hi]
  · simp [pencil, scaleEquiv_apply, hij, smul_eq_mul, Polynomial.C_mul]

/-- The actual nonzero ramification multiplier does not affect degree mass.
@isnad1 id=eq.1h4v.s7.93fdb052fa6d from=translated src=- shape=a59bbbf5 vocab=15e81d5f
-/
theorem degreeMass_smul (C : Matrix (OldIndex h) (OldIndex h) ℂ) (c : ℂ) (hc : c ≠ 0) :
    WasowPencilDescent.degreeMass (pencil (c • C)) = WasowPencilDescent.degreeMass (pencil C) := by
  rw [pencil_smul C c hc, degreeMass_smul_C _ c hc, degreeMass_scaleEquiv _ c hc]

/-- The translated eigenvalue scales by `1/c`; nilpotence is proved using
the actual scalar multiplication of the translated matrix.
@isnad1 id=isnilpot.2h4v.s8.4857826a1d21 from=translated src=- shape=57722fb1 vocab=d0b7a86f
-/
theorem isNilpotent_unscale [DecidableEq ι] (C : Matrix ι ι ℂ)
    (c α : ℂ) (hc : c ≠ 0) (hN : IsNilpotent (c • C - α • 1)) :
    IsNilpotent (C - (α / c) • 1) := by
  have he : c⁻¹ • (c • C - α • 1) = C - (α / c) • 1 := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul, smul_smul]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  rw [← he]
  exact hN.smul c⁻¹

end WasowPencilScaling
