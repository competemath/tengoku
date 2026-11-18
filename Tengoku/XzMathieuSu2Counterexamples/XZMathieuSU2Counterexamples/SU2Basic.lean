import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.SphereMomentRecurrence
import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.Bernstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxRecDepth 4000
noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples.Hopf

def definingMatrixRepresentation : MatrixRepresentation SU2 (Fin 2) where
  toMonoidHom := (Matrix.specialUnitaryGroup (Fin 2) ℂ).subtype
  continuous_entry i j := continuous_subtype_val.matrix_elem i j

def su2Entry (i j : Fin 2) : representativeFunctions (G := SU2) :=
  ⟨definingMatrixRepresentation.entry i j, entry_mem_representative _ i j⟩

/--
@isnad1 id=eq.0h3v.s13.d9fd42799d17 from=translated src=- shape=a5551314 vocab=a23adfc6
-/
@[simp] theorem su2Entry_apply (i j : Fin 2) (g : SU2) : (su2Entry i j).val g = g.val i j := rfl

def basePoint : Sphere := ⟨(1,0), by simp [a]⟩

/--
@isnad1 id=eq.0h1v.s10.7959ae0cd4b3 from=translated src=- shape=91080d1e vocab=02e0d18e
-/
theorem su2_smul_basePoint (g : SU2) : g • basePoint = su2ToSphere g := by
  apply Subtype.ext
  change g • ((1,0) : Space) = (g.val 0 0, g.val 1 0)
  simp [su2_smul_apply]

/--
@isnad1 id=eq.1h1v.s10.534d42f095db from=translated src=- shape=c3c43283 vocab=a87561e7
-/
theorem su2_firstColumn_integral {f : Sphere → ℂ} (hf : Continuous f) :
    (∫ g : SU2, f (su2ToSphere g) ∂normalizedHaar SU2) = ∫ z, f z ∂surfaceMeasure := by
  simpa only [su2_smul_basePoint] using su2_orbit_integral basePoint hf

/-- Matrix layout in the paper is [a,c;b,d].-/
def entryMonomial (r s t u : ℕ) (g : SU2) : ℂ :=
  g.val 0 0 ^ r * g.val 1 0 ^ s * g.val 0 1 ^ t * g.val 1 1 ^ u

/--
@isnad1 id=continuo.0h4v.s9.f89595910aa1 from=translated src=- shape=036edb5c vocab=9113ff1c
-/
@[fun_prop] theorem continuous_entryMonomial (r s t u : ℕ) :
    Continuous (entryMonomial r s t u) :=
  (((continuous_subtype_val.matrix_elem 0 0).pow r).mul
    ((continuous_subtype_val.matrix_elem 1 0).pow s)).mul
    ((continuous_subtype_val.matrix_elem 0 1).pow t) |>.mul
    ((continuous_subtype_val.matrix_elem 1 1).pow u)

/--
@isnad1 id=eq.0h5v.s8.5e304accb9fe from=translated src=- shape=6b91bd4e vocab=a33d87fb
-/
theorem entryMonomial_sphere (r s t u : ℕ) (g : SU2) :
    entryMonomial r s t u g = (-1 : ℂ)^t * sphereMonomial r u s t (su2ToSphere g) := by
  rw [entryMonomial, (su2_entries g).1, (su2_entries g).2]
  change g.val 0 0 ^ r * g.val 1 0 ^ s * (-star (g.val 1 0))^t * star (g.val 0 0)^u =
    (-1 : ℂ)^t * (g.val 0 0 ^ r * star (g.val 0 0)^u * g.val 1 0^s * star (g.val 1 0)^t)
  rw [neg_pow]
  ring

/--
@isnad1 id=eq.1h4v.s10.480ea868a85f from=translated src=- shape=822e09ed vocab=c029786e
-/
theorem entryMonomial_integral_left_zero (r s t u : ℕ) (h : r+t ≠ u+s) :
    (∫ g : SU2, entryMonomial r s t u g ∂normalizedHaar SU2) = 0 := by
  simp_rw [entryMonomial_sphere]
  rw [integral_const_mul, su2_firstColumn_integral (continuous_sphereMonomial r u s t),
    sphereMonomial_integral_zero r u s t h, mul_zero]

/--
@isnad1 id=eq.0h2v.s10.f34059c4abab from=translated src=- shape=00fbdcc0 vocab=10be7232
-/
theorem entryMonomial_integral_diagonal (r s : ℕ) :
    (∫ g : SU2, entryMonomial r s s r g ∂normalizedHaar SU2) =
      (-1 : ℂ)^s * ((r.factorial : ℂ) * s.factorial / (r+s+1).factorial) := by
  simp_rw [entryMonomial_sphere]
  rw [integral_const_mul, su2_firstColumn_integral (continuous_sphereMonomial r r s s)]
  rw [← mixedMoment, mixedMoment_factorial]

/-- The monomial specialization required by the counterexample.
@isnad1 id=eq.0h3v.s10.1f02dfd7af30 from=translated src=- shape=ae733bb3 vocab=b9ffbae9
-/
theorem balanced_entry_integral (r s t : ℕ) :
    (∫ g : SU2, entryMonomial r s t r g ∂normalizedHaar SU2) =
      if s = t then (-1 : ℂ)^s * ((r.factorial : ℂ) * s.factorial / (r+s+1).factorial) else 0 := by
  split_ifs with h
  · subst t; exact entryMonomial_integral_diagonal r s
  · exact entryMonomial_integral_left_zero r s t r (by omega)

/--
@isnad1 id=eq.0h1v.s10.cf07839ca2e8 from=translated src=- shape=318fdafd vocab=2d832ab3
-/
theorem su2_determinant_relation (g : SU2) :
    g.val 0 0 * g.val 1 1 - g.val 1 0 * g.val 0 1 = 1 := by
  have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  simpa [Matrix.det_fin_two, mul_comm] using h

/--
@isnad1 id=eq.0h6v.s10.aa70419d9719 from=translated src=- shape=a405e722 vocab=f97b0c4b
-/
theorem entryMonomial_right_phase (r s t u : ℕ) (θ : ℝ) (g : SU2) :
    entryMonomial r s t u (g * diagonalPhase θ) =
      Complex.exp (((r : ℂ)+s-t-u)*Complex.I*θ) * entryMonomial r s t u g := by
  have hc : star (Complex.exp (Complex.I * θ)) = Complex.exp (-Complex.I * θ) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  have hpow : Complex.exp (Complex.I * θ)^(r+s) *
      star (Complex.exp (Complex.I * θ))^(t+u) =
      Complex.exp (((r : ℂ)+s-t-u)*Complex.I*θ) := by
    rw [hc, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hpow]
  simp only [entryMonomial, diagonalPhase, sphereToSU2, sphereMatrix,
    Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [Matrix.of_apply, mul_pow, pow_add]
  ring

/--
@isnad1 id=eq.1h4v.s10.68213178c3e4 from=translated src=- shape=73b9f80b vocab=c029786e
-/
theorem entryMonomial_integral_right_zero (r s t u : ℕ) (h : r+s ≠ t+u) :
    (∫ g : SU2, entryMonomial r s t u g ∂normalizedHaar SU2) = 0 := by
  let n : ℝ := (r : ℝ)+s-t-u
  have hn : n ≠ 0 := by
    dsimp [n]
    intro hn
    have he : (r : ℝ)+s = t+u := by linarith
    exact h (by exact_mod_cast he)
  have hfreq : ((r : ℂ)+s-t-u)*Complex.I*((Real.pi/n : ℝ) : ℂ) = Real.pi*Complex.I := by
    have hnc : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    have hc : (n : ℂ) = (r : ℂ)+s-t-u := by simp [n]
    rw [← hc, Complex.ofReal_div]
    field_simp
  have he := integral_mul_right_eq_self (μ := normalizedHaar SU2)
    (entryMonomial r s t u) (diagonalPhase (Real.pi/n))
  simp_rw [entryMonomial_right_phase, hfreq, Complex.exp_pi_mul_I] at he
  rw [integral_const_mul] at he
  linear_combination -he/2

/-- The full monomial identity (4.3), with both Kronecker deltas.
@isnad1 id=eq.0h4v.s10.26804b1b4232 from=translated src=- shape=3a9febdc vocab=b9ffbae9
-/
theorem su2_monomial (r s t u : ℕ) :
    (∫ g : SU2, entryMonomial r s t u g ∂normalizedHaar SU2) =
      if r = u ∧ s = t then
        (-1 : ℂ)^s * ((r.factorial : ℂ)*s.factorial/(r+s+1).factorial) else 0 := by
  by_cases h : r = u ∧ s = t
  · rcases h with ⟨rfl,rfl⟩
    rw [ite_eq_left ⟨rfl,rfl⟩]
    exact entryMonomial_integral_diagonal _ _
  · rw [ite_eq_right h]
    by_cases hl : r+t = u+s
    · exact entryMonomial_integral_right_zero r s t u (by omega)
    · exact entryMonomial_integral_left_zero r s t u hl

end XZMathieuSU2Counterexamples.Hopf
