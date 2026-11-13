import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.MomentContinuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite moment coordinates

A vector of the first `d` monomial moments defines a total polynomial functional
by setting higher moments to zero. All degree-bounded pairings agree with the
original functional. Canonical order-`n` polynomials require only `2n` moments.
Source: Gautschi (2004), §2.1; AQ22 in the operator re-derivations.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib

section Algebra
variable {𝕜 : Type*} [Field 𝕜]

/-- A finite monomial-moment vector, extended by zero above its last coordinate.
The extension is a convention, not a positivity assertion at higher degrees.-/
def finiteMomentFunctional {d : ℕ} (m : Fin d → 𝕜) : 𝕜[X] →ₗ[𝕜] 𝕜 :=
  ∑ i : Fin d, m i • lcoeff 𝕜 i.val

/-- A fixed finite coordinate chart of polynomial functionals, paired with its
moment vector. Basis duals are a special case; no basis choice varies with `m`.-/
def coordinateMomentFunctional {d : ℕ} (c : Fin d → (𝕜[X] →ₗ[𝕜] 𝕜))
    (m : Fin d → 𝕜) : 𝕜[X] →ₗ[𝕜] 𝕜 := ∑ i : Fin d, m i • c i

/-- A coordinate functional evaluates by its finite coordinate pairing.
@isnad1 id=eq.0h5v.s9.dfc365e34933 from=translated src=- shape=cdc86b0b vocab=02606f9a
-/
@[simp] theorem coordinateMomentFunctional_apply {d : ℕ}
    (c : Fin d → (𝕜[X] →ₗ[𝕜] 𝕜)) (m : Fin d → 𝕜) (p : 𝕜[X]) :
    coordinateMomentFunctional c m p = ∑ i : Fin d, m i * c i p := by
  simp [coordinateMomentFunctional]

/-- Perturbing one moment coordinate adds its fixed dual functional.
@isnad1 id=eq.0h6v.s10.3d48a9fabf61 from=translated src=- shape=fc60c894 vocab=1001dcf1
-/
theorem coordinateMomentFunctional_add_smul_single {d : ℕ}
    (c : Fin d → (𝕜[X] →ₗ[𝕜] 𝕜)) (m : Fin d → 𝕜) (t : 𝕜) (k : Fin d) :
    coordinateMomentFunctional c (m + t • Pi.single k 1) =
      coordinateMomentFunctional c m + t • c k := by
  ext p
  simp [coordinateMomentFunctional_apply, Pi.single_apply, add_mul,
    Finset.sum_add_distrib]

/-- Fixed dual coordinate functionals give exactly the prescribed modified
moments on the corresponding polynomial basis.
@isnad1 id=eq.1h6v.s9.bf235c2087e1 from=translated src=- shape=341d30df vocab=96a2d853
-/
theorem coordinateMomentFunctional_apply_dual {d : ℕ}
    (b : Fin d → 𝕜[X]) (c : Fin d → (𝕜[X] →ₗ[𝕜] 𝕜)) (m : Fin d → 𝕜)
    (hc : ∀ i j, c i (b j) = if i = j then 1 else 0) (j : Fin d) :
    coordinateMomentFunctional c m (b j) = m j := by
  simp [coordinateMomentFunctional_apply, hc]

/-- Finite moment pairing is the coefficient dot product.
@isnad1 id=eq.0h4v.s8.89680815b1a6 from=translated src=- shape=c67537a7 vocab=260eff07
-/
@[simp] theorem finiteMomentFunctional_apply {d : ℕ} (m : Fin d → 𝕜) (p : 𝕜[X]) :
    finiteMomentFunctional m p = ∑ i : Fin d, m i * p.coeff i.val := by
  simp [finiteMomentFunctional]

/-- Truncating moments preserves every pairing below the truncation degree.
@isnad1 id=eq.1h4v.s9.4ffb5816295c from=translated src=- shape=dd4e3171 vocab=54ec1dd4
-/
theorem finiteMomentFunctional_apply_eq_of_degree_lt
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {d : ℕ} {p : 𝕜[X]} (hp : p.degree < d) :
    finiteMomentFunctional (fun i : Fin d => L (X ^ i.val)) p = L p := by
  rw [finiteMomentFunctional_apply]
  nth_rw 2 [eq_sum_monomial_fin_of_degree_lt hp]
  simp only [map_sum, ← C_mul_X_pow_eq_monomial, C_mul', map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Identical first `2n` moments give identical canonical coefficient vectors.
@isnad1 id=eq.1h4v.s9.8239ae4b876e from=translated src=- shape=dd339e5b vocab=89e20b80
-/
theorem orthogonalPolynomialCoefficients_eq_of_moments_eq
    {L M : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ}
    (h : ∀ k < 2 * n, L (X ^ k) = M (X ^ k)) :
    orthogonalPolynomialCoefficients L n = orthogonalPolynomialCoefficients M n := by
  have hH : hankelMomentMatrix L n = hankelMomentMatrix M n := by
    ext i j
    apply h
    have := i.isLt
    have := j.isLt
    omega
  have hv : (fun i : Fin n => -L (X ^ (n + i.val))) =
      fun i : Fin n => -M (X ^ (n + i.val)) := by
    funext i
    rw [h (n + i.val) (by have := i.isLt; omega)]
  simp only [orthogonalPolynomialCoefficients, hH, hv]

/-- The canonical monic polynomial depends only on the first `2n` moments.
@isnad1 id=eq.1h4v.s9.76665ab43d81 from=translated src=- shape=0165578c vocab=4e748f57
-/
theorem monicOrthogonalPolynomial_eq_of_moments_eq
    {L M : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ}
    (h : ∀ k < 2 * n, L (X ^ k) = M (X ^ k)) :
    monicOrthogonalPolynomial L n = monicOrthogonalPolynomial M n := by
  simp only [monicOrthogonalPolynomial, orthogonalPolynomialLowerPart,
    orthogonalPolynomialCoefficients_eq_of_moments_eq h]

end Algebra
section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {d n : ℕ} {m : Fin d → 𝕜}
  {r : WithTop ℕ∞}

/-- Fixed polynomial coordinates are smooth in the moment vector.
@isnad1 id=contdiff.0h5v.s9.a5b43f2e6b50 from=translated src=- shape=d2a918f5 vocab=61ba2d4e
-/
theorem contDiff_coordinateMomentFunctional_apply
    (c : Fin d → (𝕜[X] →ₗ[𝕜] 𝕜)) (p : 𝕜[X]) :
    ContDiff 𝕜 r (fun m : Fin d → 𝕜 => coordinateMomentFunctional c m p) := by
  simp only [coordinateMomentFunctional_apply]
  exact ContDiff.sum (fun i _ => (contDiff_apply 𝕜 𝕜 i).mul contDiff_const)

/-- Every fixed polynomial pairing is smooth in finite moment coordinates.
@isnad1 id=contdiff.0h4v.s8.29d35fa695f1 from=translated src=- shape=f4dc5a8b vocab=2d273d17
-/
theorem contDiff_finiteMomentFunctional_apply (p : 𝕜[X]) :
    ContDiff 𝕜 r (fun m : Fin d → 𝕜 => finiteMomentFunctional m p) := by
  simp only [finiteMomentFunctional_apply]
  exact ContDiff.sum (fun i _ => (contDiff_apply 𝕜 𝕜 i).mul contDiff_const)

/-- Monic polynomial coefficients are smooth functions of a finite moment vector
at every nonsingular Hankel system. Source: AQ22.
atlas: recurrence-coefficient-continuity (partial), recurrence-coefficient-moment-sensitivity (partial)
@isnad1 id=contdiff.1h6v.s7.556fd2b10df5 from=translated src=- shape=1a3c85bd vocab=c135b524
-/
theorem contDiffAt_coeff_monicOrthogonalPolynomial_finiteMomentFunctional
    (hn : hankelMomentDet (finiteMomentFunctional m) n ≠ 0) (k : ℕ) :
    ContDiffAt 𝕜 r (fun v : Fin d → 𝕜 =>
      (monicOrthogonalPolynomial (finiteMomentFunctional v) n).coeff k) m :=
  contDiffAt_coeff_monicOrthogonalPolynomial
    (fun j => (contDiff_finiteMomentFunctional_apply (X ^ j)).contDiffAt) hn k

/-- The finite-coordinate diagonal recurrence map is smooth at a nonzero norm.
atlas: recurrence-coefficient-continuity (partial), recurrence-coefficient-moment-sensitivity (partial)
@isnad1 id=contdiff.2h5v.s7.b16a8c97159a from=translated src=- shape=cb9c5372 vocab=6ed19b0e
-/
theorem contDiffAt_orthogonalRecurrenceAlpha_finiteMomentFunctional
    (hn : hankelMomentDet (finiteMomentFunctional m) n ≠ 0)
    (hh : orthogonalPolynomialNorm (finiteMomentFunctional m) n ≠ 0) :
    ContDiffAt 𝕜 r (fun v : Fin d → 𝕜 =>
      orthogonalRecurrenceAlpha (finiteMomentFunctional v) n) m :=
  contDiffAt_orthogonalRecurrenceAlpha
    (fun j => (contDiff_finiteMomentFunctional_apply (X ^ j)).contDiffAt) hn hh

/-- The finite-coordinate positive-order monic subdiagonal map is smooth.
atlas: recurrence-coefficient-continuity (partial), recurrence-coefficient-moment-sensitivity (partial)
@isnad1 id=contdiff.3h5v.s8.31e9813b1256 from=translated src=- shape=9e89fbd8 vocab=30f4d4ef
-/
theorem contDiffAt_orthogonalRecurrenceBeta_finiteMomentFunctional
    (hn : hankelMomentDet (finiteMomentFunctional m) n ≠ 0)
    (hprev : hankelMomentDet (finiteMomentFunctional m) (n - 1) ≠ 0)
    (hh : orthogonalPolynomialNorm (finiteMomentFunctional m) (n - 1) ≠ 0) :
    ContDiffAt 𝕜 r (fun v : Fin d → 𝕜 =>
      orthogonalRecurrenceBeta (finiteMomentFunctional v) n) m :=
  contDiffAt_orthogonalRecurrenceBeta
    (fun j => (contDiff_finiteMomentFunctional_apply (X ^ j)).contDiffAt) hn hprev hh

end Smooth
end NLAlib
