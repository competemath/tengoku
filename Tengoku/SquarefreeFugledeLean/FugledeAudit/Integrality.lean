import Tengoku.Seed.LinearAlgebra.Eigenspace.Charpoly
import Tengoku.Seed.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Tengoku.Seed.RingTheory.Polynomial.RationalRoot
import Tengoku.Seed.RingTheory.Localization.Rat
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The arithmetic obstruction from an actual Gram-matrix eigenvalue

No statement below assumes that the local regular summand exists or has the
claimed spectrum. The connection to the paper's spectral-pair hypotheses is
proved separately in ActualIntegralGram.
-/

open Matrix Polynomial

namespace FugledeAudit

/-- Every positive-order root of unity is an algebraic integer.
@isnad1 id=isintegr.2h2v.s5.fe19f2ce3c4d from=translated src=- shape=733f9193 vocab=922892e1
-/
theorem integral_of_root_of_unity (ζ : ℂ) (H : ℕ) (hH : 0 < H)
    (hζ : ζ ^ H = 1) : IsIntegral ℤ ζ := by
  exact IsIntegral.of_pow hH (hζ ▸ isIntegral_one)

/-- Entries of the actual unnormalised Gram matrix are integral whenever the
entries of the rectangular Fourier block are integral.
@isnad1 id=isintegr.1h5v.s6.afdcc356f833 from=translated src=- shape=7111723c vocab=75ce58d0
-/
theorem integral_gram_entries
    {n k : Type*} [Fintype k]
    (M : Matrix n k ℂ) (hM : ∀ i j, IsIntegral ℤ (M i j)) :
    ∀ i j, IsIntegral ℤ ((M * M.conjTranspose) i j) := by
  intro i j
  change IsIntegral ℤ (∑ x, M i x * star (M j x))
  apply IsIntegral.sum
  intro x _
  exact (hM i x).mul (map_isIntegral_int Complex.conjAe.toRingHom (hM j x))

/-- A rational algebraic integer m/q, with q nonzero, forces q to divide m.
Primality, square-freeness and prime separation are not needed for this step.
@isnad1 id=dvd.2h2v.s5.aa8978adcc78 from=translated src=- shape=3354d305 vocab=45ea38af
-/
theorem dvd_of_integral_quotient (m q : ℕ) (hq : q ≠ 0)
    (h : IsIntegral ℤ ((m : ℚ) / (q : ℚ))) : q ∣ m := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have heq : (m : ℚ) = (q : ℚ) * (z : ℚ) := by
    have hz' : (z : ℚ) = (m : ℚ) / (q : ℚ) := hz
    calc
      (m : ℚ) = ((m : ℚ) / (q : ℚ)) * (q : ℚ) :=
        (div_mul_cancel₀ _ hqQ).symm
      _ = (q : ℚ) * (z : ℚ) := by rw [← hz']; ring
  have heqZ : (m : ℤ) = (q : ℤ) * z := by exact_mod_cast heq
  have hd : (q : ℤ) ∣ (m : ℤ) := ⟨z, heqZ⟩
  exact_mod_cast hd

/-- A genuine eigenvalue of a finite matrix of algebraic integers is integral.
The integral matrix is constructed in its original basis; no unitary change
of basis is used to assert integrality of the entries.
@isnad1 id=isintegr.3h4v.s6.86aff32e4f8b from=translated src=- shape=39f31f8c vocab=b9f2df17
-/
theorem integral_of_matrix_eigenvector
    {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (hB : ∀ i j, IsIntegral ℤ (B i j))
    (μ : ℂ) (v : n → ℂ) (hv : v ≠ 0) (he : B.mulVec v = μ • v) :
    IsIntegral ℤ μ := by
  let O := integralClosure ℤ ℂ
  let B₀ : Matrix n n O := fun i j => ⟨B i j, hB i j⟩
  have hmap : B₀.map (algebraMap O ℂ) = B := by ext i j; rfl
  change B.toLin' v = μ • v at he
  have heig : Module.End.HasEigenvalue B.toLin' μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩
  have hroot : B.charpoly.IsRoot μ := by
    simpa only [Matrix.charpoly_toLin'] using
      (Module.End.hasEigenvalue_iff_isRoot_charpoly B.toLin' μ).mp heig
  have hroot₀ : aeval μ B₀.charpoly = 0 := by
    change B₀.charpoly.eval₂ (algebraMap O ℂ) μ = 0
    rw [← Polynomial.eval_map, ← Matrix.charpoly_map, hmap]
    exact hroot
  have hint : IsIntegral O μ := ⟨B₀.charpoly, Matrix.charpoly_monic _, hroot₀⟩
  exact isIntegral_trans (R := ℤ) (A := O) μ hint

end FugledeAudit
