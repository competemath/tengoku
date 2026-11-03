import Tengoku.Seed.Algebra.MvPolynomial.Equiv
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms proportional_of_two_copy_cross_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fraction_eq_coefficient_ratio` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Two-copy coefficient descent

If a rational function in one family of indeterminates agrees, after clearing
denominators, with the same rational function in a disjoint family, then one
nonzero denominator coefficient makes numerator and denominator proportional
over the coefficient field.  The final theorem records the resulting equality
inside the multivariate rational-function field.

This module supplies only the algebraic descent shortcut.  Its two-copy
identity must be proved separately from the actual invariant action families.
-/

noncomputable section
namespace AlbertLean.Generic.TwoCopyCoefficientDescent

open MvPolynomial

universe u v
variable {k : Type u} {ι : Type v} [Field k]

/-- Put a polynomial in the first of two disjoint copies of its variables.-/
def firstCopy (p : MvPolynomial ι k) : MvPolynomial (ι ⊕ ι) k :=
  rename Sum.inl p

/-- Put a polynomial in the second of two disjoint copies of its variables.-/
def secondCopy (p : MvPolynomial ι k) : MvPolynomial (ι ⊕ ι) k :=
  rename Sum.inr p

private theorem sumAlgEquiv_firstCopy (p : MvPolynomial ι k) :
    sumAlgEquiv k ι ι (firstCopy p) = map (C : k →+* MvPolynomial ι k) p := by
  have h := congrArg (fun f => f p) (sumAlgEquiv_comp_rename_inl (R := k)
    (S₁ := ι) (S₂ := ι))
  change sumAlgEquiv k ι ι (rename Sum.inl p) =
    map (C : k →+* MvPolynomial ι k) p at h
  exact h

private theorem sumAlgEquiv_secondCopy (p : MvPolynomial ι k) :
    sumAlgEquiv k ι ι (secondCopy p) = C p := by
  have h := congrArg (fun f => f p) (sumAlgEquiv_comp_rename_inr (R := k)
    (S₁ := ι) (S₂ := ι))
  change sumAlgEquiv k ι ι (rename Sum.inr p) = C p at h
  exact h

/-- Coefficient comparison in the second copy.  No infinitude, finite-variable,
or chosen evaluation point is needed.-/
theorem proportional_of_two_copy_cross_mul
    (A B : MvPolynomial ι k) (α : ι →₀ ℕ) (hBα : B.coeff α ≠ 0)
    (hcross : firstCopy A * secondCopy B = secondCopy A * firstCopy B) :
    A = C (A.coeff α / B.coeff α) * B := by
  have hcoeff := congrArg
    (fun p : MvPolynomial (ι ⊕ ι) k => (sumAlgEquiv k ι ι p).coeff α) hcross
  have hproportional : C (A.coeff α) * B = C (B.coeff α) * A := by
    simpa only [map_mul, sumAlgEquiv_firstCopy, sumAlgEquiv_secondCopy,
      coeff_C_mul, coeff_map, RingHom.coe_coe, mul_comm] using hcoeff
  apply (mul_left_cancel₀ (C_ne_zero.mpr hBα))
  calc
    C (B.coeff α) * A = C (A.coeff α) * B := hproportional.symm
    _ = C (B.coeff α) * (C (A.coeff α / B.coeff α) * B) := by
      rw [← mul_assoc, ← C_mul]
      congr 2
      rw [mul_comm, div_mul_cancel₀ _ hBα]

/-- The fraction represented by `A/B` is the image of the selected coefficient
ratio in `Frac(MvPolynomial ι k)`.-/
theorem fraction_eq_coefficient_ratio
    (A B : MvPolynomial ι k) (α : ι →₀ ℕ) (hBα : B.coeff α ≠ 0)
    (hcross : firstCopy A * secondCopy B = secondCopy A * firstCopy B) :
    algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) A /
        algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) B =
      algebraMap k (FractionRing (MvPolynomial ι k)) (A.coeff α / B.coeff α) := by
  have hAB := proportional_of_two_copy_cross_mul A B α hBα hcross
  have hB : B ≠ 0 := fun hzero => hBα (by simp [hzero])
  have hmapB : algebraMap (MvPolynomial ι k)
      (FractionRing (MvPolynomial ι k)) B ≠ 0 :=
    by simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial ι k)
        (FractionRing (MvPolynomial ι k))).ne hB
  calc
    algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) A /
          algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) B =
        algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))
            (C (A.coeff α / B.coeff α) * B) /
          algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) B := by
      exact congrArg
        (fun P => algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) P /
          algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) B) hAB
    _ = algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))
        (C (A.coeff α / B.coeff α)) := by
      rw [map_mul, mul_div_cancel_right₀ _ hmapB]
    _ = algebraMap k (FractionRing (MvPolynomial ι k))
        (A.coeff α / B.coeff α) := by
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial ι k), MvPolynomial.algebraMap_eq]

end AlbertLean.Generic.TwoCopyCoefficientDescent
