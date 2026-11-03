import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.TwoCopyCoefficientDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms firstFractionCopy` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms secondFractionCopy` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eq_coefficient_of_fraction_copy_eq` (it only prints; the queue checks the axioms of every declaration). -/

/-! Lift the two polynomial copies to their fraction fields.  Equality of the
two copied rational functions then supplies the denominator-cleared identity
required by coefficient descent. -/

noncomputable section
namespace AlbertLean.Generic.TwoCopyFractionDescent

open MvPolynomial TwoCopyCoefficientDescent

universe u v
variable {k : Type u} {ι : Type v} [Field k]

abbrev R := MvPolynomial ι k
abbrev R₂ := MvPolynomial (ι ⊕ ι) k

def firstPolynomialToFraction : R (k := k) (ι := ι) →+*
    FractionRing (R₂ (k := k) (ι := ι)) :=
  (algebraMap (R₂ (k := k) (ι := ι))
    (FractionRing (R₂ (k := k) (ι := ι)))).comp (rename Sum.inl).toRingHom

def secondPolynomialToFraction : R (k := k) (ι := ι) →+*
    FractionRing (R₂ (k := k) (ι := ι)) :=
  (algebraMap (R₂ (k := k) (ι := ι))
    (FractionRing (R₂ (k := k) (ι := ι)))).comp (rename Sum.inr).toRingHom

private theorem firstPolynomialToFraction_injective : Function.Injective
    (firstPolynomialToFraction : R (k := k) (ι := ι) →
      FractionRing (R₂ (k := k) (ι := ι))) :=
  (IsFractionRing.injective (R₂ (k := k) (ι := ι))
    (FractionRing (R₂ (k := k) (ι := ι)))).comp
      (MvPolynomial.rename_injective Sum.inl Sum.inl_injective)

private theorem secondPolynomialToFraction_injective : Function.Injective
    (secondPolynomialToFraction : R (k := k) (ι := ι) →
      FractionRing (R₂ (k := k) (ι := ι))) :=
  (IsFractionRing.injective (R₂ (k := k) (ι := ι))
    (FractionRing (R₂ (k := k) (ι := ι)))).comp
      (MvPolynomial.rename_injective Sum.inr Sum.inr_injective)

def firstFractionCopy : FractionRing (R (k := k) (ι := ι)) →+*
    FractionRing (R₂ (k := k) (ι := ι)) :=
  IsFractionRing.lift firstPolynomialToFraction_injective

def secondFractionCopy : FractionRing (R (k := k) (ι := ι)) →+*
    FractionRing (R₂ (k := k) (ι := ι)) :=
  IsFractionRing.lift secondPolynomialToFraction_injective

/-- A selected nonzero denominator coefficient and equality of the independent
fraction copies imply that the original fraction is a coefficient scalar.-/
theorem eq_coefficient_of_fraction_copy_eq
    (f : FractionRing (R (k := k) (ι := ι)))
    (A B : R (k := k) (ι := ι)) (α : ι →₀ ℕ)
    (hBα : B.coeff α ≠ 0)
    (hf : f = algebraMap (R (k := k) (ι := ι)) _ A /
      algebraMap (R (k := k) (ι := ι)) _ B)
    (hcopy : firstFractionCopy f = secondFractionCopy f) :
    f = algebraMap k (FractionRing (R (k := k) (ι := ι)))
      (A.coeff α / B.coeff α) := by
  have hB : B ≠ 0 := fun hzero => hBα (by simp [hzero])
  have hleftB : algebraMap (R₂ (k := k) (ι := ι))
      (FractionRing (R₂ (k := k) (ι := ι))) (firstCopy B) ≠ 0 := by
    have hc : firstCopy B ≠ 0 := by
      simpa only [firstCopy, map_zero] using
        (MvPolynomial.rename_injective Sum.inl Sum.inl_injective).ne hB
    simpa only [map_zero] using
      (IsFractionRing.injective (R₂ (k := k) (ι := ι))
        (FractionRing (R₂ (k := k) (ι := ι)))).ne hc
  have hrightB : algebraMap (R₂ (k := k) (ι := ι))
      (FractionRing (R₂ (k := k) (ι := ι))) (secondCopy B) ≠ 0 := by
    have hc : secondCopy B ≠ 0 := by
      simpa only [secondCopy, map_zero] using
        (MvPolynomial.rename_injective Sum.inr Sum.inr_injective).ne hB
    simpa only [map_zero] using
      (IsFractionRing.injective (R₂ (k := k) (ι := ι))
        (FractionRing (R₂ (k := k) (ι := ι)))).ne hc
  have hdiv :
      algebraMap (R₂ (k := k) (ι := ι))
        (FractionRing (R₂ (k := k) (ι := ι))) (firstCopy A) /
          algebraMap (R₂ (k := k) (ι := ι))
        (FractionRing (R₂ (k := k) (ι := ι))) (firstCopy B) =
        algebraMap (R₂ (k := k) (ι := ι))
        (FractionRing (R₂ (k := k) (ι := ι))) (secondCopy A) /
          algebraMap (R₂ (k := k) (ι := ι))
        (FractionRing (R₂ (k := k) (ι := ι))) (secondCopy B) := by
    simpa [hf, firstFractionCopy, secondFractionCopy,
      firstPolynomialToFraction, secondPolynomialToFraction,
      firstCopy, secondCopy, IsFractionRing.lift_algebraMap] using hcopy
  have hcross : firstCopy A * secondCopy B = secondCopy A * firstCopy B := by
    apply IsFractionRing.injective (R₂ (k := k) (ι := ι))
      (FractionRing (R₂ (k := k) (ι := ι)))
    simpa only [map_mul] using (div_eq_div_iff hleftB hrightB).mp hdiv
  rw [hf, fraction_eq_coefficient_ratio A B α hBα hcross]

end AlbertLean.Generic.TwoCopyFractionDescent
