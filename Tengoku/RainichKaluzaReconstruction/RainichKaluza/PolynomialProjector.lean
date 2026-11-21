import Tengoku.RainichKaluzaReconstruction.RainichKaluza.SpectralReflection
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial spectral projectors

For an algebra element satisfying `(R-aI)(R-bI)=0` with `a≠b`, the polynomial

`Pₐ = (R-bI)/(a-b)`

is the spectral projector onto the `a` branch.  This construction requires no
choice or orientation of eigenvectors and is therefore suitable for the
smooth differential reconstruction program.
-/

namespace RainichKaluza

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Numerator of the two-root spectral projector.-/
def twoRootProjectorNumerator (R : A) (b : ℝ) : A :=
  R - b • (1 : A)

/-- Polynomial projector associated with root `a` when the only two roots on
the relevant invariant block are `a,b`.-/
noncomputable def twoRootProjector (R : A) (a b : ℝ) : A :=
  (a - b)⁻¹ • twoRootProjectorNumerator R b

/-- The quadratic relation gives the scaled idempotence relation for the
projector numerator.
@isnad1 id=eq.1h4v.s7.44f2ee1b1dbd from=translated src=- shape=0f964550 vocab=0cf8e9dc
-/
theorem twoRootProjectorNumerator_sq
    (R : A) (a b : ℝ)
    (hquad :
      (R - a • (1 : A)) * (R - b • (1 : A)) = 0) :
    twoRootProjectorNumerator R b * twoRootProjectorNumerator R b =
      (a - b) • twoRootProjectorNumerator R b := by
  have hdecomp :
      twoRootProjectorNumerator R b =
        (R - a • (1 : A)) + (a - b) • (1 : A) := by
    unfold twoRootProjectorNumerator
    module
  calc
    twoRootProjectorNumerator R b * twoRootProjectorNumerator R b =
        ((R - a • (1 : A)) + (a - b) • (1 : A)) *
          twoRootProjectorNumerator R b := by rw [hdecomp]
    _ = (R - a • (1 : A)) * twoRootProjectorNumerator R b +
          ((a - b) • (1 : A)) * twoRootProjectorNumerator R b := by
            rw [add_mul]
    _ = 0 + ((a - b) • (1 : A)) *
          twoRootProjectorNumerator R b := by
            rw [twoRootProjectorNumerator, hquad]
    _ = (a - b) • twoRootProjectorNumerator R b := by simp

/-- The polynomial projector is idempotent.
@isnad1 id=eq.2h4v.s7.dc3fce6929f7 from=translated src=- shape=8ae54c9e vocab=a4979b48
-/
theorem twoRootProjector_sq
    (R : A) (a b : ℝ) (hab : a ≠ b)
    (hquad :
      (R - a • (1 : A)) * (R - b • (1 : A)) = 0) :
    twoRootProjector R a b * twoRootProjector R a b =
      twoRootProjector R a b := by
  unfold twoRootProjector
  rw [smul_mul_smul]
  rw [twoRootProjectorNumerator_sq R a b hquad]
  rw [smul_smul]
  have hgap : a - b ≠ 0 := sub_ne_zero.mpr hab
  congr 1
  field_simp

/-- The projector numerator commutes with `R`.
@isnad1 id=eq.0h3v.s5.bf6a3c61ad26 from=translated src=- shape=5896089b vocab=75795a6c
-/
theorem twoRootProjectorNumerator_commutes
    (R : A) (b : ℝ) :
    twoRootProjectorNumerator R b * R =
      R * twoRootProjectorNumerator R b := by
  unfold twoRootProjectorNumerator
  calc
    (R - b • (1 : A)) * R = R * R - (b • (1 : A)) * R := by
      rw [sub_mul]
    _ = R * R - b • R := by simp
    _ = R * R - R * (b • (1 : A)) := by simp
    _ = R * (R - b • (1 : A)) := by rw [mul_sub]

/-- The polynomial projector commutes with `R`.
@isnad1 id=eq.0h4v.s5.a7a7b64fc685 from=translated src=- shape=e2922e68 vocab=bb198c87
-/
theorem twoRootProjector_commutes
    (R : A) (a b : ℝ) :
    twoRootProjector R a b * R = R * twoRootProjector R a b := by
  unfold twoRootProjector
  rw [smul_mul_assoc, mul_smul_comm]
  rw [twoRootProjectorNumerator_commutes]

/-- The associated basis-independent reflection is involutive.
@isnad1 id=eq.2h4v.s7.6677edf26bf3 from=translated src=- shape=87d48a7f vocab=573bdae6
-/
theorem twoRootReflection_sq
    (R : A) (a b : ℝ) (hab : a ≠ b)
    (hquad :
      (R - a • (1 : A)) * (R - b • (1 : A)) = 0) :
    reflectionOfIdempotent (twoRootProjector R a b) *
      reflectionOfIdempotent (twoRootProjector R a b) = 1 :=
  reflectionOfIdempotent_sq _ (twoRootProjector_sq R a b hab hquad)

/-- The associated reflection also commutes with `R`.
@isnad1 id=eq.0h4v.s6.8a64c1411e17 from=translated src=- shape=26ea7427 vocab=daefccff
-/
theorem twoRootReflection_commutes
    (R : A) (a b : ℝ) :
    reflectionOfIdempotent (twoRootProjector R a b) * R =
      R * reflectionOfIdempotent (twoRootProjector R a b) :=
  reflectionOfIdempotent_commutes _ _ (twoRootProjector_commutes R a b)

section Endomorphism

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- On an `a` eigenvector, the polynomial projector acts as the identity.
@isnad1 id=eq.2h5v.s7.844935328d70 from=translated src=- shape=fb964dbf vocab=fd2a162a
-/
theorem twoRootProjector_apply_eq_self
    (R : Module.End ℝ E) (a b : ℝ) (hab : a ≠ b) (y : E)
    (hy : R y = a • y) :
    twoRootProjector R a b y = y := by
  have hgap : a - b ≠ 0 := sub_ne_zero.mpr hab
  simp only [twoRootProjector, twoRootProjectorNumerator,
    LinearMap.smul_apply, LinearMap.sub_apply, hy]
  calc
    (a - b)⁻¹ • (a • y - b • y) =
        ((a - b)⁻¹ * (a - b)) • y := by module
    _ = y := by rw [inv_mul_cancel₀ hgap]; simp

/-- On a `b` eigenvector, the polynomial projector vanishes.
@isnad1 id=eq.2h5v.s7.19f1ebdbeeb5 from=translated src=- shape=3c0a7e1e vocab=fd2a162a
-/
theorem twoRootProjector_apply_eq_zero
    (R : Module.End ℝ E) (a b : ℝ) (_hab : a ≠ b) (y : E)
    (hy : R y = b • y) :
    twoRootProjector R a b y = 0 := by
  simp [twoRootProjector, twoRootProjectorNumerator, hy]

end Endomorphism

end RainichKaluza
