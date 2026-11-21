import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Characteristic data for the generic Kaluza branch

This file contains only finite-dimensional polynomial algebra. It does not
assert that an arbitrary Lorentzian metric satisfies the Einstein--Maxwell--
dilaton equations, nor that the displayed factorization is sufficient for a
Kaluza interpretation.
-/

namespace RainichKaluza

/-- Coefficients of a monic quartic in the characteristic-polynomial sign
convention `x⁴ - e₁ x³ + e₂ x² - e₃ x + e₄`.-/
structure CharacteristicData where
  e1 : ℝ
  e2 : ℝ
  e3 : ℝ
  e4 : ℝ

/-- The monic quartic determined by characteristic data.-/
def monicQuartic (d : CharacteristicData) (x : ℝ) : ℝ :=
  x ^ 4 - d.e1 * x ^ 3 + d.e2 * x ^ 2 - d.e3 * x + d.e4

/-- Parameters appearing in the proposed generic factorization
`(x² - q²)(x² - R x - c)`. The name `qSq` is algebraic here; nonnegativity is
not assumed in this file.-/
structure FactorizationParameters where
  ricciTrace : ℝ
  qSq : ℝ
  residualConstant : ℝ

/-- Characteristic coefficients obtained by expanding the proposed generic
Kaluza factorization.-/
def CharacteristicData.fromFactorization
    (p : FactorizationParameters) : CharacteristicData where
  e1 := p.ricciTrace
  e2 := -(p.residualConstant + p.qSq)
  e3 := -(p.ricciTrace * p.qSq)
  e4 := p.qSq * p.residualConstant

/-- **Exact algebraic theorem.** The encoded characteristic polynomial really
is the proposed product.
@isnad1 id=eq.0h2v.s6.6711072fa9d4 from=translated src=- shape=979c2674 vocab=2099b8ee
-/
theorem monicQuartic_fromFactorization
    (p : FactorizationParameters) (x : ℝ) :
    monicQuartic (.fromFactorization p) x =
      (x ^ 2 - p.qSq) *
        (x ^ 2 - p.ricciTrace * x - p.residualConstant) := by
  simp [monicQuartic, CharacteristicData.fromFactorization]
  ring

/-- If `q² = qSq`, the positive member of the protected pair is a root.
@isnad1 id=eq.1h2v.s5.fc39f15668cb from=translated src=- shape=a1807166 vocab=536c0da9
-/
theorem protected_positive_root
    (p : FactorizationParameters) (q : ℝ) (hq : q ^ 2 = p.qSq) :
    monicQuartic (.fromFactorization p) q = 0 := by
  rw [monicQuartic_fromFactorization, hq]
  ring

/-- If `q² = qSq`, the negative member of the protected pair is a root.
@isnad1 id=eq.1h2v.s5.458a05c8a667 from=translated src=- shape=174dfd9e vocab=0047c244
-/
theorem protected_negative_root
    (p : FactorizationParameters) (q : ℝ) (hq : q ^ 2 = p.qSq) :
    monicQuartic (.fromFactorization p) (-q) = 0 := by
  rw [monicQuartic_fromFactorization]
  rw [show (-q) ^ 2 = p.qSq by simpa using hq]
  ring

end RainichKaluza
