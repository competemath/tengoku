import Tengoku.RainichKaluzaReconstruction.RainichKaluza.CharacteristicData
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraic curvature fingerprint

The obstruction in this file is a necessary polynomial consequence of the
proposed generic characteristic factorization. It is deliberately not called
a sufficient Rainich condition: differential integrability, signature,
rank-one reconstruction, Maxwell closure, and degenerate branches remain open
proof obligations.
-/

namespace RainichKaluza

/-- The candidate algebraic Kaluza obstruction
`C = e₁² e₄ - e₁ e₂ e₃ + e₃²`.-/
def kaluzaObstruction (d : CharacteristicData) : ℝ :=
  d.e1 ^ 2 * d.e4 - d.e1 * d.e2 * d.e3 + d.e3 ^ 2

/-- **Exact algebraic theorem.** Every quartic with the proposed Kaluza
factorization satisfies the candidate obstruction.-/
@[simp] theorem kaluzaObstruction_fromFactorization
    (p : FactorizationParameters) :
    kaluzaObstruction (.fromFactorization p) = 0 := by
  simp [kaluzaObstruction, CharacteristicData.fromFactorization]
  ring

/-- Curvature-only reconstruction formula for the squared protected
eigenvalue on the nonzero-trace branch.-/
noncomputable def reconstructedQSq (d : CharacteristicData) : ℝ :=
  -d.e3 / d.e1

/-- Reconstruction of the second quadratic factor's constant term.-/
noncomputable def reconstructedResidualConstant
    (d : CharacteristicData) : ℝ :=
  -d.e2 - reconstructedQSq d

/-- The curvature-only formula recovers `qSq` on factored data whenever the
Ricci trace is nonzero.-/
theorem reconstructedQSq_fromFactorization
    (p : FactorizationParameters) (hR : p.ricciTrace ≠ 0) :
    reconstructedQSq (.fromFactorization p) = p.qSq := by
  simp [reconstructedQSq, CharacteristicData.fromFactorization]
  field_simp [hR]

/-- On the nonzero-trace branch, vanishing of the obstruction is equivalent
to reconstructing the constant coefficient from the two quadratic factors.
This is a coefficient identity, not yet a geometric sufficiency theorem.-/
theorem obstruction_zero_iff_reconstructed_constant
    (d : CharacteristicData) (hR : d.e1 ≠ 0) :
    kaluzaObstruction d = 0 ↔
      d.e4 = reconstructedQSq d * reconstructedResidualConstant d := by
  simp only [kaluzaObstruction, reconstructedQSq,
    reconstructedResidualConstant]
  field_simp [hR]
  constructor <;> intro h
  · nlinarith
  · nlinarith

/-- Characteristic data for a Ricci endomorphism with perfect-fluid-like
spectrum `{a,b,b,b}`.-/
def perfectFluidData (a b : ℝ) : CharacteristicData where
  e1 := a + 3 * b
  e2 := 3 * a * b + 3 * b ^ 2
  e3 := 3 * a * b ^ 2 + b ^ 3
  e4 := a * b ^ 3

/-- **Exact adversarial check.** A generic perfect-fluid spectrum does not
silently satisfy the candidate Kaluza obstruction.-/
theorem kaluzaObstruction_perfectFluid (a b : ℝ) :
    kaluzaObstruction (perfectFluidData a b) =
      -8 * b ^ 3 * (a + b) ^ 3 := by
  simp [kaluzaObstruction, perfectFluidData]
  ring

/-- An explicit coefficient-level false positive for the obstruction.-/
def algebraicFalsePositive : CharacteristicData where
  e1 := 1
  e2 := 0
  e3 := 1
  e4 := -1

/-- The false-positive data satisfy the polynomial obstruction exactly.-/
@[simp] theorem kaluzaObstruction_algebraicFalsePositive :
    kaluzaObstruction algebraicFalsePositive = 0 := by
  norm_num [kaluzaObstruction, algebraicFalsePositive]

/-- **Exact insufficiency witness.** Although the obstruction vanishes, the
reconstructed `qSq` is negative and hence cannot equal `q²` for any real
protected eigenvalue `q`.-/
theorem algebraicFalsePositive_has_no_real_protected_pair :
    ¬ ∃ q : ℝ, q ^ 2 = reconstructedQSq algebraicFalsePositive := by
  rintro ⟨q, hq⟩
  norm_num [reconstructedQSq, algebraicFalsePositive] at hq
  nlinarith [sq_nonneg q]

end RainichKaluza
