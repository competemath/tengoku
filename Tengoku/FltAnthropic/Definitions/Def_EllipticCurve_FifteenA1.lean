import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
import Tengoku.Seed.Data.Rat.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace ModularCurve

namespace FifteenA1

open WeierstrassCurve Affine

def shortW : WeierstrassCurve.Affine ℚ := ⟨0, 5, 0, -152, -624⟩

/--
@isnad1 id=eq.0h0v.s3.ec76a92dca39 from=translated src=- shape=3701a056 vocab=47d80517
-/
@[simp] theorem shortW_a₁ : shortW.a₁ = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.4a1927c6ac03 from=translated src=- shape=3701a056 vocab=a048f6bc
-/
@[simp] theorem shortW_a₂ : shortW.a₂ = 5 := rfl
/--
@isnad1 id=eq.0h0v.s3.810c0dd9d6fe from=translated src=- shape=3701a056 vocab=efb94ad0
-/
@[simp] theorem shortW_a₃ : shortW.a₃ = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.32053e34d738 from=translated src=- shape=ef898e92 vocab=6948532b
-/
@[simp] theorem shortW_a₄ : shortW.a₄ = -152 := rfl
/--
@isnad1 id=eq.0h0v.s3.f2fdf6d73e00 from=translated src=- shape=ef898e92 vocab=7b4b8440
-/
@[simp] theorem shortW_a₆ : shortW.a₆ = -624 := rfl

def IsSqClass (d a : ℚ) : Prop := ∃ c : ℚ, c ≠ 0 ∧ a = d * c ^ 2

def deltaPair : shortW.Point → ℚ × ℚ
  | .zero => (1, 1)
  | .some X _ _ =>
      (if X = 12 then 400 else X - 12, if X = -4 then -144 else X + 4)

/--
@isnad1 id=eq.0h0v.s5.817e95e786e6 from=translated src=- shape=54da6699 vocab=1af422e0
-/
@[simp] theorem deltaPair_zero : deltaPair 0 = (1, 1) := rfl

/--
@isnad1 id=eq.1h2v.s6.6067a902a51e from=translated src=- shape=db68e2e5 vocab=92f4565b
-/
theorem deltaPair_some {X Y : ℚ} (h : shortW.Nonsingular X Y) :
    deltaPair (.some X Y h) =
      (if X = 12 then 400 else X - 12, if X = -4 then -144 else X + 4) := rfl

def V₀ : Finset (ℚ × ℚ) := {(1, 1), (-5, -1), (-1, -1), (5, 1)}

end FifteenA1

end ModularCurve
