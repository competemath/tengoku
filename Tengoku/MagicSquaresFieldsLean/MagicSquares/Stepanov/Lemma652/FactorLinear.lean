import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Core.PowerDegree
import Tengoku.Seed.Algebra.Module.Submodule.Equiv
import Tengoku.Seed.Algebra.Module.LinearMap.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F V : Type*}
  [Field F]
  [AddCommGroup V] [Module F V]

/-!
# A canonical linear choice of the factor in Corollary 6.49

Corollary 6.49 says that

    E^(n)(w f^M) = w_1 f^(M-n).

For the coefficient-count argument it matters that `w_1` depends
*linearly* on `w`.  The book uses this implicitly.  Mathlib provides the
right abstraction: multiplication by the nonzero polynomial
`f^(M-n)` is an injective linear map, and `LinearMap.codRestrictOfInjective`
recovers the unique preimage linearly.
-/

/-- Multiplication by `f^(M-n)` as an `F`-linear map.-/
noncomputable def residualPowerMulLinear
    (f : Polynomial F) (M n : ℕ) :
    Polynomial F →ₗ[F] Polynomial F :=
  LinearMap.mulLeft F (f ^ (M - n))

/-- First multiply the input `w` by `f^M`, then take the `n`th Hasse
derivative.-/
noncomputable def hassePowerTermLinear
    (f : Polynomial F) (M n : ℕ)
    (w : V →ₗ[F] Polynomial F) :
    V →ₗ[F] Polynomial F :=
  (hasseDeriv n).comp
    ((LinearMap.mulLeft F (f ^ M)).comp w)

/-- Multiplication by a nonzero power of `f` is injective.-/
theorem residualPowerMulLinear_injective
    (f : Polynomial F) (M n : ℕ)
    (hf : f ≠ 0) :
    Function.Injective
      (residualPowerMulLinear (F := F) f M n) := by
  intro a b hab
  change f ^ (M - n) * a = f ^ (M - n) * b at hab
  exact mul_left_cancel₀ (pow_ne_zero _ hf) hab

/-- The derivative map lands in the range of multiplication by
`f^(M-n)`, by Corollary 6.49.-/
theorem hassePowerTermLinear_mem_range
    (f : Polynomial F) (M n : ℕ)
    (hnt : n ≤ M)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (w : V →ₗ[F] Polynomial F)
    (v : V) :
    hassePowerTermLinear f M n w v ∈
      LinearMap.range (residualPowerMulLinear (F := F) f M n) := by
  obtain ⟨w₁, hw₁, hwdeg⟩ :=
    ln97_6_49 (w v) f M n hnt hf hfdeg
  refine ⟨w₁, ?_⟩
  change f ^ (M - n) * w₁ =
    (hasseDeriv n) (f ^ M * w v)
  simpa [mul_comm] using hw₁.symm

/-- The factor `w_1` from Corollary 6.49, chosen canonically and
linearly in the input vector.-/
noncomputable def hassePowerFactorLinear
    (f : Polynomial F) (M n : ℕ)
    (hnt : n ≤ M)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (w : V →ₗ[F] Polynomial F) :
    V →ₗ[F] Polynomial F :=
  (hassePowerTermLinear f M n w).codRestrictOfInjective
    (residualPowerMulLinear (F := F) f M n)
    (residualPowerMulLinear_injective (F := F) f M n hf)
    (hassePowerTermLinear_mem_range
      (F := F) f M n hnt hf hfdeg w)

/-- Defining identity for the canonical linear factor.-/
theorem hassePowerFactorLinear_spec
    (f : Polynomial F) (M n : ℕ)
    (hnt : n ≤ M)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (w : V →ₗ[F] Polynomial F)
    (v : V) :
    (hasseDeriv n) (f ^ M * w v) =
      f ^ (M - n) *
        hassePowerFactorLinear f M n hnt hf hfdeg w v := by
  have h := LinearMap.codRestrictOfInjective_comp_apply
    (hassePowerTermLinear f M n w)
    (residualPowerMulLinear (F := F) f M n)
    (residualPowerMulLinear_injective (F := F) f M n hf)
    (hassePowerTermLinear_mem_range
      (F := F) f M n hnt hf hfdeg w)
    v
  exact h.symm

/-- Degree estimate inherited from Corollary 6.49.-/
theorem hassePowerFactorLinear_natDegree_le
    (f : Polynomial F) (M n W : ℕ)
    (hnt : n ≤ M)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (w : V →ₗ[F] Polynomial F)
    (v : V)
    (hwdeg : (w v).natDegree ≤ W) :
    (hassePowerFactorLinear f M n hnt hf hfdeg w v).natDegree
      ≤ W + n * (f.natDegree - 1) := by
  obtain ⟨w₁, hw₁, hw₁deg⟩ :=
    ln97_6_49 (w v) f M n hnt hf hfdeg
  have hcanon :=
    hassePowerFactorLinear_spec
      (F := F) f M n hnt hf hfdeg w v
  have hw₁' :
      (hasseDeriv n) (f ^ M * w v) =
        f ^ (M - n) * w₁ := by
    simpa [mul_comm] using hw₁
  have heq :
      hassePowerFactorLinear f M n hnt hf hfdeg w v = w₁ := by
    apply residualPowerMulLinear_injective
      (F := F) f M n hf
    change f ^ (M - n) *
        hassePowerFactorLinear f M n hnt hf hfdeg w v =
      f ^ (M - n) * w₁
    exact hcanon.symm.trans hw₁'
  rw [heq]
  exact le_trans hw₁deg
    (Nat.add_le_add_right hwdeg _)

end LN97
end MagicSquares
