import Tengoku.Seed.NumberTheory.ZetaValues
import Tengoku.Seed.Analysis.Fourier.ZMod
import Tengoku.Seed.NumberTheory.LSeries.Dirichlet
import Tengoku.Seed.NumberTheory.DirichletCharacter.Orthogonality
import Tengoku.Seed.NumberTheory.DirichletCharacter.Bounds
import Tengoku.Seed.Analysis.SumOverResidueClass
import Tengoku.Seed.Analysis.PSeries
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic
import Tengoku.Seed.Data.ZMod.Units
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset Real

namespace Ws47
namespace BSpan

def wt (N : ℕ) (t : ℕ) : ℤ := 6 * (t : ℤ) ^ 2 - 6 * (N : ℤ) * (t : ℤ) + (N : ℤ) ^ 2

variable {N : ℕ} [NeZero N]

noncomputable def cosZ (a : ZMod N) : ℝ := Real.cos (2 * π * a.val / N)

end Ws47.BSpan

namespace Ws47
namespace BSpan

open Finset Real

variable {N : ℕ} [NeZero N]

noncomputable def psi (g : ZMod N → ℝ) (k : ZMod N) : ℝ := ∑ r : ZMod N, g r * cosZ (k * r)

noncomputable def Zres (M : ℕ) (c : ZMod M) : ℝ := ∑' m : ℕ, 1 / ((c.val + M * m : ℕ) : ℝ) ^ 2

end Ws47.BSpan

namespace Ws47
namespace BSpan

open Finset Real

section D
variable {N : ℕ} [NeZero N]

end D

section E
variable {N : ℕ} [NeZero N]

noncomputable def sinZ (a : ZMod N) : ℝ := Real.sin (2 * π * a.val / N)

end E

section F
variable (N : ℕ) [NeZero N]

def fam (s : ZMod N) : ZMod N → ℚ := fun r : ZMod N =>
  ((6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2 : ℤ) : ℚ)

omit [NeZero N] in
/--
@isnad1 id=eq.0h3v.s5.ab30ac1d7d04 from=translated src=- shape=2e31a381 vocab=6a10a7b7
-/
theorem fam_apply (s r : ZMod N) : fam N s r = ((wt N (s * r).val : ℤ) : ℚ) := rfl

variable {N}

omit [NeZero N] in
/--
@isnad1 id=eq.1h2v.s4.505d62a5bca1 from=translated src=- shape=9cd96027 vocab=04784122
-/
theorem wt_sub (t : ℕ) (ht : t ≤ N) : wt N (N - t) = wt N t := by
  unfold wt; push_cast [Nat.cast_sub ht]; ring

/--
@isnad1 id=eq.0h3v.s5.642cea1d637b from=translated src=- shape=3dc92769 vocab=fbd28c85
-/
theorem fam_neg (s r : ZMod N) : fam N s (-r) = fam N s r := by
  rw [fam_apply, fam_apply, mul_neg, ZMod.neg_val]
  split_ifs with h
  · rw [h, ZMod.val_zero]
  · rw [wt_sub _ (ZMod.val_lt _).le]

noncomputable def T : (ZMod N → ℚ) →ₗ[ℚ] (ZMod N → ℚ) :=
  ∑ s : ZMod N, (LinearMap.proj s : (ZMod N → ℚ) →ₗ[ℚ] ℚ).smulRight (fam N s)

/--
@isnad1 id=eq.0h3v.s7.02fc45b19408 from=translated src=- shape=97ab91b6 vocab=c7c8d93f
-/
theorem T_apply (c : ZMod N → ℚ) (r : ZMod N) : T c r = ∑ s : ZMod N, c s * fam N s r := by
  simp [T, LinearMap.sum_apply, LinearMap.smulRight_apply, Finset.sum_apply, smul_eq_mul]

/--
@isnad1 id=eq.0h3v.s8.43daf2b8e232 from=translated src=- shape=76651312 vocab=f3443346
-/
theorem T_neg (c : ZMod N → ℚ) (r : ZMod N) : T c (-r) = T c r := by
  simp only [T_apply, fam_neg]

def evenSub (N : ℕ) [NeZero N] : Submodule ℚ (ZMod N → ℚ) where
  carrier := {φ | ∀ r : ZMod N, φ (-r) = φ r}
  add_mem' ha hb r := by simp [Pi.add_apply, ha r, hb r]
  zero_mem' r := rfl
  smul_mem' c φ hφ r := by simp [Pi.smul_apply, hφ r]

noncomputable def TE : evenSub N →ₗ[ℚ] evenSub N :=
  (T (N := N)).restrict fun φ _ => fun r => T_neg φ r

end F

end Ws47.BSpan
