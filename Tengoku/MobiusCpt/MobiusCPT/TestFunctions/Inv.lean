import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Lemmas
import Tengoku.Seed.Geometry.Manifold.Algebra.LieGroup
import Tengoku.MobiusCpt.MobiusCPT.TestFunctions.Basic
import Tengoku.MobiusCpt.MobiusCPT.TestFunctions.CNorm
import Tengoku.MobiusCpt.MobiusCPT.TestFunctions.Support

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MobiusCPT.TestFunctions.Inv

The inversion of the circle and its action on smooth test functions.
-/

namespace MobiusCPT

open scoped ContDiff Manifold Topology

noncomputable section

/-- [T26], §3; the inversion `z ↦ z⁻¹` transported to test functions, `f ↦ f ∘ z⁻¹`.-/
def inv (f : TestFn) : TestFn :=
  ⟨fun z => f z⁻¹, by
    change ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      ((f : Circle → ℂ) ∘ (fun z : Circle => z⁻¹))
    exact (ContMDiffMap.contMDiff f).comp (contMDiff_inv (𝓡 1) ∞)⟩

/-- [T26], §3; evaluation of test-function inversion is pointwise circle inversion.
@isnad1 id=eq.0h2v.s5.21f9493a1e78 from=translated src=- shape=e7475efc vocab=6d7e3f57
-/
@[simp] theorem inv_apply (f : TestFn) (z : Circle) : inv f z = f z⁻¹ :=
  rfl

/-- [T26], §3; in the angle picture inversion is the reflection `θ ↦ -θ`.
@isnad1 id=eq.0h1v.s4.b961a120d9f7 from=translated src=- shape=ee6ee58b vocab=cafa1a99
-/
theorem toAngle_inv (f : TestFn) : toAngle (inv f) = fun θ => toAngle f (-θ) := by
  funext θ
  simp [toAngle]

/-- [T26], §3; inversion preserves addition of test functions.
@isnad1 id=eq.0h2v.s5.5099868e4dfe from=translated src=- shape=a13ca989 vocab=66f110a0
-/
theorem inv_add (f g : TestFn) : inv (f + g) = inv f + inv g := by
  apply TestFn.ext
  intro z
  change (f + g) z⁻¹ = f z⁻¹ + g z⁻¹
  rfl

/-- [T26], §3; inversion commutes with complex scalar multiplication.
@isnad1 id=eq.0h2v.s4.cfe30d2bbefe from=translated src=- shape=12ed3a53 vocab=553119f3
-/
theorem inv_smul (c : ℂ) (f : TestFn) : inv (c • f) = c • inv f := by
  apply TestFn.ext
  intro z
  change (c • f) z⁻¹ = c * f z⁻¹
  rfl

/-- [T26], §3; circle inversion induces an involution on test functions.
@isnad1 id=eq.0h1v.s3.5abbc6768f67 from=translated src=- shape=47dcad53 vocab=3c0edb5a
-/
theorem inv_involutive (f : TestFn) : inv (inv f) = f := by
  apply TestFn.ext
  intro z
  simp

/-- [T26], §3; inversion as a `ℂ`-linear map on `C^∞(S¹)`.-/
def invₗ : TestFn →ₗ[ℂ] TestFn where
  toFun := inv
  map_add' := inv_add
  map_smul' := inv_smul

/-- [T26], §3; inversion exchanges the two open semicircles.
@isnad1 id=iff.0h1v.s3.0fc2a9f5eac9 from=translated src=- shape=56a69fcb vocab=2c7cbdac
-/
theorem inv_supp (f : TestFn) : SuppUpper f ↔ SuppLower (inv f) := by
  constructor
  · intro hf z hz
    change 0 < (z : ℂ).im at hz
    have hz' : z⁻¹ ∈ lowerArc := by
      change ((z⁻¹ : Circle) : ℂ).im < 0
      rw [Circle.coe_inv_eq_conj, Complex.conj_im]
      exact neg_lt_zero.mpr hz
    have hzero := hf z⁻¹ hz'
    simpa only [inv_apply] using hzero
  · intro hf z hz
    change (z : ℂ).im < 0 at hz
    have hz' : z⁻¹ ∈ upperArc := by
      change 0 < ((z⁻¹ : Circle) : ℂ).im
      rw [Circle.coe_inv_eq_conj, Complex.conj_im]
      exact neg_pos.mpr hz
    have hzero := hf z⁻¹ hz'
    simpa only [inv_apply, inv_inv] using hzero

/-- [T26], §3; inversion exchanges the two open semicircles in the reverse direction.
@isnad1 id=iff.0h1v.s3.a374c039ec19 from=translated src=- shape=56a69fcb vocab=2c7cbdac
-/
theorem inv_supp' (f : TestFn) : SuppLower f ↔ SuppUpper (inv f) := by
  simpa only [inv_involutive] using (inv_supp (inv f)).symm

/-- [T26], §3; angle derivatives transform under inversion by reflection and a sign.
@isnad1 id=eq.0h2v.s5.c2660eba827f from=translated src=- shape=f8a9452f vocab=a4bb0a0d
-/
theorem angleDeriv_inv (j : ℕ) (f : TestFn) :
    angleDeriv j (inv f) = fun θ => (-1 : ℂ) ^ j * angleDeriv j f (-θ) := by
  funext θ
  change iteratedDeriv j (toAngle (inv f)) θ =
    (-1 : ℂ) ^ j * iteratedDeriv j (toAngle f) (-θ)
  rw [toAngle_inv]
  simpa [Complex.real_smul] using iteratedDeriv_comp_neg j (toAngle f) θ

/-- [T26], Lemma 3.9; the sup norm of an angle derivative is invariant under test-function
inversion.
@isnad1 id=eq.0h2v.s6.5c274dbcbece from=translated src=- shape=30624b03 vocab=b80bedf5
-/
theorem norm_angleDerivB_inv (j : ℕ) (f : TestFn) :
    ‖angleDerivB j (inv f)‖ = ‖angleDerivB j f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le
      (f := angleDerivB j (inv f)) (C := ‖angleDerivB j f‖) (norm_nonneg _)).2
    intro θ
    rw [angleDerivB_apply, angleDeriv_inv]
    simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
      norm_angleDeriv_le j f (-θ)
  · apply (BoundedContinuousFunction.norm_le
      (f := angleDerivB j f) (C := ‖angleDerivB j (inv f)‖) (norm_nonneg _)).2
    intro θ
    rw [angleDerivB_apply]
    have hθ := norm_angleDeriv_le j (inv f) (-θ)
    rw [angleDeriv_inv] at hθ
    simpa only [neg_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using hθ

/-- [T26], Lemma 3.9; the angle-derivative `C^N` norm is invariant under inversion.
@isnad1 id=eq.0h2v.s3.1475e40d75ce from=translated src=- shape=2793bf2c vocab=b6fe905d
-/
theorem cnorm_inv (N : ℕ) (f : TestFn) : cnorm N (inv f) = cnorm N f := by
  apply NNReal.eq
  rw [cnorm_eq, cnorm_eq]
  exact Finset.sum_congr rfl (fun j hj => norm_angleDerivB_inv j f)

end

end MobiusCPT
