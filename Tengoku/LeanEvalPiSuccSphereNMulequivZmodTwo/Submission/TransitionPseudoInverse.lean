import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.LevelSet
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.PolarDecompositionCLM

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The canonical transition automorphism as a globally defined smooth field

`SameFiberFrameJetNormalization.transition_unique` says that at a fiber point
of `X` at most one gauge `Φ` satisfies `D Y(p) = Φ ∘ D X(p)`, and
`transition_bijective` says that it is invertible.  Neither statement produces
`Φ`, and the bridge entry needs it as a *field*, smooth in the ambient point.

This file supplies it.  The derivative `D X(x) : ℝ^{n+1} →L ℝ^n` has the
gradient rows of `X` as its rows, so its transpose

`coDeriv X x : ℝ^n →L ℝ^{n+1}`, `w ↦ ∑ i, w i • ∇ gᵢ(x)`,

is *globally* smooth, and so is the Gram field
`gram X x = D X(x) ∘ coDeriv X x`.  Wherever the Gram field is invertible —
in particular at every regular point of `X` — the **Moore--Penrose transition**

`transition X Y x = D Y(x) ∘ coDeriv X x ∘ (gram X x)⁻¹`

is defined, and it is smooth there because inversion is smooth at a unit of a
complete normed algebra.  On the common fiber it *is* the canonical transition:
`coDeriv X p ∘ (gram X p)⁻¹` is a right inverse of `D X(p)`, so
`transition X Y p ∘ D X(p)` and `D Y(p)` differ by a map that annihilates the
kernel of `D X(p)` — and the two kernels agree, because both presentations
vanish along the same curve.

Contents:

* `coDeriv`, `gram`, `transition` and their regularity;
* `unitSet` — the open set where the construction is defined;
* `transition_comp` — the defining property on the fiber;
* `fderiv_eq_zero_of_ker` — the kernel comparison from one common tangent
  vector, via rank--nullity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission
namespace TransitionPseudoInverse

variable {n : ℕ}

/-! ## Units of the endomorphism algebra -/

section Units

variable {k : ℕ}

theorem apply_eq_mulVec
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (v : Fin k → ℝ) :
    A (WithLp.toLp 2 v) =
      WithLp.toLp 2 (Matrix.mulVec (PolarDecompositionCLM.clmMatrix A) v) := by
  conv_lhs => rw [← PolarDecompositionCLM.toEuclideanCLM_clmMatrix A]
  rfl

theorem det_clmMatrix_ne_zero_of_injective
    {A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    (h : Function.Injective A) :
    (PolarDecompositionCLM.clmMatrix A).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hmul⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := PolarDecompositionCLM.clmMatrix A)).mpr hdet
  have hA : A (WithLp.toLp 2 v) = 0 := by
    rw [apply_eq_mulVec, hmul]
    rfl
  have h0 : A (WithLp.toLp 2 v) = A 0 := by rw [hA, map_zero]
  have := h h0
  apply hv
  have hcoe := congrArg (WithLp.ofLp (p := 2)) this
  simpa using hcoe

theorem isUnit_of_det_clmMatrix_ne_zero
    {A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    (h : (PolarDecompositionCLM.clmMatrix A).det ≠ 0) : IsUnit A := by
  have hM : IsUnit (PolarDecompositionCLM.clmMatrix A) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  have hmap := hM.map (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ))
  rwa [PolarDecompositionCLM.toEuclideanCLM_clmMatrix] at hmap

theorem isUnit_of_injective
    {A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    (h : Function.Injective A) : IsUnit A :=
  isUnit_of_det_clmMatrix_ne_zero (det_clmMatrix_ne_zero_of_injective h)

end Units

/-! ## The transpose of the derivative -/

/-- The transpose of the derivative of a presentation, assembled from its
gradient rows.  This is globally smooth in the ambient point.-/
def coDeriv (X : FramedLevelSet n) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  ∑ i : Fin n, (EuclideanSpace.proj i).smulRight (gradVec X.g i x)

theorem contDiff_fderiv (X : FramedLevelSet n) :
    ContDiff ℝ ∞ fun x => fderiv ℝ X.g x :=
  X.smooth.fderiv_right (by simp)

theorem contDiff_coDeriv (X : FramedLevelSet n) :
    ContDiff ℝ ∞ (coDeriv X) := by
  refine ContDiff.sum fun i _ => ?_
  exact contDiff_const.smulRight (contDiff_gradVec X.g X.smooth i)

/-- **The transpose property.**-/
theorem inner_coDeriv (X : FramedLevelSet n)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (w : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ⟪coDeriv X x w, v⟫ = ⟪w, fderiv ℝ X.g x v⟫ := by
  rw [coDeriv, sum_apply, sum_inner]
  have hterm : ∀ i : Fin n,
      ⟪((EuclideanSpace.proj i).smulRight (gradVec X.g i x)) w, v⟫
        = WithLp.ofLp w i * WithLp.ofLp (fderiv ℝ X.g x v) i := by
    intro i
    show ⟪(EuclideanSpace.proj (𝕜 := ℝ) i) w • gradVec X.g i x, v⟫ = _
    rw [real_inner_smul_left, inner_gradVec]
    rfl
  simp_rw [hterm]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-! ## The Gram field -/

/-- The Gram field of the gradient rows.-/
def gram (X : FramedLevelSet n) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (fderiv ℝ X.g x).comp (coDeriv X x)

theorem contDiff_gram (X : FramedLevelSet n) : ContDiff ℝ ∞ (gram X) :=
  (contDiff_fderiv X).clm_comp (contDiff_coDeriv X)

theorem inner_gram_self (X : FramedLevelSet n)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (w : EuclideanSpace ℝ (Fin n)) :
    ⟪w, gram X x w⟫ = ‖coDeriv X x w‖ ^ 2 := by
  have hstep : ⟪w, gram X x w⟫ =
      ⟪coDeriv X x w, coDeriv X x w⟫ := (inner_coDeriv X x w (coDeriv X x w)).symm
  rw [hstep, real_inner_self_eq_norm_sq]

theorem coDeriv_injective (X : FramedLevelSet n)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : Function.Surjective (fderiv ℝ X.g x)) :
    Function.Injective (coDeriv X x) := by
  intro w₁ w₂ hw
  have hzero : coDeriv X x (w₁ - w₂) = 0 := by
    rw [map_sub, hw, sub_self]
  have hall : ∀ u : EuclideanSpace ℝ (Fin n), ⟪w₁ - w₂, u⟫ = 0 := by
    intro u
    obtain ⟨v, hv⟩ := hx u
    rw [← hv, ← inner_coDeriv X x (w₁ - w₂) v, hzero, inner_zero_left]
  have := hall (w₁ - w₂)
  rw [inner_self_eq_zero] at this
  exact sub_eq_zero.mp this

theorem gram_injective (X : FramedLevelSet n)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : Function.Surjective (fderiv ℝ X.g x)) :
    Function.Injective (gram X x) := by
  intro w₁ w₂ hw
  have hzero : gram X x (w₁ - w₂) = 0 := by
    rw [map_sub, hw, sub_self]
  have hns : ‖coDeriv X x (w₁ - w₂)‖ ^ 2 = 0 := by
    rw [← inner_gram_self X x (w₁ - w₂), hzero, inner_zero_right]
  have hcd : coDeriv X x (w₁ - w₂) = 0 := by
    have : ‖coDeriv X x (w₁ - w₂)‖ = 0 := by
      nlinarith [norm_nonneg (coDeriv X x (w₁ - w₂))]
    exact norm_eq_zero.mp this
  have h0 : coDeriv X x (w₁ - w₂) = coDeriv X x 0 := by rw [hcd, map_zero]
  have := coDeriv_injective X hx h0
  exact sub_eq_zero.mp this

theorem isUnit_gram (X : FramedLevelSet n)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : Function.Surjective (fderiv ℝ X.g x)) : IsUnit (gram X x) :=
  isUnit_of_injective (gram_injective X hx)

/-- The open set on which the Moore--Penrose transition is defined.-/
def unitSet (X : FramedLevelSet n) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | IsUnit (gram X x)}

theorem isOpen_unitSet (X : FramedLevelSet n) : IsOpen (unitSet X) :=
  Units.isOpen.preimage (contDiff_gram X).continuous

/-! ## The Moore--Penrose transition field -/

/-- **The transition automorphism field.**-/
def transition (X Y : FramedLevelSet n) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (fderiv ℝ Y.g x).comp ((coDeriv X x).comp (Ring.inverse (gram X x)))

theorem contDiffOn_transition (X Y : FramedLevelSet n) :
    ContDiffOn ℝ ∞ (transition X Y) (unitSet X) := by
  intro x hx
  have hinv : ContDiffAt ℝ ∞ (fun y => Ring.inverse (gram X y)) x := by
    have hu : IsUnit (gram X x) := hx
    have h1 : ContDiffAt ℝ ∞ (Ring.inverse :
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        (gram X x) := by
      have := contDiffAt_ringInverse (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞)) hu.unit
      rwa [hu.unit_spec] at this
    exact h1.comp x (contDiff_gram X).contDiffAt
  exact (((contDiff_fderiv Y).contDiffAt.clm_comp
    ((contDiff_coDeriv X).contDiffAt.clm_comp hinv))).contDiffWithinAt

/-- **The transition solves the first-jet equation** at a point where the Gram
field is invertible and the two kernels agree.-/
theorem transition_comp (X Y : FramedLevelSet n)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hu : IsUnit (gram X p))
    (hker : ∀ w, fderiv ℝ X.g p w = 0 → fderiv ℝ Y.g p w = 0) :
    (transition X Y p).comp (fderiv ℝ X.g p) = fderiv ℝ Y.g p := by
  refine ContinuousLinearMap.ext fun v => ?_
  set u : EuclideanSpace ℝ (Fin (n + 1)) :=
    coDeriv X p (Ring.inverse (gram X p) (fderiv ℝ X.g p v)) with hu_def
  have hDXu : fderiv ℝ X.g p u = fderiv ℝ X.g p v := by
    have hmul : gram X p * Ring.inverse (gram X p) = 1 :=
      Ring.mul_inverse_cancel _ hu
    have h1 : (gram X p * Ring.inverse (gram X p)) (fderiv ℝ X.g p v)
        = fderiv ℝ X.g p v := by
      rw [hmul]
      rfl
    rw [mul_apply_eq_comp] at h1
    exact h1
  have hsub : fderiv ℝ X.g p (v - u) = 0 := by
    rw [map_sub, hDXu, sub_self]
  have hY := hker _ hsub
  rw [map_sub, sub_eq_zero] at hY
  show fderiv ℝ Y.g p u = fderiv ℝ Y.g p v
  exact hY.symm

/-! ## Comparing the kernels from one common tangent vector -/

/-- **The kernel comparison.**  At a regular point of `X`, the kernel of
`D X(p)` is a line; so a single nonzero vector annihilated by both derivatives
forces the kernel of `D X(p)` to be contained in that of `D Y(p)`.-/
theorem fderiv_eq_zero_of_ker (X Y : FramedLevelSet n)
    {p : EuclideanSpace ℝ (Fin (n + 1))}
    (hsurj : Function.Surjective (fderiv ℝ X.g p))
    (t : EuclideanSpace ℝ (Fin (n + 1))) (ht : t ≠ 0)
    (hXt : fderiv ℝ X.g p t = 0) (hYt : fderiv ℝ Y.g p t = 0) :
    ∀ w, fderiv ℝ X.g p w = 0 → fderiv ℝ Y.g p w = 0 := by
  set L : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (fderiv ℝ X.g p).toLinearMap with hL
  have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := LinearMap.finrank_range_add_finrank_ker L
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by
    simp
  have hF : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have hrk : Module.finrank ℝ (LinearMap.range L) = n := by
    rw [hrange]
    rw [finrank_top]
    exact hF
  have hker : Module.finrank ℝ (LinearMap.ker L) = 1 := by
    rw [hrk, hE] at hdim
    omega
  have hmemt : t ∈ LinearMap.ker L := hXt
  have hle : (ℝ ∙ t) ≤ LinearMap.ker L := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hmemt
  have hspan : Module.finrank ℝ (ℝ ∙ t) = 1 := finrank_span_singleton ht
  have heq : (ℝ ∙ t) = LinearMap.ker L :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan, hker])
  intro w hw
  have hwmem : w ∈ LinearMap.ker L := hw
  rw [← heq] at hwmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hwmem
  rw [map_smul, hYt, smul_zero]

end TransitionPseudoInverse
end Submission
