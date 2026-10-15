import Tengoku.NavierStokesEuler.Euler.IsometricActionCalculus
import Tengoku.NavierStokesEuler.Euler.ParameterSobolevBlocks

/-!
# Exact word-norm invariance along a genuine isometric orbit

Every actual derivative word of a smooth linear-isometric orbit is the orbit
of its derivative at zero. Consequently its fixed-Sobolev word block is
independent of the translation parameter, with constant one and no radius
change. This applies equally to spatial L² and its time-function spaces.
-/

noncomputable section

namespace EulerIsometricAction

open ContinuousLinearMap Finset EulerParameterWordGevrey
open scoped ContDiff

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (τ : X → E →ₗᵢ[ℝ] E) (hadd : ∀ a b u, τ a (τ b u) = τ (a+b) u)
  (hzero : ∀ u, τ 0 u = u)

def derivativeAtZero (u : E) (v : X) : E := fderiv ℝ (fun a => τ a u) 0 v

include hadd in
/--
@isnad1 id=eq.2h6v.s9.796f3cc598a0 from=translated src=- shape=879c55ba vocab=04d6896e
-/
theorem derivativeAtZero_translation (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u)) (v a : X) :
    τ a (derivativeAtZero τ u v) = fderiv ℝ (fun b => τ b u) a v := by
  have h := hasFDerivAt_all τ hadd u (fderiv ℝ (fun b => τ b u) 0)
    ((hu.differentiable (by simp) (0 : X)).hasFDerivAt) a
  exact (congrArg (fun D : X →L[ℝ] E => D v) h.fderiv).symm

include hadd in
/--
@isnad1 id=contdiff.2h5v.s9.9f78a126a8b7 from=translated src=- shape=a64a9ec9 vocab=e2836b2b
-/
theorem derivativeAtZero_smooth (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u)) (v : X) :
    ContDiff ℝ ∞ (fun a => τ a (derivativeAtZero τ u v)) := by
  have he : (fun a => τ a (derivativeAtZero τ u v)) =
      fun a => fderiv ℝ (fun b => τ b u) a v :=
    funext (fun a => derivativeAtZero_translation τ hadd u hu v a)
  rw [he]
  exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

def wordAtZero (directions : ι → X) (u : E) {n : ℕ} (w : Fin n → ι) : E :=
  wordDerivative directions (fun a => τ a u) w 0

include hzero in
/--
@isnad1 id=eq.1h7v.s7.c44385205f3b from=translated src=- shape=0632db3c vocab=72d9b490
-/
theorem wordAtZero_zero (directions : ι → X) (u : E) (w : Fin 0 → ι) :
    wordAtZero τ directions u w = u := by
  simp only [wordAtZero,wordDerivative_zero,hzero]

include hadd in
/--
@isnad1 id=eq.2h9v.s8.337b1e53d783 from=translated src=- shape=6ac614a0 vocab=f0f0d188
-/
theorem wordAtZero_snoc (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    {n : ℕ} (w : Fin n → ι) (i : ι) :
    wordAtZero τ directions u (Fin.snoc w i) =
      wordAtZero τ directions (derivativeAtZero τ u (directions i)) w := by
  have he : directional directions (fun a => τ a u) i =
      fun a => τ a (derivativeAtZero τ u (directions i)) :=
    funext (fun a => (derivativeAtZero_translation τ hadd u hu (directions i) a).symm)
  unfold wordAtZero
  rw [wordDerivative_snoc directions _ hu w i 0,he]

include hadd hzero in
/--
@isnad1 id=eq.3h9v.s9.31ad3cb69e5a from=translated src=- shape=8cc9dc1c vocab=9d44de20
-/
theorem wordAtZero_translation (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    {n : ℕ} (w : Fin n → ι) (a : X) :
    τ a (wordAtZero τ directions u w) = wordDerivative directions (fun b => τ b u) w a := by
  induction n generalizing u with
  | zero => simp only [wordAtZero_zero τ hzero,wordDerivative_zero]
  | succ n ih =>
    have hw : wordAtZero τ directions u w =
        wordAtZero τ directions (derivativeAtZero τ u (directions (w (Fin.last n)))) (Fin.init w) := by
      simpa only [Fin.snoc_init_self] using wordAtZero_snoc τ hadd directions u hu (Fin.init w) (w (Fin.last n))
    rw [hw,ih _ (derivativeAtZero_smooth τ hadd u hu _) (Fin.init w)]
    have he : directional directions (fun b => τ b u) (w (Fin.last n)) =
        fun b => τ b (derivativeAtZero τ u (directions (w (Fin.last n)))) :=
      funext (fun b => (derivativeAtZero_translation τ hadd u hu _ b).symm)
    simpa only [Fin.snoc_init_self,he] using
      (wordDerivative_snoc directions (fun b => τ b u) hu (Fin.init w) (w (Fin.last n)) a).symm

include hadd hzero in
/--
@isnad1 id=contdiff.3h8v.s9.2c6968ab119a from=translated src=- shape=80aca8b9 vocab=fb3d231d
-/
theorem wordAtZero_smooth (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    {n : ℕ} (w : Fin n → ι) : ContDiff ℝ ∞ (fun a => τ a (wordAtZero τ directions u w)) := by
  have he : (fun a => τ a (wordAtZero τ directions u w)) =
      wordDerivative directions (fun b => τ b u) w :=
    funext (wordAtZero_translation τ hadd hzero directions u hu w)
  rw [he]
  exact wordDerivative_contDiff directions _ hu w

variable [Fintype ι]

include hadd hzero in
/--
@isnad1 id=eq.3h8v.s9.807e5ec4f0cf from=translated src=- shape=00c7795a vocab=5c688d54
-/
theorem wordSum_orbit_constant (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    (n : ℕ) (a : X) : wordSum directions (fun b => τ b u) n a =
      wordSum directions (fun b => τ b u) n 0 := by
  unfold wordSum
  apply sum_congr rfl
  intro w _
  rw [← wordAtZero_translation τ hadd hzero directions u hu w a]
  exact (τ a).norm_map (wordAtZero τ directions u w)

include hadd hzero in
/--
@isnad1 id=eq.3h8v.s9.b6f04c450da5 from=translated src=- shape=9c95b2c0 vocab=1ead6a11
-/
theorem baseSize_orbit_constant (directions : ι → X) (q : ℕ) (u : E)
    (hu : ContDiff ℝ ∞ (fun a => τ a u)) (a : X) :
    baseSize directions q (fun b => τ b u) a = baseSize directions q (fun b => τ b u) 0 := by
  unfold baseSize
  apply sum_congr rfl
  intro k _
  exact wordSum_orbit_constant τ hadd hzero directions u hu k a

include hadd hzero in
/--
@isnad1 id=eq.3h9v.s9.7575e077fea8 from=translated src=- shape=71a4d13c vocab=d106190e
-/
theorem block_orbit_constant (directions : ι → X) (q : ℕ) (u : E)
    (hu : ContDiff ℝ ∞ (fun a => τ a u)) (n : ℕ) (a : X) :
    block directions q (fun b => τ b u) n a = block directions q (fun b => τ b u) n 0 := by
  unfold block
  apply sum_congr rfl
  intro w _
  have he : wordDerivative directions (fun b => τ b u) w =
      fun b => τ b (wordAtZero τ directions u w) :=
    (funext (wordAtZero_translation τ hadd hzero directions u hu w)).symm
  rw [he]
  exact baseSize_orbit_constant τ hadd hzero directions q _
    (wordAtZero_smooth τ hadd hzero directions u hu w) a

end EulerIsometricAction
