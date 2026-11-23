import Tengoku.NavierStokesEuler.Euler.PacketGeometryData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact scale normalization from the actual parent frame and shear.
The physical interval ends at the chosen scaled horizon; no extension
beyond the source time interval is required. -/

noncomputable section

namespace EulerPacketMovingFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerPacketNormalizedPrimary EulerPacketCrossProduct

/--
@isnad1 id=other.0h5v.s8.3c3901df33a3 from=translated src=- shape=c6e8e2b7 vocab=c77499b5
-/
theorem activation_coupling_match (B : ℝ → Space →L[ℝ] Space)
    (m v : ℝ → Space) (t₀ ε : ℝ) :
    let a := normalizedCoupling (B t₀) (m t₀) (v t₀)
    rescaledFrame B m v t₀ a ε 0 0 1 = a := by
  simp [rescaledFrame,physicalTime,frameMatrix,frame,normalizedCoupling]

/--
@isnad1 id=other.2h5v.s8.402e8ef496b9 from=translated src=- shape=77895efc vocab=4eb844aa
-/
theorem activation_tilt_match (B : ℝ → Space →L[ℝ] Space)
    (m v : ℝ → Space) (t₀ ε : ℝ)
    (ha : normalizedCoupling (B t₀) (m t₀) (v t₀) ≠ 0)
    (hβ : 0 ≤ normalizedTilt (B t₀) (m t₀) (v t₀)) :
    let a := normalizedCoupling (B t₀) (m t₀) (v t₀)
    let σ := Real.sqrt (normalizedTilt (B t₀) (m t₀) (v t₀))
    rescaledFrame B m v t₀ a ε 0 2 1 = a*σ^2 := by
  dsimp only
  rw [Real.sq_sqrt hβ]
  simp only [rescaledFrame,physicalTime,mul_zero,add_zero,frameMatrix,frame,
    Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero,normalizedTilt]
  exact (mul_div_cancel₀ _ ha).symm

/--
@isnad1 id=other.2h5v.s6.6bfd4062eaaf from=translated src=- shape=d6dcddfe vocab=4039f00e
-/
theorem activation_shear_match (c : ℝ) (m v : ℝ → Space) (t₀ a : ℝ)
    (ha : 0 < a) (hh : 0 < primaryShear c m v t₀) :
    let ε := Real.sqrt (a/primaryShear c m v t₀)
    0 < ε ∧ rescaledShear c m v t₀ a ε 0 = a/ε^2 := by
  dsimp only
  have hratio := div_pos ha hh
  refine ⟨Real.sqrt_pos.mpr hratio,?_⟩
  rw [Real.sq_sqrt hratio.le]
  simp only [rescaledShear,physicalTime,mul_zero,add_zero]
  field_simp

/--
@isnad1 id=eq.2h4v.s5.021334cd548d from=translated src=- shape=58bcca08 vocab=550287c0
-/
theorem activation_horizon_exact (t₀ T a ε : ℝ) (ha : a ≠ 0) (hε : ε ≠ 0) :
    physicalTime t₀ a ε (a*(T-t₀)/ε) = T := by
  unfold physicalTime
  field_simp
  ring

/--
@isnad1 id=mapsto.2h4v.s6.31337cb11a6a from=translated src=- shape=0e7892a3 vocab=56e94034
-/
theorem activation_horizon_maps (t₀ T a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    MapsTo (physicalTime t₀ a ε) (Icc 0 (a*(T-t₀)/ε)) (Icc t₀ T) := by
  intro s hs
  constructor
  · change t₀ ≤ t₀+(ε/a)*s
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hε.le ha.le) hs.1)
  · calc
      physicalTime t₀ a ε s ≤ physicalTime t₀ a ε (a*(T-t₀)/ε) := by
        unfold physicalTime
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs.2 (div_nonneg hε.le ha.le))
      _ = T := activation_horizon_exact t₀ T a ε ha.ne' hε.ne'

end EulerPacketMovingFrame
