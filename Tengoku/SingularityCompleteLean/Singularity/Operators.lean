import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint
import Tengoku.Seed.Analysis.InnerProductSpace.LaxMilgram
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hilbert-space steps in the singularity argument

These are unconditional abstract operator lemmas. They do not construct a random
walk or assert that its Green function satisfies the hypotheses.
The scalar field may be real or complex; no self-adjointness is assumed.
-/

noncomputable section

open scoped InnerProductSpace
open RCLike ContinuousLinearMap

namespace Singularity

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The precise notion of coercivity needed in the proof.-/
def Coercive (T : E →L[𝕜] E) (c : ℝ) : Prop :=
  ∀ v, c * ‖v‖ ^ 2 ≤ re (inner 𝕜 (T v) v)

/-- The Green coercivity identity, valid for any right inverse of `I - P`.
@isnad1 id=eq.1h5v.s11.92b808c41d4a from=translated src=- shape=2e6a4b94 vocab=1dc58098
-/
theorem green_identity (P G : E →L[𝕜] E)
    (hG : ∀ v, G v - P (G v) = v) (v : E) :
    2 * re (inner 𝕜 (G v) v) - ‖v‖ ^ 2 =
      ‖G v‖ ^ 2 - ‖P (G v)‖ ^ 2 := by
  have hn := norm_sub_sq (𝕜 := 𝕜) (G v) (P (G v))
  rw [hG v] at hn
  have hi := congrArg (fun w => re (inner 𝕜 (G v) w)) (hG v)
  simp only [inner_sub_right, map_sub, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] at hi
  linarith

/-- `G = (I-P)⁻¹` is `1/2`-coercive if `P` is a contraction.
In particular, this argument does not require laziness or symmetry.
@isnad1 id=coercive.2h4v.s10.aa704ca060b6 from=translated src=- shape=06b093d5 vocab=be79a374
-/
theorem green_coercive (P G : E →L[𝕜] E)
    (hP : ∀ w, ‖P w‖ ≤ ‖w‖)
    (hG : ∀ v, G v - P (G v) = v) : Coercive G (1 / 2) := by
  intro v
  have hid := green_identity P G hG v
  have hsq : ‖P (G v)‖ ^ 2 ≤ ‖G v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hP _) 2
  linarith

/-- Coercivity supplies the lower bound used to prove closed range.
@isnad1 id=le.1h5v.s8.63feeb44e514 from=translated src=- shape=58a154a1 vocab=da7cf234
-/
theorem Coercive.norm_lower_bound {T : E →L[𝕜] E} {c : ℝ}
    (hT : Coercive T c) (v : E) : c * ‖v‖ ≤ ‖T v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    apply (mul_le_mul_iff_left₀ hnorm).mp
    have hi := re_inner_le_norm (𝕜 := 𝕜) (T v) v
    have hc := hT v
    nlinarith

/-- Coercivity implies injectivity.
@isnad1 id=injectiv.2h4v.s8.b4eec9c09a82 from=translated src=- shape=89674717 vocab=a1c64bcb
-/
theorem Coercive.injective {T : E →L[𝕜] E} {c : ℝ}
    (hT : Coercive T c) (hc : 0 < c) : Function.Injective T := by
  apply T.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  change T v = 0 at hv
  have h := hT.norm_lower_bound v
  rw [hv, norm_zero] at h
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp this

/-- Compression means `i* ∘ G ∘ i`, where `i` is an isometric inclusion.-/
def compression [CompleteSpace E] [CompleteSpace F]
    (i : F →ₗᵢ[𝕜] E) (G : E →L[𝕜] E) : F →L[𝕜] F :=
  i.toContinuousLinearMap.adjoint.comp (G.comp i.toContinuousLinearMap)

/-- Compression to a closed Hilbert subspace preserves the same coercivity constant.
@isnad1 id=coercive.1h6v.s8.6a4be73ceab2 from=translated src=- shape=b136fb85 vocab=a854146c
-/
theorem compression_coercive [CompleteSpace E] [CompleteSpace F]
    (i : F →ₗᵢ[𝕜] E) {G : E →L[𝕜] E} {c : ℝ}
    (hG : Coercive G c) : Coercive (compression i G) c := by
  intro v
  simpa only [compression, comp_apply, adjoint_inner_left,
    LinearIsometry.coe_toContinuousLinearMap, i.norm_map] using hG (i v)

/-- Closed range follows from the quantitative lower bound.
@isnad1 id=isclosed.2h4v.s8.e144a3cf8ef9 from=translated src=- shape=6dedb57b vocab=cef3520e
-/
theorem Coercive.isClosed_range [CompleteSpace E] {T : E →L[𝕜] E} {c : ℝ}
    (hT : Coercive T c) (hc : 0 < c) : IsClosed (Set.range T) := by
  have hanti : AntilipschitzWith ⟨c⁻¹, le_of_lt (inv_pos.mpr hc)⟩ T := by
    apply T.antilipschitz_of_bound
    intro v
    change ‖v‖ ≤ c⁻¹ * ‖T v‖
    exact (le_inv_mul_iff₀ hc).mpr (hT.norm_lower_bound v)
  exact hanti.isClosed_range T.uniformContinuous

/-- Surjectivity: a closed range with trivial orthogonal complement is all of `E`.
@isnad1 id=eq.2h4v.s8.ca80f29bda60 from=translated src=- shape=074393bb vocab=ca803359
-/
theorem Coercive.range_eq_top [CompleteSpace E] {T : E →L[𝕜] E} {c : ℝ}
    (hT : Coercive T c) (hc : 0 < c) : T.range = ⊤ := by
  have hclosed : IsClosed (T.range : Set E) := hT.isClosed_range hc
  have := hclosed.completeSpace_coe
  rw [← T.range.orthogonal_orthogonal, Submodule.eq_top_iff']
  intro v w hw
  have hTw : inner 𝕜 (T w) w = 0 := hw _ ⟨w, rfl⟩
  have hcw := hT w
  rw [hTw, map_zero] at hcw
  have hw0 : w = 0 := by
    have heq : c * ‖w‖ ^ 2 = 0 :=
      le_antisymm hcw (mul_nonneg hc.le (sq_nonneg _))
    have hs : ‖w‖ ^ 2 = 0 := (mul_eq_zero.mp heq).resolve_left hc.ne'
    have : ‖w‖ = 0 := sq_eq_zero_iff.mp hs
    exact norm_eq_zero.mp this
  simp [hw0]

/-- A coercive bounded operator has a bounded inverse.-/
def Coercive.equiv [CompleteSpace E] {T : E →L[𝕜] E} {c : ℝ}
    (hT : Coercive T c) (hc : 0 < c) : E ≃L[𝕜] E :=
  ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr (hT.injective hc)) (hT.range_eq_top hc)

/-- The boundary passage needs strong convergence of both vectors, not an
unjustified interchange of an entrywise double sum with a limit.
@isnad1 id=tendsto.2h9v.s9.c9f59c018dd6 from=translated src=- shape=e29459f9 vocab=4175d110
-/
theorem pairing_tendsto {α : Type*} {l : Filter α}
    (M : E →L[𝕜] E) {u v : α → E} {u₀ v₀ : E}
    (hu : Filter.Tendsto u l (nhds u₀)) (hv : Filter.Tendsto v l (nhds v₀)) :
    Filter.Tendsto (fun n => inner 𝕜 (u n) (M (v n))) l
      (nhds (inner 𝕜 u₀ (M v₀))) :=
  hu.inner (M.continuous.continuousAt.tendsto.comp hv)

end Singularity
