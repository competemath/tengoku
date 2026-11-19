import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.WavePacket
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Defs
import Tengoku.Seed.Analysis.Calculus.ContDiff.Deriv
import Tengoku.Seed.Analysis.Calculus.Deriv.Support

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# All derivatives of the rescaled off-support packet

The packet's `r`-th derivative has the exact `L¹` scaling `t⁻¹ ^ r`.
These facts provide the packet input for arbitrary-order integration by parts.
-/

open Function MeasureTheory Set
open scoped ContDiff

namespace QuadraticCarleson

set_option autoImplicit false

/-- Explicit normalized derivative of the rescaled packet.-/
noncomputable def iteratedWavePacketDeriv (r : ℕ) (s t u : ℝ) : ℝ :=
  t⁻¹ ^ (r + 1) * iteratedDeriv r baseBump ((u - s) / t)

/--
@isnad1 id=eq.0h2v.s4.ceb0791651bc from=translated src=- shape=be78588b vocab=a68e129c
-/
@[simp] theorem iteratedWavePacketDeriv_zero (s t : ℝ) :
    iteratedWavePacketDeriv 0 s t = wavePacket s t := by
  funext u
  simp [iteratedWavePacketDeriv, wavePacket]

/--
@isnad1 id=contdiff.0h1v.s5.aa3c171520a8 from=translated src=- shape=b5caa6a3 vocab=9221d7f6
-/
theorem smooth_iteratedDeriv_baseBump (r : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv r baseBump) := by
  induction r with
  | zero => simpa using baseBump_smooth
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

/--
@isnad1 id=contdiff.0h3v.s5.ce9b0dad6041 from=translated src=- shape=b74749e1 vocab=f7dc10d4
-/
theorem smooth_iteratedWavePacketDeriv (r : ℕ) (s t : ℝ) :
    ContDiff ℝ ∞ (iteratedWavePacketDeriv r s t) := by
  exact contDiff_const.mul <|
    (smooth_iteratedDeriv_baseBump r).comp
      ((contDiff_id.sub contDiff_const).div_const t)

/--
@isnad1 id=continuo.0h3v.s4.6fa39553ca2e from=translated src=- shape=167349ff vocab=0634245f
-/
theorem continuous_iteratedWavePacketDeriv (r : ℕ) (s t : ℝ) :
    Continuous (iteratedWavePacketDeriv r s t) :=
  (smooth_iteratedWavePacketDeriv r s t).continuous

/--
@isnad1 id=hasderiv.1h4v.s6.b07a9a42ea37 from=translated src=- shape=f1592493 vocab=a8bd1420
-/
theorem hasDerivAt_iteratedWavePacketDeriv (r : ℕ) (s : ℝ) {t : ℝ}
    (_ht : t ≠ 0) (u : ℝ) :
    HasDerivAt (iteratedWavePacketDeriv r s t)
      (iteratedWavePacketDeriv (r + 1) s t u) u := by
  have hd := ((smooth_iteratedDeriv_baseBump r).differentiable (by simp)
    ((u - s) / t)).hasDerivAt
  have h := (hd.comp u (((hasDerivAt_id u).sub_const s).div_const t)).const_mul
    (t⁻¹ ^ (r + 1))
  apply h.congr_deriv
  simp only [iteratedWavePacketDeriv, iteratedDeriv_succ, pow_succ,
    div_eq_mul_inv, one_mul]
  ring

/--
@isnad1 id=eq.1h3v.s5.b45f328430ee from=translated src=- shape=ad9c77d3 vocab=bd7c7a6d
-/
theorem iteratedWavePacketDeriv_eq_iteratedDeriv (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : t ≠ 0) :
    iteratedWavePacketDeriv r s t = iteratedDeriv r (wavePacket s t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ← ih]
    funext u
    exact (hasDerivAt_iteratedWavePacketDeriv r s ht u).deriv.symm

/--
@isnad1 id=le.0h1v.s6.2bdd17c9ecf8 from=translated src=- shape=dc3343b6 vocab=1f1db51a
-/
theorem iteratedDeriv_baseBump_tsupport_subset (r : ℕ) :
    tsupport (iteratedDeriv r baseBump) ⊆ Icc (-1 / 4 : ℝ) (1 / 4 : ℝ) := by
  induction r with
  | zero =>
    simpa only [iteratedDeriv_zero, tsupport] using
      (closure_minimal baseBump_support isClosed_Icc)
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

/--
@isnad1 id=le.1h3v.s6.88c73a5488b7 from=translated src=- shape=ea7637f5 vocab=607f0fab
-/
theorem iteratedWavePacketDeriv_support (r : ℕ) {s t : ℝ} (ht : 0 < t) :
    support (iteratedWavePacketDeriv r s t) ⊆ Icc (s - t / 4) (s + t / 4) := by
  intro u hu
  have hbase : iteratedDeriv r baseBump ((u - s) / t) ≠ 0 := by
    intro hzero
    apply hu
    simp [iteratedWavePacketDeriv, hzero]
  have hmem := iteratedDeriv_baseBump_tsupport_subset r (subset_tsupport _ hbase)
  constructor
  · have hscaled := (le_div_iff₀ ht).mp hmem.1
    linarith
  · have hscaled := (div_le_iff₀ ht).mp hmem.2
    linarith

/--
@isnad1 id=hascompa.1h3v.s4.e4da7ca4a49f from=translated src=- shape=0b8fb426 vocab=069f1907
-/
theorem iteratedWavePacketDeriv_hasCompactSupport (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) : HasCompactSupport (iteratedWavePacketDeriv r s t) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (iteratedWavePacketDeriv_support r ht)

/--
@isnad1 id=eq.1h3v.s5.23e999b6bc39 from=translated src=- shape=f29b9944 vocab=c170dfd5
-/
theorem iteratedWavePacketDeriv_left_third_eq_zero (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) : iteratedWavePacketDeriv r s t (s - t / 3) = 0 := by
  apply notMem_support.mp
  intro hmem
  have h := iteratedWavePacketDeriv_support r ht hmem
  linarith [h.1]

/--
@isnad1 id=eq.1h3v.s5.ff63b864c33e from=translated src=- shape=f29b9944 vocab=a61b67b7
-/
theorem iteratedWavePacketDeriv_right_third_eq_zero (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) : iteratedWavePacketDeriv r s t (s + t / 3) = 0 := by
  apply notMem_support.mp
  intro hmem
  have h := iteratedWavePacketDeriv_support r ht hmem
  linarith [h.2]

/--
@isnad1 id=integrab.0h1v.s5.1492077b4037 from=translated src=- shape=e65012e3 vocab=4d4b7be4
-/
theorem integrable_iteratedDeriv_baseBump (r : ℕ) :
    Integrable (iteratedDeriv r baseBump) := by
  apply (smooth_iteratedDeriv_baseBump r).continuous.integrable_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport _).trans (iteratedDeriv_baseBump_tsupport_subset r))

/--
@isnad1 id=integrab.0h1v.s5.c37d3c65e905 from=translated src=- shape=318603bb vocab=3a4ffa34
-/
theorem integrable_abs_iteratedDeriv_baseBump (r : ℕ) :
    Integrable (fun u : ℝ ↦ |iteratedDeriv r baseBump u|) :=
  (integrable_iteratedDeriv_baseBump r).abs

/--
@isnad1 id=integrab.1h3v.s5.8048ef5a1fd2 from=translated src=- shape=42d79f64 vocab=d19ae19a
-/
theorem integrable_iteratedWavePacketDeriv (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) : Integrable (iteratedWavePacketDeriv r s t) :=
  (continuous_iteratedWavePacketDeriv r s t).integrable_of_hasCompactSupport
    (iteratedWavePacketDeriv_hasCompactSupport r s ht)

/--
@isnad1 id=integrab.1h3v.s5.25e90aaf6b79 from=translated src=- shape=540338ad vocab=86ad856d
-/
theorem integrable_abs_iteratedWavePacketDeriv (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) : Integrable (fun u : ℝ ↦ |iteratedWavePacketDeriv r s t u|) :=
  (integrable_iteratedWavePacketDeriv r s ht).abs

/--
@isnad1 id=eq.1h3v.s6.b00cf1947c2f from=translated src=- shape=dfd20bf7 vocab=b2421a06
-/
theorem integral_abs_iteratedWavePacketDeriv (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) :
    (∫ u : ℝ, |iteratedWavePacketDeriv r s t u|) =
      t⁻¹ ^ r * ∫ v : ℝ, |iteratedDeriv r baseBump v| := by
  simp_rw [iteratedWavePacketDeriv, abs_mul, abs_pow, abs_inv, abs_of_pos ht]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun u : ℝ ↦ |iteratedDeriv r baseBump (u / t)|) s]
  have hscale : (∫ u : ℝ, |iteratedDeriv r baseBump (u / t)|) =
      t * ∫ v : ℝ, |iteratedDeriv r baseBump v| := by
    simpa [abs_of_pos ht, smul_eq_mul] using
      Measure.integral_comp_div (fun v : ℝ ↦ |iteratedDeriv r baseBump v|) t
  rw [hscale, pow_succ]
  field_simp [ht.ne']

end QuadraticCarleson
