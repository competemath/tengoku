import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.ContinuousCover
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.Analysis.SumIntegralComparisons
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The volume lower bound for normalized cube covers

This file computes the volume of the `ℓ₁` unit ball and proves the exact finite lower bound (46)
for every normalized ranked cover of a positive cube.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace BurningPath

/-- The closed `ℓ₁` ball with center `c` and radius `r`.-/
def l1ClosedBall {k : ℕ} (c : Fin k → ℝ) (r : ℝ) : Set (Fin k → ℝ) :=
  {x | realL1Dist x c ≤ r}

private theorem l1ClosedBall_eq_preimage_add {k : ℕ} (c : Fin k → ℝ) (r : ℝ) :
    l1ClosedBall c r =
      (fun x : Fin k → ℝ ↦ -c + x) ⁻¹' l1ClosedBall 0 r := by
  ext x
  simp only [l1ClosedBall, Set.mem_ofPred_eq, Set.mem_preimage]
  have hdist : realL1Dist x c = realL1Dist (-c + x) 0 := by
    rw [realL1Dist, realL1Dist]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
    congr 1
    ring
  rw [hdist]

/-- Translation does not change the volume of a closed `ℓ₁` ball.
@isnad1 id=eq.0h3v.s7.43dbbe320910 from=translated src=- shape=ca091053 vocab=37c048e9
-/
theorem volume_l1ClosedBall_center {k : ℕ} (c : Fin k → ℝ) (r : ℝ) :
    volume (l1ClosedBall c r) =
      volume (l1ClosedBall (0 : Fin k → ℝ) r) := by
  rw [l1ClosedBall_eq_preimage_add]
  exact measure_preimage_add volume (-c) (l1ClosedBall 0 r)

/-- The closed `ℓ₁` ball of radius `r` has volume
`r^k · 2^k / k!` in extended nonnegative reals.
@isnad1 id=eq.1h3v.s7.1f68c76cac27 from=translated src=- shape=758c8fb5 vocab=aefa9289
-/
theorem volume_l1ClosedBall {k : ℕ} (hk : 1 ≤ k) (c : Fin k → ℝ) (r : ℝ) :
    volume (l1ClosedBall c r) =
      ENNReal.ofReal r ^ k *
        ENNReal.ofReal ((2 : ℝ) ^ k / k.factorial) := by
  rw [volume_l1ClosedBall_center]
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (by omega)
  have h :=
    MeasureTheory.volume_sum_rpow_le (Fin k) (p := (1 : ℝ)) (by norm_num) r
  simp only [Fintype.card_fin] at h
  rw [show l1ClosedBall (0 : Fin k → ℝ) r =
      {x : Fin k → ℝ |
        (∑ i, |x i| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ r} by
    ext x
    simp [l1ClosedBall, realL1Dist]]
  rw [h]
  congr 2
  norm_num [Real.Gamma_nat_eq_factorial]

/-- The unit cross-polytope has volume `2^k / k!`.
@isnad1 id=eq.1h1v.s7.1ff8bffc2f24 from=translated src=- shape=41600548 vocab=32348b11
-/
theorem volume_crossPolytope {k : ℕ} (hk : 1 ≤ k) :
    volume (crossPolytope k) =
      ENNReal.ofReal ((2 : ℝ) ^ k / k.factorial) := by
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (by omega)
  have h :=
    MeasureTheory.volume_sum_rpow_le (Fin k) (p := (1 : ℝ)) (by norm_num) 1
  rw [show crossPolytope k =
      {x : Fin k → ℝ |
        (∑ i, |x i| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ 1} by
    ext x
    simp [crossPolytope, realL1Dist]]
  rw [h]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  congr 1
  norm_num [Real.Gamma_nat_eq_factorial]

/-- The cube `[0,L]^k` has volume `L^k` when `L` is nonnegative.
@isnad1 id=eq.1h2v.s6.06b56c183e16 from=translated src=- shape=245b29a8 vocab=e294019e
-/
theorem volume_realCube {k : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    volume (realCube k L) = ENNReal.ofReal (L ^ k) := by
  rw [show realCube k L = Set.Icc (0 : Fin k → ℝ) (fun _ ↦ L) by
    ext x
    simp only [realCube, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def, Pi.zero_apply]
    constructor
    · intro h
      exact ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩
    · rintro ⟨h0, h1⟩ i
      exact ⟨h0 i, h1 i⟩]
  rw [Real.volume_Icc_pi]
  simp only [Pi.zero_apply, sub_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  exact (ENNReal.ofReal_pow hL k).symm

/--
Volume subadditivity for a normalized cube cover, with the exact volume of every ranked
`ℓ₁` ball substituted.
@isnad1 id=le.4h4v.s7.95bf46c6e361 from=translated src=- shape=7b75fb5c vocab=f29eaeff
-/
theorem realCube_pow_le_rankedBallVolumeSum {k q : ℕ} {L : ℝ}
    (hk : 1 ≤ k) (hq : 1 ≤ q) (hL : 0 ≤ L)
    {centers : Fin q → (Fin k → ℝ)}
    (hcover : IsL1NormalizedRankedCover (realCube k L) centers) :
    L ^ k ≤ ((2 : ℝ) ^ k / k.factorial) *
      ∑ i : Fin q, ((i.1 : ℝ) / q) ^ k := by
  let balls : Fin q → Set (Fin k → ℝ) := fun i ↦
    l1ClosedBall (centers i) ((i.1 : ℝ) / q)
  have hsubset : realCube k L ⊆ ⋃ i, balls i := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover.2 x hx
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  have hvolume : volume (realCube k L) ≤ ∑ i, volume (balls i) :=
    (volume.mono hsubset).trans (measure_iUnion_fintype_le volume balls)
  rw [volume_realCube hL] at hvolume
  simp_rw [balls, volume_l1ClosedBall hk] at hvolume
  have hterm (i : Fin q) :
      ENNReal.ofReal ((i.1 : ℝ) / q) ^ k *
          ENNReal.ofReal ((2 : ℝ) ^ k / k.factorial) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hfinite :
      (∑ i : Fin q,
        ENNReal.ofReal ((i.1 : ℝ) / q) ^ k *
          ENNReal.ofReal ((2 : ℝ) ^ k / k.factorial)) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    exact fun i _ ↦ hterm i
  have hreal := ENNReal.toReal_mono hfinite hvolume
  rw [ENNReal.toReal_ofReal (pow_nonneg hL k)] at hreal
  rw [ENNReal.toReal_sum (fun i _ ↦ hterm i)] at hreal
  have hradius (i : Fin q) : 0 ≤ (i.1 : ℝ) / q := by positivity
  have hcoefficient : 0 ≤ (2 : ℝ) ^ k / k.factorial := by positivity
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (hradius _),
    ENNReal.toReal_ofReal hcoefficient] at hreal
  calc
    L ^ k ≤ ∑ i : Fin q, ((i.1 : ℝ) / q) ^ k *
        ((2 : ℝ) ^ k / k.factorial) := hreal
    _ = (∑ i : Fin q, ((i.1 : ℝ) / q) ^ k) *
        ((2 : ℝ) ^ k / k.factorial) :=
      (Finset.sum_mul Finset.univ
        (fun i : Fin q ↦ ((i.1 : ℝ) / q) ^ k) _).symm
    _ = ((2 : ℝ) ^ k / k.factorial) *
        ∑ i : Fin q, ((i.1 : ℝ) / q) ^ k := mul_comm _ _

/-- The normalized rank powers form a left Riemann sum for `x^k` on `[0,1]`.
@isnad1 id=le.1h2v.s6.27144c476171 from=translated src=- shape=1eb15232 vocab=6be98112
-/
theorem normalizedRankPowSum_le {k q : ℕ} (hq : 1 ≤ q) :
    ∑ i : Fin q, ((i.1 : ℝ) / q) ^ k ≤ (q : ℝ) / (k + 1) := by
  have hmono : MonotoneOn (fun x : ℝ ↦ x ^ k) (Set.Icc 0 (0 + q)) := by
    intro x hx y _ hxy
    exact pow_le_pow_left₀ hx.1 hxy k
  have hsum := hmono.sum_le_integral
  rw [integral_pow] at hsum
  norm_num at hsum
  let f : ℕ → ℝ := fun i ↦ ((i : ℝ) / q) ^ k
  change (∑ i : Fin q, f i.1) ≤ (q : ℝ) / (k + 1)
  rw [Fin.sum_univ_eq_sum_range f]
  dsimp [f]
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    (∑ i ∈ Finset.range q, (i : ℝ) ^ k) / (q : ℝ) ^ k ≤
        ((q : ℝ) ^ (k + 1) / (k + 1)) / (q : ℝ) ^ k :=
      div_le_div_of_nonneg_right hsum (pow_nonneg hqR.le k)
    _ = (q : ℝ) / (k + 1) := by
      rw [pow_succ]
      field_simp

/--
Every normalized ranked cover of `Q_L` has density at least
`k! (k+1) / 2^k`.
@isnad1 id=le.4h4v.s7.58e856ec252a from=translated src=- shape=a6cdbef9 vocab=4e83f3e6
-/
theorem cubeNormalizedRankedCover_ratio_lower {k q : ℕ} {L : ℝ}
    (hk : 2 ≤ k) (hL : 0 < L) (hq : 1 ≤ q)
    {centers : Fin q → (Fin k → ℝ)}
    (hcover : IsL1NormalizedRankedCover (realCube k L) centers) :
    ((k.factorial : ℝ) * (k + 1)) / (2 : ℝ) ^ k ≤
      (q : ℝ) / L ^ k := by
  have hk1 : 1 ≤ k := by omega
  have hvolume :=
    realCube_pow_le_rankedBallVolumeSum hk1 hq hL.le hcover
  have hsum := normalizedRankPowSum_le (k := k) hq
  have hcoefficient : 0 ≤ (2 : ℝ) ^ k / k.factorial := by positivity
  have hbound :
      L ^ k ≤ ((2 : ℝ) ^ k / k.factorial) *
        ((q : ℝ) / (k + 1)) :=
    hvolume.trans (mul_le_mul_of_nonneg_left hsum hcoefficient)
  have hfactorial : (k.factorial : ℝ) ≠ 0 := by positivity
  have hsucc : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hfactorial, hsucc] at hbound
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Existence-form wrapper for equation (46).
@isnad1 id=le.4h3v.s7.6e218db5e075 from=translated src=- shape=82a2c18e vocab=756f03db
-/
theorem cubeRankedCover_ratio_lower {k q : ℕ} {L : ℝ}
    (hk : 2 ≤ k) (hL : 0 < L) (hq : 1 ≤ q)
    (hcover : HasCubeRankedCover k L q) :
    ((k.factorial : ℝ) * (k + 1)) / (2 : ℝ) ^ k ≤
      (q : ℝ) / L ^ k := by
  obtain ⟨centers, hcenters⟩ := hcover
  exact cubeNormalizedRankedCover_ratio_lower hk hL hq hcenters

end BurningPath
