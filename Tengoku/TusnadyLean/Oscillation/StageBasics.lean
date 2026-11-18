import Tengoku.TusnadyLean.Oscillation.RealGrid
import Tengoku.TusnadyLean.Oscillation.GeometryBounds
import Tengoku.Seed.Probability.Process.Adapted

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual truncated base-b stages on iid horizontal real coordinates. -/
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Riesz Riesz.PointSets

def stagePotential {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (Y : Fin n → ℕ) (j : ℕ) (U : Fin n → ℝ) : ℝ :=
  actualPotential (b ^ min j h) (b ^ (h - min j h)) (b ^ min j h)
    (pow_pos hb _) (pow_pos hb _) χ Y U

def stageMass {n : ℕ} (b h : ℕ) (hb : 0 < b) (Y : Fin n → ℕ)
    (j : ℕ) (U : Fin n → ℝ) : ℝ :=
  if j < h then interiorMass (b ^ j) (b ^ (h-j-1)) b (b ^ j)
    (sampleCells n (b ^ j) (pow_pos hb _) U) Y else 0

/--
@isnad1 id=monotone.1h2v.s5.9d9c77db26ee from=translated src=- shape=b15af5a0 vocab=09ad6d74
-/
lemma sampleGridSigma_mono_pow (n b : ℕ) (hb : 0 < b) :
    Monotone (fun j ↦ sampleGridSigma n (b ^ j)) := by
  intro i j hij
  change sampleGridSigma n (b^i) ≤ sampleGridSigma n (b^j)
  have he : b ^ j = b ^ i * b ^ (j-i) := by rw [← pow_add, Nat.add_sub_of_le hij]
  rw [he]
  exact sampleGridSigma_le_mul n (b^i) (b^(j-i)) (pow_pos hb _)

def stageFiltration (n b h : ℕ) (hb : 0 < b) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → ℝ)) where
  seq j := sampleGridSigma n (b ^ min j h)
  mono' := fun _i _j hij ↦ sampleGridSigma_mono_pow n b hb (min_le_min_right h hij)
  le' j := (measurable_sampleGridIndex n (b ^ min j h)).comap_le

/--
@isnad1 id=eq.1h4v.s6.2304016cc9ae from=translated src=- shape=9bf67b62 vocab=54cd6966
-/
@[simp] lemma stageFiltration_apply (n b h : ℕ) (hb : 0 < b) (j : ℕ) :
    stageFiltration n b h hb j = sampleGridSigma n (b ^ min j h) := rfl

/--
@isnad1 id=strongly.1h5v.s6.565ecc8ddeac from=translated src=- shape=2777de30 vocab=0ab4d686
-/
lemma stagePotential_adapted {n : ℕ} (b h : ℕ) (hb : 0 < b)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) :
    StronglyAdapted (stageFiltration n b h hb) (stagePotential b h hb χ Y) := by
  intro j
  apply Measurable.stronglyMeasurable
  exact (measurable_of_countable (fun p : Fin n → ℕ ↦
    gridPotential (b ^ min j h) (b ^ (h-min j h)) (b ^ min j h)
      (pow_pos hb _) χ p Y)).comp
    (measurable_sampleCells_grid n (b ^ min j h) (pow_pos hb _))

/--
@isnad1 id=strongly.1h4v.s6.1c7b7bdf803a from=translated src=- shape=91847a56 vocab=94aec466
-/
lemma stageMass_adapted {n : ℕ} (b h : ℕ) (hb : 0 < b) (Y : Fin n → ℕ) :
    StronglyAdapted (stageFiltration n b h hb) (stageMass b h hb Y) := by
  intro j
  by_cases hj : j < h
  · have he : min j h = j := Nat.min_eq_left hj.le
    have hf : stageMass b h hb Y j = fun U ↦ interiorMass (b^j) (b^(h-j-1)) b (b^j)
        (sampleCells n (b^j) (pow_pos hb _) U) Y := by funext U; simp [stageMass, hj]
    rw [hf]
    have hmeas := (measurable_of_countable (fun p : Fin n → ℕ ↦
      interiorMass (b^j) (b^(h-j-1)) b (b^j) p Y)).comp
        (measurable_sampleCells_grid n (b^j) (pow_pos hb _))
    change StronglyMeasurable[sampleGridSigma n (b ^ min j h)]
      (fun U ↦ interiorMass (b^j) (b^(h-j-1)) b (b^j) (sampleCells n (b^j) (pow_pos hb _) U) Y)
    exact hmeas.stronglyMeasurable.mono (by rw [he])
  · have hf : stageMass b h hb Y j = fun _ ↦ (0 : ℝ) := by funext U; simp [stageMass, hj]
    rw [hf]
    exact stronglyMeasurable_const

/--
@isnad1 id=measurab.1h6v.s5.63cc5df345e2 from=translated src=- shape=b4f2282b vocab=0d57bc08
-/
lemma stagePotential_measurable {n : ℕ} (b h : ℕ) (hb : 0 < b)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) (j : ℕ) :
    Measurable (stagePotential b h hb χ Y j) :=
  ((stagePotential_adapted b h hb χ Y j).mono ((stageFiltration n b h hb).le j)).measurable

/--
@isnad1 id=measurab.1h5v.s5.baf22110e857 from=translated src=- shape=c1973687 vocab=be32eace
-/
lemma stageMass_measurable {n : ℕ} (b h : ℕ) (hb : 0 < b)
    (Y : Fin n → ℕ) (j : ℕ) : Measurable (stageMass b h hb Y j) :=
  ((stageMass_adapted b h hb Y j).mono ((stageFiltration n b h hb).le j)).measurable

/--
@isnad1 id=le.1h7v.s5.c3c737d98498 from=translated src=- shape=27f4662e vocab=4ed1b744
-/
lemma stagePotential_nonneg {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (Y : Fin n → ℕ) (j : ℕ) (U : Fin n → ℝ) : 0 ≤ stagePotential b h hb χ Y j U :=
  gridPotential_nonneg _ _ _ _ _ _ _

/--
@isnad1 id=le.2h7v.s6.c706b0765f92 from=translated src=- shape=978c8987 vocab=1e71ad7d
-/
lemma stagePotential_abs_le {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (hχ : ∀ i, |χ i| ≤ 1) (Y : Fin n → ℕ) (j : ℕ) (U : Fin n → ℝ) :
    |stagePotential b h hb χ Y j U| ≤ 2 * n := by
  rw [abs_of_nonneg (stagePotential_nonneg b h hb χ Y j U)]
  exact gridPotential_le_two_n _ _ _ _ χ hχ _ _

/--
@isnad1 id=le.1h6v.s5.59e833bfc21c from=translated src=- shape=368740fe vocab=ab872f94
-/
lemma stageMass_nonneg {n : ℕ} (b h : ℕ) (hb : 0 < b) (Y : Fin n → ℕ)
    (j : ℕ) (U : Fin n → ℝ) : 0 ≤ stageMass b h hb Y j U := by
  unfold stageMass
  split_ifs
  · exact interiorMass_nonneg _ _ _ _ _ _
  · rfl

/--
@isnad1 id=eq.1h3v.s6.dd611bd04210 from=translated src=- shape=e1271635 vocab=0e093988
-/
lemma stage_rectangles (b h j : ℕ) (hj : j < h) : b ^ j * b ^ (h-j-1) = b ^ (h-1) := by
  rw [← pow_add]
  congr 1
  omega

/--
@isnad1 id=eq.1h3v.s6.bbc3316518c3 from=translated src=- shape=fbaec9ac vocab=0e093988
-/
lemma stage_fine_vertical (b h j : ℕ) (hj : j < h) : b ^ (h-j-1) * (b * b ^ j) = b ^ h := by
  rw [← pow_succ', ← pow_add]
  congr 1
  omega

/--
@isnad1 id=le.1h6v.s6.9d532e6d9c81 from=translated src=- shape=9955dd6e vocab=62e085d0
-/
lemma stageMass_abs_le {n : ℕ} (b h : ℕ) (hb : 0 < b) (Y : Fin n → ℕ)
    (j : ℕ) (U : Fin n → ℝ) : |stageMass b h hb Y j U| ≤ (b ^ (h-1) : ℕ) * Real.sqrt n := by
  rw [abs_of_nonneg (stageMass_nonneg b h hb Y j U)]
  unfold stageMass
  split_ifs with hj
  · exact (interiorMass_le_sqrt _ _ _ _ _ _).trans_eq (by rw [stage_rectangles b h j hj])
  · positivity

/--
@isnad1 id=eq.1h6v.s5.c9918c1a0caa from=translated src=- shape=09e76a79 vocab=158dd326
-/
lemma stagePotential_zero {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (Y : Fin n → ℕ) (U : Fin n → ℝ) : stagePotential b h hb χ Y 0 U = 0 := by
  simp only [stagePotential, Nat.zero_min, pow_zero, actualPotential]
  exact gridPotential_one _ _ _ _ _

/--
@isnad1 id=eq.1h6v.s6.21170103f53e from=translated src=- shape=e8fc5a03 vocab=0b125480
-/
lemma stagePotential_terminal {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (Y : Fin n → ℕ) (U : Fin n → ℝ) : stagePotential b h hb χ Y h U =
      actualPotential (b^h) 1 (b^h) (pow_pos hb _) (pow_pos hb _) χ Y U := by
  simp [stagePotential]

end
end Oscillation
