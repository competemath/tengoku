import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.RepeatedSize
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.QuadraticPathCalculus
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.EmbeddedPerturbation
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.GenericFiniteLocalMax
import Tengoku.Seed.Analysis.Calculus.ContDiff.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Four-coordinate quadratic perturbations used in the repeated-size criterion. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open Set Filter
open scoped Topology

def repeatedFourBase (x y : ℝ) : Fin 4 → ℝ := ![x, x, y, y]

def repeatedFourVelocity (left : Bool) : Fin 4 → ℝ :=
  if left then ![1, -1, 0, 0] else ![0, 0, 1, -1]

def repeatedFourAcceleration (c : ℝ) : Fin 4 → ℝ := ![c, c, -c, -c]

def repeatedFourPath (x y c : ℝ) (left : Bool) (ε : ℝ) (i : Fin 4) : ℝ :=
  repeatedFourBase x y i + repeatedFourVelocity left i * ε + repeatedFourAcceleration c i * ε ^ 2

@[simp] theorem repeatedFourPath_zero (x y c : ℝ) (left : Bool) :
    repeatedFourPath x y c left 0 = repeatedFourBase x y := by
  ext i
  simp [repeatedFourPath]

theorem repeatedFourPath_sum (x y c ε : ℝ) (left : Bool) :
    ∑ i, repeatedFourPath x y c left ε i = ∑ i, repeatedFourBase x y i := by
  cases left <;> simp [Fin.sum_univ_succ, repeatedFourPath, repeatedFourBase,
    repeatedFourVelocity, repeatedFourAcceleration] <;> ring

theorem continuous_repeatedFourPath (x y c : ℝ) (left : Bool) :
    Continuous (repeatedFourPath x y c left) := by
  unfold repeatedFourPath
  fun_prop

theorem repeatedFourPath_eventually_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (c : ℝ) (left : Bool) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ i, 0 ≤ repeatedFourPath x y c left ε i := by
  apply Filter.eventually_all.mpr
  intro i
  have hi : 0 < repeatedFourBase x y i := by
    fin_cases i <;> simp [repeatedFourBase] <;> assumption
  have ht : Tendsto (fun ε => repeatedFourPath x y c left ε i) (𝓝 0)
      (𝓝 (repeatedFourBase x y i)) := by
    simpa [Function.comp_def] using
      ((continuous_apply i).comp (continuous_repeatedFourPath x y c left)).tendsto 0
  exact (ht.eventually (eventually_gt_nhds hi)).mono (fun _ h => h.le)

theorem repeatedFour_first_jet (f : ℝ → ℝ) (x y : ℝ) (left : Bool) :
    ∑ i, repeatedFourVelocity left i * deriv f (repeatedFourBase x y i) = 0 := by
  cases left <;> simp [Fin.sum_univ_succ, repeatedFourVelocity, repeatedFourBase]

theorem repeatedFour_second_jet (f : ℝ → ℝ) (x y c : ℝ) (left : Bool) :
    (∑ i, ((repeatedFourVelocity left i) ^ 2 * deriv (deriv f) (repeatedFourBase x y i) +
      2 * repeatedFourAcceleration c i * deriv f (repeatedFourBase x y i))) =
      2 * (if left then deriv (deriv f) x else deriv (deriv f) y) +
        4 * c * (deriv f x - deriv f y) := by
  cases left <;> simp [Fin.sum_univ_succ, repeatedFourVelocity, repeatedFourBase,
    repeatedFourAcceleration] <;> ring

/-- A continuous inequality holding strictly to the left also holds at the endpoint.-/
theorem nonpos_at_of_forall_lt {F : ℝ → ℝ} {a : ℝ} (hF : ContinuousAt F a)
    (h : ∀ c < a, F c ≤ 0) : F a ≤ 0 := by
  apply le_of_tendsto (hF.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto F (𝓝[<] a) (𝓝 (F a)))
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact h c hc

theorem repeatedFourBase_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (i : Fin 4) :
    0 < repeatedFourBase x y i := by
  fin_cases i <;> simp [repeatedFourBase] <;> assumption

/-- The genuine four-coordinate mass and upper-entropy constraint.-/
def repeatedFourConstraint (x y : ℝ) : Set (Fin 4 → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = ∑ i, repeatedFourBase x y i) ∧
    (∑ i, Real.negMulLog (v i)) ≤ ∑ i, Real.negMulLog (repeatedFourBase x y i)}

theorem localMax_repeatedFourPath {f : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hm : IsLocalMaxOn (fun v : Fin 4 → ℝ => ∑ i, f (v i))
      (repeatedFourConstraint x y) (repeatedFourBase x y))
    (c : ℝ) (left : Bool)
    (hent : IsLocalMax (fun ε => ∑ i, Real.negMulLog (repeatedFourPath x y c left ε i)) 0) :
    IsLocalMax (fun ε => ∑ i, f (repeatedFourPath x y c left ε i)) 0 := by
  have hlim : Tendsto (repeatedFourPath x y c left) (𝓝 0) (𝓝 (repeatedFourBase x y)) := by
    simpa using (continuous_repeatedFourPath x y c left).tendsto 0
  have hmem : ∀ᶠ ε : ℝ in 𝓝 0, repeatedFourPath x y c left ε ∈ repeatedFourConstraint x y := by
    filter_upwards [repeatedFourPath_eventually_nonneg hx hy c left, hent] with ε hn he
    exact ⟨hn, repeatedFourPath_sum x y c ε left, by simpa only [repeatedFourPath_zero] using he⟩
  have ht : Tendsto (repeatedFourPath x y c left) (𝓝 0)
      (𝓝[repeatedFourConstraint x y] (repeatedFourBase x y)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, hmem⟩
  change ∀ᶠ ε : ℝ in 𝓝 0, (∑ i, f (repeatedFourPath x y c left ε i)) ≤
    ∑ i, f (repeatedFourPath x y c left 0 i)
  simpa only [repeatedFourPath_zero] using ht.eventually hm

theorem weighted_bound_of_affine_nonpos {u L A D : ℝ} (hu : 0 < u) (hL : 0 < L)
    (h : 2 * A + 4 * (1 / (2 * u * L)) * (-D) ≤ 0) : u * A ≤ D / L := by
  have hm := mul_nonpos_of_nonpos_of_nonneg h (mul_pos hu hL).le
  have heq : (2 * A + 4 * (1 / (2 * u * L)) * (-D)) * (u * L) =
      2 * (u * A * L - D) := by field_simp; ring
  rw [heq] at hm
  apply (le_div_iff₀ hL).2
  linarith

namespace ProbabilityVector
variable {ι : Type*}

end ProbabilityVector
end
end EntropyConstrainedMissingMass
