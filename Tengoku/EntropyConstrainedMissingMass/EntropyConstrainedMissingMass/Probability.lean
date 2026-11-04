import Tengoku.Seed.Analysis.SpecialFunctions.Log.NegMulLog
import Tengoku.Seed.Analysis.Normed.Lp.lpSpace
import Tengoku.Seed.Topology.Algebra.InfiniteSum.ENNReal
import Tengoku.Seed.Topology.Order.LocalExtr

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Probability vectors with their genuine ℓ¹ metric, extended entropy, and missing mass.
The index type is arbitrary: in particular finite and countably infinite types are covered.
No finite support or entropy summability is part of the probability-vector definition. -/

open scoped ENNReal

namespace EntropyConstrainedMissingMass

/-- Nonnegative unit-mass elements of ℓ¹, with the induced metric.-/
def ProbabilityVector (ι : Type*) :=
  {p : lp (fun _ : ι => ℝ) 1 // (∀ i, 0 ≤ p i) ∧ (∑' i, p i) = 1}

namespace ProbabilityVector

variable {ι : Type*}

noncomputable instance : MetricSpace (ProbabilityVector ι) := inferInstanceAs (MetricSpace (Subtype _))

noncomputable def coord (p : ProbabilityVector ι) (i : ι) : ℝ := p.val i

/--
@isnad1 id=le.0h3v.s4.752fdb58d2df from=translated src=- shape=2826fe40 vocab=3258dc68
-/
@[simp] theorem coord_nonneg (p : ProbabilityVector ι) (i : ι) : 0 ≤ p.coord i := p.property.1 i

/--
@isnad1 id=eq.0h2v.s4.5effbac3676c from=translated src=- shape=1457b230 vocab=e4046579
-/
@[simp] theorem tsum_coord (p : ProbabilityVector ι) : (∑' i, p.coord i) = 1 := p.property.2

/--
@isnad1 id=summable.0h2v.s4.9880fc13135b from=translated src=- shape=57c9f1ac vocab=d90ccdae
-/
theorem summable_coord (p : ProbabilityVector ι) : Summable p.coord :=
  p.val.property.summable_of_one

/--
@isnad1 id=le.0h3v.s4.e5159c8cdc2b from=translated src=- shape=1d15dbbb vocab=3258dc68
-/
theorem coord_le_one (p : ProbabilityVector ι) (i : ι) : p.coord i ≤ 1 := by
  rw [← p.tsum_coord]
  exact p.summable_coord.le_tsum i (fun j _ => p.coord_nonneg j)

/-- The ℓ¹ representation accepts every nonnegative real probability series.-/
noncomputable def ofHasSum (p : ι → ℝ) (hn : ∀ i, 0 ≤ p i) (hs : HasSum p 1) :
    ProbabilityVector ι :=
  ⟨⟨p, memℓp_gen (by simpa [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hs.summable)⟩,
    hn, hs.tsum_eq⟩

/--
@isnad1 id=eq.2h2v.s5.b76296d7d999 from=translated src=- shape=53e28117 vocab=d98fcf81
-/
@[simp] theorem coord_ofHasSum (p : ι → ℝ) (hn : ∀ i, 0 ≤ p i) (hs : HasSum p 1) :
    (ofHasSum p hn hs).coord = p := rfl

/--
@isnad1 id=hassum.0h2v.s4.7e8b03461403 from=translated src=- shape=31b96128 vocab=a43089d2
-/
theorem hasSum_coord (p : ProbabilityVector ι) : HasSum p.coord 1 := by
  simpa using p.summable_coord.hasSum

/-- The induced metric is exactly the manuscript's sum of absolute coordinate differences.
@isnad1 id=eq.0h3v.s5.38e8721c00b5 from=translated src=- shape=7175149b vocab=d93ef90e
-/
theorem dist_eq_tsum (p q : ProbabilityVector ι) :
    dist p q = ∑' i, |p.coord i - q.coord i| := by
  change dist p.val q.val = _
  rw [dist_eq_norm, lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal)]
  simp [coord, Real.norm_eq_abs]

/--
@isnad1 id=eq.0h2v.s5.c3ae40a78a32 from=translated src=- shape=26def084 vocab=ff590e91
-/
theorem tsum_abs_coord (p : ProbabilityVector ι) : (∑' i, |p.coord i|) = 1 := by
  simpa only [abs_of_nonneg (p.coord_nonneg _)] using p.tsum_coord

/-- Extended entropy prevents divergent real series from being assigned the value zero.-/
noncomputable def entropy (p : ProbabilityVector ι) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (Real.negMulLog (p.coord i))

/--
@isnad1 id=le.0h3v.s4.d69b846e7ff2 from=translated src=- shape=b2ad42d6 vocab=767d12c0
-/
theorem entropy_term_nonneg (p : ProbabilityVector ι) (i : ι) :
    0 ≤ Real.negMulLog (p.coord i) :=
  Real.negMulLog_nonneg (p.coord_nonneg i) (p.coord_le_one i)

/--
@isnad1 id=iff.0h2v.s5.aee0bfd8ddb5 from=translated src=- shape=3e312e94 vocab=e2821364
-/
theorem entropy_ne_top_iff (p : ProbabilityVector ι) :
    p.entropy ≠ ⊤ ↔ Summable (fun i => Real.negMulLog (p.coord i)) := by
  constructor
  · intro h
    have hs := ENNReal.summable_toReal h
    simpa [ENNReal.toReal_ofReal, p.entropy_term_nonneg] using hs
  · intro h
    rw [entropy, ← ENNReal.ofReal_tsum_of_nonneg p.entropy_term_nonneg h]
    exact ENNReal.ofReal_ne_top

/--
@isnad1 id=eq.1h2v.s5.bb9f88ad7f2d from=translated src=- shape=985d4a5b vocab=170a538f
-/
theorem entropy_eq_ofReal_tsum (p : ProbabilityVector ι)
    (h : p.entropy ≠ ⊤) :
    p.entropy = ENNReal.ofReal (∑' i, Real.negMulLog (p.coord i)) := by
  exact (ENNReal.ofReal_tsum_of_nonneg p.entropy_term_nonneg
    (p.entropy_ne_top_iff.mp h)).symm

/--
@isnad1 id=eq.1h2v.s5.3c69289721e8 from=translated src=- shape=d270777d vocab=95258e44
-/
theorem entropy_toReal (p : ProbabilityVector ι) (h : p.entropy ≠ ⊤) :
    p.entropy.toReal = ∑' i, Real.negMulLog (p.coord i) := by
  rw [p.entropy_eq_ofReal_tsum h, ENNReal.toReal_ofReal (tsum_nonneg p.entropy_term_nonneg)]

end ProbabilityVector

/-- A single atom's contribution after `t` samples; `t=0` is useful for identities.-/
def missingMassTerm (t : ℕ) (u : ℝ) : ℝ := u * (1 - u) ^ t

/--
@isnad1 id=le.2h2v.s5.c92d3987b853 from=translated src=- shape=a13d5172 vocab=6bfeaff2
-/
theorem missingMassTerm_nonneg (t : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ missingMassTerm t u :=
  mul_nonneg h0 (pow_nonneg (sub_nonneg.mpr h1) _)

/--
@isnad1 id=le.2h2v.s5.bde329b8e289 from=translated src=- shape=a27010e6 vocab=6bfeaff2
-/
theorem missingMassTerm_le (t : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    missingMassTerm t u ≤ u := by
  exact (mul_le_mul_of_nonneg_left
    (pow_le_one₀ (sub_nonneg.mpr h1) (sub_le_self _ h0)) h0).trans_eq (mul_one u)

namespace ProbabilityVector
variable {ι : Type*}

/--
@isnad1 id=summable.0h3v.s4.d4fd0baebd66 from=translated src=- shape=8f4a11f7 vocab=ef90630b
-/
theorem objective_summable (p : ProbabilityVector ι) (t : ℕ) :
    Summable (fun i => missingMassTerm t (p.coord i)) :=
  .of_nonneg_of_le
    (fun i => missingMassTerm_nonneg t (p.coord_nonneg i) (p.coord_le_one i))
    (fun i => missingMassTerm_le t (p.coord_nonneg i) (p.coord_le_one i)) p.summable_coord

noncomputable def objective (p : ProbabilityVector ι) (t : ℕ) : ℝ :=
  ∑' i, missingMassTerm t (p.coord i)

/--
@isnad1 id=le.0h3v.s4.78fd0810ff9c from=translated src=- shape=ca923f56 vocab=97e1ae3a
-/
theorem objective_nonneg (p : ProbabilityVector ι) (t : ℕ) : 0 ≤ p.objective t :=
  tsum_nonneg (fun i => missingMassTerm_nonneg t (p.coord_nonneg i) (p.coord_le_one i))

/--
@isnad1 id=le.0h3v.s4.61360752bef3 from=translated src=- shape=6b3b8763 vocab=97e1ae3a
-/
theorem objective_le_one (p : ProbabilityVector ι) (t : ℕ) : p.objective t ≤ 1 := by
  rw [← p.tsum_coord]
  exact (p.objective_summable t).tsum_le_tsum
    (fun i => missingMassTerm_le t (p.coord_nonneg i) (p.coord_le_one i)) p.summable_coord

/--
@isnad1 id=eq.0h2v.s4.1f43f585a042 from=translated src=- shape=24de7c07 vocab=5174f6ad
-/
@[simp] theorem objective_zero (p : ProbabilityVector ι) : p.objective 0 = 1 := by
  simp [objective, missingMassTerm]

/-- Feasibility uses extended entropy and a real budget, without any support restriction.-/
def Feasible (h : ℝ) : Set (ProbabilityVector ι) := {p | p.entropy ≤ ENNReal.ofReal h}

/-- This uses the ℓ¹ metric, not the pointwise product topology or stationarity.-/
def LocalMaximizer (t : ℕ) (h : ℝ) (p : ProbabilityVector ι) : Prop :=
  p ∈ Feasible h ∧ IsLocalMaxOn (fun q => q.objective t) (Feasible h) p

/--
@isnad1 id=ne.1h3v.s4.f78b20ddfe89 from=translated src=- shape=6f5c49fd vocab=023a2a00
-/
theorem finite_entropy_of_feasible {p : ProbabilityVector ι} {h : ℝ}
    (hp : p ∈ Feasible h) : p.entropy ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp

end ProbabilityVector
end EntropyConstrainedMissingMass
