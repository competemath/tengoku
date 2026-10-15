import Tengoku.NavierStokesEuler.Euler.StrongOperatorDerivative
import Tengoku.NavierStokesEuler.Euler.MetricHeatEnergy

/-! The genuine cylinder heat semigroup solves the Laplacian evolution equation. -/

noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerMetricHeatEnergy EulerStrongOperatorDerivative
open scoped ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The real extension of a finite commuting heat product. -/
def realHeatList (directions : List LiftTangent) (t : ℝ) (f : LiftL2 period) : LiftL2 period :=
  match directions with
  | [] => f
  | a :: tail => realLineHeat period a t (realHeatList tail t f)

/--
@isnad1 id=eq.1h4v.s11.15462f9e5e4a from=translated src=- shape=44768f56 vocab=f2ea230f
-/
theorem realHeatList_eq (directions : List LiftTangent) {t : ℝ} (ht : 0 ≤ t) (f : LiftL2 period) :
    realHeatList period directions t f = heatList period directions ⟨t, ht⟩ f := by
  induction directions with
  | nil => rfl
  | cons a tail ih =>
    change realLineHeat period a t (realHeatList period tail t f) =
      lineHeat period a ⟨t, ht⟩ (heatList period tail ⟨t, ht⟩ f)
    rw [realLineHeat_eq period a ht, ih]

/--
@isnad1 id=eq.0h5v.s14.2e843370ff36 from=translated src=- shape=b2f953df vocab=6611ea33
-/
theorem realLineHeat_add (a : LiftTangent) (t : ℝ) (f g : LiftL2 period) :
    realLineHeat period a t (f+g) = realLineHeat period a t f + realLineHeat period a t g := by
  simp only [realLineHeat_eq_toNNReal, lineHeat_add]

/--
@isnad1 id=eq.0h5v.s15.484bb480c930 from=translated src=- shape=cafabc1c vocab=6a7be7b7
-/
theorem realLineHeat_smul (a : LiftTangent) (t c : ℝ) (f : LiftL2 period) :
    realLineHeat period a t (c • f) = c • realLineHeat period a t f := by
  simp only [realLineHeat_eq_toNNReal, lineHeat_smul]

/--
@isnad1 id=eq.0h5v.s14.d7f7d0ab77a6 from=translated src=- shape=193c975b vocab=46a8c84b
-/
theorem realHeatList_add (directions : List LiftTangent) (t : ℝ) (f g : LiftL2 period) :
    realHeatList period directions t (f+g) = realHeatList period directions t f + realHeatList period directions t g := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [realHeatList, ih, realLineHeat_add]

/--
@isnad1 id=eq.0h5v.s15.834ff80e0084 from=translated src=- shape=13a5533d vocab=8a47243b
-/
theorem realHeatList_smul (directions : List LiftTangent) (t c : ℝ) (f : LiftL2 period) :
    realHeatList period directions t (c • f) = c • realHeatList period directions t f := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [realHeatList, ih, realLineHeat_smul]

/--
@isnad1 id=eq.0h3v.s12.cb0d5e5c6a50 from=translated src=- shape=0af240dd vocab=f4703a7b
-/
@[simp] theorem realHeatList_zero_field (directions : List LiftTangent) (t : ℝ) :
    realHeatList period directions t 0 = 0 := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [realHeatList, ih, realLineHeat_eq_toNNReal, ← lineHeatOperator_apply, map_zero]

/--
@isnad1 id=eq.0h3v.s11.1496e494fe1f from=translated src=- shape=8ab5795c vocab=f4703a7b
-/
@[simp] theorem realHeatList_zero_time (directions : List LiftTangent) (f : LiftL2 period) :
    realHeatList period directions 0 f = f := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [realHeatList, realLineHeat_zero, ih]

/--
@isnad1 id=eq.0h4v.s11.516f5f9004af from=translated src=- shape=45ad812b vocab=4b9f3863
-/
theorem realHeatList_eq_toNNReal (directions : List LiftTangent) (t : ℝ) (f : LiftL2 period) :
    realHeatList period directions t f = heatList period directions t.toNNReal f := by
  induction directions with
  | nil => rfl
  | cons a tail ih =>
    change realLineHeat period a t (realHeatList period tail t f) =
      lineHeat period a t.toNNReal (heatList period tail t.toNNReal f)
    rw [realLineHeat_eq_toNNReal, ih]

/--
@isnad1 id=continuo.0h3v.s13.53b750c98e72 from=translated src=- shape=adaa6f8e vocab=cb2c2853
-/
theorem realHeatList_continuous (directions : List LiftTangent) (f : LiftL2 period) :
    Continuous (fun t : ℝ => realHeatList period directions t f) := by
  simp_rw [realHeatList_eq_toNNReal]
  exact (heatList_continuous period directions f).comp continuous_real_toNNReal

/-- Every strong coordinate derivative commutes with every finite heat product.
@isnad1 id=hasderiv.1h6v.s14.afc036a8724d from=translated src=- shape=595293e7 vocab=9690a16e
-/
theorem realHeatList_strongDerivative (directions : List LiftTangent) (a : LiftTangent) (t : ℝ)
    (f g : LiftL2 period) (hD : HasDerivAt (lineOrbit period a f) g 0) :
    HasDerivAt (lineOrbit period a (realHeatList period directions t f))
      (realHeatList period directions t g) 0 := by
  induction directions with
  | nil => exact hD
  | cons b tail ih =>
    simp only [realHeatList, realLineHeat_eq_toNNReal]
    exact lineHeat_strongDerivative period b a t.toNNReal _ _ ih

/-- The finite directional heat product has the sum of its actual second derivatives as generator.
@isnad1 id=hasderiv.3h8v.s15.69c13d992bac from=translated src=- shape=c7baecf4 vocab=ce4b2340
-/
theorem realHeatList_generator_pos {ι : Type*} (indices : List ι) (direction : ι → LiftTangent)
    (f : LiftL2 period) (df ddf : ι → LiftL2 period)
    (hD : ∀ i ∈ indices, HasDerivAt (lineOrbit period (direction i) f) (df i) 0)
    (hDD : ∀ i ∈ indices, HasDerivAt (lineOrbit period (direction i) (df i)) (ddf i) 0)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => realHeatList period (indices.map direction) s f)
      ((1/2 : ℝ) • realHeatList period (indices.map direction) t ((indices.map ddf).sum)) t := by
  induction indices with
  | nil => simpa only [List.map_nil, List.sum_nil, realHeatList, smul_zero] using hasDerivAt_const t f
  | cons i tail ih =>
    have htailD := fun j hj => hD j (List.mem_cons_of_mem i hj)
    have htailDD := fun j hj => hDD j (List.mem_cons_of_mem i hj)
    have hinput := ih htailD htailDD
    have hfirst := realHeatList_strongDerivative period (tail.map direction) (direction i) t f (df i)
      (hD i (List.mem_cons_self ..))
    have hsecond := realHeatList_strongDerivative period (tail.map direction) (direction i) t (df i) (ddf i)
      (hDD i (List.mem_cons_self ..))
    have h := realLineHeat_varying_input period (direction i)
      (fun s => realHeatList period (tail.map direction) s f) t _ _ _ ht hinput hfirst hsecond
    have halg : realLineHeat period (direction i) t
          ((1/2 : ℝ) • realHeatList period (tail.map direction) t ((tail.map ddf).sum)) +
        (1/2 : ℝ) • realLineHeat period (direction i) t (realHeatList period (tail.map direction) t (ddf i)) =
        (1/2 : ℝ) • realHeatList period ((i::tail).map direction) t (((i::tail).map ddf).sum) := by
      rw [realLineHeat_smul, ← smul_add, ← realLineHeat_add, ← realHeatList_add]
      simp only [List.map_cons, List.sum_cons, realHeatList]
      rw [add_comm ((tail.map ddf).sum)]
    rw [halg] at h
    exact h

/-- The full directional generator identity holds as a right derivative at zero as well.
@isnad1 id=hasderiv.2h7v.s15.02996d30f1b4 from=translated src=- shape=c141005c vocab=00d7cf1d
-/
theorem realHeatList_generator_zero {ι : Type*} (indices : List ι) (direction : ι → LiftTangent)
    (f : LiftL2 period) (df ddf : ι → LiftL2 period)
    (hD : ∀ i ∈ indices, HasDerivAt (lineOrbit period (direction i) f) (df i) 0)
    (hDD : ∀ i ∈ indices, HasDerivAt (lineOrbit period (direction i) (df i)) (ddf i) 0) :
    HasDerivWithinAt (fun s => realHeatList period (indices.map direction) s f)
      ((1/2 : ℝ) • (indices.map ddf).sum) (Set.Ici 0) 0 := by
  have hlim : Filter.Tendsto (fun s => (1/2 : ℝ) • realHeatList period (indices.map direction) s ((indices.map ddf).sum))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1/2 : ℝ) • (indices.map ddf).sum)) := by
    have hc : ContinuousAt (fun s => (1/2 : ℝ) • realHeatList period (indices.map direction) s ((indices.map ddf).sum)) 0 :=
      ((realHeatList_continuous period _ _).const_smul (1/2 : ℝ)).continuousAt
    simpa only [realHeatList_zero_time] using (hc.continuousWithinAt (s := Set.Ioi 0)).tendsto
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    (fun t ht => (realHeatList_generator_pos period indices direction f df ddf hD hDD ht).differentiableAt.differentiableWithinAt)
    (realHeatList_continuous period _ _).continuousAt.continuousWithinAt self_mem_nhdsWithin
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (realHeatList_generator_pos period indices direction f df ddf hD hDD ht).deriv.symm

end EulerGaussianCylinderHeat
