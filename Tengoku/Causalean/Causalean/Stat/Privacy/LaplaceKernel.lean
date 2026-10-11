module
public import Tengoku.Causalean.Causalean.Stat.Privacy.LaplaceMechanism
public import Tengoku

/-!
# Measurable finite-product Laplace mechanism

The existing finite-coordinate mechanism is packaged as a Markov kernel for
any measurable query and positive scale. Its value at each input is exactly
the primary library's mechanism, so measure-kernel composition applies directly.
-/

@[expose] public section

namespace Causalean.Stat.Privacy

open MeasureTheory ProbabilityTheory Causalean.Stat.Privacy

variable {D ι : Type*} [MeasurableSpace D] [Fintype ι]

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q) and [its measurability certificate](hyp:hq), [the finite-product Laplace
release depends measurably on its input](goal).

Build a constant product-noise kernel, pair it with the deterministic query
kernel, and map by addition; prove its value is `laplaceMechPi b q d`.
This obligation is independent of all moment calculations.
@isnad1 id=measurab.2h4v.s6.eae7ab715f5a from=translated src=- shape=3ccd6ec6 vocab=9aca0de0
-/
@[fun_prop]
theorem measurable_laplaceMechPi (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (hq : Measurable q) : Measurable (laplaceMechPi b q) := by
  let : IsProbabilityMeasure (laplaceMeasure b) :=
    laplaceMeasure_isProbabilityMeasure b hb
  let noise : Kernel D (ι → ℝ) :=
    Kernel.const D (Measure.pi fun _ : ι => laplaceMeasure b)
  let add : (ι → ℝ) × (ι → ℝ) → (ι → ℝ) := fun p => p.2 + p.1
  have hadd : Measurable add := measurable_snd.add measurable_fst
  let release := ((Kernel.deterministic q hq).prod noise).map add
  have hrelease (d : D) : release d = laplaceMechPi b q d := by
    rw [Kernel.map_apply _ hadd, Kernel.prod_apply,
      Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
      Measure.map_map hadd measurable_prodMk_left]
    rfl
  have heq : (fun d => release d) = laplaceMechPi b q := funext hrelease
  rw [← heq]
  exact release.measurable

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q) and [its measurability certificate](hyp:hq), [the finite-coordinate release
defines a kernel with the existing mechanism's inputwise measures](goal). -/
noncomputable def laplaceMechPiKernel (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (hq : Measurable q) : Kernel D (ι → ℝ) where
  toFun := laplaceMechPi b q
  measurable' := measurable_laplaceMechPi b hb q hq

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [its measurability certificate](hyp:hq), and [an input](hyp:d), [the
kernel equals the existing Laplace mechanism at that input](goal).
@isnad1 id=eq.2h5v.s6.1f824263251f from=translated src=- shape=1ce21777 vocab=54553e7e
-/
@[simp]
theorem laplaceMechPiKernel_apply (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (hq : Measurable q) (d : D) :
    laplaceMechPiKernel b hb q hq d = laplaceMechPi b q d := rfl

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q) and [its measurability certificate](hyp:hq), [the resulting kernel is a
Markov kernel](goal).
@isnad1 id=ismarkov.2h4v.s6.8c42563a1835 from=translated src=- shape=b776490e vocab=52becc9f
-/
instance laplaceMechPiKernel_isMarkovKernel (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (hq : Measurable q) :
    IsMarkovKernel (laplaceMechPiKernel b hb q hq) :=
  ⟨fun d => laplaceMechPi_isProbabilityMeasure b hb q d⟩

end Causalean.Stat.Privacy
