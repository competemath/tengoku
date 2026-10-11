module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Certified.NormalCDF.Central
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Certified.NormalCDF.Tail

/-!
# Top-level certified standard-normal CDF checker

The public checker consumes a caller-supplied rational interval and finite
certificate data.  It dispatches the caller-selected central power-series or
Mills-tail check, validates every rational side condition, and proves that the
reported interval contains the exact standard-normal CDF.  It also exposes
the subtraction rule needed for transition probabilities formed from CDF
differences.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Analysis.IntervalArithmetic.Contour
/-- The top-level certificate method is either a central-series certificate or
a tail certificate tied to the endpoint whose exponential it encloses. -/
inductive MethodCertificate (q : ℚ) where
  /-- Use the central alternating Gaussian-integral series. -/
  | central (certificate : CentralCertificate)
  /-- Use the Mills-ratio tail evaluator. -/
  | tail (certificate : TailCertificate q)

/-- The top-level executable checker dispatches to the selected method and
validates the caller-supplied rational enclosure. -/
def normalCDFCheck (q : ℚ) (method : MethodCertificate q)
    (reported : RatInterval) : Bool :=
  match method with
  | .central certificate => centralCheck q certificate reported
  | .tail certificate => tailCheck q certificate reported

/-- When [the selected top-level certificate check succeeds](hyp:hcheck),
[the reported interval contains the exact standard-normal CDF value](goal).
@isnad1 id=contains.1h3v.s4.28929931c41f from=translated src=- shape=d08aac5b vocab=6b0d9d7c
-/
theorem normalCDFCheck_sound {q : ℚ} {method : MethodCertificate q}
    {reported : RatInterval} (hcheck : normalCDFCheck q method reported = true) :
    reported.Contains (Causalean.Mathlib.stdNormalCDF (q : ℝ)) := by
  cases method with
  | central c => exact centralCheck_sound hcheck
  | tail c => exact tailCheck_sound hcheck

/-- At [an endpoint](hyp:q), with [a caller-selected method](hyp:method) and
[a reported interval](hyp:reported), [the fine checker](goal) accepts exactly
when the soundness checker accepts and the data satisfy the endpoint and width
acceptance limits `|q| ≤ 193/5` and `width ≤ 10⁻¹²`. -/
def fineNormalCDFCheck (q : ℚ) (method : MethodCertificate q)
    (reported : RatInterval) : Bool :=
  normalCDFCheck q method reported &&
    decide (|q| ≤ acceptedEndpointBound ∧ reported.width ≤ targetWidth)

/-- When [the fine checker accepts](hyp:hcheck),
[CDF containment and both rational acceptance limits follow](goal).
@isnad1 id=and.1h3v.s5.541069150db9 from=translated src=- shape=e1f18d79 vocab=19963798
-/
theorem fineNormalCDFCheck_sound {q : ℚ} {method : MethodCertificate q}
    {reported : RatInterval} (hcheck : fineNormalCDFCheck q method reported = true) :
    reported.Contains (Causalean.Mathlib.stdNormalCDF (q : ℝ)) ∧
      |q| ≤ acceptedEndpointBound ∧ reported.width ≤ targetWidth := by
  simp only [fineNormalCDFCheck, Bool.and_eq_true] at hcheck
  have hc := hcheck
  have hlimits := of_decide_eq_true hc.2
  exact ⟨normalCDFCheck_sound hc.1, hlimits⟩

/-- At [a rational endpoint](hyp:q), a central-or-tail endpoint certificate packages
[finite method data](hyp:method) and [a rational enclosure](hyp:enclosure) with
[successful evaluation of the exact checker](hyp:checked). -/
structure NormalCDFCertificate (q : ℚ) where
  /-- Central or tail finite certificate data. -/
  method : MethodCertificate q
  /-- Rational interval supplied by the caller. -/
  enclosure : RatInterval
  /-- The exact checker accepts the supplied interval. -/
  checked : normalCDFCheck q method enclosure = true

/-- Every proof-producing endpoint certificate soundly encloses the exact CDF.
@isnad1 id=contains.0h2v.s3.ef1cd10d0bc2 from=translated src=- shape=628cf842 vocab=90f068d1
-/
theorem NormalCDFCertificate.sound {q : ℚ} (c : NormalCDFCertificate q) :
    c.enclosure.Contains (Causalean.Mathlib.stdNormalCDF (q : ℝ)) :=
  normalCDFCheck_sound c.checked

/-- At [a rational endpoint](hyp:q), a fine endpoint certificate packages [finite method
data](hyp:method) and [a rational enclosure](hyp:enclosure) with [successful evaluation of the
fine checker](hyp:checked); range and width are acceptance conditions, not a guarantee that such
certificates can be generated. -/
structure FineNormalCDFCertificate (q : ℚ) where
  /-- Central or tail finite certificate data. -/
  method : MethodCertificate q
  /-- Rational interval supplied by the caller. -/
  enclosure : RatInterval
  /-- The exact checker accepts containment, range, and width simultaneously. -/
  checked : fineNormalCDFCheck q method enclosure = true

/-- From [a fine endpoint certificate](hyp:c), [forgetting the acceptance limits yields the
corresponding central-or-tail certificate](goal). -/
def FineNormalCDFCertificate.toNormalCDFCertificate {q : ℚ}
    (c : FineNormalCDFCertificate q) : NormalCDFCertificate q where
  method := c.method
  enclosure := c.enclosure
  checked := by
    have h := c.checked
    simp only [fineNormalCDFCheck, Bool.and_eq_true] at h
    exact h.1

/-- [A fine certificate](hyp:c)
[gives containment together with checked endpoint and width bounds](goal).
@isnad1 id=and.0h2v.s5.3f24de37e024 from=translated src=- shape=0b701d5b vocab=64205bb4
-/
theorem FineNormalCDFCertificate.sound_range_and_width {q : ℚ}
    (c : FineNormalCDFCertificate q) :
    c.enclosure.Contains (Causalean.Mathlib.stdNormalCDF (q : ℝ)) ∧
      |q| ≤ acceptedEndpointBound ∧ c.enclosure.width ≤ targetWidth :=
  fineNormalCDFCheck_sound c.checked

/-- Subtracting two checked endpoint enclosures contains the corresponding CDF
difference, the form used by Gaussian threshold-cell transition probabilities.
@isnad1 id=contains.0h4v.s5.7ccea0f25a7f from=translated src=- shape=187748d3 vocab=4dbded35
-/
theorem normalCDFDifference_sound {a b : ℚ}
    (ca : NormalCDFCertificate a) (cb : NormalCDFCertificate b) :
    (cb.enclosure.sub ca.enclosure).Contains
      (Causalean.Mathlib.stdNormalCDF (b : ℝ) -
        Causalean.Mathlib.stdNormalCDF (a : ℝ)) := by
  exact RatInterval.sub_sound cb.sound ca.sound

/-- Subtracting two fine checked endpoint cells contains their exact CDF
difference while retaining executable validation of each endpoint's range and
`10⁻¹²` width bound.
@isnad1 id=contains.0h4v.s5.28e8646f655b from=translated src=- shape=187748d3 vocab=55da37fc
-/
theorem fineNormalCDFDifference_sound {a b : ℚ}
    (ca : FineNormalCDFCertificate a) (cb : FineNormalCDFCertificate b) :
    (cb.enclosure.sub ca.enclosure).Contains
      (Causalean.Mathlib.stdNormalCDF (b : ℝ) -
        Causalean.Mathlib.stdNormalCDF (a : ℝ)) := by
  exact normalCDFDifference_sound ca.toNormalCDFCertificate cb.toNormalCDFCertificate

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure
