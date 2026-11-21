import Tengoku.RainichKaluzaReconstruction.RainichKaluza.MaxwellDualityOrbit
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differential complexion rate

A smooth duality parameter `(c,s)` obeys `c²+s²=1`.  Evaluating a derivative
gives the tangency equation `c dc+s ds=0`.  This file proves constructively
that there is then a unique scalar rate `omega` with

`dc=-omega s`, `ds=omega c`.

Thus the pointwise duality circle contributes exactly one differential
complexion degree of freedom.  The EMD Bianchi/Maxwell equations must determine
this rate (and the coupling), rather than an arbitrary pair `(dc,ds)`.
-/

namespace RainichKaluza

/-- Algebraically reconstructed infinitesimal complexion rate.-/
def complexionRate (c s dc ds : ℝ) : ℝ :=
  c * ds - s * dc

/-- The unit-circle tangency equation reconstructs both parameter derivatives
from the complexion rate.-/
theorem dualityParameter_derivative_eq_complexionRate
    (c s dc ds : ℝ)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (htangent : c * dc + s * ds = 0) :
    dc = -complexionRate c s dc ds * s ∧
      ds = complexionRate c s dc ds * c := by
  constructor
  · have hzero : dc + complexionRate c s dc ds * s = 0 := by
      calc
        dc + complexionRate c s dc ds * s =
            (c ^ 2 + s ^ 2) * dc + (c * ds - s * dc) * s := by
          simp only [complexionRate, hunit, one_mul]
        _ = c * (c * dc + s * ds) := by ring
        _ = 0 := by rw [htangent]; ring
    linarith
  · have hzero : ds - complexionRate c s dc ds * c = 0 := by
      calc
        ds - complexionRate c s dc ds * c =
            (c ^ 2 + s ^ 2) * ds - (c * ds - s * dc) * c := by
          simp only [complexionRate, hunit, one_mul]
        _ = s * (c * dc + s * ds) := by ring
        _ = 0 := by rw [htangent]; ring
    linarith

/-- Any rate producing the two unit-circle derivatives equals the constructive
complexion rate.-/
theorem complexionRate_unique
    (c s dc ds omega : ℝ)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hdc : dc = -omega * s) (hds : ds = omega * c) :
    omega = complexionRate c s dc ds := by
  unfold complexionRate
  rw [hdc, hds]
  calc
    omega = omega * (c ^ 2 + s ^ 2) := by rw [hunit]; ring
    _ = c * (omega * c) - s * (-omega * s) := by ring

/-- **Infinitesimal duality-orbit theorem.** Tangency to the unit circle is
equivalent to existence of a unique complexion rate.-/
theorem duality_tangent_iff_existsUnique_complexionRate
    (c s dc ds : ℝ) (hunit : c ^ 2 + s ^ 2 = 1) :
    c * dc + s * ds = 0 ↔
      ∃! omega : ℝ, dc = -omega * s ∧ ds = omega * c := by
  constructor
  · intro htangent
    refine ⟨complexionRate c s dc ds,
      dualityParameter_derivative_eq_complexionRate c s dc ds hunit htangent,
      ?_⟩
    intro omega homega
    exact complexionRate_unique c s dc ds omega hunit
      homega.1 homega.2
  · rintro ⟨omega, ⟨hdc, hds⟩, _⟩
    rw [hdc, hds]
    ring

/-- A constant change of duality seed preserves the infinitesimal complexion
rate. This is the overlap invariance needed for local patching.-/
theorem complexionRate_constant_duality_invariant
    (p : DualityParameter) (c s dc ds : ℝ) :
    complexionRate (dualityElectric p c s) (dualityMagnetic p c s)
        (dualityElectric p dc ds) (dualityMagnetic p dc ds) =
      complexionRate c s dc ds := by
  unfold complexionRate dualityElectric dualityMagnetic
  calc
    (p.c * c - p.s * s) * (p.s * dc + p.c * ds) -
        (p.s * c + p.c * s) * (p.c * dc - p.s * ds) =
      (p.c ^ 2 + p.s ^ 2) * (c * ds - s * dc) := by ring
    _ = c * ds - s * dc := by rw [p.unit]; ring

/-- Product-rule derivative of the electric component after a variable
duality transition. The transition parameter has value `(u,v)` and derivative
`(du,dv)`, while the original local parameter has value `(c,s)` and derivative
`(dc,ds)`.-/
def variableDualityElectricDerivative
    (u v du dv c s dc ds : ℝ) : ℝ :=
  du * c + u * dc - dv * s - v * ds

/-- Product-rule derivative of the magnetic component after a variable
duality transition.-/
def variableDualityMagneticDerivative
    (u v du dv c s dc ds : ℝ) : ℝ :=
  dv * c + v * dc + du * s + u * ds

/-- Before imposing the two unit-circle equations, the rate of a product of
duality parameters splits into the two rates weighted by the opposite squared
magnitudes.-/
theorem complexionRate_variable_duality_weighted
    (u v du dv c s dc ds : ℝ) :
    complexionRate (u * c - v * s) (v * c + u * s)
        (variableDualityElectricDerivative u v du dv c s dc ds)
        (variableDualityMagneticDerivative u v du dv c s dc ds) =
      (u ^ 2 + v ^ 2) * complexionRate c s dc ds +
        (c ^ 2 + s ^ 2) * complexionRate u v du dv := by
  unfold complexionRate variableDualityElectricDerivative
    variableDualityMagneticDerivative
  ring

/-- **Variable duality gauge law.** On an overlap, a unit transition with
infinitesimal rate `tau` adds that rate to the original local complexion rate.
This is the exact connection term absent for constant seed changes.-/
theorem complexionRate_variable_duality_add
    (p r : DualityParameter) (du dv dc ds : ℝ) :
    complexionRate (dualityElectric p r.c r.s)
        (dualityMagnetic p r.c r.s)
        (variableDualityElectricDerivative p.c p.s du dv r.c r.s dc ds)
        (variableDualityMagneticDerivative p.c p.s du dv r.c r.s dc ds) =
      complexionRate r.c r.s dc ds + complexionRate p.c p.s du dv := by
  unfold dualityElectric dualityMagnetic
  rw [complexionRate_variable_duality_weighted]
  rw [p.unit, r.unit]
  ring

/-- Product-rule derivative of the cosine coordinate of a composed transition.-/
def dualityComposeCDerivative
    (p r : DualityParameter) (dpc dps drc drs : ℝ) : ℝ :=
  variableDualityElectricDerivative p.c p.s dpc dps r.c r.s drc drs

/-- Product-rule derivative of the sine coordinate of a composed transition.-/
def dualityComposeSDerivative
    (p r : DualityParameter) (dpc dps drc drs : ℝ) : ℝ :=
  variableDualityMagneticDerivative p.c p.s dpc dps r.c r.s drc drs

/-- The infinitesimal transition rate is additive under the overlap group law.
This is the differentiated cocycle identity on triple overlaps.-/
theorem complexionRate_dualityComposeDerivative
    (p r : DualityParameter) (dpc dps drc drs : ℝ) :
    complexionRate (dualityCompose p r).c (dualityCompose p r).s
        (dualityComposeCDerivative p r dpc dps drc drs)
        (dualityComposeSDerivative p r dpc dps drc drs) =
      complexionRate p.c p.s dpc dps +
        complexionRate r.c r.s drc drs := by
  change complexionRate (dualityElectric p r.c r.s)
      (dualityMagnetic p r.c r.s)
      (variableDualityElectricDerivative p.c p.s dpc dps r.c r.s drc drs)
      (variableDualityMagneticDerivative p.c p.s dpc dps r.c r.s drc drs) = _
  rw [complexionRate_variable_duality_add]
  ring

/-- The infinitesimal rate of the inverse transition is the negative of the
original transition rate.-/
theorem complexionRate_dualityInverseDerivative
    (p : DualityParameter) (dc ds : ℝ) :
    complexionRate (dualityInverse p).c (dualityInverse p).s dc (-ds) =
      -complexionRate p.c p.s dc ds := by
  unfold complexionRate dualityInverse
  ring

/-- Subtracting a local connection coefficient removes the inhomogeneous
transition-rate term.-/
def gaugeCorrectedComplexionRate (omega connection : ℝ) : ℝ :=
  omega - connection

/-- The connection-corrected complexion rate is overlap invariant when both
the raw rate and the local connection coefficient acquire the same transition
rate.-/
theorem gaugeCorrectedComplexionRate_invariant
    (omega connection tau : ℝ) :
    gaugeCorrectedComplexionRate (omega + tau) (connection + tau) =
      gaugeCorrectedComplexionRate omega connection := by
  unfold gaugeCorrectedComplexionRate
  ring

end RainichKaluza
