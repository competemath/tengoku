import Tengoku.TdaLib.TDA.Reeb.GraphPLHeight
import Tengoku.TdaLib.TDA.Reeb.CriticalValues
import Tengoku.TdaLib.TDA.Reeb.GraphRealizationExamples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fixtures for piecewise-linear heights on graph realizations

Acceptance fixtures for `TDA.Reeb.GraphPLHeight`, on the single edge `false — true` of
`⊤ : SimpleGraph Bool` with its dart `d₀ : false → true` from
`TDA.Reeb.Examples.GraphRealization`:

* **Reversal formulas.** With heights `0` and `2`, `dartHeight h02 d₀ t = 2t` and
  `dartHeight h02 d₀.symm t = 2 - 2t` for every `t`, and the reversal equation holds at every `t`.
  At `t = 1/4` the two orientations have different heights; at the midpoint they agree, so a
  witness at `1/2` alone cannot discriminate orientation.
* **Support.** The edge is active over `(1/4, 3/4)` although neither endpoint height lies in it,
  the midpoint is not a witness there, and the reversed dart supports the same edge at the reversed
  parameter. Over `(-∞, 1/2)` one endpoint survives, the other does not, and the edge is active,
  with an interior witness obtained from the endpoint parameter by openness. Over `(3, ∞)` the edge
  is inactive. Activity passes from `(1/4, 3/4)` to `(0, 2)`.
* **Horizontal edge.** With constant height `1`, the edge is active over `I` exactly when `1 ∈ I`:
  active over `(0, 2)` and inactive over `(2, 3)`.
* **Injectivity.** The reversed dart of the edge with heights `0` and `2` has injective height,
  while the horizontal dart does not, so `dartHeight_injective` needs unequal endpoint heights.

The short names `quarter` and `coe_quarter` also occur in `TDA.Reeb.Examples.ConstructibleSmoothing`,
and `support_mono` as `TDA.Filtration.support_mono`.
-/

open SimpleGraph Topology Set CategoryTheory

/-- The reversal of the unit interval; `open unitInterval` would make `I` a token.-/
local notation "σ" => unitInterval.symm

namespace TDA.Reeb.Examples.GraphPL

open TDA.Reeb.GraphRealization TDA.Reeb.GraphPL TDA.Reeb.OpenInterval
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ edgeGraph_dart half edge_param_injective)

noncomputable section

/--
@isnad1 id=eq.0h0v.s5.c3f926609ab9 from=translated src=- shape=35126999 vocab=cfea3e38
-/
theorem coe_half : (half : ℝ) = 1 / 2 := rfl

/-- The parameter `1/4`, which distinguishes the two orientations of a dart.-/
def quarter : unitInterval := ⟨1 / 4, by norm_num, by norm_num⟩

/--
@isnad1 id=eq.0h0v.s5.62c5336d2cd9 from=translated src=- shape=35126999 vocab=b0900685
-/
theorem coe_quarter : (quarter : ℝ) = 1 / 4 := rfl

/-- Heights `0` and `2` on the single edge `false — true`.-/
def h02 : Bool → ℝ
  | false => 0
  | true => 2

/--
@isnad1 id=eq.0h1v.s5.6bb74721ca12 from=translated src=- shape=0f1306d0 vocab=3ac223b5
-/
theorem dartHeight_d₀ (t : unitInterval) : dartHeight h02 d₀ t = 2 * t := by
  show (1 - (t : ℝ)) * h02 false + (t : ℝ) * h02 true = 2 * t
  simp only [h02]
  ring

/--
@isnad1 id=eq.0h1v.s5.088a4dc7a364 from=translated src=- shape=ff3c1f22 vocab=b60209c1
-/
theorem dartHeight_d₀_symm (t : unitInterval) : dartHeight h02 d₀.symm t = 2 - 2 * t := by
  show (1 - (t : ℝ)) * h02 true + (t : ℝ) * h02 false = 2 - 2 * t
  simp only [h02]
  ring

/-- Reversal of the two darts at an arbitrary parameter.
@isnad1 id=eq.0h1v.s4.b24d53959d1c from=translated src=- shape=dde4c330 vocab=8e70bdc6
-/
theorem d₀_reversal (t : unitInterval) :
    dartHeight h02 d₀.symm (σ t) = dartHeight h02 d₀ t :=
  dartHeight_symm h02 d₀ t

/--
@isnad1 id=eq.0h0v.s4.3259f9ae88d3 from=translated src=- shape=27246a7d vocab=e07e8e24
-/
theorem d₀_quarter : dartHeight h02 d₀ quarter = 1 / 2 := by
  rw [dartHeight_d₀, coe_quarter]; norm_num

/--
@isnad1 id=eq.0h0v.s5.37a9adb71d41 from=translated src=- shape=24395bea vocab=d160db16
-/
theorem d₀_symm_quarter : dartHeight h02 d₀.symm quarter = 3 / 2 := by
  rw [dartHeight_d₀_symm, coe_quarter]; norm_num

/-- At the parameter `1/4` the two orientations have different heights.
@isnad1 id=ne.0h0v.s4.1700f9671fe3 from=translated src=- shape=2ab00e77 vocab=b0824cf0
-/
theorem orientation_quarter_ne : dartHeight h02 d₀ quarter ≠ dartHeight h02 d₀.symm quarter := by
  rw [d₀_quarter, d₀_symm_quarter]; norm_num

/-- At the midpoint the two orientations agree, so a witness at `1/2` alone cannot discriminate
orientation.
@isnad1 id=eq.0h0v.s4.fc1261bf6f53 from=translated src=- shape=2ab00e77 vocab=c9d13a3b
-/
theorem orientation_half_eq : dartHeight h02 d₀ half = dartHeight h02 d₀.symm half := by
  rw [dartHeight_d₀, dartHeight_d₀_symm, coe_half]; norm_num

/-- The single edge is the only element of the edge set.
@isnad1 id=eq.0h1v.s4.f6577e28222c from=translated src=- shape=34579205 vocab=ffcbf175
-/
theorem edgeGraph_edge_eq (e : edgeGraph.edgeSet) : e = dartEdge d₀ := by
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
  rcases edgeGraph_dart d with rfl | rfl
  · rfl
  · exact dartEdge_symm d₀

/-- Interior-only support: neither endpoint height lies in `(1/4, 3/4)`, yet the edge is active.
@isnad1 id=edgeacti.0h0v.s5.c993e1890de1 from=translated src=- shape=e4bf574d vocab=13999627
-/
theorem support_interior_active : EdgeActive edgeGraph h02 (ioo (1 / 4) (3 / 4)) (dartEdge d₀) :=
  edgeActive_dartEdge_of_mem (t := quarter) (by rw [d₀_quarter, mem_ioo]; norm_num)

/--
@isnad1 id=and.0h0v.s6.1e908056386f from=translated src=- shape=7599dd32 vocab=055eaf55
-/
theorem support_interior_no_endpoint :
    h02 false ∉ ioo (1 / 4) (3 / 4) ∧ h02 true ∉ ioo (1 / 4) (3 / 4) := by
  constructor <;> (rw [mem_ioo]; norm_num [h02])

/-- The midpoint is not a support witness there.
@isnad1 id=not.0h0v.s5.e5fd2f9c68c9 from=translated src=- shape=f1c98c07 vocab=266d6eba
-/
theorem support_half_not_witness : dartHeight h02 d₀ half ∉ ioo (1 / 4) (3 / 4) := by
  rw [dartHeight_d₀, coe_half, mem_ioo]; norm_num

/-- The reversed dart supports the same edge at the reversed parameter.
@isnad1 id=mem.0h0v.s6.bf1b96c21dda from=translated src=- shape=3235132d vocab=d91a5fd5
-/
theorem support_reversed_witness : dartHeight h02 d₀.symm (σ quarter) ∈ ioo (1 / 4) (3 / 4) := by
  rw [d₀_reversal, d₀_quarter, mem_ioo]; norm_num

/-- One surviving endpoint: the incident edge is active.
@isnad1 id=edgeacti.0h0v.s5.26c3bcdab22d from=translated src=- shape=ab75bbe1 vocab=d95963c6
-/
theorem support_endpoint_active : EdgeActive edgeGraph h02 (iio (1 / 2)) (dartEdge d₀) :=
  edgeActive_of_mem (fst_mem_dartEdge d₀) (by show (0 : ℝ) < 1 / 2; norm_num)

/--
@isnad1 id=not.0h0v.s5.e58056d681a6 from=translated src=- shape=a5277ef0 vocab=481acb43
-/
theorem support_endpoint_other_out : h02 true ∉ iio (1 / 2) := by
  rw [mem_iio]; norm_num [h02]

/-- From the endpoint parameter `0`, openness yields an interior support witness.
@isnad1 id=ex.0h0v.s6.33320421a434 from=translated src=- shape=99fc3575 vocab=04633a07
-/
theorem support_endpoint_interior :
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ dartHeight h02 d₀ t ∈ iio (1 / 2) :=
  exists_interior_of_mem (t := 0) (by rw [dartHeight_zero]; show (0 : ℝ) < 1 / 2; norm_num)

/-- No endpoint and no interior point: the edge is inactive.
@isnad1 id=not.0h0v.s4.68cce94c4f79 from=translated src=- shape=26e3318c vocab=b8e81129
-/
theorem support_inactive : ¬ EdgeActive edgeGraph h02 (ioi 3) (dartEdge d₀) := by
  rw [edgeActive_dartEdge_iff_nonempty]
  rintro ⟨t, ht⟩
  rw [dartHeight_d₀, mem_ioi] at ht
  linarith [unitInterval.le_one t]

/-- Monotonicity in the interval.
@isnad1 id=edgeacti.0h0v.s4.3b80ce01e735 from=translated src=- shape=c09b3c1b vocab=5af36b5e
-/
theorem support_mono : EdgeActive edgeGraph h02 (ioo 0 2) (dartEdge d₀) :=
  support_interior_active.mono (OpenInterval.le_iff_subset.2 fun x hx => by
    obtain ⟨h₁, h₂⟩ := hx
    show (0 : ℝ) < x ∧ x < 2
    constructor <;> linarith)

/-- Constant height `1`: a horizontal edge.-/
def hconst : Bool → ℝ := fun _ => 1

/--
@isnad1 id=iff.0h1v.s4.fb3d9226055c from=translated src=- shape=b894d1b0 vocab=fac55b05
-/
theorem horizontal_active_iff (I : OpenInterval) :
    EdgeActive edgeGraph hconst I (dartEdge d₀) ↔ (1 : ℝ) ∈ I :=
  edgeActive_dartEdge_iff_of_eq rfl

/--
@isnad1 id=edgeacti.0h0v.s4.26eb90a35492 from=translated src=- shape=c09b3c1b vocab=4b14f104
-/
theorem horizontal_inside_active : EdgeActive edgeGraph hconst (ioo 0 2) (dartEdge d₀) :=
  (horizontal_active_iff _).2 (by rw [mem_ioo]; norm_num)

/--
@isnad1 id=not.0h0v.s4.e725b80e23a4 from=translated src=- shape=602ee9ce vocab=4b14f104
-/
theorem horizontal_outside_inactive : ¬ EdgeActive edgeGraph hconst (ioo 2 3) (dartEdge d₀) :=
  fun he => by
    have h1 := (horizontal_active_iff _).1 he
    rw [mem_ioo] at h1
    norm_num at h1

/-- The reversed nonhorizontal dart has injective height.
@isnad1 id=injectiv.0h0v.s3.fcd44346013e from=translated src=- shape=4df668c2 vocab=f6fd2aef
-/
theorem reversed_injective : Function.Injective (dartHeight h02 d₀.symm) :=
  dartHeight_injective h02 fun hne => by
    have h01 := (dartHeight_zero h02 d₀.symm).trans (hne.trans (dartHeight_one h02 d₀.symm).symm)
    rw [dartHeight_d₀_symm, dartHeight_d₀_symm] at h01
    norm_num at h01

/-- A horizontal dart has noninjective height, so the nonhorizontal hypothesis is needed.
@isnad1 id=not.0h0v.s3.4baae37d5a1a from=translated src=- shape=1bcdf3cc vocab=ffa01fa1
-/
theorem horizontal_not_injective : ¬ Function.Injective (dartHeight hconst d₀) := fun hinj => by
  have h01 := congrArg (fun t : unitInterval => (t : ℝ))
    (hinj ((dartHeight_of_eq hconst rfl 0).trans (dartHeight_of_eq hconst rfl 1).symm))
  norm_num at h01

end

end TDA.Reeb.Examples.GraphPL
