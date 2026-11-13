import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.BridgeLevel
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SphereClose

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The inverse Pontryagin--Thom comparison for bridge representatives

For bridge data `B`, this file constructs an explicit Thom-collapse representative
of the northern part of the regular fiber of `B.fls`.  Its ambient numerator is

`plateauAux u - plateauA (vertC u) • embedCLM n B.y`,

where `u = nprep B.approx x`.  Thus its horizontal coordinates are exactly
`plateauA (vertC u) • B.fls.g x`.  Along the northern fiber the cutoff is one,
so the differential in normal directions is the original regular-value framing.
On the southern cap the numerator is the south pole.

The numerator has positive inner product with `u`.  Consequently its normalization
is pointwise non-antipodal to the original bridge representative, and normalized
straight chords give the explicit relative homotopy proving equality of classes.
-/

noncomputable section

open scoped Topology unitInterval RealInnerProductSpace ContDiff
open Metric Set Function Topology.Homotopy

namespace Submission

variable {n : ℕ}
variable {z : HomotopyGroup (Fin (n + 1))
    (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}

namespace BridgeData

variable (B : BridgeData n z)

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))
local notation "F" => EuclideanSpace ℝ (Fin n)

/-! ## Ambient collapse -/

/-- The everywhere-defined sphere representative underlying the bridge, transported
to the Euclidean domain.-/
def northSource (x : E) : E := nprep B.approx (WithLp.ofLp x)

/--
@isnad1 id=eq.0h4v.s9.741645863292 from=translated src=- shape=1fd8ce2b vocab=f95ac9cb
-/
lemma norm_northSource (x : E) : ‖B.northSource x‖ = 1 :=
  norm_nprep B.approx (WithLp.ofLp x)

/--
@isnad1 id=contdiff.0h3v.s10.b721fb5fdb73 from=translated src=- shape=329912ff vocab=cff38304
-/
lemma contDiff_northSource : ContDiff ℝ ∞ B.northSource := by
  exact (contDiff_nprep B.approx).comp
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).contDiff

/-- The northern cutoff.  It is zero below latitude `-1/2` and one above
latitude `-1/4`.-/
def northCutoff (x : E) : ℝ := plateauA (vertC (B.northSource x))

/--
@isnad1 id=le.0h4v.s9.3e305259f634 from=translated src=- shape=edb5aa8f vocab=6506c215
-/
lemma northCutoff_nonneg (x : E) : 0 ≤ B.northCutoff x :=
  plateauA_nonneg _

/--
@isnad1 id=le.0h4v.s9.030b535f35af from=translated src=- shape=bd01b761 vocab=6506c215
-/
lemma northCutoff_le_one (x : E) : B.northCutoff x ≤ 1 :=
  plateauA_le_one _

/--
@isnad1 id=contdiff.0h3v.s9.0081d1229159 from=translated src=- shape=611f7ff0 vocab=b1d40ae7
-/
lemma contDiff_northCutoff : ContDiff ℝ ∞ B.northCutoff := by
  exact contDiff_plateauA.comp (contDiff_vertC.comp B.contDiff_northSource)

/-- The unnormalized northern Thom collapse.  Near the northern fiber it is
`northSource x - embed B.y`; on the southern cap it is the south pole.-/
def northThomRaw (x : E) : E :=
  plateauAux (B.northSource x) - B.northCutoff x • embedCLM n B.y

/--
@isnad1 id=contdiff.0h3v.s10.d85769f58b0f from=translated src=- shape=329912ff vocab=b300db63
-/
lemma contDiff_northThomRaw : ContDiff ℝ ∞ B.northThomRaw := by
  exact (contDiff_plateauAux.comp B.contDiff_northSource).sub
    (B.contDiff_northCutoff.smul contDiff_const)

/-- The horizontal embedding is adjoint to forgetting the last coordinate.
@isnad1 id=eq.0h3v.s11.a75d4da800cb from=translated src=- shape=db42855b vocab=df898377
-/
lemma inner_embedCLM_left (y : F) (u : E) :
    ⟪embedCLM n y, u⟫ = ⟪y, initCLM n u⟫ := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_castSucc,
    embedCLM_apply_castSucc, embedCLM_apply_last, initCLM_apply]

/-- Closed form for the pairing of the collapse numerator with the source point.
@isnad1 id=eq.0h4v.s10.7d4b5e5bce04 from=translated src=- shape=ddf45210 vocab=7d5b9667
-/
lemma inner_northThomRaw_source (x : E) :
    ⟪B.northThomRaw x, B.northSource x⟫ =
      plateauA (vertC (B.northSource x)) *
        (1 + vertC (B.northSource x) -
          ⟪B.y, initCLM n (B.northSource x)⟫) -
        vertC (B.northSource x) := by
  rw [northThomRaw, inner_sub_left, real_inner_smul_left,
    inner_plateauAux_self (B.norm_northSource x),
    inner_embedCLM_left (n := n), northCutoff]
  ring

/-- The collapse numerator pairs positively with the original sphere point.
@isnad1 id=lt.0h4v.s9.cd682ad15e4e from=translated src=- shape=fce5cf25 vocab=3c7ef1ea
-/
lemma inner_northThomRaw_source_pos (x : E) :
    0 < ⟪B.northThomRaw x, B.northSource x⟫ := by
  rw [B.inner_northThomRaw_source]
  let u := B.northSource x
  let t := vertC u
  let h := initCLM n u
  have hu : ‖u‖ = 1 := B.norm_northSource x
  have ht_abs : |t| ≤ 1 := abs_vertC_le_one hu
  have ht_lower : -1 ≤ t := neg_le_of_abs_le ht_abs
  have hh : ‖h‖ ≤ 1 := by
    have hs := norm_sq_split u
    rw [hu] at hs
    have hh0 := norm_nonneg h
    nlinarith [sq_nonneg t]
  have hip_abs : |⟪B.y, h⟫| < 1 / 8 := by
    calc
      |⟪B.y, h⟫| ≤ ‖B.y‖ * ‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖B.y‖ * 1 := mul_le_mul_of_nonneg_left hh (norm_nonneg B.y)
      _ < 1 / 8 := by simpa using B.norm_y_lt
  by_cases hlow : t ≤ -(1 / 2)
  · rw [plateauA_of_le hlow]
    linarith
  by_cases hhigh : -(1 / 4) ≤ t
  · rw [plateauA_of_ge hhigh]
    have hip_lt : ⟪B.y, h⟫ < 1 / 8 :=
      lt_of_le_of_lt (le_abs_self _) hip_abs
    linarith
  · have htneg : t < -(1 / 4) := lt_of_not_ge hhigh
    have httrans : -(1 / 2) < t := lt_of_not_ge hlow
    have hip_lt : ⟪B.y, h⟫ < 1 / 8 :=
      lt_of_le_of_lt (le_abs_self _) hip_abs
    have hbracket : 0 < 1 + t - ⟪B.y, h⟫ := by linarith
    have hprod : 0 ≤ plateauA t * (1 + t - ⟪B.y, h⟫) :=
      mul_nonneg (plateauA_nonneg t) hbracket.le
    linarith

/--
@isnad1 id=ne.0h4v.s9.9b569d3ce372 from=translated src=- shape=ded31342 vocab=69ddd301
-/
lemma northThomRaw_ne_zero (x : E) : B.northThomRaw x ≠ 0 := by
  intro h0
  have hpos := B.inner_northThomRaw_source_pos x
  rw [h0, inner_zero_left] at hpos
  exact lt_irrefl 0 hpos

/-- The normalized northern Thom collapse.-/
def northThom (x : E) : UnitSphere E :=
  ⟨‖B.northThomRaw x‖⁻¹ • B.northThomRaw x,
    mem_sphere_zero_iff_norm.mpr (norm_normalize (B.northThomRaw_ne_zero x))⟩

/--
@isnad1 id=eq.0h4v.s10.947e31e14387 from=translated src=- shape=9e22bb02 vocab=27244663
-/
lemma northThom_coe (x : E) :
    (B.northThom x : E) = ‖B.northThomRaw x‖⁻¹ • B.northThomRaw x := rfl

/--
@isnad1 id=contdiff.0h3v.s10.25de2d7860c6 from=translated src=- shape=ef6a31d1 vocab=cdd14a89
-/
lemma contDiff_northThom : ContDiff ℝ ∞ fun x => (B.northThom x : E) :=
  contDiff_normalize_comp B.contDiff_northThomRaw B.northThomRaw_ne_zero

/--
@isnad1 id=continuo.0h3v.s10.d33e20bc5b94 from=translated src=- shape=040a9532 vocab=e65c76ca
-/
lemma continuous_northThom : Continuous B.northThom := by
  exact Continuous.subtype_mk B.contDiff_northThom.continuous _

def northThomCM : C(E, UnitSphere E) :=
  ⟨B.northThom, B.continuous_northThom⟩

/-! ## Local normal-coordinate contract -/

/-- On the northern fiber the cutoff is identically one.
@isnad1 id=eq.1h4v.s9.108482f9c2d6 from=translated src=- shape=5bc3b02e vocab=723a3328
-/
lemma northCutoff_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) : B.northCutoff x = 1 := by
  rw [northCutoff, hx]
  exact plateauA_of_ge (by
    have := vertC_northPoint_pos B.norm_y_lt_one
    linarith)

/-- Horizontal north-pole chart applied to the normalized Thom collapse.-/
def northThomHorizontal (x : E) : F := initCLM n (B.northThom x : E)

/-! ## Exact north fiber -/

/-- The target north pole of the collapse.-/
def ptNorthPole : UnitSphere E :=
  ⟨eLast n, by rw [mem_sphere_zero_iff_norm, norm_eLast]⟩

/--
@isnad1 id=eq.0h1v.s8.680511f51034 from=translated src=- shape=83d7ce35 vocab=5fa71cf1
-/
@[simp] lemma ptNorthPole_coe : (ptNorthPole (n := n) : E) = eLast n := rfl

/-! ## Southern collapse and cubical loop -/

/--
@isnad1 id=eq.1h4v.s9.8bb68e9ef73c from=translated src=- shape=38b19927 vocab=b1224bf5
-/
lemma northThomRaw_of_southCap {x : E}
    (hx : vertC (B.northSource x) ≤ -(1 / 2)) :
    B.northThomRaw x = -eLast n := by
  rw [northThomRaw, plateauAux_of_le hx, northCutoff, plateauA_of_le hx]
  simp

/--
@isnad1 id=eq.1h4v.s9.d0ed1abe84e7 from=translated src=- shape=55f2206c vocab=a7cc75cf
-/
theorem northThom_of_southCap {x : E}
    (hx : vertC (B.northSource x) ≤ -(1 / 2)) :
    B.northThom x = southPole n := by
  apply Subtype.ext
  rw [northThom_coe, B.northThomRaw_of_southCap hx, southPole_coe,
    norm_neg, norm_eLast]
  simp

/--
@isnad1 id=le.0h3v.s9.ac4231b4a7f0 from=translated src=- shape=4315fde0 vocab=adcfabd6
-/
lemma southPointOf_mem_southCap :
    vertC (southPointOf B.y) ≤ -(1 / 2) := by
  rw [vertC_southPointOf]
  have harg : 0 ≤ 1 - ‖B.y‖ ^ 2 := by
    have h0 := norm_nonneg B.y
    have h1 := B.norm_y_lt_one
    nlinarith
  have hs0 := Real.sqrt_nonneg (1 - ‖B.y‖ ^ 2)
  have hs2 := Real.sq_sqrt harg
  have hy0 := norm_nonneg B.y
  have hy8 := B.norm_y_lt
  nlinarith

/-- The unit cube as a subset of the Euclidean source used by `B.fls`.-/
def cubeToBridgeDomain (t : I^(Fin (n + 1))) : E :=
  WithLp.toLp 2 fun i => (t i : ℝ)

/--
@isnad1 id=eq.0h3v.s6.f44454153aa2 from=translated src=- shape=6d6257e8 vocab=6b136938
-/
@[simp] lemma cubeToBridgeDomain_apply (t : I^(Fin (n + 1))) (i : Fin (n + 1)) :
    cubeToBridgeDomain t i = (t i : ℝ) := rfl

/--
@isnad1 id=continuo.0h1v.s7.2a984dd1ff0e from=translated src=- shape=393619d2 vocab=9c9bdd9b
-/
lemma continuous_cubeToBridgeDomain :
    Continuous (cubeToBridgeDomain (n := n)) := by
  have h : cubeToBridgeDomain (n := n) = fun t =>
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (fun i => (t i : ℝ)) := rfl
  rw [h]
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp (continuous_apply i)

/--
@isnad1 id=eq.0h4v.s9.eb3d4c9fe52b from=translated src=- shape=b8072c27 vocab=50b20cd0
-/
lemma northSource_cube (t : I^(Fin (n + 1))) :
    B.northSource (cubeToBridgeDomain t) =
      nprep B.approx (fun i => (t i : ℝ)) := rfl

/--
@isnad1 id=eq.1h4v.s9.4db5512299a6 from=translated src=- shape=a14cc3d3 vocab=781b1185
-/
lemma northSource_cube_boundary {t : I^(Fin (n + 1))}
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    B.northSource (cubeToBridgeDomain t) = -eLast n := by
  rw [B.northSource_cube]
  exact nprep_of_mem_collar B.approx (coords_mem_closedAmbientCollar ht)

/--
@isnad1 id=eq.1h4v.s9.fa636e05ee1c from=translated src=- shape=e03ea320 vocab=7986668d
-/
theorem northThom_cube_boundary {t : I^(Fin (n + 1))}
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    B.northThom (cubeToBridgeDomain t) = southPole n := by
  apply B.northThom_of_southCap
  rw [B.northSource_cube_boundary ht]
  show (-eLast n) (Fin.last n) ≤ -(1 / 2 : ℝ)
  simp [eLast]
  norm_num

/-- The cubical generalized loop of the northern Thom collapse.-/
def northThomLoop :
    Ω^ (Fin (n + 1)) (UnitSphere E) (southPole n) :=
  ⟨B.northThomCM.comp
      ⟨cubeToBridgeDomain, continuous_cubeToBridgeDomain⟩,
    fun _ ht => B.northThom_cube_boundary ht⟩

/--
@isnad1 id=eq.0h4v.s11.dac2b6ab9668 from=translated src=- shape=e17f7844 vocab=f1f121ad
-/
@[simp] lemma northThomLoop_apply (t : I^(Fin (n + 1))) :
    B.northThomLoop t = B.northThom (cubeToBridgeDomain t) := rfl

/-! ## Explicit normalized-chord comparison -/

/-- The original bridge source, packaged as a point of the unit sphere.-/
def northSourcePoint (x : E) : UnitSphere E :=
  ⟨B.northSource x,
    mem_sphere_zero_iff_norm.mpr (B.norm_northSource x)⟩

/--
@isnad1 id=eq.0h4v.s10.4286999a5c9f from=translated src=- shape=96d8143e vocab=ab2cd109
-/
@[simp] lemma northSourcePoint_coe (x : E) :
    (B.northSourcePoint x : E) = B.northSource x := rfl

/--
@isnad1 id=lt.0h4v.s10.8d1ef6f143d4 from=translated src=- shape=75396099 vocab=67738c14
-/
lemma inner_northThom_source_pos (x : E) :
    0 < ⟪(B.northThom x : E), B.northSource x⟫ := by
  rw [northThom_coe, real_inner_smul_left]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (B.northThomRaw_ne_zero x)))
    (B.inner_northThomRaw_source_pos x)

/--
@isnad1 id=ne.0h4v.s10.8990c70bb973 from=translated src=- shape=17ba4385 vocab=efda2aed
-/
lemma northSourcePoint_ne_neg_northThom (x : E) :
    B.northSourcePoint x ≠ -B.northThom x := by
  intro hc
  have hcoe : B.northSource x = -(B.northThom x : E) := by
    have := congrArg Subtype.val hc
    simpa [northSourcePoint_coe, coe_neg_sphere] using this
  have hpos := B.inner_northThom_source_pos x
  rw [hcoe, inner_neg_right, real_inner_self_eq_norm_sq,
    UnitSphere.norm_coe] at hpos
  norm_num at hpos

/--
@isnad1 id=lt.0h4v.s10.3ec435c25c22 from=translated src=- shape=4b4a4ba4 vocab=9436350b
-/
lemma dist_northSourcePoint_northThom_lt_two (x : E) :
    dist (B.northSourcePoint x) (B.northThom x) < 2 :=
  dist_lt_two_of_ne_neg _ _ (B.northSourcePoint_ne_neg_northThom x)

/--
@isnad1 id=eq.0h4v.s11.c57194d62791 from=translated src=- shape=b3a3c218 vocab=cff63f2b
-/
lemma prepLoop_eq_northSourcePoint (t : I^(Fin (n + 1))) :
    prepLoop B.approx t = B.northSourcePoint (cubeToBridgeDomain t) := by
  apply Subtype.ext
  rw [prepLoop_coe, northSourcePoint_coe, B.northSource_cube]

/--
@isnad1 id=lt.0h4v.s12.b718c2a4cf72 from=translated src=- shape=1b36de04 vocab=59e33d5e
-/
lemma dist_prepLoop_northThomLoop_lt_two (t : I^(Fin (n + 1))) :
    dist (prepLoop B.approx t) (B.northThomLoop t) < 2 := by
  rw [B.prepLoop_eq_northSourcePoint, northThomLoop_apply]
  exact B.dist_northSourcePoint_northThom_lt_two _

/-- The promised explicit Pontryagin--Thom homotopy: normalize the straight chord
from the bridge representative to the northern Thom collapse.  It is relative to
the entire cubical boundary.-/
def prepLoopToNorthThomHomotopy :
    ContinuousMap.HomotopyRel (prepLoop B.approx).1 B.northThomLoop.1
      (Cube.boundary (Fin (n + 1))) :=
  chordHomotopyRel (prepLoop B.approx).1 B.northThomLoop.1
    B.dist_prepLoop_northThomLoop_lt_two
    (Cube.boundary (Fin (n + 1))) fun t ht =>
      ((prepLoop B.approx).2 t ht).trans (B.northThomLoop.2 t ht).symm

end BridgeData

end Submission
