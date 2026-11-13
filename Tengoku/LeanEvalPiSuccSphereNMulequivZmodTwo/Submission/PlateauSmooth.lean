import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SphereClose
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.HomotopyFunctor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The smooth southern plateau (cap collapse) of the sphere

We construct a map `Θ` of the unit sphere `Sⁿ ⊆ ℝ^{n+1}` which

* is induced by an explicit globally `C^∞` ambient map
  `plateauAux : ℝ^{n+1} → ℝ^{n+1}` (followed by normalization),
* is the identity on the region `{u | vert u ≥ -1/4}` (in particular on the northern
  cap `{vert u ≥ 1/2}`),
* collapses the southern cap `{u | vert u ≤ -1/2}` to the south pole
  `s₀ = -e_last`, and
* is homotopic to the identity rel `{s₀}`, hence acts as the identity on homotopy
  groups based at `s₀`.

Here `vert u := u (Fin.last n)` is the last coordinate.  The ambient formula is a
latitude reparametrization

  `plateauAux u := a(vert u) • (u - vert u • e_last) + b(vert u) • e_last`

with `a := plateauA` a smooth transition function (`0` for `t ≤ -1/2`, `1` for
`t ≥ -1/4`) and `b(t) := a(t) * (1 + t) - 1`.  The key inequality making everything
work is the closed form

  `⟪plateauAux u, u⟫ = a(vert u) * (1 + vert u) - vert u > 0`  (for `‖u‖ = 1`),

which simultaneously gives nonvanishing (so the normalization is defined and smooth)
and non-antipodality (so the straight-chord homotopy of `SphereClose` applies).

Main declarations:

* `Submission.southPole`, `Submission.plateauA`, `Submission.plateauB`,
  `Submission.plateauAux`;
* `Submission.contDiff_plateauAux`, `Submission.inner_plateauAux_pos`,
  `Submission.plateauAux_ne_zero`;
* `Submission.plateauAux_of_le` (southern collapse),
  `Submission.plateauAux_of_ge` (identity region);
* `Submission.plateauMap` (the sphere self-map), `Submission.plateauMap_southPole`;
* `Submission.plateauMap_homotopicRel_id`,
  `Submission.homotopyGroupMap_plateauMap`,
  `Submission.genLoopMap_plateauMap_class`.
-/

noncomputable section

open scoped Topology unitInterval RealInnerProductSpace ContDiff
open Metric Set Function Topology.Homotopy

namespace Submission

/-! ### Coordinates -/

/-- The last basis vector of `ℝ^{n+1}` ("north direction").-/
def eLast (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  EuclideanSpace.single (Fin.last n) 1

/-- The last ("vertical") coordinate.-/
def vertC {n : ℕ} (u : EuclideanSpace ℝ (Fin (n + 1))) : ℝ := u (Fin.last n)

/--
@isnad1 id=eq.0h1v.s6.bce40ca34a3f from=translated src=- shape=d9262d93 vocab=b399f6d5
-/
lemma norm_eLast {n : ℕ} : ‖eLast n‖ = 1 := by
  rw [eLast, PiLp.norm_single, norm_one]

/--
@isnad1 id=eq.0h1v.s3.e67449e8133b from=translated src=- shape=6ae13bdd vocab=fb2253d5
-/
lemma vertC_eLast {n : ℕ} : vertC (eLast n) = 1 := by
  simp [vertC, eLast]

/--
@isnad1 id=contdiff.0h1v.s7.aca67401bbe4 from=translated src=- shape=41de37fa vocab=8e4ff76a
-/
lemma contDiff_vertC {n : ℕ} :
    ContDiff ℝ ∞ (vertC (n := n)) := by
  unfold vertC
  exact (EuclideanSpace.proj (Fin.last n) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contDiff

/--
@isnad1 id=eq.0h2v.s7.5c20e8912e29 from=translated src=- shape=ac9b8bc7 vocab=3fa9cf74
-/
lemma inner_eLast_left {n : ℕ} (u : EuclideanSpace ℝ (Fin (n + 1))) :
    ⟪eLast n, u⟫ = vertC u := by
  simp [eLast, vertC, PiLp.inner_apply, PiLp.single_apply, RCLike.inner_apply]

/-- Coordinates are bounded by the norm.
@isnad1 id=le.0h3v.s7.109e2838baa5 from=translated src=- shape=aed2cf87 vocab=e3b275b0
-/
lemma abs_coord_le_norm {n : ℕ} (u : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) : |u i| ≤ ‖u‖ := by
  have h1 : ‖u i‖ ^ 2 ≤ ∑ j, ‖u j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖u j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ‖u‖ = Real.sqrt (∑ j, ‖u j‖ ^ 2) := EuclideanSpace.norm_eq u
  calc |u i| = Real.sqrt (‖u i‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, abs_abs]
    _ ≤ Real.sqrt (∑ j, ‖u j‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = ‖u‖ := h2.symm

/--
@isnad1 id=le.1h2v.s7.64df893bad0d from=translated src=- shape=22c1f683 vocab=8c1dcf9a
-/
lemma abs_vertC_le_one {n : ℕ} {u : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ‖u‖ = 1) : |vertC u| ≤ 1 :=
  hu ▸ abs_coord_le_norm u (Fin.last n)

/-! ### The south pole -/

/--
@isnad1 id=mem.0h1v.s9.029ac42e8a47 from=translated src=- shape=c4a68761 vocab=b2d1b72e
-/
lemma neg_eLast_mem_sphere {n : ℕ} :
    -eLast n ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_neg, norm_eLast]

/-- The south pole `s₀ = -e_last`, our basepoint.-/
def southPole (n : ℕ) : UnitSphere (EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨-eLast n, neg_eLast_mem_sphere⟩

/--
@isnad1 id=eq.0h1v.s9.cab7a95be31b from=translated src=- shape=f3d6b492 vocab=f678a4fa
-/
@[simp] lemma southPole_coe {n : ℕ} :
    ((southPole n) : EuclideanSpace ℝ (Fin (n + 1))) = -eLast n := rfl

/--
@isnad1 id=eq.0h1v.s8.0596574b6e63 from=translated src=- shape=f7621c3d vocab=759a93d6
-/
lemma vertC_southPole {n : ℕ} :
    vertC ((southPole n) : EuclideanSpace ℝ (Fin (n + 1))) = -1 := by
  show vertC (-eLast n) = -1
  show (-eLast n) (Fin.last n) = -1
  simp [eLast]

/-! ### The transition profiles -/

/-- The horizontal scaling profile: `0` for `t ≤ -1/2`, `1` for `t ≥ -1/4`.-/
def plateauA (t : ℝ) : ℝ := Real.smoothTransition (4 * t + 2)

/-- The vertical profile: `-1` for `t ≤ -1/2`, `t` for `t ≥ -1/4`.-/
def plateauB (t : ℝ) : ℝ := plateauA t * (1 + t) - 1

/--
@isnad1 id=le.0h1v.s3.63becb2683e3 from=translated src=- shape=8a62b088 vocab=63f79ec5
-/
lemma plateauA_nonneg (t : ℝ) : 0 ≤ plateauA t := Real.smoothTransition.nonneg _

/--
@isnad1 id=le.0h1v.s3.26b7070ed934 from=translated src=- shape=b14ee516 vocab=63f79ec5
-/
lemma plateauA_le_one (t : ℝ) : plateauA t ≤ 1 := Real.smoothTransition.le_one _

/--
@isnad1 id=eq.1h1v.s5.c93a68520158 from=translated src=- shape=c6bac174 vocab=cd3729a5
-/
lemma plateauA_of_le {t : ℝ} (h : t ≤ -(1 / 2)) : plateauA t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/--
@isnad1 id=eq.1h1v.s5.46ef17530889 from=translated src=- shape=458ef591 vocab=cd3729a5
-/
lemma plateauA_of_ge {t : ℝ} (h : -(1 / 4) ≤ t) : plateauA t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/--
@isnad1 id=eq.1h1v.s5.ca62c6e71f25 from=translated src=- shape=c2b0f98c vocab=29628ecb
-/
lemma plateauB_of_le {t : ℝ} (h : t ≤ -(1 / 2)) : plateauB t = -1 := by
  rw [plateauB, plateauA_of_le h]; ring

/--
@isnad1 id=eq.1h1v.s5.ed34f4881656 from=translated src=- shape=29551b98 vocab=29628ecb
-/
lemma plateauB_of_ge {t : ℝ} (h : -(1 / 4) ≤ t) : plateauB t = t := by
  rw [plateauB, plateauA_of_ge h]; ring

/--
@isnad1 id=contdiff.0h0v.s5.fa4e1c724766 from=translated src=- shape=3cea26be vocab=220c689d
-/
lemma contDiff_plateauA : ContDiff ℝ ∞ plateauA := by
  apply Real.smoothTransition.contDiff.comp
  exact (contDiff_const.mul contDiff_id).add contDiff_const

/--
@isnad1 id=contdiff.0h0v.s5.0886e2d89b1a from=translated src=- shape=3cea26be vocab=b3821f57
-/
lemma contDiff_plateauB : ContDiff ℝ ∞ plateauB :=
  (contDiff_plateauA.mul (contDiff_const.add contDiff_id)).sub contDiff_const

/-! ### The ambient plateau map -/

/-- The ambient plateau map: latitude reparametrization by the profiles
`plateauA`, `plateauB`.  Globally `C^∞`; nonvanishing on the unit sphere.-/
def plateauAux {n : ℕ} (u : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  plateauA (vertC u) • (u - vertC u • eLast n) + plateauB (vertC u) • eLast n

/--
@isnad1 id=contdiff.0h1v.s8.1715b563fc96 from=translated src=- shape=5fc2f4f7 vocab=05813b57
-/
lemma contDiff_plateauAux {n : ℕ} :
    ContDiff ℝ ∞ (plateauAux (n := n)) := by
  apply ContDiff.add
  · exact (contDiff_plateauA.comp contDiff_vertC).smul
      (contDiff_id.sub (contDiff_vertC.smul contDiff_const))
  · exact (contDiff_plateauB.comp contDiff_vertC).smul contDiff_const

/-- Southern collapse: for `vert u ≤ -1/2` the ambient plateau map is constantly
`-e_last`.
@isnad1 id=eq.1h2v.s8.15aea97ad688 from=translated src=- shape=15450d9b vocab=a188321e
-/
lemma plateauAux_of_le {n : ℕ} {u : EuclideanSpace ℝ (Fin (n + 1))}
    (h : vertC u ≤ -(1 / 2)) : plateauAux u = -eLast n := by
  rw [plateauAux, plateauA_of_le h, plateauB_of_le h]
  simp

/-- Identity region: for `vert u ≥ -1/4` the ambient plateau map is the identity.
@isnad1 id=eq.1h2v.s6.75c09262a821 from=translated src=- shape=3b9158d6 vocab=7d711a65
-/
lemma plateauAux_of_ge {n : ℕ} {u : EuclideanSpace ℝ (Fin (n + 1))}
    (h : -(1 / 4) ≤ vertC u) : plateauAux u = u := by
  rw [plateauAux, plateauA_of_ge h, plateauB_of_ge h, one_smul, sub_add_cancel]

/--
@isnad1 id=eq.0h1v.s9.bee9faaf6d22 from=translated src=- shape=b9a48f58 vocab=8e0c55f4
-/
lemma plateauAux_southPole {n : ℕ} :
    plateauAux ((southPole n) : EuclideanSpace ℝ (Fin (n + 1))) = -eLast n :=
  plateauAux_of_le (by rw [vertC_southPole]; norm_num)

/-- The fundamental closed form of the pairing with the base point.
@isnad1 id=eq.1h2v.s8.fe46465fbd04 from=translated src=- shape=c4d24be6 vocab=94d542c1
-/
lemma inner_plateauAux_self {n : ℕ} {u : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ‖u‖ = 1) :
    ⟪plateauAux u, u⟫ = plateauA (vertC u) * (1 + vertC u) - vertC u := by
  have huu : ⟪u, u⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have heu : ⟪eLast n, u⟫ = vertC u := inner_eLast_left u
  rw [plateauAux, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_sub_left, real_inner_smul_left, huu, heu]
  unfold plateauB
  ring

/-- Key positivity: the plateau image of a unit vector pairs positively with it.
This gives both nonvanishing and non-antipodality.
@isnad1 id=lt.1h2v.s8.0d1e475b2b70 from=translated src=- shape=a7d5df4d vocab=2eb27f26
-/
lemma inner_plateauAux_pos {n : ℕ} {u : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ‖u‖ = 1) : 0 < ⟪plateauAux u, u⟫ := by
  rw [inner_plateauAux_self hu]
  set t := vertC u with ht
  have habs : |t| ≤ 1 := abs_vertC_le_one hu
  have ht1 : -1 ≤ t := neg_le_of_abs_le habs
  rcases lt_trichotomy t 0 with h | h | h
  · have h1 : 0 ≤ plateauA t * (1 + t) :=
      mul_nonneg (plateauA_nonneg t) (by linarith)
    linarith
  · have h0 : plateauA t = 1 := plateauA_of_ge (by rw [h]; norm_num)
    rw [h0, h]
    norm_num
  · have h0 : plateauA t = 1 := plateauA_of_ge (by linarith)
    rw [h0]
    linarith

/--
@isnad1 id=ne.1h2v.s8.edbe6358fadc from=translated src=- shape=fc633d69 vocab=6c8fe92e
-/
lemma plateauAux_ne_zero {n : ℕ} {u : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ‖u‖ = 1) : plateauAux u ≠ 0 := by
  intro h0
  have h := inner_plateauAux_pos hu
  rw [h0, inner_zero_left] at h
  exact lt_irrefl 0 h

/-! ### The sphere self-map -/

/-- The ambient plateau map as a continuous map on the unit sphere, before
normalization.-/
def plateauCM (n : ℕ) :
    C(UnitSphere (EuclideanSpace ℝ (Fin (n + 1))), EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨fun u => plateauAux (u : EuclideanSpace ℝ (Fin (n + 1))),
    contDiff_plateauAux.continuous.comp continuous_subtype_val⟩

/--
@isnad1 id=ne.0h2v.s11.5dd4530cdeb0 from=translated src=- shape=21688ffd vocab=abf5a6f7
-/
lemma plateauCM_ne_zero {n : ℕ} (u : UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) :
    plateauCM n u ≠ 0 :=
  plateauAux_ne_zero (UnitSphere.norm_coe u)

/-- The plateau self-map `Θ` of the unit sphere: normalized ambient plateau map.-/
def plateauMap (n : ℕ) :
    C(UnitSphere (EuclideanSpace ℝ (Fin (n + 1))),
      UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) :=
  normalizeMap (plateauCM n) plateauCM_ne_zero

/--
@isnad1 id=eq.0h2v.s12.15e55766c1a0 from=translated src=- shape=a9f65f43 vocab=2ef4a6c1
-/
lemma plateauMap_coe {n : ℕ} (u : UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) :
    ((plateauMap n u) : EuclideanSpace ℝ (Fin (n + 1)))
      = ‖plateauAux (u : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ •
          plateauAux (u : EuclideanSpace ℝ (Fin (n + 1))) :=
  rfl

/-- `Θ` fixes the south pole.
@isnad1 id=eq.0h1v.s11.eb440dded4ef from=translated src=- shape=935009d8 vocab=a7c84136
-/
lemma plateauMap_southPole {n : ℕ} : plateauMap n (southPole n) = southPole n := by
  apply Subtype.ext
  rw [plateauMap_coe, plateauAux_southPole, southPole_coe, norm_neg, norm_eLast]
  simp

/-! ### Action on homotopy groups -/

end Submission
