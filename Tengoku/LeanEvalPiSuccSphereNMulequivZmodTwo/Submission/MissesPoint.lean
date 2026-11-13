import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SphereClose

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Loops missing a point of the sphere are nullhomotopic

A generalized loop in the unit sphere that misses some point `y` is homotopic rel
boundary to the constant loop: transport the loop through the stereographic
projection centred at `y` (whose source is exactly the complement of `y` and whose
target is the whole orthogonal complement), contract the affine straight line
towards the image of the basepoint, and map back.

Main declarations:

* `Submission.missHomotopy`: the based contraction, as a `HomotopyRel`;
* `Submission.homotopic_const_of_misses`;
* `Submission.homotopy_class_eq_one_of_misses` (group version).
-/

noncomputable section

open scoped Topology unitInterval
open Topology.Homotopy Metric

namespace Submission

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : Type*} {x : UnitSphere E}

/-- A point of the sphere distinct from `y` lies in the source of the stereographic
projection centred at `y`.
@isnad1 id=mem.1h3v.s10.631b6970bf3b from=translated src=- shape=e55c6543 vocab=60659f41
-/
theorem mem_stereographic_source {y z : UnitSphere E} (h : z ≠ y) :
    z ∈ (stereographic (UnitSphere.norm_coe y)).source := by
  rw [stereographic_source, Set.mem_compl_singleton_iff]
  exact fun hz => h (hz.trans (Subtype.ext rfl))

/-- The based contraction of a generalized loop missing the point `y`: inside the
stereographic chart centred at `y`, slide along the straight line to the image of
the basepoint.-/
def missHomotopy (p : Ω^ N (UnitSphere E) x) (y : UnitSphere E)
    (h : ∀ t, p t ≠ y) (hxy : x ≠ y) :
    ContinuousMap.HomotopyRel p.1 (GenLoop.const : Ω^ N (UnitSphere E) x).1
      (Cube.boundary N) where
  toFun st :=
    (stereographic (UnitSphere.norm_coe y)).symm
      ((1 - (st.1 : ℝ)) • stereographic (UnitSphere.norm_coe y) (p.1 st.2)
        + (st.1 : ℝ) • stereographic (UnitSphere.norm_coe y) x)
  continuous_toFun := by
    have hsymm : Continuous (stereographic (UnitSphere.norm_coe y)).symm := by
      have hc := (stereographic (UnitSphere.norm_coe y)).continuousOn_symm
      rw [stereographic_target] at hc
      exact continuousOn_univ.mp hc
    have hA : Continuous fun t : I^N =>
        stereographic (UnitSphere.norm_coe y) (p.1 t) := by
      refine ContinuousOn.comp_continuous
        (stereographic (UnitSphere.norm_coe y)).continuousOn
        (map_continuous p.1) fun t => ?_
      exact mem_stereographic_source (h t)
    have hs : Continuous fun st : I × (I^N) => (st.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact hsymm.comp
      (((continuous_const.sub hs).smul (hA.comp continuous_snd)).add
        (hs.smul continuous_const))
  map_zero_left t := by
    show (stereographic (UnitSphere.norm_coe y)).symm _ = p.1 t
    have hcoef : (1 - ((0 : I) : ℝ)) = 1 := by
      rw [Set.Icc.coe_zero]; ring
    rw [hcoef, one_smul, Set.Icc.coe_zero, zero_smul, add_zero]
    exact (stereographic (UnitSphere.norm_coe y)).left_inv
      (mem_stereographic_source (h t))
  map_one_left t := by
    show (stereographic (UnitSphere.norm_coe y)).symm _ = x
    have hcoef : (1 - ((1 : I) : ℝ)) = 0 := by
      rw [Set.Icc.coe_one]; ring
    rw [hcoef, zero_smul, zero_add, Set.Icc.coe_one, one_smul]
    exact (stereographic (UnitSphere.norm_coe y)).left_inv
      (mem_stereographic_source hxy)
  prop' s t ht := by
    show (stereographic (UnitSphere.norm_coe y)).symm _ = p.1 t
    have hpt : p.1 t = x := p.2 t ht
    rw [hpt, ← add_smul, sub_add_cancel, one_smul]
    exact (stereographic (UnitSphere.norm_coe y)).left_inv
      (mem_stereographic_source hxy)

/-- A generalized loop in the unit sphere missing some point is homotopic rel
boundary to the constant loop.
@isnad1 id=homotopi.1h5v.s9.17895aa72da4 from=translated src=- shape=198418ab vocab=7318c0e5
-/
theorem homotopic_const_of_misses [Nonempty N] (p : Ω^ N (UnitSphere E) x)
    (y : UnitSphere E) (h : ∀ t, p t ≠ y) : GenLoop.Homotopic p GenLoop.const := by
  have hxy : x ≠ y := by
    have hb : (fun _ => 0 : I^N) ∈ Cube.boundary N :=
      ⟨Classical.arbitrary N, Or.inl rfl⟩
    have hpx : p.1 (fun _ => 0) = x := p.2 _ hb
    rw [← hpx]
    exact h _
  exact ⟨missHomotopy p y h hxy⟩

/-- Quotient version: the class of a generalized loop missing a point is the class
of the constant loop.
@isnad1 id=eq.1h5v.s10.c5ae896eed9e from=translated src=- shape=d232c451 vocab=6a078789
-/
theorem homotopy_class_eq_const_of_misses [Nonempty N] (p : Ω^ N (UnitSphere E) x)
    (y : UnitSphere E) (h : ∀ t, p t ≠ y) :
    (⟦p⟧ : HomotopyGroup N (UnitSphere E) x) = ⟦GenLoop.const⟧ :=
  Quotient.sound (homotopic_const_of_misses p y h)

/-- Group version: the class of a generalized loop missing a point is the identity
element of the homotopy group.
@isnad1 id=eq.1h5v.s10.4f72765dbdb6 from=translated src=- shape=a426434f vocab=bbc3d5cb
-/
theorem homotopy_class_eq_one_of_misses [DecidableEq N] [Nonempty N]
    (p : Ω^ N (UnitSphere E) x) (y : UnitSphere E) (h : ∀ t, p t ≠ y) :
    ⟦p⟧ = (1 : HomotopyGroup N (UnitSphere E) x) := by
  rw [HomotopyGroup.one_def]
  exact homotopy_class_eq_const_of_misses p y h

end Submission
