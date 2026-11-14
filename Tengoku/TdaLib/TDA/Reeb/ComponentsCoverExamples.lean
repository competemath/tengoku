import Tengoku.TdaLib.TDA.Reeb.ComponentsCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Point-form component chain fixture

Regression fixture for `TDA.Reeb.componentFunctor_reflTransGen_of_mk_eq` on the identity of `ℝ`
with `W = ⊤` and the two overlapping opens `(-∞, 2/3)` and `(1/3, ∞)`. The points `0` and `1`
have the same class over `ℝ`, so they are linked by a chain whose links have equal classes over
a single member. No single member contains both points, so no single link relates them.
-/

open Set

namespace TDA.Reeb.Examples

/-- `(-∞, 2/3)` and `(1/3, ∞)` as opens of `ℝ`.-/
def twoOpens : Bool → TopologicalSpace.Opens ℝ
  | false => ⟨Iio (2 / 3), isOpen_Iio⟩
  | true => ⟨Ioi (1 / 3), isOpen_Ioi⟩

/--
@isnad1 id=le.0h0v.s7.20553d1c3300 from=translated src=- shape=cf9a99ac vocab=fe160e79
-/
theorem twoOpens_cover : (⊤ : TopologicalSpace.Opens ℝ) ≤ ⨆ b, twoOpens b := fun z _ => by
  refine TopologicalSpace.Opens.mem_iSup.2 ?_
  rcases lt_or_ge z (2 / 3) with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, show (1 / 3 : ℝ) < z by linarith⟩

/-- The points `0` and `1` of `ℝ = id ⁻¹ ⊤` are linked by a chain whose links have equal classes
over a single member of `twoOpens`.
@isnad1 id=refltran.0h0v.s11.bb102a24a830 from=translated src=- shape=78706649 vocab=3113758a
-/
theorem twoOpens_zero_one_chain :
    Relation.ReflTransGen
      (fun a b : {x : ℝ // ContinuousMap.id ℝ x ∈ (⊤ : TopologicalSpace.Opens ℝ)} =>
        ∃ i, ∃ (ha : ContinuousMap.id ℝ a.1 ∈ twoOpens i)
          (hb : ContinuousMap.id ℝ b.1 ∈ twoOpens i),
          (ZerothHomotopy.mk ⟨a.1, ha⟩ : (componentFunctor (ContinuousMap.id ℝ)).obj (twoOpens i)) =
            ZerothHomotopy.mk ⟨b.1, hb⟩)
      ⟨0, TopologicalSpace.Opens.mem_top _⟩ ⟨1, TopologicalSpace.Opens.mem_top _⟩ :=
  componentFunctor_reflTransGen_of_mk_eq (ContinuousMap.id ℝ) twoOpens twoOpens_cover
    ((componentFunctor_mk_eq_iff_joined _ _ _ _).2
      ⟨{ toFun := fun s => ⟨(s : ℝ), TopologicalSpace.Opens.mem_top _⟩
         continuous_toFun := continuous_subtype_val.subtype_mk _
         source' := rfl
         target' := rfl }⟩)

/-- No single link relates `0` and `1`: no member of `twoOpens` contains both points.
@isnad1 id=not.0h0v.s9.92567f15b091 from=translated src=- shape=15be169d vocab=4cff140d
-/
theorem twoOpens_zero_one_not_single_link :
    ¬ ∃ i, ∃ (ha : ContinuousMap.id ℝ 0 ∈ twoOpens i) (hb : ContinuousMap.id ℝ 1 ∈ twoOpens i),
      (ZerothHomotopy.mk ⟨0, ha⟩ : (componentFunctor (ContinuousMap.id ℝ)).obj (twoOpens i)) =
        ZerothHomotopy.mk ⟨1, hb⟩ := by
  rintro ⟨i, ha, hb, -⟩
  cases i
  · change (1 : ℝ) < 2 / 3 at hb
    norm_num at hb
  · change (1 / 3 : ℝ) < 0 at ha
    norm_num at ha

end TDA.Reeb.Examples
