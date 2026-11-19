import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedDensity.Definitions
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Elementary transport of arbitrary-target rooted universality. -/

namespace HadwigerLean.RootedDensity

universe u v
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]
  {G G' : SimpleGraph V} {H : SimpleGraph W} {X : Finset V}

/-- Adding host edges preserves rooted universality.
@isnad1 id=universa.2h6v.s5.27558a8b0615 from=translated src=- shape=11910603 vocab=55e150f6
-/
theorem UniversalAt.mono_graph
    (hGG' : G ≤ G') (h : UniversalAt G H X) :
    UniversalAt G' H X := by
  intro Y root hinj hrange
  obtain ⟨M⟩ := h Y root hinj hrange
  exact ⟨M.mono hGG'⟩

/-- At a full-size root set, universality gives the actual rooted `H`
model for any prescribed bijection from target labels to roots.
@isnad1 id=nonempty.3h6v.s5.dcbf6d771b24 from=translated src=- shape=1cb1c055 vocab=52fcbf5a
-/
theorem UniversalAt.full
    (h : UniversalAt G H X) (root : W → V)
    (hinj : Function.Injective root)
    (hrange : Set.range root = (X : Set V)) :
    Nonempty (RootedMinorModel H G root) := by
  classical
  let Y : Finset W := Finset.univ
  let r : ↥(Y : Set W) → V := fun w => root w.1
  have hrinj : Function.Injective r := by
    intro x y hxy
    apply Subtype.ext
    exact hinj hxy
  have hrrange : Set.range r = (X : Set V) := by
    calc
      Set.range r = Set.range root := by
        ext x
        simp [r, Y]
      _ = (X : Set V) := hrange
  obtain ⟨M⟩ := h Y r hrinj hrrange
  let f : W → ↥(Y : Set W) := fun w => ⟨w, by simp [Y]⟩
  refine ⟨{
    toMinorModel := {
      branch := fun w => M.branch (f w)
      connected := fun w => M.connected (f w)
      disjoint := ?_
      adjacent := ?_
    }
    root_mem := ?_
  }⟩
  · intro i j hij
    apply M.disjoint
    intro heq
    exact hij (congrArg Subtype.val heq)
  · intro i j hij
    exact M.adjacent hij
  · intro i
    exact M.root_mem (f i)

/-- No target edge can have both ends in an assignment to at most one
root, so these partial rooted models use singleton branches.
@isnad1 id=universa.1h5v.s5.e409b892767d from=translated src=- shape=858f008e vocab=e616740f
-/
theorem UniversalAt.of_card_le_one
    (G : SimpleGraph V) (H : SimpleGraph W) (X : Finset V)
    (hX : X.card ≤ 1) : UniversalAt G H X := by
  classical
  intro Y root hinj hrange
  let f : (H.induce (Y : Set W)) →g G := {
    toFun := root
    map_rel' := by
      intro i j hij
      exfalso
      have hij' : i ≠ j := (H.induce (Y : Set W)).ne_of_adj hij
      have hri : root i ∈ X := by
        have hi : root i ∈ Set.range root := ⟨i, rfl⟩
        simpa only [hrange, Finset.mem_coe] using hi
      have hrj : root j ∈ X := by
        have hj : root j ∈ Set.range root := ⟨j, rfl⟩
        simpa only [hrange, Finset.mem_coe] using hj
      have hsub : ({root i, root j} : Finset V) ⊆ X := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hri
        · exact hrj
      have htwo : ({root i, root j} : Finset V).card = 2 := by
        simp [hinj.ne hij']
      have hle := Finset.card_le_card hsub
      omega
  }
  simpa [f, Function.comp_def] using
    (show Nonempty (RootedMinorModel (H.induce (Y : Set W)) G (f ∘ id)) from
      ⟨(RootedMinorModel.refl (H.induce (Y : Set W))).map f hinj⟩)
end HadwigerLean.RootedDensity
