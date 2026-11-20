module

public import Tengoku.Leancondensed.LeanCondensed.Projects.FreeCondensed.SequentialModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

noncomputable section

open CategoryTheory LightCondensed LightCondSet LightCondAb Limits
open scoped BigOperators BoundedContinuousFunction

namespace LightProfinite

/-- The finite quotient projections of a light profinite space jointly separate points.-/
lemma eq_of_forall_proj_eq (S : LightProfinite.{0}) {x y : S}
    (h : ∀ n : ℕ, S.proj n x = S.proj n y) : x = y := by
  let X : LightProfinite.{0} := LightProfinite.of PUnit
  let fx : X ⟶ S := X.const x
  let fy : X ⟶ S := X.const y
  have hfg : fx = fy := by
    apply S.asLimit.hom_ext
    intro n
    ext p
    change S.proj n.unop (fx p) = S.proj n.unop (fy p)
    have hx : fx p = x := rfl
    have hy : fy p = y := rfl
    rw [hx, hy]
    exact h n.unop
  have hp := ConcreteCategory.congr_hom hfg PUnit.unit
  have hx : fx PUnit.unit = x := rfl
  have hy : fy PUnit.unit = y := rfl
  simpa [hx, hy] using hp

/-- Distinct points of a light profinite space are separated by some finite quotient projection.
@isnad1 id=ex.1h3v.s10.c2d620187847 from=translated src=- shape=d101a8f2 vocab=04debc31
-/
lemma exists_proj_ne (S : LightProfinite.{0}) {x y : S} (hxy : x ≠ y) :
    ∃ n : ℕ, S.proj n x ≠ S.proj n y := by
  by_contra h
  apply hxy
  apply eq_of_forall_proj_eq S
  intro n
  by_contra hn
  exact h ⟨n, hn⟩

/-- Distinct maps into a light profinite space are separated after postcomposition with some finite
quotient projection.
@isnad1 id=ex.1h4v.s7.bcf0a817a8ec from=translated src=- shape=8f7235e2 vocab=fa095a86
-/
lemma exists_proj_comp_ne_of_ne {U S : LightProfinite.{0}} {g h : U ⟶ S} (hgh : g ≠ h) :
    ∃ n : ℕ, g ≫ S.proj n ≠ h ≫ S.proj n := by
  obtain ⟨u, hu⟩ : ∃ u : U, g u ≠ h u := by
    by_contra H
    apply hgh
    ext u
    by_contra hu
    exact H ⟨u, hu⟩
  obtain ⟨n, hn⟩ := exists_proj_ne S hu
  refine ⟨n, ?_⟩
  intro H
  apply hn
  exact ConcreteCategory.congr_hom H u

/-- Separation by a finite quotient persists after passing to any later quotient.
@isnad1 id=ne.2h6v.s8.d6ab90619458 from=translated src=- shape=6c330a0f vocab=9bbf85da
-/
lemma proj_comp_ne_of_le {U S : LightProfinite.{0}} {g h : U ⟶ S} {k n : ℕ}
    (hkn : k ≤ n) (hne : g ≫ S.proj k ≠ h ≫ S.proj k) :
    g ≫ S.proj n ≠ h ≫ S.proj n := by
  intro H
  apply hne
  calc
    g ≫ S.proj k = g ≫ (S.proj n ≫ S.transitionMapLE hkn) := by
      rw [S.proj_comp_transitionMapLE hkn]
    _ = (g ≫ S.proj n) ≫ S.transitionMapLE hkn := by rw [Category.assoc]
    _ = (h ≫ S.proj n) ≫ S.transitionMapLE hkn := by rw [H]
    _ = h ≫ (S.proj n ≫ S.transitionMapLE hkn) := by rw [Category.assoc]
    _ = h ≫ S.proj k := by rw [S.proj_comp_transitionMapLE hkn]

/-- A finite set of maps into a light profinite space is separated by one finite quotient.
@isnad1 id=ex.0h3v.s7.c0474d0b63ab from=translated src=- shape=9267887e vocab=b72d4d81
-/
lemma exists_proj_injective_on_finset_hom (U S : LightProfinite.{0}) (t : Finset (U ⟶ S)) :
    ∃ n : ℕ, Set.InjOn (fun g : U ⟶ S => g ≫ S.proj n) (↑t : Set (U ⟶ S)) := by
  classical
  let sep : (U ⟶ S) × (U ⟶ S) → ℕ := fun p =>
    if h : p.1 ≠ p.2 then Classical.choose (exists_proj_comp_ne_of_ne h) else 0
  let N := (t.product t).sup sep
  refine ⟨N, ?_⟩
  intro g hg h hh H
  by_contra hne
  have hsep : g ≫ S.proj (sep (g, h)) ≠ h ≫ S.proj (sep (g, h)) := by
    dsimp [sep]
    rw [dite_eq_left hne]
    exact Classical.choose_spec (exists_proj_comp_ne_of_ne hne)
  have hle : sep (g, h) ≤ N := by
    dsimp [N]
    exact Finset.le_sup (s := t.product t) (f := sep) (b := (g, h)) (by
      exact (Finset.mem_product).mpr ⟨hg, hh⟩)
  exact proj_comp_ne_of_le hle hsep H

/-- A finite set of points in a light profinite space is separated by one finite quotient.
@isnad1 id=ex.0h2v.s9.6523066db2af from=translated src=- shape=86d545e8 vocab=6c9989e5
-/
lemma exists_proj_injective_on_finset_points (S : LightProfinite.{0}) (t : Finset S) :
    ∃ n : ℕ, Set.InjOn (fun s : S => S.proj n s) (↑t : Set S) := by
  classical
  let X : LightProfinite.{0} := LightProfinite.of PUnit
  let c : S → (X ⟶ S) := fun s => X.const s
  obtain ⟨n, hn⟩ := exists_proj_injective_on_finset_hom X S (t.image c)
  refine ⟨n, ?_⟩
  intro x hx y hy hxy
  have hcx : c x ∈ t.image c := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hcy : c y ∈ t.image c := Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hcproj : c x ≫ S.proj n = c y ≫ S.proj n := by
    ext p
    exact hxy
  have hc : c x = c y := hn hcx hcy hcproj
  have hpt := ConcreteCategory.congr_hom hc PUnit.unit
  have hx : c x PUnit.unit = x := rfl
  have hy : c y PUnit.unit = y := rfl
  simpa [hx, hy] using hpt

end LightProfinite
