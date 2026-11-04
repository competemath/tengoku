import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.FiniteMultiplicity
import Tengoku.Seed.Topology.Separation.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Countable semialgebraic fibers are finite. The line case is unconditional;
arbitrary finite dimension uses the explicitly unproved projection input. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

/--
@isnad1 id=finite.2h3v.s6.179de3df326d from=translated src=- shape=4f93ec79 vocab=3d028b55
-/
theorem IsSemialgebraic.finite_polynomial_preimage_of_countable {ι : Type*}
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) (g : ι → Polynomial ℝ)
    (hcount : ({t : ℝ | (fun i => (g i).eval t) ∈ S}).Countable) :
    ({t : ℝ | (fun i => (g i).eval t) ∈ S}).Finite := by
  obtain ⟨C, hC, hconv, hcover⟩ := hS.finite_convex_cover_polynomial_curve g
  rw [← hcover]
  apply hC.sUnion
  intro A hA
  have hsub : A ⊆ {t : ℝ | (fun i => (g i).eval t) ∈ S} := by
    rw [← hcover]
    exact subset_sUnion_of_mem hA
  exact (hcount.isTotallyDisconnected A hsub (hconv A hA).isPreconnected).finite

/--
@isnad1 id=finite.2h3v.s6.2a2a038e79da from=translated src=- shape=eaf1488a vocab=54f87d63
-/
theorem IsSemialgebraic.finite_line_fiber_of_countable {ι : Type*}
    {S : Set ((ι ⊕ Unit) → ℝ)} (hS : IsSemialgebraic (ι ⊕ Unit) S) (a : ι → ℝ)
    (hc : ({t : ℝ | Sum.elim a (fun _ => t) ∈ S}).Countable) :
    ({t : ℝ | Sum.elim a (fun _ => t) ∈ S}).Finite := by
  let g : (ι ⊕ Unit) → Polynomial ℝ :=
    Sum.elim (fun i => Polynomial.C (a i)) (fun _ => Polynomial.X)
  have he (t : ℝ) : (fun i => (g i).eval t) = Sum.elim a (fun _ => t) := by
    funext i
    cases i <;> simp [g]
  have hset : {t : ℝ | (fun i => (g i).eval t) ∈ S} =
      {t : ℝ | Sum.elim a (fun _ => t) ∈ S} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    rw [he t]
  have h := hS.finite_polynomial_preimage_of_countable g
  rw [hset] at h
  exact h hc

/-- Countable semialgebraic fibers in arbitrary finite dimension are finite,
conditional on the explicit coordinate-projection theorem.
@isnad1 id=finite.3h4v.s6.5fe2aa79249e from=translated src=- shape=deb2cc50 vocab=d80941bb
-/
theorem IsSemialgebraic.finite_fiber_of_countable_of_projection
    (hproj : SemialgebraicProjectionObligation) {ι κ : Type} [Finite ι] [Fintype κ]
    {S : Set ((ι ⊕ κ) → ℝ)} (hS : IsSemialgebraic (ι ⊕ κ) S) (a : ι → ℝ)
    (hc : ({x : κ → ℝ | Sum.elim a x ∈ S}).Countable) :
    ({x : κ → ℝ | Sum.elim a x ∈ S}).Finite := by
  classical
  let F : Set (κ → ℝ) := {x | Sum.elim a x ∈ S}
  let C (i : κ) : Set ℝ := (fun x : κ → ℝ => x i) '' F
  have hC (i : κ) : (C i).Finite := by
    have h := (semialgebraic_fiber_coordinate_image hproj hS i).finite_line_fiber_of_countable a
    change (C i).Countable → (C i).Finite at h
    exact h (hc.image _)
  let : ∀ i, Finite (C i) := hC
  let f (x : F) : ∀ i, C i := fun i => ⟨x.val i, ⟨x.val, x.property, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  let : Finite F := Finite.of_injective f hf
  exact Set.toFinite F

end
end DuistermaatVanDerKallen
