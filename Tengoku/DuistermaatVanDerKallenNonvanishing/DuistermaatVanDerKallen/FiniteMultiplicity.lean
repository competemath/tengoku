import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicLineFamilies
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.RadiusProjection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform bounds for finite fibers in arbitrary finite dimension, conditional
only on the explicit coordinate-projection obligation. Projecting each finite
fiber to its coordinate lines reduces the count to the proved one-dimensional
bounds. The parameter and target value are both retained for families of maps.
No integration inequality or higher-dimensional component theorem is asserted. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

/-- Incidence description of a fiber coordinate projection, retaining parameters.
@isnad1 id=issemial.2h4v.s6.fa8fbd24a405 from=translated src=- shape=1e9e0eeb vocab=9b5c06fa
-/
theorem semialgebraic_fiber_coordinate_image
    (hproj : SemialgebraicProjectionObligation) {ι κ : Type} [Finite ι] [Finite κ]
    {S : Set ((ι ⊕ κ) → ℝ)} (hS : IsSemialgebraic (ι ⊕ κ) S) (i : κ) :
    IsSemialgebraic (ι ⊕ Unit) {q | ∃ x : κ → ℝ,
      Sum.elim (fun j => q (.inl j)) x ∈ S ∧ x i = q (.inr ())} := by
  let g : (ι ⊕ κ) → MvPolynomial ((ι ⊕ Unit) ⊕ κ) ℝ :=
    Sum.elim (fun k => MvPolynomial.X (.inl (.inl k))) (fun k => MvPolynomial.X (.inr k))
  let T : Set (((ι ⊕ Unit) ⊕ κ) → ℝ) := {q |
    Sum.elim (fun k => q (.inl (.inl k))) (fun k => q (.inr k)) ∈ S ∧
      q (.inr i) = q (.inl (.inr ()))}
  have he (q : ((ι ⊕ Unit) ⊕ κ) → ℝ) : (fun j => MvPolynomial.eval q (g j)) =
      Sum.elim (fun k => q (.inl (.inl k))) (fun k => q (.inr k)) := by
    funext j
    cases j <;> simp [g]
  have hT : IsSemialgebraic ((ι ⊕ Unit) ⊕ κ) T := by
    have hU := hS.polynomial_preimage g
    have hV := IsSemialgebraic.eq (ι := ((ι ⊕ Unit) ⊕ κ))
      (MvPolynomial.X (.inr i)) (MvPolynomial.X (.inl (.inr ())))
    convert hU.inter hV using 1
    ext q
    simp only [T, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      MvPolynomial.eval_X, he]
  convert hproj (ι ⊕ Unit) κ T hT using 1
  ext q
  simp only [Set.mem_ofPred_eq, T, Sum.elim_inl, Sum.elim_inr]

/--
@isnad1 id=le.1h2v.s5.2345ff116401 from=translated src=- shape=20ec5492 vocab=365188f9
-/
theorem ncard_le_product_coordinate_images {κ : Type*} [Fintype κ]
    (S : Set (κ → ℝ)) (hS : S.Finite) :
    S.ncard ≤ ∏ i, ((fun x : κ → ℝ => x i) '' S).ncard := by
  classical
  let C (i : κ) := (fun x : κ → ℝ => x i) '' S
  let : ∀ i, Fintype (C i) := fun i => (hS.image _).fintype
  let f (x : S) : ∀ i, C i := fun i => ⟨x.val i, ⟨x.val, x.property, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_pi, Nat.card_coe_set_eq] using h

end
end DuistermaatVanDerKallen
