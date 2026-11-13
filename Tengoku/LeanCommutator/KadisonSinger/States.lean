import Tengoku.Seed.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Tengoku.Seed.Analysis.CStarAlgebra.Projection
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped ComplexOrder

/-!
# State extensions from projection paving

This file proves the functional-analytic implication from arbitrarily fine projection paving to
unique extension of pure states across an expected commutative C*-subalgebra. States are normalized
positive linear functionals; purity is the ordinary extreme-point condition, not a substitute paving
condition. The concrete inclusion, positive expectation, and paving theorem remain explicit inputs
of `State.existsUnique_extension_of_paving`.
-/

noncomputable section

namespace KadisonSinger

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A state is a positive complex linear functional taking the unit to one.-/
def State := {φ : A →ₚ[ℂ] ℂ // φ 1 = 1}

namespace State

variable {A}

/-- Purity is the usual extreme-point condition in the convex set of states.-/
def IsPure (φ : State A) : Prop :=
  ∀ (ψ χ : State A) (t : ℝ), 0 < t → t < 1 →
    (∀ a, φ.val a = t • ψ.val a + (1 - t) • χ.val a) → ψ = φ

omit [StarOrderedRing A] in
/--
@isnad1 id=eq.0h2v.s8.2e5b9244f82a from=translated src=- shape=859b3868 vocab=31feaa06
-/
lemma apply_one (φ : State A) : φ.val 1 = 1 := φ.property

/--
@isnad1 id=eq.2h4v.s9.e47748f439ae from=translated src=- shape=a9df7738 vocab=bd716d36
-/
lemma apply_mul_eq_zero_of_projection (φ : State A) {p : A} (hp : IsStarProjection p)
    (hφp : φ.val p = 0) (a : A) : φ.val (p * a) = 0 := by
  have hn : ‖φ.val.toPreGNS p‖ = 0 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, hφp]
  have h := norm_inner_le_norm (𝕜 := ℂ) (φ.val.toPreGNS p) (φ.val.toPreGNS a)
  rw [hn, zero_mul] at h
  have hz := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  simpa [PositiveLinearMap.preGNS_inner_def, hp.isSelfAdjoint.star_eq] using hz

/--
@isnad1 id=eq.2h4v.s9.0b51ab94c9b6 from=translated src=- shape=24e23dff vocab=bd716d36
-/
lemma apply_mul_eq_zero_of_projection_right (φ : State A) {p : A}
    (hp : IsStarProjection p) (hφp : φ.val p = 0) (a : A) : φ.val (a * p) = 0 := by
  have hn : ‖φ.val.toPreGNS p‖ = 0 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, hφp]
  have h := norm_inner_le_norm (𝕜 := ℂ) (φ.val.toPreGNS (star a)) (φ.val.toPreGNS p)
  rw [hn, mul_zero] at h
  have hz := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  simpa [PositiveLinearMap.preGNS_inner_def] using hz

/--
@isnad1 id=eq.2h4v.s9.bd732bf7b237 from=translated src=- shape=9c3562ce vocab=bd716d36
-/
lemma apply_eq_compression (φ : State A) {p : A} (hp : IsStarProjection p)
    (hφp : φ.val p = 1) (a : A) : φ.val a = φ.val (p * a * p) := by
  have hq : φ.val (1 - p) = 0 := by simp [map_sub, φ.apply_one, hφp]
  have hl := φ.apply_mul_eq_zero_of_projection hp.one_sub hq a
  have hr := φ.apply_mul_eq_zero_of_projection_right hp.one_sub hq (p * a)
  rw [sub_mul, one_mul, map_sub, sub_eq_zero] at hl
  rw [mul_sub, mul_one, map_sub, sub_eq_zero] at hr
  exact hl.trans hr

/-- The state obtained by conditioning on a projection of nonzero state mass.-/
def corner (φ : State A) {p : A} (hp : IsStarProjection p)
    (ht : 0 < (φ.val p).re) : State A :=
  ⟨PositiveLinearMap.mk₀
    { toFun := fun a ↦ ((φ.val p).re)⁻¹ • φ.val (p * a * p)
      map_add' := by intro a b; simp [mul_add, add_mul]
      map_smul' := by intro c a; simp [mul_left_comm] }
    (by
      intro a ha
      exact smul_nonneg (inv_nonneg.mpr ht.le)
        (φ.val.map_nonneg (hp.isSelfAdjoint.conjugate_nonneg ha))), by
    change ((φ.val p).re)⁻¹ • φ.val (p * 1 * p) = 1
    rw [mul_one, hp.isIdempotentElem.eq]
    have hi := (Complex.nonneg_iff.mp (φ.val.map_nonneg hp.nonneg)).2
    apply Complex.ext <;> simp [hi.symm, ht.ne']⟩

/--
@isnad1 id=eq.2h4v.s10.cbedfe963aa5 from=translated src=- shape=f8dc0f3a vocab=6f29f944
-/
lemma corner_apply (φ : State A) {p : A} (hp : IsStarProjection p)
    (ht : 0 < (φ.val p).re) (a : A) :
    (φ.corner hp ht).val a = ((φ.val p).re)⁻¹ • φ.val (p * a * p) := rfl

/-- A pure state takes every central projection to either zero or one.
@isnad1 id=or.3h3v.s9.33e45fcd59b1 from=translated src=- shape=e11a9679 vocab=f6289dfb
-/
theorem apply_central_projection_eq_zero_or_one (φ : State A) (hφ : φ.IsPure)
    {p : A} (hp : IsStarProjection p) (hcentral : ∀ a, Commute p a) :
    φ.val p = 0 ∨ φ.val p = 1 := by
  have hnonneg := Complex.nonneg_iff.mp (φ.val.map_nonneg hp.nonneg)
  have hle := OrderHomClass.mono φ.val hp.le_one
  rw [φ.apply_one] at hle
  by_cases hzero : φ.val p = 0
  · exact Or.inl hzero
  by_cases hone : φ.val p = 1
  · exact Or.inr hone
  have ht : 0 < (φ.val p).re := by
    refine lt_of_le_of_ne hnonneg.1 ?_
    intro h
    apply hzero
    exact Complex.ext h.symm hnonneg.2.symm
  have ht' : (φ.val p).re < 1 := by
    refine lt_of_le_of_ne hle.1 ?_
    intro h
    apply hone
    exact Complex.ext h hnonneg.2.symm
  have hqt : 0 < (φ.val (1 - p)).re := by
    simp only [map_sub, φ.apply_one, Complex.sub_re, Complex.one_re]
    linarith
  have hdecomp (a : A) :
      p * a * p + (1 - p) * a * (1 - p) = a := by
    have hpa : p * a * p = p * a := by
      rw [(hcentral a).eq, mul_assoc, hp.isIdempotentElem.eq]
    have hqa : (1 - p) * a * (1 - p) = (1 - p) * a := by
      have hqcentral : Commute (1 - p) a := (Commute.one_left a).sub_left (hcentral a)
      rw [hqcentral.eq, mul_assoc, hp.one_sub.isIdempotentElem.eq]
    rw [hpa, hqa, ← add_mul, add_sub_cancel, one_mul]
  have heq : φ.corner hp ht = φ := by
    apply hφ (φ.corner hp ht) (φ.corner hp.one_sub hqt) (φ.val p).re ht ht'
    intro a
    have hqre : (φ.val (1 - p)).re = 1 - (φ.val p).re := by
      simp [map_sub, φ.apply_one]
    simp only [corner_apply, hqre]
    have hqn : (1 : ℂ) - ((φ.val p).re : ℂ) ≠ 0 := by
      exact_mod_cast (sub_pos.mpr ht').ne'
    simp [ht.ne', hqn, ← map_add, hdecomp]
  have hcorner : (φ.corner hp ht).val p = 1 := by
    rw [corner_apply]
    simp only [hp.isIdempotentElem.eq]
    have h := (φ.corner hp ht).apply_one
    rw [corner_apply, mul_one, hp.isIdempotentElem.eq] at h
    exact h
  rw [heq] at hcorner
  exact Or.inr hcorner

end State

variable {A}
variable {D : Type*} [CommCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- Projection paving relative to an inclusion and a diagonal expectation. This is an explicit
hypothesis for the state-extension bridge, not a definition of the Kadison--Singer conjecture.-/
def ProjectionPaving (ι : D →⋆ₐ[ℂ] A) (E : A →ₚ[ℂ] D) : Prop :=
  ∀ a : A, E a = 0 → ∀ ε : ℝ, 0 < ε →
    ∃ (r : ℕ) (p : Fin r → D), (∀ i, IsStarProjection (p i)) ∧
      (∑ i, p i) = 1 ∧ ∀ i, ‖ι (p i) * a * ι (p i)‖ ≤ ε

/-- The self-adjoint version of projection paving.-/
def SelfAdjointProjectionPaving (ι : D →⋆ₐ[ℂ] A) (E : A →ₚ[ℂ] D) : Prop :=
  ∀ a : A, IsSelfAdjoint a → E a = 0 → ∀ ε : ℝ, 0 < ε →
    ∃ (r : ℕ) (p : Fin r → D), (∀ i, IsStarProjection (p i)) ∧
      (∑ i, p i) = 1 ∧ ∀ i, ‖ι (p i) * a * ι (p i)‖ ≤ ε

namespace State

/-- Composition with a positive unital expectation gives a state extension.-/
def throughExpectation (φ : State D) (E : A →ₚ[ℂ] D) (hE : E 1 = 1) : State A :=
  ⟨{ toLinearMap := φ.val.toLinearMap.comp E.toLinearMap
     monotone' := fun _ _ h ↦ OrderHomClass.mono φ.val (OrderHomClass.mono E h) }, by
    change φ.val (E 1) = 1
    rw [hE, φ.apply_one]⟩

omit [StarOrderedRing A] [StarOrderedRing D] in
/--
@isnad1 id=eq.1h5v.s9.7bb8fe85209b from=translated src=- shape=6cc422e0 vocab=cfa39de8
-/
lemma throughExpectation_apply (φ : State D) (E : A →ₚ[ℂ] D) (hE : E 1 = 1) (a : A) :
    (φ.throughExpectation E hE).val a = φ.val (E a) := rfl

end State
end KadisonSinger
