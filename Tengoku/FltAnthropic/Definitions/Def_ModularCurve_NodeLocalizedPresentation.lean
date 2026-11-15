import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_NodeLocalized

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace NodeLocalized

open MvPolynomial

section Presentation

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)

def modularEvalAt : MvPolynomial (Fin 2) A →+* modularLocalizedAtPoint N A red a b :=
  (modularEval N A).codRestrict _ (modularEval_mem_modularLocalizedAtPoint N A red a b)

/--
@isnad1 id=eq.0h8v.s11.3517e2a9e26c from=translated src=- shape=02b2e69f vocab=47563053
-/
@[simp] theorem coe_modularEvalAt (p : MvPolynomial (Fin 2) A) :
    (modularEvalAt N A red a b p : LaurentSeries L) = modularEval N A p := rfl

abbrev evalRange : Subring (LaurentSeries L) := (modularEval N A).range

/--
@isnad1 id=le.0h7v.s8.6e0842344a86 from=translated src=- shape=6e864319 vocab=f52cf05a
-/
theorem evalRange_le : evalRange N A ≤ modularLocalizedAtPoint N A red a b := by
  rintro _ ⟨p, rfl⟩
  exact modularEval_mem_modularLocalizedAtPoint N A red a b p

instance algebraEvalRange : Algebra (evalRange N A) (modularLocalizedAtPoint N A red a b) :=
  (Subring.inclusion (evalRange_le N A red a b)).toAlgebra

/--
@isnad1 id=eq.0h8v.s12.fb51a26dd3c4 from=translated src=- shape=f8b45ee7 vocab=5c6de1ce
-/
theorem algebraMap_evalRange_coe (y : evalRange N A) :
    ((algebraMap (evalRange N A) (modularLocalizedAtPoint N A red a b) y : modularLocalizedAtPoint N A red a b) :
      LaurentSeries L) = y := rfl

/--
@isnad1 id=eq.0h8v.s13.05054d0ca627 from=translated src=- shape=6f4cb373 vocab=53335732
-/
theorem algebraMap_evalRange_rangeRestrict (p : MvPolynomial (Fin 2) A) :
    algebraMap (evalRange N A) (modularLocalizedAtPoint N A red a b) ((modularEval N A).rangeRestrict p)
      = modularEvalAt N A red a b p := rfl

def nodeDenominators : Submonoid (evalRange N A) where
  carrier := {y | ∃ s : MvPolynomial (Fin 2) A, pointEval A red a b s ≠ 0 ∧ (modularEval N A).rangeRestrict s = y}
  one_mem' := ⟨1, by rw [map_one]; exact one_ne_zero, by rw [map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, by rw [map_mul]⟩

/--
@isnad1 id=mem.1h8v.s12.0cae780534d6 from=translated src=- shape=a62fc20f vocab=c08045bf
-/
theorem rangeRestrict_mem_nodeDenominators {s : MvPolynomial (Fin 2) A} (hs : pointEval A red a b s ≠ 0) :
    (modularEval N A).rangeRestrict s ∈ nodeDenominators N A red a b :=
  ⟨s, hs, rfl⟩

/--
@isnad1 id=iff.0h8v.s12.1b78fcbf68bb from=translated src=- shape=f1d37844 vocab=f4167c42
-/
theorem mem_nodeDenominators_iff (y : evalRange N A) :
    y ∈ nodeDenominators N A red a b ↔ ∃ s : MvPolynomial (Fin 2) A, pointEval A red a b s ≠ 0 ∧ modularEval N A s = y := by
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, Subtype.ext h⟩

section KerLE

variable [hker : Fact (RingHom.ker (modularEval N A) ≤ RingHom.ker (pointEval A red a b))]

/--
@isnad1 id=ne.1h8v.s12.c15f30003efa from=translated src=- shape=836032eb vocab=c25da2c2
-/
theorem modularEval_ne_zero_of_pointEval_ne_zero {s : MvPolynomial (Fin 2) A} (hs : pointEval A red a b s ≠ 0) :
    modularEval N A s ≠ 0 := fun h => hs (hker.out ((RingHom.mem_ker).mpr h))

/--
@isnad1 id=isunit.1h8v.s12.ec4f039f1b37 from=translated src=- shape=1f6907e9 vocab=621df47e
-/
theorem isUnit_modularEvalAt {s : MvPolynomial (Fin 2) A} (hs : pointEval A red a b s ≠ 0) :
    IsUnit (modularEvalAt N A red a b s) := by
  have hs0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hs
  refine isUnit_iff_exists_inv.mpr ⟨⟨(modularEval N A s)⁻¹, 1, s, hs, ?_⟩, Subtype.ext ?_⟩
  · rw [map_one, inv_mul_cancel₀ hs0]
  · exact mul_inv_cancel₀ hs0

/--
@isnad1 id=islocali.0h7v.s11.0333bc91bf93 from=translated src=- shape=9b26b3b1 vocab=9d3aa6e2
-/
instance isLocalization_nodeDenominators :
    IsLocalization (nodeDenominators N A red a b) (modularLocalizedAtPoint N A red a b) where
  map_units := by
    rintro ⟨_, s, hs, rfl⟩
    rw [algebraMap_evalRange_rangeRestrict]
    exact isUnit_modularEvalAt N A red a b hs
  surj := fun z => by
    obtain ⟨r, s, hs, h⟩ := z.2
    exact ⟨⟨(modularEval N A).rangeRestrict r, ⟨(modularEval N A).rangeRestrict s,
      rangeRestrict_mem_nodeDenominators N A red a b hs⟩⟩, Subtype.ext h⟩
  exists_of_eq := fun {x y} h => ⟨1, by
    simp only [OneMemClass.coe_one, one_mul]
    exact Subtype.ext (congrArg (fun w : modularLocalizedAtPoint N A red a b => (w : LaurentSeries L)) h)⟩

/--
@isnad1 id=islocalr.0h7v.s11.f972d27d7b93 from=translated src=- shape=1edecdfa vocab=25e1cdfd
-/
instance isLocalRing_modularLocalizedAtPoint : IsLocalRing (modularLocalizedAtPoint N A red a b) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨r, s, hs, h⟩ := z.2
  have hs0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hs
  have hz : (z : LaurentSeries L) = modularEval N A r * (modularEval N A s)⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  by_cases hr : pointEval A red a b r = 0
  · right
    have hsr : pointEval A red a b (s - r) ≠ 0 := by rw [map_sub, hr, sub_zero]; exact hs
    have hsr0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hsr
    have hsr0' : modularEval N A s - modularEval N A r ≠ 0 := by rwa [map_sub] at hsr0
    refine isUnit_iff_exists_inv.mpr ⟨⟨modularEval N A s * (modularEval N A (s - r))⁻¹, s, s - r, hsr, ?_⟩, Subtype.ext ?_⟩
    · rw [mul_assoc, inv_mul_cancel₀ hsr0, mul_one]
    · show (1 - (z : LaurentSeries L)) * (modularEval N A s * (modularEval N A (s - r))⁻¹) = 1
      rw [hz, map_sub]
      field_simp
  · left
    have hr0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hr
    refine isUnit_iff_exists_inv.mpr ⟨⟨modularEval N A s * (modularEval N A r)⁻¹, s, r, hr, ?_⟩, Subtype.ext ?_⟩
    · rw [mul_assoc, inv_mul_cancel₀ hr0, mul_one]
    · show (z : LaurentSeries L) * (modularEval N A s * (modularEval N A r)⁻¹) = 1
      rw [hz]
      field_simp

end KerLE

/--
@isnad1 id=mem.0h3v.s10.1ac339af9d3b from=translated src=- shape=6d6b7a9e vocab=de484d1c
-/
theorem sub_C_eval_mem_span {R : Type*} [CommRing R] (v : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    p - C (eval v p) ∈ Ideal.span {(X 0 - C (v 0) : MvPolynomial (Fin 2) R), X 1 - C (v 1)} := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [eval_C, sub_self]; exact zero_mem _
  | add p r hp hr =>
    have : p + r - C (eval v (p + r)) = (p - C (eval v p)) + (r - C (eval v r)) := by rw [map_add, map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p i hp =>
    have : p * X i - C (eval v (p * X i)) = (p - C (eval v p)) * X i + C (eval v p) * (X i - C (v i)) := by
      rw [map_mul, eval_X, map_mul]; ring
    rw [this]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

/--
@isnad1 id=eq.3h9v.s12.55aa49a83fab from=translated src=- shape=7dd23235 vocab=560fb976
-/
theorem ker_pointEval_eq_span (x y : A) (hx : red x = a) (hy : red y = b) (ϖ : A)
    (hϖ : ∀ c : A, red c = 0 ↔ ∃ d, c = ϖ * d) :
    RingHom.ker (pointEval A red a b) = Ideal.span {C ϖ, X 0 - C x, X 1 - C y} := by
  have hpe : ∀ p : MvPolynomial (Fin 2) A, pointEval A red a b p = red (eval ![x, y] p) := by
    intro p
    have hfun : (![a, b] : Fin 2 → k) = red ∘ ![x, y] := by
      funext i; fin_cases i <;> simp [hx, hy]
    rw [pointEval, coe_eval₂Hom, hfun, eval, coe_eval₂Hom, eval₂_comp_left, RingHom.comp_id]
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker, hpe] at hp
    obtain ⟨d, hd⟩ := (hϖ _).mp hp
    have : p = (p - C (eval ![x, y] p)) + C ϖ * C d := by rw [hd, map_mul]; ring
    rw [this]
    refine add_mem ?_ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    exact Ideal.span_mono (Set.subset_insert _ _) (sub_C_eval_mem_span ![x, y] p)
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, RingHom.mem_ker, hpe]
    · rw [eval_C]; exact (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
    · simp
    · simp

end Presentation

end NodeLocalized
end ModularCurve

end
