import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredProduct
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms triple_pairwise_orthogonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Laws.orthogonal` (it only prints; the queue checks the axioms of every declaration). -/

namespace AlbertLean.Generic.SourceFrameLaws

noncomputable section

variable {K V : Type*} [Field K] [CharZero K]
variable [AddCommGroup V] [Module K V]

/-- Three idempotents summing to the unit are pairwise orthogonal.  No trace,
primitivity, Jordan identity, or associativity is used.
@isnad1 id=and.6h7v.s12.d0ccaf00d179 from=translated src=- shape=131f5ac4 vocab=acd1a2a2
-/
theorem triple_pairwise_orthogonal
    (μ : V →ₗ[K] V →ₗ[K] V) (one p q r : V)
    (hcomm : ∀ x y, μ x y = μ y x)
    (hunit : ∀ x, μ x one = x)
    (hpp : μ p p = p) (hqq : μ q q = q) (hrr : μ r r = r)
    (hsum : p + q + r = one) :
    μ p q = 0 ∧ μ p r = 0 ∧ μ q r = 0 := by
  have hp0 : μ p q + μ p r = 0 := by
    have hpAll := congrArg (fun x => μ p x) hsum
    simp only [map_add, hpp, hunit] at hpAll
    linear_combination (norm := module) hpAll
  have hq0 : μ p q + μ q r = 0 := by
    have hqAll := congrArg (fun x => μ q x) hsum
    simp only [map_add, hqq, hunit] at hqAll
    rw [hcomm q p] at hqAll
    linear_combination (norm := module) hqAll
  have hr0 : μ p r + μ q r = 0 := by
    have hrAll := congrArg (fun x => μ r x) hsum
    simp only [map_add, hrr, hunit] at hrAll
    rw [hcomm r p, hcomm r q] at hrAll
    linear_combination (norm := module) hrAll
  have hpq2 : (2 : K) • μ p q = 0 := by
    linear_combination (norm := module) hp0 + hq0 - hr0
  have hpq : μ p q = 0 :=
    (smul_eq_zero.mp hpq2).resolve_left (by norm_num)
  have hpr : μ p r = 0 := by
    linear_combination (norm := module) hp0 - hpq
  have hqr : μ q r = 0 := by
    linear_combination (norm := module) hq0 - hpq
  exact ⟨hpq, hpr, hqr⟩

open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredProduct

variable {F : Type*} [Field F] [CharZero F]

/-- The elementary source-frame laws, deliberately separate from primitivity.-/
structure Laws (P : Fin 3 → JCoord F) : Prop where
  idempotent : ∀ i, sourceProduct (P i) (P i) = P i
  trace_one : ∀ i, sourceTrace (P i) = 1
  sum_one : P 0 + P 1 + P 2 = sourceOne

/--
@isnad1 id=and.1h2v.s8.1adb00731cef from=translated src=- shape=c396c2ec vocab=d489b924
-/
theorem Laws.orthogonal_triple {P : Fin 3 → JCoord F} (hP : Laws P) :
    sourceProduct (P 0) (P 1) = 0 ∧
      sourceProduct (P 0) (P 2) = 0 ∧
        sourceProduct (P 1) (P 2) = 0 := by
  exact triple_pairwise_orthogonal sourceProductLinear sourceOne
    (P 0) (P 1) (P 2) sourceProduct_comm sourceProduct_one_right
    (hP.idempotent 0) (hP.idempotent 1) (hP.idempotent 2) hP.sum_one

/--
@isnad1 id=eq.2h4v.s6.a7c307173e57 from=translated src=- shape=90f18566 vocab=d489b924
-/
theorem Laws.orthogonal {P : Fin 3 → JCoord F} (hP : Laws P)
    {i j : Fin 3} (hij : i ≠ j) : sourceProduct (P i) (P j) = 0 := by
  obtain ⟨h01, h02, h12⟩ := hP.orthogonal_triple
  have h10 := (sourceProduct_comm (P 1) (P 0)).trans h01
  have h20 := (sourceProduct_comm (P 2) (P 0)).trans h02
  have h21 := (sourceProduct_comm (P 2) (P 1)).trans h12
  fin_cases i <;> fin_cases j <;> simp_all

end

end AlbertLean.Generic.SourceFrameLaws
