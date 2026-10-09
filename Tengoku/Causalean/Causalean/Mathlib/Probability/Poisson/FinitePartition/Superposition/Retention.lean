module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Poisson.FinitePartition.Superposition.Canonical
public import Tengoku

/-!
# Retained mark-ordered prefixes

This file gives the measurable retained-prefix map for a finite marked Poisson
sample and proves that, conditional on having enough points, forgetting the
marks of the smallest-mark prefix has the exact independent product law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]

/-- For [a fallback sample value](hyp:x₀), [a prefix length](hyp:n), and
[a finite sample of value--mark pairs](hyp:s), the [retained-observations vector](goal) consists of
the values attached to the first `n` sample points after ordering by their marks when the sample
contains at least `n` points, and otherwise consists entirely of the fallback value. -/
noncomputable def retainedObservations (x₀ : X) (n : ℕ)
    (s : FiniteSample (X × ℝ)) : Fin n → X :=
  if h : n ≤ s.count then
    fun k => ((orderByMarks s).points
      (Fin.cast (orderByMarks_count s).symm (Fin.castLE h k))).1
  else fun _ => x₀

/-- For [a fallback sample value](hyp:y₀), [a prefix length](hyp:n),
[a position in that prefix](hyp:k), and [a finite sample](hyp:s), the
[prefix point with fallback](goal) is the point there when the sample contains at least `n`
points, and is otherwise the fallback value. -/
noncomputable def prefixPointOr {Y : Type*} [MeasurableSpace Y]
    (y₀ : Y) (n : ℕ) (k : Fin n) (s : FiniteSample Y) : Y :=
  if h : n ≤ s.count then s.points (Fin.castLE h k) else y₀

/-- For [a fallback value](hyp:y₀), [a required sample size](hyp:n), and
[a position below that size](hyp:k),
[reading that point with a fallback for short samples is measurable](goal). -/
@[fun_prop]
lemma measurable_prefixPointOr {Y : Type*} [MeasurableSpace Y]
    (y₀ : Y) (n : ℕ) (k : Fin n) :
    Measurable (prefixPointOr y₀ n k : FiniteSample Y → Y) := by
  intro t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet
    ((fun x : Fin m → Y => if h : n ≤ m then x (Fin.castLE h k) else y₀) ⁻¹' t)
  by_cases h : n ≤ m
  · simp only [dite_eq_left h]
    exact ht.preimage (measurable_pi_apply (Fin.castLE h k))
  · simp only [dite_eq_right h]
    exact measurable_const ht

/-- For [a fallback observation](hyp:x₀) and [a prefix length](hyp:n),
[retaining the smallest-mark prefix and forgetting marks is measurable](goal). -/
@[fun_prop]
lemma measurable_retainedObservations (x₀ : X) (n : ℕ) :
    Measurable (retainedObservations x₀ n :
      FiniteSample (X × ℝ) → (Fin n → X)) := by
  apply measurable_pi_lambda
  intro k
  have h := (measurable_prefixPointOr (x₀, 0) n k).fst.comp
    measurable_orderByMarks
  convert h using 1
  funext c
  unfold retainedObservations prefixPointOr
  by_cases hn : n ≤ c.count <;> simp [hn]

private noncomputable def markOrderPermutation {m : ℕ} (r : Fin m → ℝ) :
    Fin m ≃ Fin m := by
  let s : FiniteSample (Unit × ℝ) := fixedSizeEmbed m (fun i => ((), r i))
  let f : Fin m → Fin m := fun k =>
    (ofLex (((markedKeys s).orderIsoOfFin (markedKeys_card s) k).1)).2
  refine Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨?_, rfl⟩)
  intro a b hab
  apply ((markedKeys s).orderIsoOfFin (markedKeys_card s)).injective
  apply Subtype.ext
  have ha := markedKey_decode s
    (((markedKeys s).orderIsoOfFin (markedKeys_card s) a).2)
  have hb := markedKey_decode s
    (((markedKeys s).orderIsoOfFin (markedKeys_card s) b).2)
  rw [← ha, ← hb]
  change toLex (r (f a), f a) = toLex (r (f b), f b)
  rw [hab]

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
