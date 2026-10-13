/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.SAT.Semantics
public import Tengoku

/-!
# Variable renaming and satisfiability transport

Renaming the variables of a CNF along an *injective* map preserves
satisfiability. This justifies re-indexing the Cook–Levin tableau variables
from the `Nat.pair`-based scheme (convenient for injectivity bookkeeping in
the correctness proof) to a flat mixed-radix scheme computable by a Turing
machine with unary multiplication and addition only — the form the reduction
machine actually emits (`docs/A5-ReductionEmitter.md`).

## Main definitions

- `SAT.Lit.mapVar`, `SAT.Clause.mapVar`, `SAT.CNF.mapVar` — variable renaming

## Main results

- `SAT.CNF.eval_mapVar_eq` — evaluation commutes with renaming, given
  pointwise-agreeing assignments on the occurring variables
- `SAT.CNF.satisfiable_mapVar_iff` — renaming along an injective map
  preserves satisfiability
-/

@[expose] public section

namespace Complexity

namespace SAT

-- ════════════════════════════════════════════════════════════════════════
-- Renaming
-- ════════════════════════════════════════════════════════════════════════

/-- Rename a literal's variable along `f`. -/
def Lit.mapVar (f : ℕ → ℕ) (ℓ : Lit) : Lit := ⟨ℓ.sign, f ℓ.var⟩

/-- Rename every variable of a clause along `f`. -/
def Clause.mapVar (f : ℕ → ℕ) (c : Clause) : Clause := c.map (Lit.mapVar f)

/-- Rename every variable of a CNF along `f`. -/
def CNF.mapVar (f : ℕ → ℕ) (φ : CNF) : CNF := φ.map (Clause.mapVar f)

/-- Renaming the empty CNF yields the empty CNF.
@isnad1 id=eq.0h1v.s3.99e95680a0a0 from=translated src=- shape=6378e097 vocab=b6384a8d
-/
@[simp] theorem CNF.mapVar_nil (f : ℕ → ℕ) : CNF.mapVar f [] = [] := rfl

/-- Renaming distributes over `cons`: rename the head clause and the tail CNF.
@isnad1 id=eq.0h3v.s4.e08cfa913564 from=translated src=- shape=74729b3b vocab=9664c8b3
-/
theorem CNF.mapVar_cons (f : ℕ → ℕ) (c : Clause) (φ : CNF) :
    CNF.mapVar f (c :: φ) = Clause.mapVar f c :: CNF.mapVar f φ := rfl

/-- Renaming distributes over CNF concatenation.
@isnad1 id=eq.0h3v.s5.39e49cab75fe from=translated src=- shape=352ca3f9 vocab=fd5466a6
-/
theorem CNF.mapVar_append (f : ℕ → ℕ) (φ ψ : CNF) :
    CNF.mapVar f (φ ++ ψ) = CNF.mapVar f φ ++ CNF.mapVar f ψ :=
  List.map_append ..

-- ════════════════════════════════════════════════════════════════════════
-- Assignment helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Out-of-range variables read `false`.
@isnad1 id=eq.1h2v.s4.9deea6f1931c from=translated src=- shape=af277a0f vocab=5710e61e
-/
theorem Assignment.get_of_length_le {α : Assignment} {v : ℕ} (h : α.length ≤ v) :
    α.get v = false := by
  rw [Assignment.get, List.getElem?_eq_none h]
  rfl

/-- Tabulate the first `M` values of a Boolean function as an assignment. -/
def Assignment.ofFn (M : ℕ) (g : ℕ → Bool) : Assignment := (List.range M).map g

/-- The tabulated assignment `Assignment.ofFn M g` has length `M`.
@isnad1 id=eq.0h2v.s3.93a93c74411e from=translated src=- shape=b1813261 vocab=f57cbcb1
-/
@[simp] theorem Assignment.ofFn_length (M : ℕ) (g : ℕ → Bool) :
    (Assignment.ofFn M g).length = M := by
  simp [Assignment.ofFn]

/-- Reading `Assignment.ofFn M g` at an in-range variable `v < M` returns `g v`.
@isnad1 id=eq.1h3v.s4.141fd9831312 from=translated src=- shape=61f62cfc vocab=03d820b1
-/
theorem Assignment.ofFn_get {M v : ℕ} (g : ℕ → Bool) (h : v < M) :
    (Assignment.ofFn M g).get v = g v := by
  simp [Assignment.ofFn, Assignment.get, List.getElem?_map, List.getElem?_range h]

-- ════════════════════════════════════════════════════════════════════════
-- Evaluation commutes with renaming
-- ════════════════════════════════════════════════════════════════════════

/-- Clause evaluation commutes with renaming, given assignments that agree
    pointwise (through `f`) on the clause's variables.
@isnad1 id=eq.1h4v.s5.cb1da4e2c196 from=translated src=- shape=51547562 vocab=a6c1b159
-/
theorem Clause.eval_mapVar_eq (α β : Assignment) (f : ℕ → ℕ) (c : Clause)
    (h : ∀ ℓ ∈ c, α.get (f ℓ.var) = β.get ℓ.var) :
    Clause.eval α (c.mapVar f) = Clause.eval β c := by
  induction c with
  | nil => rfl
  | cons ℓ ℓs ih =>
    have h1 : Lit.eval α (Lit.mapVar f ℓ) = Lit.eval β ℓ := by
      simp only [Lit.eval, Lit.mapVar]
      rw [h ℓ List.mem_cons_self]
    have h2 := ih (fun ℓ' hℓ' => h ℓ' (List.mem_cons_of_mem _ hℓ'))
    simp only [Clause.mapVar, List.map_cons, Clause.eval, List.any_cons] at h2 ⊢
    rw [h1, h2]

/-- CNF evaluation commutes with renaming, given assignments that agree
    pointwise (through `f`) on the formula's variables.
@isnad1 id=eq.1h4v.s5.ccf08f0d34f8 from=translated src=- shape=5d4cd5e9 vocab=4183a4d6
-/
theorem CNF.eval_mapVar_eq (α β : Assignment) (f : ℕ → ℕ) (φ : CNF)
    (h : ∀ c ∈ φ, ∀ ℓ ∈ c, α.get (f ℓ.var) = β.get ℓ.var) :
    CNF.eval α (CNF.mapVar f φ) = CNF.eval β φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have h1 := Clause.eval_mapVar_eq α β f c (h c List.mem_cons_self)
    have h2 := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    simp only [CNF.mapVar, List.map_cons, CNF.eval, List.all_cons] at h2 ⊢
    rw [h1, h2]

-- ════════════════════════════════════════════════════════════════════════
-- Satisfiability transport
-- ════════════════════════════════════════════════════════════════════════

/-- Renaming preserves satisfiability, forward direction: push the satisfying
    assignment along the (injective) renaming.
@isnad1 id=satisfia.2h2v.s4.3502cd750b50 from=translated src=- shape=baf7a006 vocab=6eb33888
-/
theorem CNF.Satisfiable.mapVar {f : ℕ → ℕ} (hf : Function.Injective f) {φ : CNF}
    (h : CNF.Satisfiable φ) : CNF.Satisfiable (CNF.mapVar f φ) := by
  classical
  obtain ⟨β, hβ⟩ := h
  set M := ((List.range β.length).map f).foldr max 0 + 1 with hM
  set α := Assignment.ofFn M
    (fun w => decide (∃ v, v < β.length ∧ f v = w ∧ β.get v = true)) with hα
  have hpoint : ∀ v, α.get (f v) = β.get v := by
    intro v
    by_cases hv : v < β.length
    · have hfv : f v < M := by
        rw [hM]
        exact Nat.lt_succ_of_le
          (List.le_max_of_le' 0 (List.mem_map_of_mem (List.mem_range.mpr hv)) le_rfl)
      rw [hα, Assignment.ofFn_get _ hfv]
      cases hβv : β.get v with
      | false =>
        apply decide_eq_false
        rintro ⟨v', _, hfeq, hget⟩
        cases hf hfeq
        rw [hβv] at hget
        exact Bool.noConfusion hget
      | true => exact decide_eq_true ⟨v, hv, rfl, hβv⟩
    · rw [Assignment.get_of_length_le (by omega : β.length ≤ v)]
      by_cases hfv : f v < M
      · rw [hα, Assignment.ofFn_get _ hfv]
        apply decide_eq_false
        rintro ⟨v', hv', hfeq, _⟩
        cases hf hfeq
        exact hv hv'
      · exact Assignment.get_of_length_le (by rw [hα, Assignment.ofFn_length]; omega)
  refine ⟨α, ?_⟩
  rw [CNF.eval_mapVar_eq α β f φ (fun c _ ℓ _ => hpoint ℓ.var)]
  exact hβ

/-- Renaming reflects satisfiability, backward direction: pull the satisfying
    assignment back through the renaming (no injectivity needed).
@isnad1 id=satisfia.1h2v.s3.6476bd8f36ad from=translated src=- shape=0207419e vocab=3a2ad9ac
-/
theorem CNF.Satisfiable.of_mapVar {f : ℕ → ℕ} {φ : CNF}
    (h : CNF.Satisfiable (CNF.mapVar f φ)) : CNF.Satisfiable φ := by
  obtain ⟨α, hα⟩ := h
  refine ⟨Assignment.ofFn (CNF.maxVar φ + 1) (fun v => α.get (f v)), ?_⟩
  rw [← CNF.eval_mapVar_eq α _ f φ ?_]
  · exact hα
  · intro c hc ℓ hℓ
    have hle : ℓ.var ≤ CNF.maxVar φ :=
      le_trans (Clause.var_le_maxVar hℓ) (CNF.clause_maxVar_le_maxVar hc)
    rw [Assignment.ofFn_get _ (by omega)]

/-- **Satisfiability is invariant under injective variable renaming.**
@isnad1 id=iff.1h2v.s4.d7032954fefc from=translated src=- shape=7378aa52 vocab=6eb33888
-/
theorem CNF.satisfiable_mapVar_iff {f : ℕ → ℕ} (hf : Function.Injective f) (φ : CNF) :
    CNF.Satisfiable (CNF.mapVar f φ) ↔ CNF.Satisfiable φ :=
  ⟨CNF.Satisfiable.of_mapVar, fun h => h.mapVar hf⟩

end SAT

end Complexity
