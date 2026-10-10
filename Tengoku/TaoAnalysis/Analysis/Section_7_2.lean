import Tengoku

/-!
# Analysis I, Section 7.2: Infinite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Formal series and their limits.
- Absolute convergence; basic series laws.

-/

namespace Chapter7

open BigOperators

/--
  Definition 7.2.1 (Formal infinite series). This is similar to Chapter 6 sequence, but is
  manipulated differently. As with Chapter 5, we will start series from 0 by default.
-/
@[ext]
structure Series where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Functions from ℕ to ℝ can be thought of as series. -/
instance Series.instCoe : Coe (ℕ → ℝ) Series where
  coe := fun a ↦ {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind
  }

@[simp]
theorem Series.eval_coe (a: ℕ → ℝ) (n: ℕ) : (a: Series).seq n = a n := by simp

abbrev Series.mk' {m:ℤ} (a: { n // n ≥ m } → ℝ) : Series where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by grind

theorem Series.eval_mk' {m:ℤ} (a : { n // n ≥ m } → ℝ) {n : ℤ} (h:n ≥ m) :
    (Series.mk' a).seq n = a ⟨ n, h ⟩ := by simp [h]

/-- Definition 7.2.2 (Convergence of series) -/
noncomputable abbrev Series.partial (s : Series) (N:ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n

abbrev Series.convergesTo (s : Series) (L:ℝ) : Prop := Filter.atTop.Tendsto (s.partial) (nhds L)

abbrev Series.converges (s : Series) : Prop := ∃ L, s.convergesTo L

abbrev Series.diverges (s : Series) : Prop := ¬s.converges

open Classical in
noncomputable abbrev Series.sum (s : Series) : ℝ := if h : s.converges then h.choose else 0

/-- Example 7.2.4 -/
noncomputable abbrev Series.example_7_2_4 := mk' (m := 1) (fun n ↦ (2:ℝ)^(-n:ℤ))

noncomputable abbrev Series.example_7_2_4' := mk' (m := 1) (fun n ↦ (2:ℝ)^(n:ℤ))

/-- Definition 7.2.8 (Absolute convergence) -/
abbrev Series.abs (s:Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)

abbrev Series.absConverges (s:Series) : Prop := s.abs.converges

abbrev Series.condConverges (s:Series) : Prop := s.converges ∧ ¬ s.absConverges

/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) / (n:ℤ)))

instance Series.inst_add : Add Series where
  add a b := {
    m := min a.m b.m
    seq n := a.seq n + b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.add_coe (a b: ℕ → ℝ) : (a:Series) + (b:Series) = (fun n ↦ a n + b n) := by
  ext n; rfl
  change (a:Series).seq n + (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]

instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq n := if n ≥ s.m then c * s.seq n else 0
    vanish := by grind
  }

theorem Series.smul_coe (a: ℕ → ℝ) (c: ℝ) : (c • a:Series) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- The corresponding API for subtraction was not in the textbook, but is useful in later sections, so is included here. -/
instance Series.inst_sub : Sub Series where
  sub a b := {
    m := min a.m b.m
    seq n := a.seq n - b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.sub_coe (a b: ℕ → ℝ) : (a:Series) - (b:Series) = (fun n ↦ a n - b n) := by
  ext n; rfl
  change (a:Series).seq n - (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]

abbrev Series.from (s:Series) (m₁:ℤ) : Series := mk' (m := max s.m m₁) (fun n ↦ s.seq (n:ℤ))

end Chapter7
