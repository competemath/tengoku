/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.SinCosBinarySplitting
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Lemmas
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv
import Tengoku.Seed.LinearAlgebra.Dimension.Finite
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs
import Tengoku.Seed.RingTheory.Derivation.DifferentialRing
import Tengoku.Seed.RingTheory.Finiteness.Subalgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.9.2: The bit-burst algorithm — holonomic functions

The binary-splitting algorithms for `arctan`, `exp`, `sin` rely on functional equations; the
bit-burst algorithm needs none and applies to *holonomic* (D-finite, differentiably finite)
functions: `f` satisfies a linear homogeneous differential equation with polynomial coefficients,
equivalently its Taylor coefficients satisfy a linear homogeneous recurrence with coefficients
polynomial in `k`.  Holonomic functions are closed under addition and multiplication but not
division (`exp`, `ln`, `sin`, `cos` are holonomic, `tan` is not).  The hypergeometric functions
(`u_{k+1}/u_k = R(k)` rational, §4.4) are the order-one case `u_{k+1} Q(k) − u_k P(k) = 0`;
holonomic
functions are much more general (Exercise 4.48): the ratio of consecutive hypergeometric terms
has size `O(log k)`, a holonomic one can be much larger.

What is formalized (all proven):

* The concrete notions on `ℝ`: `IsHolonomic f` (an ODE `∑_{i≤r} a_i(x) f^{(i)}(x) = 0` with
  polynomial `a_i`, not all zero) and `IsPRecursive u` (a recurrence `∑_{j≤s} c_j(k) u_{k+j} = 0`);
  the examples `isHolonomic_exp` (`f′ − f = 0`), `isHolonomic_sin`, `isHolonomic_cos`
  (`f″ + f = 0`) and `isHolonomic_log` (`x f″ + f′ = 0`, valid everywhere with Lean's `log`);
  `RationalRatio.isPRecursive`: a hypergeometric coefficient sequence (§4.4's `RationalRatio`,
  `a(k+δ) = P(k)/Q(k) · a(k)`) is P-recursive via `Q(k) a(k+δ) − P(k) a(k) = 0`.
* The algebraic theory, in a differential field extension `B/A` (Mathlib's `Differential`,
  `DifferentialAlgebra`; think `A = ℝ(x)`, `B` = formal Laurent series): `iterDeriv n b = b^{(n)}`,
  `derivSpan A b` = the `A`-span of all derivatives, `IsDFinite A b` = it is finitely generated.
  **Closure**: `IsDFinite.add`, `IsDFinite.mul` (the span of the derivatives of `ab` lies in the
  product of the two spans, which is finitely generated); and the equivalence with a linear ODE
  over `A`: `IsDFinite.exists_relation` (`∑_{i≤r} c_i b^{(i)} = 0`, some `c_i ≠ 0`) and
  `isDFinite_of_relation` (conversely; the top nonzero coefficient lets every derivative be
  expressed in the first `r`).

Not formalized: the equivalence between the ODE and the coefficient recurrence for power series
(index bookkeeping with `ascPochhammer`; both notions are defined), `tan` not holonomic, the
`O(log k)` size statement, Exercise 4.48.  The algorithm follows in the next chunk.
-/

namespace Azurite

namespace BZ

open Polynomial Finset

/-! ### Holonomic functions and P-recursive sequences on `ℝ` -/

/-- `f` is holonomic: `∑_{i≤r} a_i(x) f^{(i)}(x) = 0` with polynomials `a_i`, not all zero.-/
def IsHolonomic (f : ℝ → ℝ) : Prop :=
  ∃ (r : ℕ) (a : Fin (r + 1) → ℝ[X]), (∃ i, a i ≠ 0) ∧
    ∀ x : ℝ, ∑ i, (a i).eval x * iteratedDeriv i f x = 0

/-- `u` is P-recursive: `∑_{j≤s} c_j(k) u_{k+j} = 0` with polynomials `c_j`, not all zero.-/
def IsPRecursive (u : ℕ → ℝ) : Prop :=
  ∃ (s : ℕ) (c : Fin (s + 1) → ℝ[X]), (∃ j, c j ≠ 0) ∧
    ∀ k : ℕ, ∑ j, (c j).eval (k : ℝ) * u (k + j) = 0

/-- `exp′ − exp = 0`.
@isnad1 id=isholono.0h0v.s1.882c1755bec0 from=translated src=- shape=49959d42 vocab=4077d30a
-/
theorem isHolonomic_exp : IsHolonomic Real.exp := by
  refine ⟨1, ![C (-1), C 1], ⟨1, by simp⟩, fun x => ?_⟩
  simp [Fin.sum_univ_two, iteratedDeriv_one, Real.deriv_exp]

/-- `sin″ + sin = 0`.
@isnad1 id=isholono.0h0v.s1.0b6e13ad489f from=translated src=- shape=49959d42 vocab=dcec2d11
-/
theorem isHolonomic_sin : IsHolonomic Real.sin := by
  refine ⟨2, ![C 1, 0, C 1], ⟨0, by simp⟩, fun x => ?_⟩
  simp [Fin.sum_univ_three, iteratedDeriv_succ, Real.deriv_sin, Real.deriv_cos']

/-- `cos″ + cos = 0`.
@isnad1 id=isholono.0h0v.s1.eae15731590f from=translated src=- shape=49959d42 vocab=9fe25dcd
-/
theorem isHolonomic_cos : IsHolonomic Real.cos := by
  refine ⟨2, ![C 1, 0, C 1], ⟨0, by simp⟩, fun x => ?_⟩
  simp [Fin.sum_univ_three, iteratedDeriv_succ, Real.deriv_sin, Real.deriv_cos']

/-- `x log″ + log′ = 0` (everywhere, with Lean's `log` and `0⁻¹ = 0`).
@isnad1 id=isholono.0h0v.s1.3a2c02fc88f4 from=translated src=- shape=49959d42 vocab=f9b0f525
-/
theorem isHolonomic_log : IsHolonomic Real.log := by
  refine ⟨2, ![0, C 1, X], ⟨1, by simp⟩, fun x => ?_⟩
  have h2 : iteratedDeriv 2 Real.log = fun x => -(x ^ 2)⁻¹ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_log']
    exact deriv_inv'
  rw [Fin.sum_univ_three]
  simp [h2, Real.deriv_log, iteratedDeriv_one]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · field_simp
    ring

/-- A hypergeometric coefficient sequence (`a(k+δ) = P(k)/Q(k) · a(k)`, §4.4) is P-recursive:
`Q(k) a(k+δ) − P(k) a(k) = 0`.
@isnad1 id=isprecur.1h3v.s4.0b6ebf5e7df0 from=translated src=- shape=a7114757 vocab=dc975ec9
-/
theorem RationalRatio.isPRecursive {a : ℕ → ℝ} {δ : ℕ} (h : RationalRatio a δ) (hδ : 0 < δ) :
    IsPRecursive a := by
  obtain ⟨m, rfl⟩ : ∃ m, δ = m + 1 := ⟨δ - 1, by omega⟩
  refine ⟨m + 1, fun j => if j = 0 then -h.num else if j = Fin.last (m + 1) then h.den else 0,
    ⟨Fin.last (m + 1), ?_⟩, fun k => ?_⟩
  · have hne : (Fin.last (m + 1) : Fin (m + 2)) ≠ 0 := by
      rw [Ne, Fin.ext_iff]
      simp
    simp only [hne, ite_false, ite_true]
    intro hden
    have := h.den_ne_zero 0
    rw [hden] at this
    simp at this
  · have hsplit : ∀ j : Fin (m + 2),
        (if j = 0 then -h.num else if j = Fin.last (m + 1) then h.den else 0).eval (k : ℝ)
            * a (k + j)
          = (if j = 0 then -h.num.eval (k : ℝ) * a k else 0)
            + (if j = Fin.last (m + 1) then h.den.eval (k : ℝ) * a (k + (m + 1)) else 0) := by
      intro j
      have hne : (Fin.last (m + 1) : Fin (m + 2)) ≠ 0 := by
        rw [Ne, Fin.ext_iff]
        simp
      by_cases h0 : j = 0
      · subst h0
        simp [hne.symm]
      · by_cases hl : j = Fin.last (m + 1)
        · subst hl
          simp [hne]
        · simp [h0, hl]
    simp_rw [hsplit]
    rw [sum_add_distrib, sum_ite_eq', sum_ite_eq']
    simp only [mem_univ, ite_true]
    have hr := h.ratio k
    have hd := h.den_ne_zero k
    rw [hr]
    field_simp
    ring

/-! ### D-finite elements of a differential field extension -/

section DFinite

open scoped Differential

variable {A B : Type*} [Field A] [Field B] [Algebra A B] [Differential A] [Differential B]
  [DifferentialAlgebra A B]

/-- The `n`-th derivative `b^{(n)}`.-/
def iterDeriv (n : ℕ) (b : B) : B := (fun x : B => x′)^[n] b

/--
@isnad1 id=eq.0h2v.s4.115230103db9 from=translated src=- shape=67dc05e9 vocab=eae4ec72
-/
theorem iterDeriv_zero (b : B) : iterDeriv 0 b = b := rfl

/--
@isnad1 id=eq.0h3v.s7.902e4e815a7d from=translated src=- shape=e6abc41e vocab=9e1c1429
-/
theorem iterDeriv_succ (n : ℕ) (b : B) : iterDeriv (n + 1) b = (iterDeriv n b)′ :=
  Function.iterate_succ_apply' _ _ _

/--
@isnad1 id=eq.0h4v.s6.d7c41a871e3b from=translated src=- shape=ceac57f3 vocab=d63c19c9
-/
theorem iterDeriv_add (n : ℕ) (a b : B) : iterDeriv n (a + b) = iterDeriv n a + iterDeriv n b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterDeriv_succ, iterDeriv_succ, iterDeriv_succ, ih, map_add]

/--
@isnad1 id=eq.0h2v.s5.ab01d65b4a5b from=translated src=- shape=6dec58e9 vocab=eae4ec72
-/
theorem iterDeriv_zero_right (n : ℕ) : iterDeriv n (0 : B) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterDeriv_succ, ih, map_zero]

/-- `(c • x)′ = c′ • x + c • x′` for `c ∈ A`.
@isnad1 id=eq.0h4v.s8.e1c55b769d01 from=translated src=- shape=d0d0ad5d vocab=62b161a5
-/
theorem deriv_smul_coeff (c : A) (x : B) : (c • x)′ = c′ • x + c • x′ := by
  rw [Algebra.smul_def, Derivation.leibniz, deriv_algebraMap, smul_eq_mul, smul_eq_mul,
    Algebra.smul_def, Algebra.smul_def]
  ring

/-- A span whose generators have derivatives in the span is closed under `′`.
@isnad1 id=mem.2h4v.s9.255202271fa2 from=translated src=- shape=05cba13a vocab=2a969568
-/
theorem span_deriv_closed {s : Set B} (hs : ∀ x ∈ s, x′ ∈ Submodule.span A s) :
    ∀ x ∈ Submodule.span A s, x′ ∈ Submodule.span A s := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x hxmem hx =>
    rw [deriv_smul_coeff]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hxmem) (Submodule.smul_mem _ _ hx)

variable (A) in
/-- The `A`-span of `b, b′, b″, …`.-/
def derivSpan (b : B) : Submodule A B := Submodule.span A (Set.range fun n : ℕ => iterDeriv n b)

variable (A) in
/-- `b` is D-finite over `A`: its derivatives span a finitely generated `A`-module.-/
def IsDFinite (b : B) : Prop := (derivSpan A b).FG

omit [Differential A] [DifferentialAlgebra A B] in
/--
@isnad1 id=mem.0h4v.s7.78f326585203 from=translated src=- shape=2eea7fae vocab=e75edabc
-/
theorem iterDeriv_mem_derivSpan (b : B) (n : ℕ) : iterDeriv n b ∈ derivSpan A b :=
  Submodule.subset_span ⟨n, rfl⟩

/--
@isnad1 id=mem.1h4v.s8.c6235f5446fd from=translated src=- shape=4bb5d4c4 vocab=557a54b4
-/
theorem derivSpan_deriv_closed (b : B) : ∀ x ∈ derivSpan A b, x′ ∈ derivSpan A b :=
  span_deriv_closed (by
    rintro _ ⟨n, rfl⟩
    show (iterDeriv n b)′ ∈ _
    rw [← iterDeriv_succ]
    exact iterDeriv_mem_derivSpan b (n + 1))

omit [Differential A] [Differential B] [DifferentialAlgebra A B] in
/-- Over a field, a submodule of a finitely generated submodule is finitely generated.
@isnad1 id=fg.2h4v.s8.a87b7f703e4c from=translated src=- shape=8d9f33be vocab=4f713aec
-/
theorem fg_of_le_fg {U V : Submodule A B} (h : U ≤ V) (hV : V.FG) : U.FG := by
  rw [Submodule.fg_iff_finiteDimensional] at hV ⊢
  exact Submodule.finiteDimensional_of_le h

omit [Differential A] [DifferentialAlgebra A B] in
/-- Holonomic functions are closed under addition.
@isnad1 id=isdfinit.2h4v.s6.34c85ff54d63 from=translated src=- shape=11de8b3d vocab=9cc80e86
-/
theorem IsDFinite.add {a b : B} (ha : IsDFinite A a) (hb : IsDFinite A b) :
    IsDFinite A (a + b) := by
  refine fg_of_le_fg ?_ (ha.sup hb)
  rw [derivSpan, Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  show iterDeriv n (a + b) ∈ _
  rw [iterDeriv_add]
  exact Submodule.add_mem_sup (iterDeriv_mem_derivSpan a n) (iterDeriv_mem_derivSpan b n)

/-- Holonomic functions are closed under multiplication.
@isnad1 id=isdfinit.2h4v.s6.d8a14c398a49 from=translated src=- shape=0ca90076 vocab=b12b5e08
-/
theorem IsDFinite.mul {a b : B} (ha : IsDFinite A a) (hb : IsDFinite A b) :
    IsDFinite A (a * b) := by
  have hclosed : ∀ x ∈ derivSpan A a * derivSpan A b, x′ ∈ derivSpan A a * derivSpan A b := by
    intro x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro u hu v hv
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm v]
      exact Submodule.add_mem _ (Submodule.mul_mem_mul hu (derivSpan_deriv_closed b v hv))
        (Submodule.mul_mem_mul (derivSpan_deriv_closed a u hu) hv)
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hmem : ∀ n, iterDeriv n (a * b) ∈ derivSpan A a * derivSpan A b := by
    intro n
    induction n with
    | zero =>
      exact Submodule.mul_mem_mul (iterDeriv_mem_derivSpan a 0) (iterDeriv_mem_derivSpan b 0)
    | succ n ih =>
      rw [iterDeriv_succ]
      exact hclosed _ ih
  refine fg_of_le_fg (Submodule.span_le.mpr ?_) (Submodule.FG.mul ha hb)
  rintro _ ⟨n, rfl⟩
  exact hmem n

omit [Differential A] [DifferentialAlgebra A B] in
/-- A D-finite element satisfies a linear ODE over `A`: `∑_{i≤r} c_i b^{(i)} = 0`, not all
`c_i` zero (here `r = dim`).
@isnad1 id=ex.1h3v.s8.093cc051e36d from=translated src=- shape=cfe12300 vocab=0fd6c663
-/
theorem IsDFinite.exists_relation {b : B} (hb : IsDFinite A b) :
    ∃ (r : ℕ) (c : Fin (r + 1) → A), (∃ i, c i ≠ 0) ∧ ∑ i, c i • iterDeriv (i : ℕ) b = 0 := by
  have hfd : FiniteDimensional A (derivSpan A b) :=
    (Submodule.fg_iff_finiteDimensional _).mp hb
  set d := Module.finrank A (derivSpan A b) with hd
  let v : Fin (d + 1) → derivSpan A b := fun i => ⟨iterDeriv i b, iterDeriv_mem_derivSpan b i⟩
  have hnot : ¬ LinearIndependent A v := fun h => by
    have := h.fintype_card_le_finrank
    simp [← hd] at this
  obtain ⟨s, g, hsum, i, hi, hgi⟩ := not_linearIndependent_iff.mp hnot
  refine ⟨d, fun i => if i ∈ s then g i else 0, ⟨i, by simp [hi, hgi]⟩, ?_⟩
  calc ∑ i, (if i ∈ s then g i else 0) • iterDeriv (i : ℕ) b
      = ∑ i ∈ s, g i • iterDeriv (i : ℕ) b := by
        simp_rw [ite_smul, zero_smul]
        rw [sum_ite_mem, univ_inter]
    _ = ((∑ i ∈ s, g i • v i : derivSpan A b) : B) := by simp [v]
    _ = 0 := by rw [hsum]; rfl

/-- Conversely, a linear ODE over `A` makes `b` D-finite.
@isnad1 id=isdfinit.2h5v.s8.80cc86196ac3 from=translated src=- shape=03bca6d9 vocab=46c19df9
-/
theorem isDFinite_of_relation {b : B} :
    ∀ (r : ℕ) (c : Fin (r + 1) → A), (∃ i, c i ≠ 0) →
      ∑ i, c i • iterDeriv (i : ℕ) b = 0 → IsDFinite A b := by
  intro r
  induction r with
  | zero =>
    intro c ⟨i, hi⟩ hsum
    rw [Fin.sum_univ_one] at hsum
    have hc : c 0 ≠ 0 := by rwa [Subsingleton.elim (0 : Fin 1) i]
    have hb0 : b = 0 := by
      rw [Fin.val_zero, iterDeriv_zero] at hsum
      exact (smul_eq_zero.mp hsum).resolve_left hc
    subst hb0
    refine fg_of_le_fg ?_ Submodule.fg_bot
    rw [derivSpan, Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    simp [iterDeriv_zero_right]
  | succ r ih =>
    intro c hc hsum
    by_cases hlast : c (Fin.last (r + 1)) = 0
    · rw [Fin.sum_univ_castSucc, hlast, zero_smul, add_zero] at hsum
      obtain ⟨i, hi⟩ := hc
      have hi' : i ≠ Fin.last (r + 1) := fun h => hi (h ▸ hlast)
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi'
      exact ih (fun j => c (Fin.castSucc j)) ⟨j, hi⟩ (by simpa using hsum)
    · set W : Submodule A B :=
        Submodule.span A (Set.range fun i : Fin (r + 1) => iterDeriv (i : ℕ) b) with hW
      have hWfg : W.FG := Submodule.fg_span (Set.finite_range _)
      have htop : iterDeriv (r + 1) b ∈ W := by
        rw [Fin.sum_univ_castSucc] at hsum
        simp only [Fin.val_castSucc, Fin.val_last] at hsum
        have h2 := eq_neg_of_add_eq_zero_right hsum
        rw [← inv_smul_smul₀ hlast (iterDeriv (r + 1) b), h2]
        exact W.smul_mem _ (W.neg_mem (Submodule.sum_mem _ fun i _ =>
          W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)))
      have hclosed : ∀ x ∈ W, x′ ∈ W := span_deriv_closed (by
        rintro _ ⟨i, rfl⟩
        show (iterDeriv (i : ℕ) b)′ ∈ W
        rw [← iterDeriv_succ]
        rcases Nat.lt_or_ge ((i : ℕ) + 1) (r + 1) with h | h
        · exact Submodule.subset_span ⟨⟨(i : ℕ) + 1, h⟩, rfl⟩
        · have : (i : ℕ) + 1 = r + 1 := by have := i.isLt; omega
          rw [this]
          exact htop)
      have hmem : ∀ n, iterDeriv n b ∈ W := by
        intro n
        induction n with
        | zero => exact Submodule.subset_span ⟨0, by simp [iterDeriv_zero]⟩
        | succ n ih =>
          rw [iterDeriv_succ]
          exact hclosed _ ih
      refine fg_of_le_fg ?_ hWfg
      rw [derivSpan, Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      exact hmem n

end DFinite

end BZ

end Azurite
