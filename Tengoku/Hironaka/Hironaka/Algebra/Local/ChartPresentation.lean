/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.Local.ChartRing
public import Tengoku.Seed.RingTheory.Regular.RegularSequence
import Tengoku.Hironaka.Hironaka.Algebra.Local.BirationalTransform
import Tengoku.Hironaka.Hironaka.Algebra.Local.Regular
import Tengoku.Hironaka.Hironaka.Algebra.Local.RegularSystem
import Tengoku.Hironaka.Hironaka.Scheme.BlowUp.LinearType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The kernel of the chart presentation

Kollár asserts that `y₁ = x₁/x_r, …, y_{r-1} = x_{r-1}/x_r, y_r = x_r, …` "give local coordinates
on a chart" [Kol07, Definition 60]; Hauser states that for a regular sequence `g₁, …, g_k` the
only relations among the `gⱼ/gᵢ` over `R` are the trivial ones, so that
`R[g₁/gᵢ, …, g_k/gᵢ] ≅ R[t₁, …, t_k]/(gᵢ tⱼ − gⱼ)` [Hau14, Theorem 4.20 (b)].
`Hironaka/Algebra/Local/Chart.lean` gives the presentation `R[Y₀, …, Y_{r-1}] → R' = R[xᵢ/x_r]`,
`Yᵢ ↦ yᵢ`, and its surjectivity; this file proves that its kernel is exactly the ideal
`⟨x_r Yᵢ − xᵢ⟩` of the obvious relations:

* the list `[x_r, x₀, …, x_{r-1}]` is weakly regular on `R` — it is a prefix of a permutation of
  the regular system of parameters, which is a regular sequence
  (`Hironaka/Algebra/Local/RegularSystem.lean`);
* the assembly: `⟨x_r Yᵢ − xᵢ⟩ ⊆ ker` because `x_r yᵢ = xᵢ` in `R'`; for `p` in the kernel, the
  elimination lemma of `Hironaka/Scheme/BlowUp/LinearType.lean` gives `x_rᵈ p ≡ c (mod ⟨x_r Yᵢ −
  xᵢ⟩)` with `c ∈ R`, so `c = 0` in `R[1/x_r]`, hence `x_rᵏ c = 0` in `R` and `c = 0` (`x_r` is a
  nonzerodivisor); then `x_rᵈ p ∈ ⟨x_r Yᵢ − xᵢ⟩` and the torsion-freeness of the ideal of
  relations modulo `x_r` (`Hironaka/Scheme/BlowUp/LinearType.lean`, for a weakly regular sequence)
  gives `p ∈ ⟨x_r Yᵢ − xᵢ⟩`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPolynomial RingTheory.Sequence AlgebraicGeometry.affineBlowUpAlgebra

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ} (x : Fin n → R) (r : Fin n)

/-- The list `[x_r, x₀, …, x_{r-1}]`: the denominator first, then the divided coordinates.-/
noncomputable abbrev chartList : List R :=
  x r :: List.ofFn fun i : Fin r => x (Fin.castLE r.2.le i)

/-- The remaining parameters `x_{r+1}, …, x_{n-1}`.-/
noncomputable abbrev chartTail : List R :=
  List.ofFn fun i : Fin (n - r - 1) => x ⟨r + 1 + i, by omega⟩

omit [IsRegularLocalRing R] in
/--
@isnad1 id=eq.0h4v.s6.5ba97cad2a5e from=translated src=- shape=e1af0692 vocab=2972609e
-/
theorem ofList_chartList_append_chartTail :
    Ideal.ofList (chartList x r ++ chartTail x r) = Ideal.span (Set.range x) := by
  change Ideal.span {y | y ∈ chartList x r ++ chartTail x r} = _
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.mem_ofFn, Set.mem_range]
  constructor
  · rintro ((rfl | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨r, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    rcases lt_trichotomy i.val r.val with hlt | heq | hgt
    · exact Or.inl (Or.inr ⟨⟨i.val, hlt⟩, rfl⟩)
    · exact Or.inl (Or.inl (congrArg x (Fin.ext heq)))
    · refine Or.inr ⟨⟨i.val - r.val - 1, by omega⟩, ?_⟩
      congr 1
      ext
      simp only []
      omega

omit [CommRing R] [IsRegularLocalRing R] in
/--
@isnad1 id=eq.0h4v.s5.d6fcb9abee49 from=translated src=- shape=2e742860 vocab=e97d24ad
-/
theorem length_chartList_append_chartTail : (chartList x r ++ chartTail x r).length = n := by
  simp only [List.length_append, List.length_cons, List.length_ofFn]
  omega

/-- `[x_r, x₀, …, x_{r-1}]` is weakly regular on `R` (a prefix of a permutation of a regular
system of parameters; regular sequences as in [Sta, Tag 00LJ]).
@isnad1 id=isweakly.2h4v.s6.01f284fb274a from=translated src=- shape=210933bd vocab=b47353a8
-/
theorem isWeaklyRegular_chartList (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : IsWeaklyRegular R (chartList x r) := by
  have hreg := isRegular_of_span_eq_maximalIdeal (chartList x r ++ chartTail x r)
    (by rw [ofList_chartList_append_chartTail, hx])
    (by rw [length_chartList_append_chartTail]; exact hn)
  exact ((isWeaklyRegular_append_iff R _ _).mp hreg.toIsWeaklyRegular).1

/-- `x_r` is a nonzerodivisor of `R` (the head of the weakly regular list).
@isnad1 id=issmulre.2h4v.s6.b3ee60454021 from=translated src=- shape=64bff503 vocab=6905e7b2
-/
theorem isSMulRegular_x (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : IsSMulRegular R (x r) :=
  isSMulRegular_head _ _ (isWeaklyRegular_chartList x r hx hn)

/-! ### The kernel of the presentation -/

omit [IsRegularLocalRing R] in
/--
@isnad1 id=eq.0h5v.s11.2d73b1024474 from=translated src=- shape=220e6b56 vocab=4486fd14
-/
theorem chartPresentation_sub_eq_zero (i : Fin r) :
    chartPresentation x r (C (x r) * X i - C (x (Fin.castLE r.2.le i))) = 0 := by
  rw [chartPresentation, map_sub, map_mul, aeval_C, aeval_X, aeval_C,
    algebraMap_x_eq_mul_chartYR x r (show Fin.castLE r.2.le i < r from i.2), sub_self]

omit [IsRegularLocalRing R] in
/-- `⟨x_r Yᵢ − xᵢ⟩ ⊆ ker`.
@isnad1 id=le.0h4v.s10.f4bfacc97878 from=translated src=- shape=1a897f60 vocab=342ba536
-/
theorem chartRelations_le_ker_chartPresentation :
    chartRelations x r ≤ RingHom.ker (chartPresentation x r) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact RingHom.mem_ker.mpr (chartPresentation_sub_eq_zero x r i)

end IsLocalRing
