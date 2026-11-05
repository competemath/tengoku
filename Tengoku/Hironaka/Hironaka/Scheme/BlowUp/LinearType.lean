/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Scheme.BlowUp.Presentation
public import Tengoku.Seed.RingTheory.Regular.RegularSequence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Torsion-freeness of the chart presentation

Let `A` be a commutative ring, `a ∈ A`, `g : Fin k → A`, and suppose the list
`[a, g₀, …, g_{k-1}]` is weakly regular on `A`: `a` is a nonzerodivisor of `A` and each `gⱼ` is a
nonzerodivisor of `A/(a, g₀, …, g_{j-1})` (Mathlib's `RingTheory.Sequence.IsWeaklyRegular`, whose
definition is exactly this colon condition along `List.take`).  In `M = A[Y₀, …, Y_{k-1}]` let
`J = ⟨a Yᵢ − gᵢ⟩` be the presentation ideal of the affine blow-up algebra
(`Hironaka.Scheme.BlowUp.Presentation`).  Then `a f ∈ J` implies `f ∈ J`, so `a` and its powers are
nonzerodivisors on `M/J`.  This is the statement the Stacks Project proves for `H₁`-regular
sequences through the Koszul complex [Sta, Tag 0BIQ], and the reason Hauser's presentation of a
chart ring by a regular sequence has no torsion — the only linear relations among the generators
are the trivial ones [Hau14, Theorem 4.20 (b)]; the proof below is elementary and never leaves
`M`.  It is used to identify the chart rings of the blow-up of a smooth scheme along a regular
sequence of coordinates as quotients of polynomial rings.

**The peeling induction.**  With `J_j = ⟨a Yᵢ − gᵢ : i < j⟩` and `Q_j = (a, g₀, …, g_{j-1}) ⊆ A`,
two identities of ideals of `M`: `J_{j+1} = J_j + ⟨a Yⱼ − gⱼ⟩`, and `J_j + ⟨a⟩ = Q_j M`
(`aYᵢ − gᵢ ∈ (a, gᵢ)M`; conversely `gᵢ = aYᵢ − (aYᵢ − gᵢ)`).  Base `j = 0`: `J₀ = 0` and `a f = 0`
forces `f = 0` coefficientwise.  Step: from `a f = h + (aYⱼ − gⱼ) q` with `h ∈ J_j` we get
`gⱼ q = h + a Yⱼ q − a f ∈ J_j + ⟨a⟩ = Q_j M`, i.e. `gⱼ · coeff_m(q) ∈ Q_j` for every monomial `m`
(`MvPolynomial.mem_map_C_iff`); the regularity of `gⱼ` modulo `Q_j` gives `coeff_m(q) ∈ Q_j`, so
`q ∈ Q_j M = J_j + ⟨a⟩`, `q = h' + a q'`; substituting, `a (f − (aYⱼ − gⱼ) q') ∈ J_j`, the
induction hypothesis gives `f − (aYⱼ − gⱼ) q' ∈ J_j`, and `f ∈ J_{j+1}`.  The order with `a`
first is what the induction uses (`a = x`, `g₀ = xy` in `ℚ[x, y]` is a counterexample to the
statement without it).
-/

@[expose] public section

namespace AlgebraicGeometry.affineBlowUpAlgebra

open MvPolynomial RingTheory.Sequence

universe u

variable {A : Type u} [CommRing A] {k : ℕ} (a : A) (g : Fin k → A)

/-! ### The partial presentation ideals and their base ideals -/

/-- `J_j = ⟨a Yᵢ − gᵢ : i < j⟩`.-/
noncomputable def partialPresentationIdeal (j : ℕ) : Ideal (MvPolynomial (Fin k) A) :=
  Ideal.span ((fun i : Fin k => C a * X i - C (g i)) '' {i | i.val < j})

/-- `Q_j = (a, g₀, …, g_{j-1}) ⊆ A`.-/
noncomputable def partialBase (j : ℕ) : Ideal A :=
  Ideal.span (insert a (g '' {i : Fin k | i.val < j}))

/--
@isnad1 id=eq.0h4v.s7.15e76cfc5be9 from=translated src=- shape=4fa79d67 vocab=be7846b1
-/
theorem partialPresentationIdeal_zero : partialPresentationIdeal a g 0 = ⊥ := by
  have : {i : Fin k | i.val < 0} = ∅ :=
    Set.eq_empty_of_forall_notMem fun i hi => Nat.not_lt_zero _ hi
  rw [partialPresentationIdeal, this, Set.image_empty, Ideal.span_empty]

/--
@isnad1 id=eq.1h5v.s9.1f496aae9741 from=translated src=- shape=ef415c8f vocab=8f3d8c2a
-/
theorem partialPresentationIdeal_succ {j : ℕ} (hj : j < k) :
    partialPresentationIdeal a g (j + 1) =
      partialPresentationIdeal a g j ⊔ Ideal.span {C a * X ⟨j, hj⟩ - C (g ⟨j, hj⟩)} := by
  have : {i : Fin k | i.val < j + 1} = insert ⟨j, hj⟩ {i : Fin k | i.val < j} := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  rw [partialPresentationIdeal, partialPresentationIdeal, this, Set.image_insert_eq,
    Ideal.span_insert, sup_comm]

/--
@isnad1 id=eq.1h5v.s6.28d0a4ee87a3 from=translated src=- shape=67d93c0e vocab=eb773fcc
-/
theorem partialPresentationIdeal_eq_of_le {j : ℕ} (hj : k ≤ j) :
    partialPresentationIdeal a g j = presentationIdeal a g := by
  have : {i : Fin k | i.val < j} = Set.univ :=
    Set.eq_univ_of_forall fun i => lt_of_lt_of_le i.2 hj
  rw [partialPresentationIdeal, this, Set.image_univ]
  rfl

/--
@isnad1 id=mem.0h5v.s6.ce1d82e5efb6 from=translated src=- shape=2ace278f vocab=2681c3e2
-/
theorem a_mem_partialBase (j : ℕ) : a ∈ partialBase a g j :=
  Ideal.subset_span (Set.mem_insert _ _)

/--
@isnad1 id=mem.1h6v.s6.1fd58dc7fb51 from=translated src=- shape=2744ef93 vocab=0943667b
-/
theorem g_mem_partialBase {j : ℕ} {i : Fin k} (hi : i.val < j) : g i ∈ partialBase a g j :=
  Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩)

/-- The identity `J_j + ⟨a⟩ = Q_j M`.
@isnad1 id=eq.0h5v.s8.e5fcad74fc50 from=translated src=- shape=aaec5fc8 vocab=fb642798
-/
theorem partialPresentationIdeal_sup_span_C (j : ℕ) :
    partialPresentationIdeal a g j ⊔ Ideal.span {C a} =
      (partialBase a g j).map (C : A →+* MvPolynomial (Fin k) A) := by
  apply le_antisymm
  · refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨i, hi, rfl⟩
      exact Ideal.sub_mem _
        (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (a_mem_partialBase a g j)))
        (Ideal.mem_map_of_mem _ (g_mem_partialBase a g hi))
    · rintro _ rfl
      exact Ideal.mem_map_of_mem _ (a_mem_partialBase a g j)
  · rw [partialBase, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | ⟨i, hi, rfl⟩
    · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    · have : (C (g i) : MvPolynomial (Fin k) A) = C a * X i - (C a * X i - C (g i)) := by ring
      rw [this]
      exact Ideal.sub_mem _
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
        (Ideal.mem_sup_left (Ideal.subset_span ⟨i, hi, rfl⟩))

/-! ### The regularity hypotheses, extracted from `IsWeaklyRegular` -/

/--
@isnad1 id=issmulre.1h4v.s5.37a6417a54ca from=translated src=- shape=ef25cd2f vocab=484bfe81
-/
theorem isSMulRegular_head (h : IsWeaklyRegular A (a :: List.ofFn g)) : IsSMulRegular A a :=
  ((isWeaklyRegular_cons_iff A a _).mp h).1

/--
@isnad1 id=eq.0h5v.s5.7b6407a6e05a from=translated src=- shape=b927bd91 vocab=b56771f0
-/
theorem ofList_take_cons_ofFn (j : ℕ) :
    Ideal.ofList ((a :: List.ofFn g).take (j + 1)) = partialBase a g j := by
  rw [List.take_succ_cons, Ideal.ofList_cons, partialBase, Ideal.span_insert]
  congr 1
  change Ideal.span {r | r ∈ (List.ofFn g).take j} = _
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_image, List.mem_iff_getElem, List.length_take,
    List.length_ofFn, List.getElem_take, List.getElem_ofFn, lt_min_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi.2⟩, hi.1, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, ⟨hi, i.2⟩, rfl⟩

/-- The `j`-th clause of weak regularity, in colon form: `gⱼ c ∈ Q_j ⟹ c ∈ Q_j`.
@isnad1 id=mem.2h6v.s7.e9fea7e1501c from=translated src=- shape=b77898ed vocab=058f8c2f
-/
theorem mem_partialBase_of_mul_mem (h : IsWeaklyRegular A (a :: List.ofFn g)) (j : Fin k)
    {c : A} (hc : g j * c ∈ partialBase a g j) : c ∈ partialBase a g j := by
  have hreg := h.regular_mod_prev (j.val + 1) (by simp)
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hreg
  have hQ : (Ideal.ofList ((a :: List.ofFn g).take (j.val + 1)) • ⊤ : Submodule A A) =
      partialBase a g j := by
    rw [ofList_take_cons_ofFn a g j.val, smul_eq_mul, Ideal.mul_top]
  rw [hQ] at hreg
  simp only [List.getElem_cons_succ, List.getElem_ofFn, Fin.eta] at hreg
  exact hreg c (by rw [smul_eq_mul]; exact hc)

/-! ### The peeling induction -/

end AlgebraicGeometry.affineBlowUpAlgebra
