/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.LinearAlgebra.Lagrange
import Tengoku.Seed.RingTheory.Algebraic.Basic
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.RingTheory.Polynomial.GaussLemma
import Tengoku.AclGeom.AclGeom.Correspondence.CurveIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rational function fields over a relatively closed base

The specialization brick for base-change irreducibility (step 4a of the
fused curve-coset chain): over an infinite field `k` that is algebraically
closed in `K`, a polynomial in `K[t]` satisfying a nontrivial algebraic
relation over `k[t]` has all its coefficients in `k`. Consequently `k(t)` is
relatively algebraically closed in `K(t)`.

The proof is by specialization: evaluating the relation at all but finitely
many points `τ ∈ k` shows the value `x(τ)` is algebraic over `k`, hence lies
in `k`; Lagrange interpolation through `deg x + 1` such nodes then forces
every coefficient of `x` into `k`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, checklist C7 support).
-/

namespace AclGeom

open Polynomial

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Specialization brick** (one-variable relative closure of rational
function fields, polynomial form): if `k` is infinite and algebraically
closed in `K`, then a polynomial `x ∈ K[t]` satisfying a nontrivial
polynomial relation with coefficients in `k[t]` is defined over `k`.-/
theorem exists_map_eq_of_eval₂_eq_zero [Infinite k]
    (hk : ∀ y : K, IsAlgebraic k y → y ∈ (algebraMap k K).range)
    {x : Polynomial K} {P : Polynomial (Polynomial k)} (hP : P ≠ 0)
    (hPx : Polynomial.eval₂ (mapRingHom (algebraMap k K)) x P = 0) :
    ∃ y : Polynomial k, x = y.map (algebraMap k K) := by
  classical
  set φ := algebraMap k K with hφ
  -- A nonzero coefficient of the relation, whose roots are the bad nodes.
  obtain ⟨i₀, hi₀⟩ := Polynomial.support_nonempty.2 hP
  have hc₀ : P.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.1 hi₀
  set bad : Finset k := (P.coeff i₀).roots.toFinset with hbad
  -- Specializing the relation at a good node makes the value algebraic.
  have hval : ∀ τ : k, τ ∉ bad → ∃ c : k, x.eval (φ τ) = φ c := by
    intro τ hτ
    have hPτ : P.map (evalRingHom τ) ≠ 0 := by
      intro h0
      have hcoeff := congrArg (fun q ↦ Polynomial.coeff q i₀) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hcoeff
      exact hτ (Multiset.mem_toFinset.2 (Polynomial.mem_roots'.2 ⟨hc₀, hcoeff⟩))
    have hcomp : (evalRingHom (φ τ)).comp (mapRingHom φ) =
        φ.comp (evalRingHom τ) := by
      refine RingHom.ext fun q ↦ ?_
      simp only [RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom]
      rw [eval_map, eval₂_at_apply]
    have hrel : Polynomial.eval₂ (φ.comp (evalRingHom τ)) (x.eval (φ τ)) P = 0 := by
      have h := congrArg (evalRingHom (φ τ)) hPx
      rw [map_zero, Polynomial.hom_eval₂, hcomp] at h
      exact h
    have halg : IsAlgebraic k (x.eval (φ τ)) := by
      refine ⟨P.map (evalRingHom τ), hPτ, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      exact hrel
    obtain ⟨c, hc⟩ := RingHom.mem_range.1 (hk _ halg)
    exact ⟨c, hc.symm⟩
  -- Choose `natDegree x + 1` good nodes.
  obtain ⟨s, hs_sub, hs_card⟩ := Set.Infinite.exists_subset_card_eq
    ((Set.infinite_univ (α := k)).sdiff bad.finite_toSet) (x.natDegree + 1)
  have hs_good : ∀ τ ∈ s, τ ∉ bad := fun τ hτ ↦ (hs_sub hτ).2
  -- The interpolated polynomial over `k`.
  set r : k → k := fun τ ↦ if h : τ ∉ bad then Classical.choose (hval τ h) else 0
    with hr
  have hrspec : ∀ τ ∈ s, x.eval (φ τ) = φ (r τ) := by
    intro τ hτ
    rw [hr]
    simp only [hs_good τ hτ]
    exact Classical.choose_spec (hval τ (hs_good τ hτ))
  set y : Polynomial k := Lagrange.interpolate s id r with hy
  refine ⟨y, ?_⟩
  -- Two polynomials of degree `< s.card` agreeing on the `s`-nodes coincide.
  have hinj : Set.InjOn (fun τ : k ↦ φ τ) s := fun a _ b _ h ↦
    (algebraMap k K).injective h
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (v := fun τ : k ↦ φ τ)
    s hinj ?_ ?_ ?_
  · calc x.degree ≤ (x.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < (s.card : WithBot ℕ) := by
          rw [hs_card]
          exact_mod_cast Nat.lt_succ_self _
  · calc (y.map φ).degree ≤ y.degree := Polynomial.degree_map_le
      _ < (s.card : WithBot ℕ) :=
          Lagrange.degree_interpolate_lt _ (Set.injOn_id _)
  · intro τ hτ
    have hnode := Lagrange.eval_interpolate_at_node (v := id) (r := r)
      (Set.injOn_id _) hτ
    simp only [id_eq] at hnode
    rw [eval_map, eval₂_at_apply, hy, hnode]
    exact hrspec τ hτ

/-- Over an algebraically closed base, algebraic elements of any extension
already lie in the base (element-level form).-/
theorem mem_range_algebraMap_of_isAlgebraic [IsAlgClosed k] {y : K}
    (hy : IsAlgebraic k y) : y ∈ (algebraMap k K).range := by
  have hint : IsIntegral k y := hy.isIntegral
  refine ⟨-(minpoly k y).coeff 0, ?_⟩
  have hq : (minpoly k y).leadingCoeff = 1 := minpoly.monic hint
  have h1 : (minpoly k y).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
  have h0 : aeval y (minpoly k y) = 0 := minpoly.aeval k y
  rw [eq_X_add_C_of_degree_eq_one h1, hq, C_1, one_mul, aeval_add, aeval_X,
    aeval_C, add_eq_zero_iff_eq_neg] at h0
  exact (map_neg (algebraMap k K) ((minpoly k y).coeff 0)).symm ▸ h0.symm

/-- The specialization brick in `IsAlgClosed` form.-/
theorem exists_map_eq_of_eval₂_eq_zero_of_isAlgClosed [IsAlgClosed k]
    {x : Polynomial K} {P : Polynomial (Polynomial k)} (hP : P ≠ 0)
    (hPx : Polynomial.eval₂ (mapRingHom (algebraMap k K)) x P = 0) :
    ∃ y : Polynomial k, x = y.map (algebraMap k K) :=
  exists_map_eq_of_eval₂_eq_zero (fun _ hy ↦ mem_range_algebraMap_of_isAlgebraic hy)
    hP hPx

section CoordPoly

variable {k K' : Type*} [Field k] [Field K'] [Algebra k K']
variable {ι : Type*}

/-- The `j`-th coordinate polynomial of a `K'`-polynomial along a `k`-basis:
apply the coordinate functional coefficientwise.-/
def coordPoly (b : Module.Basis ι k K') (j : ι) (q : Polynomial K') :
    Polynomial k :=
  q.sum fun m a ↦ Polynomial.C (b.repr a j) * Polynomial.X ^ m

theorem coordPoly_coeff (b : Module.Basis ι k K') (j : ι) (q : Polynomial K')
    (m : ℕ) : (coordPoly b j q).coeff m = b.repr (q.coeff m) j := by
  classical
  rw [coordPoly, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  rw [Finset.sum_congr rfl fun i _ ↦
    Polynomial.coeff_C_mul_X_pow (b.repr (q.coeff i) j) i m]
  rw [Finset.sum_ite_eq q.support m fun i ↦ b.repr (q.coeff i) j]
  by_cases hm : m ∈ q.support
  · rw [ite_eq_left hm]
  · rw [ite_eq_right hm, Polynomial.notMem_support_iff.1 hm, map_zero,
      Finsupp.coe_zero, Pi.zero_apply]

/-- Coordinate polynomials commute with evaluation at points of `k`.-/
theorem eval_coordPoly (b : Module.Basis ι k K') (j : ι) (q : Polynomial K')
    (τ : k) :
    (coordPoly b j q).eval τ = b.repr (q.eval (algebraMap k K' τ)) j := by
  classical
  rw [coordPoly, Polynomial.sum_def, Polynomial.eval_finsetSum]
  have hq : q.eval (algebraMap k K' τ) = ∑ m ∈ q.support, τ ^ m • q.coeff m := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [Algebra.smul_def, map_pow, mul_comm]
  rw [hq, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- Coordinate polynomials are `k[X]`-linear in the `k`-defined factor.-/
theorem coordPoly_mul_map (b : Module.Basis ι k K') (j : ι)
    (r : Polynomial K') (q : Polynomial k) :
    coordPoly b j (r * q.map (algebraMap k K')) = coordPoly b j r * q := by
  classical
  ext m
  rw [coordPoly_coeff, Polynomial.coeff_mul, Polynomial.coeff_mul, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Polynomial.coeff_map, coordPoly_coeff]
  have h1 : r.coeff x.1 * algebraMap k K' (q.coeff x.2) =
      q.coeff x.2 • r.coeff x.1 := by
    rw [Algebra.smul_def, mul_comm]
  rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

end CoordPoly

section Descent

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

variable {k K' Ω : Type*} [Field k] [Field K'] [Field Ω]
variable [Algebra k K'] [Algebra K' Ω] [Algebra k Ω] [IsScalarTower k K' Ω]

/-- **The descent brick** (chunk α of the base-change argument): over an
infinite field `k` that is algebraically closed in `K'`, an element of
`K'(u)` that is algebraic over `k(u)` already lies in `k(u)`, for `u`
transcendental over `K'`. The proof homogenizes the algebraic relation into
a polynomial identity, decomposes numerator and denominator along a
`k`-basis of `K'`, and specializes at the points of `k`: the values are
algebraic over `k`, hence in `k`, and cross-multiplied coordinates agree on
a cofinite set, hence everywhere.-/
theorem mem_adjoin_base_of_isAlgebraic [Infinite k]
    (hk : ∀ y : K', IsAlgebraic k y → y ∈ (algebraMap k K').range)
    {u c : Ω} (hu : Transcendental K' u)
    (hcK : c ∈ adjoin K' ({u} : Set Ω))
    (hcalg : IsAlgebraic ↥(adjoin k ({u} : Set Ω)) c) :
    c ∈ adjoin k ({u} : Set Ω) := by
  classical
  set φ' := algebraMap k K' with hφ'
  -- Write `c` as a ratio of `K'`-polynomial values at `u`.
  obtain ⟨r, s, hc⟩ := (mem_adjoin_simple_iff K' c).1 hcK
  rcases eq_or_ne (Polynomial.aeval u s) 0 with hs0 | hs0
  · rw [hc, hs0, div_zero]
    exact zero_mem _
  have hcs : c * Polynomial.aeval u s = Polynomial.aeval u r := by
    rw [hc, div_mul_cancel₀ _ hs0]
  have hs_ne : s ≠ 0 := fun h ↦ hs0 (by rw [h, map_zero])
  -- The algebraic relation, with coefficients polynomial in `u`.
  have hcalg' : IsAlgebraic ↥(Algebra.adjoin k ({u} : Set Ω)) c :=
    (IsFractionRing.isAlgebraic_iff (Algebra.adjoin k ({u} : Set Ω))
      (adjoin k ({u} : Set Ω)) Ω).2 hcalg
  obtain ⟨p, hp0, hpc⟩ := hcalg'
  have hrepr : ∀ m : ℕ, ∃ P : Polynomial k,
      Polynomial.aeval u P = (p.coeff m : Ω) := by
    intro m
    have hle := (Algebra.adjoin_singleton_eq_range_aeval k u).le
    exact (AlgHom.mem_range _).1 (hle (p.coeff m).2)
  choose P hP using hrepr
  set n := p.natDegree with hn
  have hlead : Polynomial.aeval u (P n) ≠ 0 := by
    rw [hP n]
    exact_mod_cast Polynomial.leadingCoeff_ne_zero.2 hp0
  have hPn : P n ≠ 0 := fun h ↦ hlead (by rw [h, map_zero])
  -- Transcendence of `u` over `k` as well.
  have huk : Transcendental k u := fun halg ↦ hu (halg.tower_top K')
  -- Homogenize: a polynomial identity over `K'`.
  set E : Polynomial K' := ∑ m ∈ Finset.range (n + 1),
    (P m).map φ' * r ^ m * s ^ (n - m) with hE
  have hEval : Polynomial.aeval u E = 0 := by
    have hexp : Polynomial.aeval c p =
        ∑ m ∈ Finset.range (n + 1), (p.coeff m : Ω) * c ^ m := by
      rw [Polynomial.aeval_eq_sum_range]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [Algebra.smul_def]
      rfl
    have hzero : ∑ m ∈ Finset.range (n + 1), (p.coeff m : Ω) * c ^ m = 0 := by
      rw [← hexp, hpc]
    have hkey : Polynomial.aeval u E =
        (∑ m ∈ Finset.range (n + 1), (p.coeff m : Ω) * c ^ m) *
          (Polynomial.aeval u s) ^ n := by
      rw [hE, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
      rw [map_mul, map_mul, map_pow, map_pow,
        Polynomial.aeval_map_algebraMap, hP m, ← hcs]
      have hsplit : (Polynomial.aeval u s : Ω) ^ n =
          (Polynomial.aeval u s) ^ m * (Polynomial.aeval u s) ^ (n - m) := by
        rw [← pow_add, Nat.add_sub_cancel' hmn]
      rw [hsplit]
      ring
    rw [hkey, hzero, zero_mul]
  have hE0 : E = 0 := by
    by_contra hne
    exact hu ⟨E, hne, hEval⟩
  -- Basis decomposition of numerator and denominator.
  set b := Module.Basis.ofVectorSpace k K' with hb
  -- A coordinate where the denominator is visible.
  obtain ⟨ms, hms⟩ := Polynomial.support_nonempty.2 hs_ne
  have hms0 : s.coeff ms ≠ 0 := Polynomial.mem_support_iff.1 hms
  obtain ⟨j₀, hj₀⟩ : ∃ j, b.repr (s.coeff ms) j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hms0 (b.repr.injective (by ext j; simp [hall j]))
  have hSj₀ : coordPoly b j₀ s ≠ 0 := fun h ↦ by
    have := coordPoly_coeff b j₀ s ms
    rw [h, Polynomial.coeff_zero] at this
    exact hj₀ this.symm
  -- The bad specialization points: roots of `P n` and of the denominator.
  set badP : Finset k := (P n).roots.toFinset with hbadP
  have hsroots : Set.Finite {τ : k | s.eval (φ' τ) = 0} := by
    have hsub : {τ : k | s.eval (φ' τ) = 0} ⊆
        (fun τ ↦ φ' τ) ⁻¹' {y : K' | s.eval y = 0} := fun τ hτ ↦ hτ
    refine Set.Finite.subset (Set.Finite.preimage
      (Set.injOn_of_injective (algebraMap k K').injective)
      (Polynomial.finite_setOfPred_isRoot hs_ne)) hsub
  -- Pointwise coordinate identities on the good set.
  have hgood : ∀ τ : k, τ ∉ badP → s.eval (φ' τ) ≠ 0 → ∀ j,
      (coordPoly b j r * coordPoly b j₀ s).eval τ =
      (coordPoly b j₀ r * coordPoly b j s).eval τ := by
    intro τ hτP hτs j
    -- The specialized value is algebraic over `k`, hence in `k`.
    have hspec : ∑ m ∈ Finset.range (n + 1),
        φ' ((P m).eval τ) * r.eval (φ' τ) ^ m * s.eval (φ' τ) ^ (n - m) = 0 := by
      have h := congrArg (Polynomial.eval (φ' τ)) hE0
      rw [hE, Polynomial.eval_finsetSum, Polynomial.eval_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_pow, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    set w : K' := r.eval (φ' τ) / s.eval (φ' τ) with hw
    have hwalg : IsAlgebraic k w := by
      refine ⟨∑ m ∈ Finset.range (n + 1),
        Polynomial.C ((P m).eval τ) * Polynomial.X ^ m, ?_, ?_⟩
      · intro h0
        have hcoeff := congrArg (fun q ↦ Polynomial.coeff q n) h0
        simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hcoeff
        rw [Finset.sum_congr rfl fun m _ ↦
          Polynomial.coeff_C_mul_X_pow ((P m).eval τ) m n] at hcoeff
        rw [Finset.sum_ite_eq (Finset.range (n + 1)) n fun m ↦ (P m).eval τ,
          ite_eq_left (Finset.self_mem_range_succ n)] at hcoeff
        exact hτP (Multiset.mem_toFinset.2
          (Polynomial.mem_roots'.2 ⟨hPn, hcoeff⟩))
      · rw [Polynomial.aeval_def, Polynomial.eval₂_finsetSum]
        have hterm : ∀ m ∈ Finset.range (n + 1),
            Polynomial.eval₂ φ' w (Polynomial.C ((P m).eval τ) *
              Polynomial.X ^ m) =
            φ' ((P m).eval τ) * r.eval (φ' τ) ^ m * s.eval (φ' τ) ^ (n - m) /
              s.eval (φ' τ) ^ n := by
          intro m hm
          have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
          rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
            Polynomial.eval₂_X, hw, div_pow, ← mul_div_assoc,
            div_eq_div_iff (pow_ne_zero m hτs) (pow_ne_zero n hτs)]
          have hsplit : s.eval (φ' τ) ^ n =
              s.eval (φ' τ) ^ m * s.eval (φ' τ) ^ (n - m) := by
            rw [← pow_add, Nat.add_sub_cancel' hmn]
          rw [hsplit]
          ring
        rw [Finset.sum_congr rfl hterm]
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, hspec, zero_mul]
    obtain ⟨cτ, hcτ⟩ := RingHom.mem_range.1 (hk w hwalg)
    -- Numerator = value • denominator, coordinatewise.
    have hrs : r.eval (φ' τ) = cτ • s.eval (φ' τ) := by
      rw [Algebra.smul_def, hcτ, hw, div_mul_cancel₀ _ hτs]
    simp only [Polynomial.eval_mul]
    rw [eval_coordPoly, eval_coordPoly, eval_coordPoly, eval_coordPoly, hrs,
      map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  -- Cross-multiplied coordinates agree everywhere.
  have hD : ∀ j, coordPoly b j r * coordPoly b j₀ s =
      coordPoly b j₀ r * coordPoly b j s := by
    intro j
    have hbadfin : Set.Finite ((badP : Set k) ∪ {τ : k | s.eval (φ' τ) = 0}) :=
      Set.Finite.union badP.finite_toSet hsroots
    have hroots : {τ : k | (coordPoly b j r * coordPoly b j₀ s -
        coordPoly b j₀ r * coordPoly b j s).IsRoot τ}.Infinite := by
      refine Set.Infinite.mono ?_
        (Set.Infinite.sdiff (Set.infinite_univ (α := k)) hbadfin)
      intro τ hτ
      have hτP : τ ∉ badP := fun h ↦ hτ.2 (Or.inl h)
      have hτs : s.eval (φ' τ) ≠ 0 := fun h ↦ hτ.2 (Or.inr h)
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, Polynomial.eval_sub]
      rw [hgood τ hτP hτs j, sub_self]
    have := Polynomial.eq_zero_of_infinite_isRoot _ hroots
    rw [sub_eq_zero] at this
    exact this
  -- Reconstruct the polynomial identity over `K'` and divide at `u`.
  have hpoly : r * (coordPoly b j₀ s).map φ' = (coordPoly b j₀ r).map φ' * s := by
    ext m
    have hcoord : ∀ j, b.repr ((r * (coordPoly b j₀ s).map φ').coeff m) j =
        b.repr (((coordPoly b j₀ r).map φ' * s).coeff m) j := by
      intro j
      rw [← coordPoly_coeff b j, ← coordPoly_coeff b j, coordPoly_mul_map]
      have hcomm : (coordPoly b j₀ r).map φ' * s =
          s * (coordPoly b j₀ r).map φ' := mul_comm _ _
      rw [hcomm, coordPoly_mul_map, hD j]
      ring_nf
    exact b.repr.injective (Finsupp.ext fun j ↦ hcoord j)
  have hnum : Polynomial.aeval u r * Polynomial.aeval u (coordPoly b j₀ s) =
      Polynomial.aeval u (coordPoly b j₀ r) * Polynomial.aeval u s := by
    have h := congrArg (Polynomial.aeval u) hpoly
    rw [map_mul, map_mul, Polynomial.aeval_map_algebraMap,
      Polynomial.aeval_map_algebraMap] at h
    exact h
  have hSu : Polynomial.aeval u (coordPoly b j₀ s) ≠ 0 := fun h ↦
    huk ⟨coordPoly b j₀ s, hSj₀, h⟩
  -- Conclude: `c` is a ratio of `k`-polynomial values at `u`.
  have hcval : c = Polynomial.aeval u (coordPoly b j₀ r) /
      Polynomial.aeval u (coordPoly b j₀ s) := by
    rw [hc, div_eq_div_iff hs0 hSu, hnum]
  rw [hcval]
  have hmemP : ∀ Q : Polynomial k,
      Polynomial.aeval u Q ∈ adjoin k ({u} : Set Ω) := by
    intro Q
    have hmem : Polynomial.aeval u Q ∈ Algebra.adjoin k ({u} : Set Ω) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact (AlgHom.mem_range _).2 ⟨Q, rfl⟩
    exact algebra_adjoin_le_adjoin k _ hmem
  exact div_mem (hmemP _) (hmemP _)

end Descent

section MinpolyDescent

open IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **Minimal polynomials descend** (the keystone of base-change
irreducibility): for `k` algebraically closed, `K` an intermediate field, and
`u` transcendental over `K`, the coefficients of the minimal polynomial over
`K(u)` of an element algebraic over `k(u)` already lie in `k(u)`. The
coefficients are integral over `k(u)` by the Gauss argument (they divide the
image of the monic minimal polynomial from below), and integral elements of
`K(u)` over `k(u)` descend by the specialization brick.-/
theorem minpoly_coeff_mem [IsAlgClosed k] {K : IntermediateField k Ω}
    {u v : Ω} (hu : Transcendental ↥K u)
    (hv : IsAlgebraic ↥(adjoin k ({u} : Set Ω)) v) (i : ℕ) :
    ((minpoly ↥(adjoin ↥K ({u} : Set Ω)) v).coeff i : Ω) ∈
      adjoin k ({u} : Set Ω) := by
  classical
  set L₀ : IntermediateField k Ω := adjoin k ({u} : Set Ω) with hL₀
  set L : IntermediateField ↥K Ω := adjoin ↥K ({u} : Set Ω) with hL
  -- The inclusion `k(u) → K(u)` as an algebra.
  have hle : L₀ ≤ L.restrictScalars k := by
    rw [hL₀]
    refine adjoin_le_iff.2 ?_
    intro x hx
    rcases hx with rfl
    exact subset_adjoin ↥K _ rfl
  set incl : ↥L₀ →ₐ[k] ↥(L.restrictScalars k) := IntermediateField.inclusion hle
  letI : Algebra ↥L₀ ↥L := incl.toRingHom.toAlgebra
  haveI htow : IsScalarTower ↥L₀ ↥L Ω := IsScalarTower.of_algebraMap_eq' rfl
  -- The two minimal polynomials.
  have hvL : IsAlgebraic ↥L v := by
    obtain ⟨p, hp0, hpv⟩ := hv
    refine ⟨p.map (algebraMap ↥L₀ ↥L), ?_, ?_⟩
    · exact fun h ↦ hp0 ((Polynomial.map_eq_zero_iff
        (algebraMap ↥L₀ ↥L).injective).1 h)
    · rw [Polynomial.aeval_map_algebraMap]
      exact hpv
  set m₀ := minpoly ↥L₀ v with hm₀
  set m := minpoly ↥L v with hm
  have hm₀monic : m₀.Monic := minpoly.monic hv.isIntegral
  have hmdvd : m ∣ m₀.map (algebraMap ↥L₀ ↥L) := by
    refine minpoly.dvd ↥L v ?_
    rw [Polynomial.aeval_map_algebraMap]
    exact minpoly.aeval ↥L₀ v
  -- Gauss: the coefficients of `m` are integral over `k(u)`.
  have hmmonic : m.Monic := minpoly.monic hvL.isIntegral
  have hlifts := integralClosure.mem_lifts_of_monic_of_dvd_map ↥L
    hm₀monic hmmonic hmdvd
  rw [Polynomial.lifts_iff_coeff_lifts] at hlifts
  obtain ⟨w, hw⟩ := hlifts i
  -- `w` is integral over `k(u)`; push everything into `Ω` and descend.
  have hint : IsIntegral ↥L₀ (m.coeff i) := by
    have h2 : IsIntegral ↥L₀
        (algebraMap ↥(integralClosure ↥L₀ ↥L) ↥L w) := w.2
    exact hw ▸ h2
  have halg : IsAlgebraic ↥L₀ ((m.coeff i : ↥L) : Ω) :=
    (hint.map (IsScalarTower.toAlgHom ↥L₀ ↥L Ω)).isAlgebraic
  have hmem : ((m.coeff i : ↥L) : Ω) ∈ adjoin ↥K ({u} : Set Ω) := (m.coeff i).2
  exact mem_adjoin_base_of_isAlgebraic
    (fun y hy ↦ mem_range_algebraMap_of_isAlgebraic hy) hu hmem halg

/-- **The degree bridge**: the minimal polynomial over `K(u)` has the same
degree as the one over `k(u)` — it descends coefficientwise by
`minpoly_coeff_mem`, and the descended polynomial mutually divides the
`k(u)`-minimal polynomial.-/
theorem natDegree_minpoly_adjoin_eq [IsAlgClosed k] {K : IntermediateField k Ω}
    {u v : Ω} (hu : Transcendental ↥K u)
    (hv : IsAlgebraic ↥(adjoin k ({u} : Set Ω)) v) :
    (minpoly ↥(adjoin ↥K ({u} : Set Ω)) v).natDegree =
      (minpoly ↥(adjoin k ({u} : Set Ω)) v).natDegree := by
  classical
  set L₀ : IntermediateField k Ω := adjoin k ({u} : Set Ω) with hL₀
  set L : IntermediateField ↥K Ω := adjoin ↥K ({u} : Set Ω) with hL
  have hle : L₀ ≤ L.restrictScalars k := by
    rw [hL₀]
    refine adjoin_le_iff.2 ?_
    intro x hx
    rcases hx with rfl
    exact subset_adjoin ↥K _ rfl
  set incl : ↥L₀ →ₐ[k] ↥(L.restrictScalars k) := IntermediateField.inclusion hle
  letI : Algebra ↥L₀ ↥L := incl.toRingHom.toAlgebra
  haveI htow : IsScalarTower ↥L₀ ↥L Ω := IsScalarTower.of_algebraMap_eq' rfl
  have hinj : Function.Injective (algebraMap ↥L₀ ↥L) := by
    intro a b hab
    have h2 : ((a : Ω)) = ((b : Ω)) := congrArg (Subtype.val : ↥L → Ω) hab
    exact Subtype.ext h2
  have hvL : IsAlgebraic ↥L v := by
    obtain ⟨p, hp0, hpv⟩ := hv
    refine ⟨p.map (algebraMap ↥L₀ ↥L), ?_, ?_⟩
    · exact fun h ↦ hp0 ((Polynomial.map_eq_zero_iff hinj).1 h)
    · rw [Polynomial.aeval_map_algebraMap]
      exact hpv
  set m₀ := minpoly ↥L₀ v with hm₀def
  set m := minpoly ↥L v with hmdef
  have hm₀monic : m₀.Monic := minpoly.monic hv.isIntegral
  have hmmonic : m.Monic := minpoly.monic hvL.isIntegral
  -- The descended polynomial `m'`.
  set m' : Polynomial ↥L₀ := ∑ i ∈ Finset.range (m.natDegree + 1),
    Polynomial.C (⟨(m.coeff i : Ω), minpoly_coeff_mem hu hv i⟩ : ↥L₀) *
      Polynomial.X ^ i with hm'def
  have hm'coeff : ∀ j, ((m'.coeff j : Ω)) = (m.coeff j : Ω) := by
    intro j
    rw [hm'def, Polynomial.finsetSum_coeff]
    rw [Finset.sum_congr rfl fun i _ ↦ Polynomial.coeff_C_mul_X_pow _ i j]
    rw [Finset.sum_ite_eq (Finset.range (m.natDegree + 1)) j
      fun i ↦ (⟨(m.coeff i : Ω), minpoly_coeff_mem hu hv i⟩ : ↥L₀)]
    by_cases hj : j ∈ Finset.range (m.natDegree + 1)
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj]
      have hj' : m.natDegree < j := by
        by_contra hle'
        exact hj (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_not_lt hle')))
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj']
      simp
  have hmap : m'.map (algebraMap ↥L₀ ↥L) = m := by
    ext j
    rw [Polynomial.coeff_map]
    have h2 : (((algebraMap ↥L₀ ↥L) (m'.coeff j) : ↥L) : Ω) =
        ((m.coeff j : ↥L) : Ω) := by
      have h3 : (((algebraMap ↥L₀ ↥L) (m'.coeff j) : ↥L) : Ω) =
          ((m'.coeff j : ↥L₀) : Ω) := rfl
      rw [h3]
      exact hm'coeff j
    exact h2
  -- Mutual divisibility with the `k(u)`-minimal polynomial.
  have hm'v : Polynomial.aeval v m' = 0 := by
    have h := minpoly.aeval ↥L v
    rw [← hmdef, ← hmap, Polynomial.aeval_map_algebraMap] at h
    exact h
  have hdvd₀ : m₀ ∣ m' := minpoly.dvd ↥L₀ v hm'v
  have hdvd' : m' ∣ m₀ := by
    have hmdvd : m ∣ m₀.map (algebraMap ↥L₀ ↥L) := by
      refine minpoly.dvd ↥L v ?_
      rw [Polynomial.aeval_map_algebraMap]
      exact minpoly.aeval ↥L₀ v
    have hm'monic : m'.Monic := by
      have h1 : (algebraMap ↥L₀ ↥L) m'.leadingCoeff = 1 := by
        have h2 : m'.natDegree = m.natDegree := by
          rw [← hmap, Polynomial.natDegree_map_eq_of_injective hinj]
        rw [Polynomial.leadingCoeff, h2]
        refine Subtype.ext ?_
        rw [show (((algebraMap ↥L₀ ↥L) (m'.coeff m.natDegree) : ↥L) : Ω) =
          ((m'.coeff m.natDegree : ↥L₀) : Ω) from rfl, hm'coeff]
        exact congrArg Subtype.val hmmonic
      exact hinj (by rw [h1, map_one])
    have hmod : (m₀ %ₘ m').map (algebraMap ↥L₀ ↥L) = 0 := by
      rw [Polynomial.map_modByMonic _ hm'monic, hmap]
      exact (Polynomial.modByMonic_eq_zero_iff_dvd hmmonic).2 hmdvd
    have h0 : m₀ %ₘ m' = 0 := (Polynomial.map_eq_zero_iff hinj).1 hmod
    exact (Polynomial.modByMonic_eq_zero_iff_dvd hm'monic).1 h0
  have hm'monic : m'.Monic := by
    have h2 : m'.natDegree = m.natDegree := by
      rw [← hmap, Polynomial.natDegree_map_eq_of_injective hinj]
    have h1 : (algebraMap ↥L₀ ↥L) m'.leadingCoeff = 1 := by
      rw [Polynomial.leadingCoeff, h2]
      refine Subtype.ext ?_
      rw [show (((algebraMap ↥L₀ ↥L) (m'.coeff m.natDegree) : ↥L) : Ω) =
        ((m'.coeff m.natDegree : ↥L₀) : Ω) from rfl, hm'coeff]
      exact congrArg Subtype.val hmmonic
    exact hinj (by rw [h1, map_one])
  have hm'eq : m' = m₀ :=
    Polynomial.eq_of_monic_of_associated hm'monic hm₀monic
      (associated_of_dvd_dvd hdvd' hdvd₀)
  calc m.natDegree = m'.natDegree := by
        rw [← hmap, Polynomial.natDegree_map_eq_of_injective hinj]
    _ = m₀.natDegree := by rw [hm'eq]

end MinpolyDescent

section CurveDictionary

open MvPolynomial IntermediateField

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- Partial evaluation of a plane polynomial at a point `u` in the first
coordinate: `g(X, Y) ↦ g(u, Y)`, a one-variable polynomial with coefficients
in `K(u)`. This is the dictionary between the curve ideal in `K[X, Y]` and
minimal polynomials over `K(u)`.-/
def evalFst (u : Ω) :
    MvPolynomial (Fin 2) K →ₐ[K] Polynomial ↥(adjoin K ({u} : Set Ω)) :=
  aeval ![Polynomial.C ⟨u, subset_adjoin K _ rfl⟩, Polynomial.X]

/-- Evaluating the second variable recovers the joint evaluation: the
dictionary is compatible with taking points.-/
theorem eval₂_evalFst (u v : Ω) (g : MvPolynomial (Fin 2) K) :
    Polynomial.eval₂ (algebraMap ↥(adjoin K ({u} : Set Ω)) Ω) v
      (evalFst (K := K) u g) = MvPolynomial.aeval ![u, v] g := by
  have hcomp : ((Polynomial.eval₂RingHom
        (algebraMap ↥(adjoin K ({u} : Set Ω)) Ω) v).comp
      (evalFst (K := K) u).toRingHom) = (MvPolynomial.aeval ![u, v]).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · simp [evalFst, IntermediateField.algebraMap_apply]
    · fin_cases i <;> simp [evalFst]
  exact congrArg (fun (f : MvPolynomial (Fin 2) K →+* Ω) ↦ f g) hcomp

/-- Membership in the vanishing ideal of a plane point, through the
dictionary: `g` vanishes at `(u, v)` iff its partial evaluation at `u`
annihilates `v`.-/
theorem mem_idealOf_iff_evalFst {u v : Ω} {g : MvPolynomial (Fin 2) K} :
    g ∈ idealOf K ![u, v] ↔
      Polynomial.eval₂ (algebraMap ↥(adjoin K ({u} : Set Ω)) Ω) v
        (evalFst (K := K) u g) = 0 := by
  rw [mem_idealOf_iff, eval₂_evalFst]

/-- `evalFst` factors through the variable-separation equivalence: it is the
coefficientwise evaluation of the `Y`-separated form.-/
theorem evalFst_apply_eq (u : Ω) (g : MvPolynomial (Fin 2) K) :
    evalFst (K := K) u g =
      (finSuccEquiv K 1 (rename (Equiv.swap 0 1) g)).map
        (MvPolynomial.aeval
          ![(⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω)))]).toRingHom := by
  have hcomp : (evalFst (K := K) u (Ω := Ω)).toRingHom =
      ((Polynomial.mapRingHom (MvPolynomial.aeval
          ![(⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω)))]).toRingHom).comp
        ((finSuccEquiv K 1 : MvPolynomial (Fin 2) K ≃ₐ[K] _).toRingEquiv.toRingHom.comp
          (rename (Equiv.swap (0 : Fin 2) 1)).toRingHom)) := by
    have hXone : finSuccEquiv K 1 (X (1 : Fin 2)) = Polynomial.C (X 0) := by
      have h := finSuccEquiv_X_succ (R := K) (n := 1) (j := 0)
      simpa using h
    have hC : ∀ c : K, finSuccEquiv K 1 (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) := fun c ↦ by
      simp [finSuccEquiv_apply, eval₂Hom_C]
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · simp [evalFst, hC]
    · fin_cases i
      · have h1 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := by decide
        simp [evalFst, h1, hXone]
      · have h1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by decide
        simp [evalFst, h1, finSuccEquiv_X_zero]
  exact congrArg (fun (f : MvPolynomial (Fin 2) K →+* _) ↦ f g) hcomp

/-- **Degree preservation**: for `u` transcendental over `K`, the partial
evaluation at `u` preserves the degree in the second variable. This is the
count that transfers divisibility bounds between the plane and `K(u)[Y]`.-/
theorem natDegree_evalFst {u : Ω} (hu : Transcendental K u)
    (g : MvPolynomial (Fin 2) K) :
    (evalFst (K := K) u g).natDegree = g.degreeOf 1 := by
  have htr : Transcendental K
      (⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω))) := by
    intro halg
    exact hu (by
      have := (halg.isIntegral.map
        (adjoin K ({u} : Set Ω)).val).isAlgebraic
      simpa using this)
  have hind : AlgebraicIndependent K
      ![(⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω)))] :=
    algebraicIndependent_unique_type_iff.2 htr
  have hinj : Function.Injective (MvPolynomial.aeval
      ![(⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω)))]).toRingHom :=
    hind
  rw [evalFst_apply_eq, Polynomial.natDegree_map_eq_of_injective hinj,
    natDegree_finSuccEquiv]
  have hswap := degreeOf_rename_of_injective
    (Equiv.injective (Equiv.swap (0 : Fin 2) 1)) (p := g) 1
  rw [Equiv.swap_apply_right] at hswap
  exact hswap

/-- `evalFst` is injective when `u` is transcendental over `K`.-/
theorem evalFst_injective {u : Ω} (hu : Transcendental K u) :
    Function.Injective (evalFst (K := K) u) := by
  have htr : Transcendental K
      (⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω))) := by
    intro halg
    exact hu (by
      have := (halg.isIntegral.map (adjoin K ({u} : Set Ω)).val).isAlgebraic
      simpa using this)
  have hind : AlgebraicIndependent K
      ![(⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω)))] :=
    algebraicIndependent_unique_type_iff.2 htr
  intro g₁ g₂ h
  rw [evalFst_apply_eq, evalFst_apply_eq] at h
  have h2 := Polynomial.map_injective _ (hind : Function.Injective _) h
  have h3 := (finSuccEquiv K 1).injective h2
  exact (rename_injective _ (Equiv.injective (Equiv.swap (0 : Fin 2) 1))) h3

/-- The reverse dictionary on generators: substituting `X 0` into a
one-variable polynomial partially evaluates to a constant.-/
theorem evalFst_polyAevalX (u : Ω) (P : Polynomial K) :
    evalFst (K := K) u (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) P) =
      Polynomial.C (Polynomial.aeval
        (⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω))) P) := by
  have hcomp : ((evalFst (K := K) u (Ω := Ω)).comp
      (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K))) =
      ((Polynomial.C : ↥(adjoin K ({u} : Set Ω)) →+* _).comp
        (Polynomial.aeval
          (⟨u, subset_adjoin K _ rfl⟩ : ↥(adjoin K ({u} : Set Ω)))).toRingHom
        : Polynomial K →+* _) := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp [evalFst]
    · simp [evalFst]
  exact congrArg (fun (f : Polynomial K →+* _) ↦ f P) hcomp

/-- Joint evaluation through the `X 0` substitution: the reverse dictionary
is compatible with taking points.-/
theorem aeval_polyAevalX (u v : Ω) (P : Polynomial K) :
    MvPolynomial.aeval ![u, v]
      (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) P) =
      Polynomial.aeval u P := by
  have hcomp : ((MvPolynomial.aeval ![u, v]).comp
      (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K))) =
      (Polynomial.aeval u : Polynomial K →ₐ[K] Ω) := by
    refine Polynomial.algHom_ext ?_
    simp
  exact congrArg (fun (f : Polynomial K →ₐ[K] Ω) ↦ f P) hcomp

/-- **The reverse dictionary**: every one-variable polynomial over the ring
`K[u]` is the partial evaluation of a plane polynomial over `K` whose degree
in the second variable is controlled.-/
theorem exists_evalFst_eq {u : Ω} (hu : Transcendental K u)
    (N : Polynomial ↥(Algebra.adjoin K ({u} : Set Ω))) :
    ∃ W : MvPolynomial (Fin 2) K,
      evalFst (K := K) u W = N.map (Subalgebra.inclusion
        (algebra_adjoin_le_adjoin K ({u} : Set Ω))).toRingHom ∧
      degreeOf 1 W ≤ N.natDegree := by
  classical
  -- Represent each coefficient as a polynomial value at `u`.
  have hrepr : ∀ i : ℕ, ∃ P : Polynomial K,
      Polynomial.aeval u P = (N.coeff i : Ω) := by
    intro i
    have hle := (Algebra.adjoin_singleton_eq_range_aeval K u).le
    exact (AlgHom.mem_range _).1 (hle (N.coeff i).2)
  choose P hP using hrepr
  set W : MvPolynomial (Fin 2) K := ∑ i ∈ Finset.range (N.natDegree + 1),
    Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) (P i) * X 1 ^ i with hW
  have heq : evalFst (K := K) u W = N.map (Subalgebra.inclusion
      (algebra_adjoin_le_adjoin K ({u} : Set Ω))).toRingHom := by
    rw [hW, map_sum]
    have hterm : ∀ i ∈ Finset.range (N.natDegree + 1),
        evalFst (K := K) u
          (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K) (P i) * X 1 ^ i) =
        Polynomial.C ((⟨(N.coeff i : Ω), algebra_adjoin_le_adjoin K _
          (N.coeff i).2⟩ : ↥(adjoin K ({u} : Set Ω)))) * Polynomial.X ^ i := by
      intro i _
      rw [map_mul, map_pow, evalFst_polyAevalX]
      have hXone : evalFst (K := K) u (X 1 : MvPolynomial (Fin 2) K) =
          Polynomial.X := by
        simp [evalFst]
      rw [hXone]
      congr 2
      exact Subtype.ext ((Polynomial.aeval_algHom_apply
        (adjoin K ({u} : Set Ω)).val _ _).symm.trans (hP i))
    rw [Finset.sum_congr rfl hterm]
    -- Compare with the coefficientwise image of `N`.
    ext m
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_congr rfl fun i _ ↦ Polynomial.coeff_C_mul_X_pow _ i m]
    rw [Finset.sum_ite_eq (Finset.range (N.natDegree + 1)) m
      fun i ↦ (⟨(N.coeff i : Ω), algebra_adjoin_le_adjoin K _ (N.coeff i).2⟩ :
        ↥(adjoin K ({u} : Set Ω)))]
    rw [Polynomial.coeff_map]
    by_cases hm : m ∈ Finset.range (N.natDegree + 1)
    · rw [ite_eq_left hm]
      rfl
    · rw [ite_eq_right hm]
      have hm' : N.natDegree < m := by
        by_contra hle
        exact hm (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_not_lt hle)))
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hm', map_zero]
  refine ⟨W, heq, ?_⟩
  rw [← natDegree_evalFst hu W, heq]
  exact Polynomial.natDegree_map_le

end CurveDictionary

section MinimalityCount

open MvPolynomial IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **The minimality count**: if the vanishing ideal of `(u, v)` is generated
by `F`, then the minimal polynomial of `v` over `k(u)` has degree exactly the
`Y`-degree of `F`. Divisibility gives `≤`; for `≥`, clearing denominators
with the integer normalization and lifting through the reverse dictionary
produces a member of the ideal, hence a multiple of `F`, of the minimal
degree.-/
theorem natDegree_minpoly_adjoin {u v : Ω} (hu : Transcendental k u)
    {F : MvPolynomial (Fin 2) k} (hF0 : F ≠ 0)
    (hFspan : idealOf k ![u, v] = Ideal.span {F})
    (hv : IsAlgebraic ↥(adjoin k ({u} : Set Ω)) v) :
    (minpoly ↥(adjoin k ({u} : Set Ω)) v).natDegree = degreeOf 1 F := by
  classical
  set m₀ := minpoly ↥(adjoin k ({u} : Set Ω)) v with hm₀def
  have hm₀ne : m₀ ≠ 0 := minpoly.ne_zero hv.isIntegral
  have hf0 : evalFst (K := k) u F ≠ 0 := fun h ↦
    hF0 (evalFst_injective hu (by rw [h, map_zero]))
  -- (≤): the minimal polynomial divides the partial evaluation of `F`.
  have hFv : F ∈ idealOf k ![u, v] := hFspan ▸ Ideal.subset_span rfl
  have hdvd : m₀ ∣ evalFst (K := k) u F := by
    refine minpoly.dvd _ v ?_
    rw [Polynomial.aeval_def]
    exact mem_idealOf_iff_evalFst.1 hFv
  have hle : m₀.natDegree ≤ degreeOf 1 F := by
    rw [← natDegree_evalFst hu]
    exact Polynomial.natDegree_le_of_dvd hdvd hf0
  -- (≥): clear denominators and lift through the reverse dictionary.
  set N := IsLocalization.integerNormalization
    (nonZeroDivisors ↥(Algebra.adjoin k ({u} : Set Ω))) m₀ with hNdef
  have hNne : N ≠ 0 := fun h0 ↦
    hm₀ne ((IsLocalization.integerNormalization_eq_zero_iff le_rfl m₀).1 h0)
  obtain ⟨W, hWeq, -⟩ := exists_evalFst_eq (K := k) hu N
  have hinclinj : Function.Injective (Subalgebra.inclusion
      (algebra_adjoin_le_adjoin k ({u} : Set Ω))).toRingHom := by
    have h := Subalgebra.inclusion_injective
      (algebra_adjoin_le_adjoin k ({u} : Set Ω))
    exact h
  have hWmem : W ∈ idealOf k ![u, v] := by
    rw [mem_idealOf_iff_evalFst, hWeq, Polynomial.eval₂_map]
    have hg : ((algebraMap ↥(adjoin k ({u} : Set Ω)) Ω).comp
        (Subalgebra.inclusion (algebra_adjoin_le_adjoin k ({u} : Set Ω))).toRingHom) =
        ((algebraMap ↥(adjoin k ({u} : Set Ω)) Ω).comp
          (algebraMap ↥(Algebra.adjoin k ({u} : Set Ω))
            ↥(adjoin k ({u} : Set Ω)))) := by
      refine RingHom.ext fun x ↦ ?_
      rfl
    rw [hg, hNdef]
    refine IsLocalization.integerNormalization_eval₂_eq_zero _ _ m₀ ?_
    rw [← Polynomial.aeval_def]
    exact minpoly.aeval _ v
  rw [hFspan, Ideal.mem_span_singleton] at hWmem
  obtain ⟨H₂, hH₂⟩ := hWmem
  have hWne : W ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hWeq
    exact hNne ((Polynomial.map_eq_zero_iff hinclinj).1 hWeq.symm)
  have hH₂ne : H₂ ≠ 0 := fun h ↦ hWne (by rw [hH₂, h, mul_zero])
  have hNdeg : N.natDegree ≤ m₀.natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    have hnot : i ∉ m₀.support := fun hmem ↦
      (Polynomial.mem_support_iff.1 hmem)
        (Polynomial.coeff_eq_zero_of_natDegree_lt hi)
    have hnotN : i ∉ N.support := fun hmem ↦
      hnot (IsLocalization.integerNormalization_support _ _ hmem)
    exact Polynomial.notMem_support_iff.1 hnotN
  have hge : degreeOf 1 F ≤ m₀.natDegree := by
    calc degreeOf 1 F = (evalFst (K := k) u F).natDegree :=
          (natDegree_evalFst hu F).symm
      _ ≤ (evalFst (K := k) u F).natDegree +
            (evalFst (K := k) u H₂).natDegree := Nat.le_add_right _ _
      _ = (evalFst (K := k) u W).natDegree := by
          rw [hH₂, map_mul, Polynomial.natDegree_mul hf0 fun h ↦
            hH₂ne (evalFst_injective hu (by rw [h, map_zero]))]
      _ ≤ N.natDegree := by
          rw [hWeq]
          exact Polynomial.natDegree_map_le
      _ ≤ m₀.natDegree := hNdeg
  exact le_antisymm hle hge

end MinimalityCount

section Assembly

open MvPolynomial IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Coefficient extension along an injective map preserves the degree in each
variable.-/
theorem degreeOf_map_eq {K : Type*} [Field K] [Algebra k K] (i : Fin 2)
    (F : MvPolynomial (Fin 2) k) :
    degreeOf i (MvPolynomial.map (algebraMap k K) F) = degreeOf i F := by
  have hsupp : (MvPolynomial.map (algebraMap k K) F).support = F.support := by
    refine Finset.ext fun m ↦ ?_
    rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff,
      MvPolynomial.coeff_map]
    exact map_ne_zero_iff _ (algebraMap k K).injective
  rw [degreeOf_eq_sup, degreeOf_eq_sup, hsupp]

/-- Vanishing ideals transform by the variable swap.-/
theorem idealOf_swap_span {u v : Ω} {F : MvPolynomial (Fin 2) k}
    (h : idealOf k ![u, v] = Ideal.span {F}) :
    idealOf k ![v, u] = Ideal.span {rename (Equiv.swap (0 : Fin 2) 1) F} := by
  classical
  have hcomp : ∀ g : MvPolynomial (Fin 2) k,
      MvPolynomial.aeval (![v, u] : Fin 2 → Ω) g =
        MvPolynomial.aeval ![u, v] (rename (Equiv.swap (0 : Fin 2) 1) g) := by
    intro g
    have hfun : ((![u, v] : Fin 2 → Ω) ∘ (Equiv.swap (0 : Fin 2) 1)) = ![v, u] := by
      funext i
      fin_cases i <;> simp
    rw [aeval_rename, hfun]
  have hswapswap : ∀ g : MvPolynomial (Fin 2) k,
      rename (Equiv.swap (0 : Fin 2) 1) (rename (Equiv.swap (0 : Fin 2) 1) g) =
        g := by
    intro g
    rw [rename_rename]
    have hid : ((Equiv.swap (0 : Fin 2) 1) ∘ (Equiv.swap (0 : Fin 2) 1)) = id := by
      funext i
      fin_cases i <;> simp
    rw [hid, rename_id]
    rfl
  ext g
  rw [mem_idealOf_iff, Ideal.mem_span_singleton]
  constructor
  · intro hg
    have hmem : rename (Equiv.swap (0 : Fin 2) 1) g ∈ idealOf k ![u, v] := by
      rw [mem_idealOf_iff, ← hcomp]
      exact hg
    rw [h, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨rename (Equiv.swap (0 : Fin 2) 1) c, ?_⟩
    have := congrArg (rename (Equiv.swap (0 : Fin 2) 1)) hc
    rw [hswapswap, map_mul] at this
    exact this
  · rintro ⟨c, rfl⟩
    rw [hcomp, map_mul, hswapswap F, map_mul]
    have hF0' : MvPolynomial.aeval (![u, v] : Fin 2 → Ω) F = 0 :=
      (mem_idealOf_iff k).1 (h ▸ Ideal.subset_span rfl)
    rw [hF0', zero_mul]

/-- The degree count in the second variable: a cofactor of the extended
generator against the `K`-generator has no `Y`-degree.-/
theorem degreeOf_one_factor_eq_zero [IsAlgClosed k] {K : IntermediateField k Ω}
    {u v : Ω} (hu : Transcendental ↥K u) (hv : v ∈ racl k {u})
    {F : MvPolynomial (Fin 2) k} (hF0 : F ≠ 0)
    (hFspan : idealOf k ![u, v] = Ideal.span {F})
    {G H : MvPolynomial (Fin 2) ↥K}
    (hGspan : idealOf ↥K ![u, v] = Ideal.span {G})
    (hFGH : MvPolynomial.map (algebraMap k ↥K) F = G * H) :
    degreeOf 1 H = 0 := by
  classical
  have huk : Transcendental k u := fun h ↦ hu (h.tower_top ↥K)
  have hvalg : IsAlgebraic ↥(adjoin k ({u} : Set Ω)) v := (mem_racl_iff k).1 hv
  have hFK0 : MvPolynomial.map (algebraMap k ↥K) F ≠ 0 := fun h ↦
    hF0 (MvPolynomial.map_injective _ (algebraMap k ↥K).injective
      (by rw [h, map_zero]))
  have hG0 : G ≠ 0 := fun h ↦ hFK0 (by rw [hFGH, h, zero_mul])
  have hH0 : H ≠ 0 := fun h ↦ hFK0 (by rw [hFGH, h, mul_zero])
  -- The minimal polynomial divides the partial evaluation of `G`.
  have hGv : G ∈ idealOf ↥K ![u, v] := hGspan ▸ Ideal.subset_span rfl
  have hmdvd : minpoly ↥(adjoin ↥K ({u} : Set Ω)) v ∣ evalFst (K := ↥K) u G := by
    refine minpoly.dvd _ v ?_
    rw [Polynomial.aeval_def]
    exact mem_idealOf_iff_evalFst.1 hGv
  have hGne : evalFst (K := ↥K) u G ≠ 0 := fun h ↦
    hG0 (evalFst_injective hu (by rw [h, map_zero]))
  have h1 : (minpoly ↥(adjoin ↥K ({u} : Set Ω)) v).natDegree ≤ degreeOf 1 G := by
    rw [← natDegree_evalFst hu]
    exact Polynomial.natDegree_le_of_dvd hmdvd hGne
  have h2 : (minpoly ↥(adjoin ↥K ({u} : Set Ω)) v).natDegree = degreeOf 1 F := by
    rw [natDegree_minpoly_adjoin_eq hu hvalg]
    exact natDegree_minpoly_adjoin huk hF0 hFspan hvalg
  have hadd : degreeOf 1 (MvPolynomial.map (algebraMap k ↥K) F) =
      degreeOf 1 G + degreeOf 1 H := by
    rw [← natDegree_evalFst hu, hFGH, map_mul,
      Polynomial.natDegree_mul hGne fun h ↦
        hH0 (evalFst_injective hu (by rw [h, map_zero])),
      natDegree_evalFst hu, natDegree_evalFst hu]
  have hFKdeg : degreeOf 1 (MvPolynomial.map (algebraMap k ↥K) F) =
      degreeOf 1 F := degreeOf_map_eq 1 F
  omega

/-- **Base-change irreducibility** (steps 4a/4b of the fused curve-coset
chain): for `k` algebraically closed and a plane point `(u, v)` two-way
generic over the intermediate field `K` and two-way interalgebraic over `k`,
the vanishing ideal over `K` is generated by the extension of the generator
over `k`. In particular the extended generator is prime.-/
theorem idealOf_map_eq_span [IsAlgClosed k] {K : IntermediateField k Ω}
    {u v : Ω} (hu : Transcendental ↥K u) (hv : v ∈ racl k {u})
    (hv' : Transcendental ↥K v) (hu' : u ∈ racl k {v})
    {F : MvPolynomial (Fin 2) k} (hF0 : F ≠ 0)
    (hFspan : idealOf k ![u, v] = Ideal.span {F}) :
    idealOf ↥K ![u, v] =
      Ideal.span {MvPolynomial.map (algebraMap k ↥K) F} := by
  classical
  have hvK : v ∈ racl ↥K {u} := racl_subset_racl_base K {u} hv
  obtain ⟨G, hGp, hGspan⟩ := exists_prime_span_idealOf ↥K hu hvK
  have hFKmem : MvPolynomial.map (algebraMap k ↥K) F ∈ idealOf ↥K ![u, v] := by
    rw [mem_idealOf_iff, MvPolynomial.aeval_map_algebraMap]
    exact (mem_idealOf_iff k).1 (hFspan ▸ Ideal.subset_span rfl)
  obtain ⟨H, hFGH⟩ := Ideal.mem_span_singleton.1 (hGspan ▸ hFKmem)
  have hFK0 : MvPolynomial.map (algebraMap k ↥K) F ≠ 0 := fun h ↦
    hF0 (MvPolynomial.map_injective _ (algebraMap k ↥K).injective
      (by rw [h, map_zero]))
  have hH0 : H ≠ 0 := fun h ↦ hFK0 (by rw [hFGH, h, mul_zero])
  -- Count in the second variable.
  have hcount1 : degreeOf 1 H = 0 :=
    degreeOf_one_factor_eq_zero hu hv hF0 hFspan hGspan hFGH
  -- Count in the first variable, by swapping.
  have hcount0 : degreeOf 0 H = 0 := by
    have hswapF : idealOf k ![v, u] =
        Ideal.span {rename (Equiv.swap (0 : Fin 2) 1) F} := idealOf_swap_span hFspan
    have hswapG : idealOf ↥K ![v, u] =
        Ideal.span {rename (Equiv.swap (0 : Fin 2) 1) G} := idealOf_swap_span hGspan
    have hswapF0 : rename (Equiv.swap (0 : Fin 2) 1) F ≠ 0 := fun h ↦
      hF0 (rename_injective _ (Equiv.injective _) (by rw [h, map_zero]))
    have hswapFGH : MvPolynomial.map (algebraMap k ↥K)
        (rename (Equiv.swap (0 : Fin 2) 1) F) =
        rename (Equiv.swap (0 : Fin 2) 1) G *
          rename (Equiv.swap (0 : Fin 2) 1) H := by
      rw [map_rename, hFGH, map_mul]
    have h1 := degreeOf_one_factor_eq_zero hv' hu' hswapF0 hswapF hswapG hswapFGH
    have h2 := degreeOf_rename_of_injective
      (Equiv.injective (Equiv.swap (0 : Fin 2) 1)) (p := H) 0
    rw [Equiv.swap_apply_left] at h2
    rw [← h2]
    exact h1
  -- The cofactor is a nonzero constant, hence a unit.
  have htot : H.totalDegree = 0 := by
    refine Nat.eq_zero_of_le_zero ?_
    rw [totalDegree_eq]
    refine Finset.sup_le fun m hm ↦ ?_
    have h0 : m 0 = 0 := Nat.eq_zero_of_le_zero
      ((monomial_le_degreeOf 0 hm).trans (le_of_eq hcount0))
    have h1 : m 1 = 0 := Nat.eq_zero_of_le_zero
      ((monomial_le_degreeOf 1 hm).trans (le_of_eq hcount1))
    have hm0 : m = 0 := by
      ext i
      fin_cases i
      · exact h0
      · exact h1
    rw [hm0]
    simp
  have hHC : H = MvPolynomial.C (H.coeff 0) :=
    totalDegree_eq_zero_iff_eq_C.1 htot
  have hc0 : H.coeff 0 ≠ 0 := fun h ↦ hH0 (by rw [hHC, h, map_zero])
  have hHunit : IsUnit H := by
    rw [hHC]
    exact (isUnit_iff_ne_zero.2 hc0).map
      (MvPolynomial.C : ↥K →+* MvPolynomial (Fin 2) ↥K)
  rw [hGspan]
  exact Ideal.span_singleton_eq_span_singleton.2
    ⟨hHunit.unit, by rw [IsUnit.unit_spec]; exact hFGH.symm⟩

end Assembly

end

end AclGeom
