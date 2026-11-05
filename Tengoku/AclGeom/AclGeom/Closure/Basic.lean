/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.FieldTheory.AlgebraicClosure
import Tengoku.Seed.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relative algebraic closure as a pregeometry

`racl k S`: elements of `K` algebraic over `k(S)`, built from
`IntermediateField.adjoin` and `algebraicClosure` with restriction of scalars.
This file exposes the carrier-level membership theorem immediately; subsequent
files should almost never unfold the tower of intermediate-field definitions
(blueprint §Foundation I).

Contents (blueprint Prop 4.1):
* `racl` and `mem_racl_iff`, the public membership criterion;
* extensivity (`subset_racl`), monotonicity (`racl_mono`), and
  idempotence (`racl_racl`);
* finite character (`exists_finset_racl`);
* exchange (`isAlgebraic_adjoin_exchange`, `racl_exchange`);
* equivariance (`racl_map`) and power invariance (`racl_image_pow`);
* base monotonicity (`racl_subset_racl_base`);
* the representative calculus, part (a)
  (`algebraicIndependent_iff_forall_notMem_racl`): independence is exactly
  avoidance of the closures of the other members (blueprint Lemma 4.2(a)).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M1).
-/

namespace AclGeom

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

noncomputable section

variable (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K]

/-- The relative algebraic closure of a set `S` in a field extension `K/k`:
the intermediate field of all elements of `K` algebraic over `k(S)`.

Implementation: the relative algebraic closure of `k(S) = adjoin k S` in `K`,
restricted back to a `k`-intermediate field. Do not unfold this; use
`mem_racl_iff`.-/
def racl (S : Set K) : IntermediateField k K :=
  (algebraicClosure (adjoin k S) K).restrictScalars k

/-- The public membership criterion for `racl` (blueprint §Foundation I):
`x ∈ racl k S` iff `x` is algebraic over `k(S)`.
@isnad1 id=iff.0h4v.s7.ec99f74d624a from=translated src=- shape=885a8a59 vocab=f184e079
-/
theorem mem_racl_iff {S : Set K} {x : K} :
    x ∈ racl k S ↔ IsAlgebraic (adjoin k S) x := by
  rw [racl, mem_restrictScalars, mem_algebraicClosure_iff]

/-- Membership in `racl` is equivalently algebraicity over the ring
subalgebra `k[S]`.  This is the fraction-field bridge between the algebraic
matroid API, whose closure uses `Algebra.adjoin`, and the intermediate-field
definition of `racl`.
@isnad1 id=iff.0h4v.s7.3d885de09f09 from=translated src=- shape=38c4106a vocab=df5818ac
-/
theorem mem_racl_iff_isAlgebraic_adjoin {S : Set K} {x : K} :
    x ∈ racl k S ↔ IsAlgebraic (Algebra.adjoin k S) x := by
  rw [mem_racl_iff]
  exact (IsFractionRing.isAlgebraic_iff (Algebra.adjoin k S)
    (adjoin k S) K).symm

/-- `k(S)` is contained in the relative algebraic closure of `S`.
@isnad1 id=le.0h3v.s6.bd26efd1a0f6 from=translated src=- shape=d02e1986 vocab=20f894c0
-/
theorem adjoin_le_racl (S : Set K) : adjoin k S ≤ racl k S := by
  intro x hx
  rw [mem_racl_iff]
  exact isAlgebraic_algebraMap (⟨x, hx⟩ : adjoin k S)

/-- Extensivity: `S ⊆ racl k S`.
@isnad1 id=le.0h3v.s5.4e2140d10667 from=translated src=- shape=e0eccb47 vocab=eeaa97bf
-/
theorem subset_racl (S : Set K) : S ⊆ (racl k S : Set K) :=
  (subset_adjoin k S).trans (adjoin_le_racl k S)

variable {k}

/-- An element annihilated by a nonzero polynomial whose coefficients lie in an
intermediate field `E` is algebraic over `E`.
@isnad1 id=isalgebr.3h5v.s7.fcc8e9215d72 from=translated src=- shape=72a0eda2 vocab=d747064c
-/
theorem isAlgebraic_of_coeff_mem {E : IntermediateField k K} {x : K} {p : Polynomial K}
    (hp : p ≠ 0) (hpx : p.eval x = 0) (hc : ∀ n, p.coeff n ∈ E) : IsAlgebraic E x := by
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts (f := algebraMap E K) p).1 <|
    (Polynomial.lifts_iff_coeff_lifts p).2 fun n ↦ ⟨(⟨p.coeff n, hc n⟩ : E), rfl⟩
  refine ⟨q, fun h0 ↦ hp ?_, ?_⟩
  · rw [← hq, h0, Polynomial.map_zero]
  · rw [Polynomial.aeval_def, ← Polynomial.eval_map, hq, hpx]

/-- Algebraicity over an intermediate field is monotone in the base field.
@isnad1 id=isalgebr.2h5v.s8.cf414d304242 from=translated src=- shape=cb79a776 vocab=b1eaf09c
-/
theorem isAlgebraic_of_le {E₁ E₂ : IntermediateField k K} (h : E₁ ≤ E₂) {x : K}
    (hx : IsAlgebraic E₁ x) : IsAlgebraic E₂ x := by
  obtain ⟨p, hp0, hpx⟩ := hx
  refine isAlgebraic_of_coeff_mem ((Polynomial.map_ne_zero_iff
    (algebraMap E₁ K).injective).2 hp0) ?_ fun n ↦ ?_
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def, hpx]
  · rw [Polynomial.coeff_map]
    exact h (p.coeff n).2

/-- Monotonicity of `racl` in the set argument.
@isnad1 id=le.1h4v.s6.b5a6c87842d7 from=translated src=- shape=c875d1d7 vocab=04722d76
-/
theorem racl_mono {S T : Set K} (h : S ⊆ T) : racl k S ≤ racl k T := fun _ hx ↦
  (mem_racl_iff k).2 (isAlgebraic_of_le (adjoin.mono k S T h) ((mem_racl_iff k).1 hx))

variable (k)

/-- Idempotence: taking `racl` twice gives nothing new (blueprint Prop 4.1).
@isnad1 id=eq.0h3v.s6.8ea8438aee42 from=translated src=- shape=8afabe62 vocab=8b3434cd
-/
theorem racl_racl (S : Set K) : racl k (racl k S : Set K) = racl k S := by
  refine le_antisymm ?_ (fun x hx ↦ (racl_mono (subset_racl k S)) hx)
  intro x hx
  rw [mem_racl_iff, adjoin_self] at hx
  rw [mem_racl_iff]
  -- `x` is algebraic over `racl k S`, which is algebraic over `k(S)`;
  -- conclude by transitivity of integrality. `racl k S` is by definition a
  -- scalar restriction of `algebraicClosure (adjoin k S) K`, with the same
  -- carrier and the same algebra map into `K`, so the hypothesis transports
  -- definitionally.
  have : Algebra.IsIntegral (adjoin k S) (algebraicClosure (adjoin k S) K) :=
    Algebra.IsAlgebraic.isIntegral
  rw [isAlgebraic_iff_isIntegral] at hx ⊢
  have hx' : IsIntegral (algebraicClosure (adjoin k S) K) x := hx
  exact isIntegral_trans x hx'

variable {k}

/-- The closure of a subset of `racl k S` is contained in `racl k S`.
@isnad1 id=le.1h4v.s6.07fd6477bb0e from=translated src=- shape=577780f5 vocab=eeaa97bf
-/
theorem racl_le_of_subset_racl {S T : Set K} (h : T ⊆ racl k S) :
    racl k T ≤ racl k S := by
  rw [← racl_racl k S]
  exact racl_mono h

/-- Absorption: inserting an element of the closure changes nothing.
@isnad1 id=eq.1h4v.s6.ef4e6929770b from=translated src=- shape=3691bc91 vocab=d4ca595c
-/
theorem racl_insert_of_mem {S : Set K} {y : K} (hy : y ∈ racl k S) :
    racl k (insert y S) = racl k S :=
  le_antisymm (racl_le_of_subset_racl (Set.insert_subset hy (subset_racl k S)))
    (racl_mono (Set.subset_insert y S))

/-- A transcendental element avoids the closure of the empty set.
@isnad1 id=not.1h3v.s6.93778ccdf77d from=translated src=- shape=5d2527cf vocab=ebe18cc3
-/
theorem notMem_racl_empty_of_transcendental {x : K} (hx : Transcendental k x) :
    x ∉ racl k (∅ : Set K) := by
  intro hmem
  refine hx ?_
  have halg : IsAlgebraic ↥(adjoin k (∅ : Set K)) x := (mem_racl_iff k).1 hmem
  rw [adjoin_empty] at halg
  haveI : Algebra.IsIntegral k ↥(⊥ : IntermediateField k K) := by
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 z.2
    have hz : z = algebraMap k ↥(⊥ : IntermediateField k K) c :=
      Subtype.ext hc.symm
    rw [hz]
    exact isIntegral_algebraMap
  rw [isAlgebraic_iff_isIntegral] at halg ⊢
  exact isIntegral_trans x halg

/-- Converse companion to `isAlgebraic_of_coeff_mem`: an element algebraic over
an intermediate field `E` is annihilated by a nonzero polynomial over `K` whose
coefficients lie in `E`.
@isnad1 id=ex.1h4v.s8.df306a782d89 from=translated src=- shape=0ed62f28 vocab=d747064c
-/
theorem exists_poly_of_isAlgebraic {E : IntermediateField k K} {x : K}
    (hx : IsAlgebraic E x) :
    ∃ q : Polynomial K, q ≠ 0 ∧ q.eval x = 0 ∧ ∀ n, q.coeff n ∈ E := by
  obtain ⟨p, hp0, hpx⟩ := hx
  refine ⟨p.map (algebraMap E K),
    (Polynomial.map_ne_zero_iff (algebraMap E K).injective).2 hp0, ?_, fun n ↦ ?_⟩
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def, hpx]
  · rw [Polynomial.coeff_map]
    exact (p.coeff n).2

/-- Finite character: an element of `racl k S` already lies in `racl k T` for
some finite `T ⊆ S` (blueprint Prop 4.1).
@isnad1 id=ex.1h4v.s6.7c5cd998aefa from=translated src=- shape=f5944c6e vocab=1997e123
-/
theorem exists_finset_racl {S : Set K} {x : K} (hx : x ∈ racl k S) :
    ∃ T : Finset K, ↑T ⊆ S ∧ x ∈ racl k (T : Set K) := by
  classical
  obtain ⟨q, hq0, hqx, hcoeff⟩ := exists_poly_of_isAlgebraic ((mem_racl_iff k).1 hx)
  -- For each of the finitely many coefficients, collect a finite subset of `S`
  -- generating it.
  choose T hTS hTmem using fun n ↦ exists_finset_of_mem_adjoin (hcoeff n)
  refine ⟨q.support.biUnion T, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, -, hn⟩ := Finset.mem_biUnion.1 hy
    exact hTS n hn
  · rw [mem_racl_iff]
    refine isAlgebraic_of_coeff_mem hq0 hqx fun n ↦ ?_
    by_cases hn : n ∈ q.support
    · exact adjoin.mono _ _ _ (by exact_mod_cast Finset.subset_biUnion_of_mem T hn)
        (hTmem n)
    · simp [Polynomial.notMem_support_iff.1 hn]

section Exchange

open scoped IntermediateField.algebraAdjoinAdjoin

variable {F : Type*} [Field F] [Algebra F K]

/-- Exchange over a base field: if `x` is algebraic over `F(y)` and
transcendental over `F`, then `y` is algebraic over `F(x)`
(the exchange step of blueprint Prop 4.1).
@isnad1 id=isalgebr.2h4v.s8.448c5fb73e0e from=translated src=- shape=c901e19a vocab=a2cb6e3d
-/
theorem isAlgebraic_adjoin_exchange {x y : K}
    (hx : IsAlgebraic (adjoin F {y}) x) (hx' : Transcendental F x) :
    IsAlgebraic (adjoin F {x}) y := by
  by_contra hy
  -- Bridge `¬(algebraic over the field F(x))` down to the ring `F[x]`.
  have hy' : Transcendental (Algebra.adjoin F ({x} : Set K)) y := fun h ↦
    hy ((IsFractionRing.isAlgebraic_iff (Algebra.adjoin F ({x} : Set K)) (adjoin F {x}) K).1 h)
  -- The pair `(y, x)` is then algebraically independent over `F`.
  have hxInd : AlgebraicIndependent F (fun _ : Unit ↦ x) :=
    algebraicIndependent_unique_type_iff.2 hx'
  have hpair : AlgebraicIndependent F (fun o : Option Unit ↦ o.elim y fun _ ↦ x) := by
    refine (hxInd.option_iff_transcendental y).2 ?_
    rwa [Set.range_const]
  -- Swap the pair to `(x, y)` and read the equivalence the other way:
  -- `x` is transcendental over `F[y]`, contradicting `hx`.
  have hfun : ((fun o : Option Unit ↦ o.elim y fun _ ↦ x) ∘ Equiv.swap none (some ())) =
      fun o : Option Unit ↦ o.elim x fun _ ↦ y := by
    funext o
    rcases o with - | -
    · simp
    · simp
  have hswap : AlgebraicIndependent F (fun o : Option Unit ↦ o.elim x fun _ ↦ y) :=
    hfun ▸ hpair.comp (Equiv.swap none (some ())) (Equiv.injective _)
  have hyInd : AlgebraicIndependent F (fun _ : Unit ↦ y) :=
    hswap.comp some (Option.some_injective Unit)
  have hxTr : Transcendental (Algebra.adjoin F (Set.range fun _ : Unit ↦ y)) x :=
    (hyInd.option_iff_transcendental x).1 hswap
  rw [Set.range_const] at hxTr
  exact hxTr
    ((IsFractionRing.isAlgebraic_iff (Algebra.adjoin F ({y} : Set K)) (adjoin F {y}) K).2 hx)

/-- Adjoining then closing collapses a tower step: membership in
`racl k (insert z S)` is algebraicity over `k(S)(z)`.
@isnad1 id=iff.0h5v.s10.f999c8e74d82 from=translated src=- shape=c94b5fc1 vocab=9830cd76
-/
theorem mem_racl_insert_iff {S : Set K} {z x : K} :
    x ∈ racl k (insert z S) ↔
      IsAlgebraic ↥(adjoin ↥(adjoin k S) ({z} : Set K)) x := by
  rw [mem_racl_iff]
  have key : adjoin k (insert z S) =
      (adjoin (adjoin k S) {z}).restrictScalars k := by
    rw [adjoin_adjoin_left, Set.union_singleton]
  rw [key]
  exact ⟨fun h ↦ h, fun h ↦ h⟩

/-- Changing the base from `k` to the field generated by `P` is the same
as adjoining `P` to the closure parameters.  This is the general tower
form of `mem_racl_insert_iff` and is the bridge used to regard a generic
incidence as a finite correspondence over its parameter field.
@isnad1 id=iff.0h5v.s8.e42753521c81 from=translated src=- shape=8c4dc297 vocab=eb49f683
-/
theorem mem_racl_adjoin_base_iff {P S : Set K} {x : K} :
    x ∈ racl ↥(adjoin k P) S ↔ x ∈ racl k (P ∪ S) := by
  rw [mem_racl_iff, mem_racl_iff]
  have key : adjoin k (P ∪ S) =
      (adjoin (adjoin k P) S).restrictScalars k := by
    rw [adjoin_adjoin_left]
  rw [key]
  exact ⟨fun h ↦ h, fun h ↦ h⟩

/-- Exchange for `racl` (blueprint Prop 4.1): if `x ∈ racl k (S ∪ {y})` but
`x ∉ racl k S`, then `y ∈ racl k (S ∪ {x})`.
@isnad1 id=mem.2h5v.s7.2a831f6156bf from=translated src=- shape=b4218451 vocab=d4ca595c
-/
theorem racl_exchange {S : Set K} {x y : K}
    (hxy : x ∈ racl k (insert y S)) (hx : x ∉ racl k S) :
    y ∈ racl k (insert x S) := by
  rw [mem_racl_iff] at hxy hx ⊢
  have key : ∀ z : K, adjoin k (insert z S) =
      (adjoin (adjoin k S) {z}).restrictScalars k := fun z ↦ by
    rw [adjoin_adjoin_left, Set.union_singleton]
  rw [key y] at hxy
  rw [key x]
  -- Transport across `restrictScalars` (definitionally the same carrier and
  -- algebra map into `K`), apply exchange over the base field `adjoin k S`.
  have hxy' : IsAlgebraic (adjoin (adjoin k S) {y}) x := hxy
  have h := isAlgebraic_adjoin_exchange hxy' hx
  exact h

end Exchange

section Equivariance

variable {L : Type*} [Field L] [Algebra k L]

/-- A `k`-algebra isomorphism carries `racl k S` into `racl k (σ '' S)`
(one half of the equivariance in blueprint Prop 4.1). For extensions over
different base fields, transport the algebra structure along the base
isomorphism first.
@isnad1 id=mem.1h6v.s7.556fae4b7b16 from=translated src=- shape=e8a50e18 vocab=4a3657de
-/
theorem mem_racl_map (σ : K ≃ₐ[k] L) {S : Set K} {x : K} (hx : x ∈ racl k S) :
    σ x ∈ racl k (σ '' S) := by
  obtain ⟨q, hq0, hqx, hc⟩ := exists_poly_of_isAlgebraic ((mem_racl_iff k).1 hx)
  rw [mem_racl_iff]
  refine isAlgebraic_of_coeff_mem (p := q.map (σ : K →+* L))
    ((Polynomial.map_ne_zero_iff (σ : K →+* L).injective).2 hq0) ?_ fun n ↦ ?_
  · rw [Polynomial.eval_map,
      show σ x = (σ : K →+* L) x from rfl, Polynomial.eval₂_at_apply, hqx, map_zero]
  · rw [Polynomial.coeff_map]
    have h1 : σ (q.coeff n) ∈ (adjoin k S).map σ.toAlgHom := ⟨q.coeff n, hc n, rfl⟩
    rw [adjoin_map] at h1
    simpa using h1

/-- Equivariance of `racl` (blueprint Prop 4.1): a `k`-algebra isomorphism
maps the relative algebraic closure of `S` onto that of `σ '' S`.
@isnad1 id=eq.0h5v.s7.71c24205b83e from=translated src=- shape=8e8ae32d vocab=9194d645
-/
theorem racl_map (σ : K ≃ₐ[k] L) (S : Set K) :
    (racl k S).map σ.toAlgHom = racl k (σ '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using mem_racl_map σ hx
  · intro hy
    refine ⟨σ.symm y, ?_, by simp⟩
    have h2 := mem_racl_map σ.symm hy
    rwa [show σ.symm '' (σ '' S) = S by rw [← Set.image_comp]; simp] at h2

end Equivariance

section PowerInvariance

end PowerInvariance

section RepresentativeCalculus

open scoped IntermediateField.algebraAdjoinAdjoin

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- Blueprint Lemma 4.2(a): a family is algebraically independent over `k`
iff no member lies in the relative algebraic closure of the others.
@isnad1 id=iff.0h4v.s6.e5d59349d093 from=translated src=- shape=49968593 vocab=5d7b4486
-/
theorem algebraicIndependent_iff_forall_notMem_racl {ι : Type*} {v : ι → K} :
    AlgebraicIndependent k v ↔ ∀ i, v i ∉ racl k (v '' {i}ᶜ) := by
  constructor
  · intro h i hmem
    refine ((AlgebraicIndependent.iff_transcendental_adjoin_image (x := v) i).1 h).2 ?_
    exact (IsFractionRing.isAlgebraic_iff (Algebra.adjoin k (v '' {i}ᶜ))
      (adjoin k (v '' {i}ᶜ)) K).2 ((mem_racl_iff k).1 hmem)
  · intro h
    refine algebraicIndependent_of_finite_type' (algebraMap k K).injective
      fun t _ _ i hit halg ↦ h i ?_
    rw [mem_racl_iff]
    have h2 : IsAlgebraic (adjoin k (v '' t)) (v i) :=
      (IsFractionRing.isAlgebraic_iff (Algebra.adjoin k (v '' t))
        (adjoin k (v '' t)) K).1 halg
    refine isAlgebraic_of_le (adjoin.mono _ _ _ (Set.image_mono ?_)) h2
    exact fun j hj hji ↦ hit (hji ▸ hj)

/-- Chain extension: an independent tuple extends by any element outside
the closure of its range.
@isnad1 id=algebrai.2h5v.s7.b28173d70c85 from=translated src=- shape=5b71131c vocab=bb4431c7
-/
theorem algebraicIndependent_snoc {n : ℕ} {t : Fin n → K}
    (ht : AlgebraicIndependent k t) {z : K}
    (hz : z ∉ racl k (Set.range t)) :
    AlgebraicIndependent k (Fin.snoc t z) := by
  have htr : Transcendental (Algebra.adjoin k (Set.range t)) z := by
    intro halg
    refine hz ?_
    rw [mem_racl_iff]
    exact (IsFractionRing.isAlgebraic_iff (Algebra.adjoin k (Set.range t))
      (adjoin k (Set.range t)) K).1 halg
  have h1 : AlgebraicIndependent k (fun o : Option (Fin n) ↦ o.elim z t) :=
    (AlgebraicIndependent.option_iff_transcendental ht z).2 htr
  have h2 := AlgebraicIndependent.comp h1 finSuccEquivLast
    (Equiv.injective _)
  have heq : ((fun o : Option (Fin n) ↦ o.elim z t) ∘ finSuccEquivLast) =
      Fin.snoc t z := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [finSuccEquivLast_last]
    · simp [finSuccEquivLast_castSucc]
  rwa [heq] at h2

/-- The pair form of blueprint Lemma 4.2(a), forward direction: the second
member of an independent pair is not algebraic over the first.
@isnad1 id=not.1h4v.s6.9dd9bda167eb from=translated src=- shape=4f0964d4 vocab=4789c72c
-/
theorem AlgebraicIndependent.notMem_racl_pair {x y : K}
    (h : AlgebraicIndependent k ![x, y]) : y ∉ racl k {x} := by
  intro hy
  have h1 := algebraicIndependent_iff_forall_notMem_racl.1 h 1
  refine h1 ?_
  refine racl_mono ?_ hy
  intro z hz
  refine ⟨0, ?_, ?_⟩
  · simp
  · simpa using hz.symm

/-- The symmetric pair form of blueprint Lemma 4.2(a): the first member of
an independent pair is not algebraic over the second.
@isnad1 id=not.1h4v.s6.acc2d7e882eb from=translated src=- shape=3fb2688a vocab=4789c72c
-/
theorem AlgebraicIndependent.notMem_racl_pair' {x y : K}
    (h : AlgebraicIndependent k ![x, y]) : x ∉ racl k {y} := by
  intro hx
  have h0 := algebraicIndependent_iff_forall_notMem_racl.1 h 0
  refine h0 ?_
  refine racl_mono ?_ hx
  intro z hz
  refine ⟨1, ?_, ?_⟩
  · simp
  · simpa using hz.symm

end RepresentativeCalculus

section BaseMono

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- Relative algebraic closure is monotone in the base field: enlarging the
base from `k` to an intermediate field `K₀` enlarges the closure.
@isnad1 id=le.0h4v.s7.bf8d759d8f59 from=translated src=- shape=c944269b vocab=eb806782
-/
theorem racl_subset_racl_base (K₀ : IntermediateField k K) (S : Set K) :
    (racl k S : Set K) ⊆ (racl ↥K₀ S : Set K) := by
  intro x hx
  rw [SetLike.mem_coe, mem_racl_iff] at hx
  obtain ⟨q, hq0, hqx, hqc⟩ := exists_poly_of_isAlgebraic hx
  have hsub : (adjoin k S : Set K) ⊆ ((adjoin ↥K₀ S : IntermediateField ↥K₀ K) : Set K) := by
    have hle : adjoin k S ≤ (adjoin ↥K₀ S).restrictScalars k :=
      adjoin_le_iff.2 fun y hy ↦ subset_adjoin ↥K₀ S hy
    exact fun y hy ↦ hle hy
  rw [SetLike.mem_coe, mem_racl_iff]
  exact isAlgebraic_of_coeff_mem (E := adjoin ↥K₀ S) hq0 hqx fun m ↦ hsub (hqc m)

end BaseMono

section Intersection

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- Two independent extensions of a common base intersect in the base: if
`w` is algebraic over both `k(A, a)` and `k(A, b)`, and `b` is not algebraic
over `k(A, a)`, then `w` is algebraic over `k(A)` already.
@isnad1 id=mem.3h6v.s7.b2d713886a96 from=translated src=- shape=011b51f1 vocab=d4ca595c
-/
theorem mem_racl_of_mem_racl_insert {A : Set K} {a b w : K}
    (hwa : w ∈ racl k (insert a A)) (hwb : w ∈ racl k (insert b A))
    (hb : b ∉ racl k (insert a A)) : w ∈ racl k A := by
  by_contra hw
  have hbex : b ∈ racl k (insert w A) := racl_exchange hwb hw
  have hwsub : (insert w A : Set K) ⊆ racl k (insert a A) := by
    rintro z (rfl | hz)
    · exact hwa
    · exact subset_racl k _ (Set.mem_insert_of_mem _ hz)
  exact hb (racl_le_of_subset_racl hwsub hbex)

/-- Elements of `racl k ∅` are algebraic over `k`.
@isnad1 id=isalgebr.1h3v.s6.374f5392175d from=translated src=- shape=48f5ab3d vocab=3ed05bc0
-/
theorem isAlgebraic_of_mem_racl_empty {x : K}
    (hx : x ∈ racl k (∅ : Set K)) : IsAlgebraic k x := by
  by_contra h
  exact notMem_racl_empty_of_transcendental h hx

/-- An element is algebraic over any of its powers.
@isnad1 id=mem.1h4v.s6.6bf9eb1b71ec from=translated src=- shape=1f759459 vocab=dbd0a5e7
-/
theorem mem_racl_singleton_pow {x : K} {n : ℕ} (hn : n ≠ 0) :
    x ∈ racl k {x ^ n} := by
  rw [mem_racl_iff]
  refine ⟨Polynomial.X ^ n - Polynomial.C ⟨x ^ n, subset_adjoin k _ rfl⟩,
    Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) _, ?_⟩
  rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C]
  exact sub_self _

/-- An element is algebraic over any of its integer powers.
@isnad1 id=mem.1h4v.s6.03342cc83112 from=translated src=- shape=1f759459 vocab=f08153d3
-/
theorem mem_racl_singleton_zpow {x : K} {a : ℤ} (ha : a ≠ 0) :
    x ∈ racl k {x ^ a} := by
  rcases a with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact mem_racl_singleton_pow (Int.ofNat_ne_zero.1 ha)
  · rw [zpow_negSucc]
    have hx : x ^ (n + 1) ∈ racl k {(x ^ (n + 1))⁻¹} := by
      have hgen : (x ^ (n + 1))⁻¹ ∈ racl k {(x ^ (n + 1))⁻¹} :=
        subset_racl k _ rfl
    -- The inverse of the generator recovers the power.
      have hinv := inv_mem hgen
      rwa [inv_inv] at hinv
    exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hx)
      (mem_racl_singleton_pow (Nat.succ_ne_zero n))

/-- Algebraicity descends along nonzero integer powers, in `racl` form.
@isnad1 id=mem.2h4v.s6.c1108af46333 from=translated src=- shape=0f657efa vocab=7d61c412
-/
theorem mem_racl_empty_of_zpow {x : K} {a : ℤ} (ha : a ≠ 0)
    (h : x ^ a ∈ racl k (∅ : Set K)) : x ∈ racl k (∅ : Set K) := by
  have h1 : x ∈ racl k {x ^ a} := mem_racl_singleton_zpow ha
  have h2 : racl k ({x ^ a} : Set K) = racl k (∅ : Set K) := by
    have h3 := racl_insert_of_mem (S := (∅ : Set K)) h
    simpa using h3
  rwa [h2] at h1

end Intersection

section SingletonCalculus

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- Mutual membership gives equality of singleton closures.
@isnad1 id=eq.2h4v.s7.9dd8be7337f7 from=translated src=- shape=51ab6b9c vocab=6ed771df
-/
theorem racl_singleton_congr {z w : K} (hzw : z ∈ racl k {w})
    (hwz : w ∈ racl k {z}) : racl k ({z} : Set K) = racl k {w} :=
  le_antisymm (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hzw))
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hwz))

/-- Scaling by a nonzero constant preserves the singleton closure.
@isnad1 id=eq.1h4v.s7.47d0f2d5a9b7 from=translated src=- shape=f590ff0e vocab=9b86998a
-/
theorem racl_algebraMap_mul {e : k} (he : e ≠ 0) (z : K) :
    racl k ({algebraMap k K e * z} : Set K) = racl k {z} := by
  refine racl_singleton_congr ?_ ?_
  · exact MulMemClass.mul_mem (IntermediateField.algebraMap_mem _ _)
      (subset_racl k _ rfl)
  · have hmem : algebraMap k K e⁻¹ * (algebraMap k K e * z) ∈
        racl k ({algebraMap k K e * z} : Set K) :=
      MulMemClass.mul_mem (IntermediateField.algebraMap_mem _ _)
        (subset_racl k _ rfl)
    have h : algebraMap k K e⁻¹ * (algebraMap k K e * z) = z := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one, one_mul]
    rwa [h] at hmem

/-- Translating by a constant preserves the singleton closure.
@isnad1 id=eq.0h4v.s7.9564dd285e2c from=translated src=- shape=f0ff7ba2 vocab=ef1f921d
-/
theorem racl_add_algebraMap (z : K) (e : k) :
    racl k ({z + algebraMap k K e} : Set K) = racl k {z} := by
  refine racl_singleton_congr ?_ ?_
  · exact add_mem (subset_racl k _ rfl) (IntermediateField.algebraMap_mem _ _)
  · have hmem : (z + algebraMap k K e) - algebraMap k K e ∈
        racl k ({z + algebraMap k K e} : Set K) :=
      sub_mem (subset_racl k _ rfl) (IntermediateField.algebraMap_mem _ _)
    rwa [add_sub_cancel_right] at hmem

/-- Adding one preserves the singleton closure.
@isnad1 id=eq.0h3v.s6.363ab162101c from=translated src=- shape=7c9ebbb5 vocab=64f85e5c
-/
theorem racl_one_add (z : K) :
    racl k ({1 + z} : Set K) = racl k {z} := by
  refine racl_singleton_congr ?_ ?_
  · exact add_mem (one_mem _) (subset_racl k _ rfl)
  · have hmem : (1 + z) - 1 ∈ racl k ({1 + z} : Set K) :=
      sub_mem (subset_racl k _ rfl) (one_mem _)
    have h : (1 + z) - 1 = z := by ring
    rwa [h] at hmem

/-- Nonzero powers preserve the singleton closure.
@isnad1 id=eq.1h4v.s6.40da880d7085 from=translated src=- shape=e3e8c87c vocab=8b48203b
-/
theorem racl_pow (z : K) {w : ℕ} (hw : w ≠ 0) :
    racl k ({z ^ w} : Set K) = racl k {z} := by
  have hz : z ∈ racl k ({z} : Set K) := subset_racl k _ rfl
  exact racl_singleton_congr (pow_mem hz w) (mem_racl_singleton_pow hw)

/-- Inversion preserves the singleton closure.
@isnad1 id=eq.0h3v.s6.0a4c898a98bf from=translated src=- shape=1bb7ae6c vocab=11620995
-/
theorem racl_inv (z : K) :
    racl k ({z⁻¹} : Set K) = racl k {z} := by
  refine racl_singleton_congr ?_ ?_
  · exact inv_mem (subset_racl k _ rfl)
  · have hmem : (z⁻¹)⁻¹ ∈ racl k ({z⁻¹} : Set K) :=
      inv_mem (subset_racl k _ rfl)
    rwa [inv_inv] at hmem

/-- Mutual containment of generating sets in each other's closures gives
equality of closures.
@isnad1 id=eq.2h4v.s6.1b9d0854cbe7 from=translated src=- shape=229018b3 vocab=eeaa97bf
-/
theorem racl_congr_of_subset_racl {S T : Set K} (hST : S ⊆ racl k T)
    (hTS : T ⊆ racl k S) : racl k S = racl k T :=
  le_antisymm (racl_le_of_subset_racl hST) (racl_le_of_subset_racl hTS)

/-- Elements algebraic over the base lie in the closure of the empty set —
the converse of `isAlgebraic_of_mem_racl_empty`.
@isnad1 id=mem.1h3v.s6.6bd0bbcfa16c from=translated src=- shape=5ca6b91a vocab=3ed05bc0
-/
theorem mem_racl_empty_of_isAlgebraic {x : K} (hx : IsAlgebraic k x) :
    x ∈ racl k (∅ : Set K) :=
  (mem_racl_iff k).2 (hx.tower_top _)

/-- Closing part of a generating set first does not change the closure.
@isnad1 id=eq.0h4v.s6.8e18459c4452 from=translated src=- shape=681250e2 vocab=a773c1d7
-/
theorem racl_union_left (S T : Set K) :
    racl k ((racl k S : Set K) ∪ T) = racl k (S ∪ T) := by
  refine le_antisymm ?_ ?_
  · have h1 : (racl k S : Set K) ∪ T ⊆ (racl k (S ∪ T) : Set K) := by
      refine Set.union_subset ?_ ?_
      · exact SetLike.coe_subset_coe.2 (racl_mono Set.subset_union_left)
      · exact fun z hz ↦ subset_racl k _ (Set.mem_union_right _ hz)
    calc racl k ((racl k S : Set K) ∪ T)
        ≤ racl k (racl k (S ∪ T) : Set K) := racl_mono h1
      _ = racl k (S ∪ T) := racl_racl _ _
  · refine racl_mono (Set.union_subset_union_left T ?_)
    exact subset_racl k S

/-- Closing part of a generating set first does not change the closure.
@isnad1 id=eq.0h4v.s6.0011fc77a4f9 from=translated src=- shape=c8576dc1 vocab=a773c1d7
-/
theorem racl_union_right (S T : Set K) :
    racl k (S ∪ (racl k T : Set K)) = racl k (S ∪ T) := by
  rw [Set.union_comm S, Set.union_comm S]
  exact racl_union_left T S

/-- Pairwise closure exclusion gives algebraic independence.
@isnad1 id=algebrai.2h4v.s7.c27a5c2b133f from=translated src=- shape=05a46034 vocab=4789c72c
-/
theorem algebraicIndependent_pair {z₁ z₂ : K} (h₁ : z₁ ∉ racl k {z₂})
    (h₂ : z₂ ∉ racl k {z₁}) : AlgebraicIndependent k ![z₁, z₂] := by
  rw [algebraicIndependent_iff_forall_notMem_racl, Fin.forall_fin_two]
  constructor
  · have himg : ((![z₁, z₂] : Fin 2 → K) ''
        ({(0 : Fin 2)}ᶜ : Set (Fin 2))) = {z₂} := by
      have hcompl : ({(0 : Fin 2)}ᶜ : Set (Fin 2)) = {1} := by
        ext i
        fin_cases i <;> simp
      rw [hcompl, Set.image_singleton]
      simp
    rw [himg]
    exact h₁
  · have himg : ((![z₁, z₂] : Fin 2 → K) ''
        ({(1 : Fin 2)}ᶜ : Set (Fin 2))) = {z₁} := by
      have hcompl : ({(1 : Fin 2)}ᶜ : Set (Fin 2)) = {0} := by
        ext i
        fin_cases i <;> simp
      rw [hcompl, Set.image_singleton]
      simp
    rw [himg]
    exact h₂

/-- No member of an independent family is algebraic over any subfamily
avoiding it.
@isnad1 id=not.2h6v.s6.ffdfdf3b2f1f from=translated src=- shape=6750065e vocab=d437fd1f
-/
theorem AlgebraicIndependent.notMem_racl_image {n : ℕ} {v : Fin n → K}
    (hv : AlgebraicIndependent k v) {S : Set (Fin n)} {i : Fin n}
    (hi : i ∉ S) : v i ∉ racl k (v '' S) := by
  intro hmem
  refine algebraicIndependent_iff_forall_notMem_racl.1 hv i ?_
  refine racl_mono (Set.image_mono ?_) hmem
  exact fun j hj hji ↦ hi ((hji : j = i) ▸ hj)

/-- Any two distinct members of an independent family form an independent
pair.
@isnad1 id=algebrai.2h6v.s6.b44265ed4535 from=translated src=- shape=23254597 vocab=dd1bc422
-/
theorem AlgebraicIndependent.comp_pair {n : ℕ} {v : Fin n → K}
    (hv : AlgebraicIndependent k v) {i j : Fin n} (hij : i ≠ j) :
    AlgebraicIndependent k ![v i, v j] := by
  refine algebraicIndependent_pair ?_ ?_
  · have h := AlgebraicIndependent.notMem_racl_image hv (S := {j}) hij
    rwa [Set.image_singleton] at h
  · have h := AlgebraicIndependent.notMem_racl_image hv (S := {i})
      (Ne.symm hij)
    rwa [Set.image_singleton] at h

end SingletonCalculus

end

end AclGeom
