/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.Algebra.MvPolynomial.Funext
import Tengoku.AclGeom.AclGeom.Correspondence.GenericPoints
import Tengoku.AclGeom.AclGeom.Correspondence.AddPolynomial
import Tengoku.AclGeom.AclGeom.Correspondence.CurveIdeal
import Tengoku.AclGeom.AclGeom.Correspondence.BaseChange
import Tengoku.AclGeom.AclGeom.Correspondence.TranslationDescent
import Tengoku.AclGeom.AclGeom.Closure.ClosedLattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The additive correspondence theorem: two-pair core

Two finite correspondences `(x₁, y₁)`, `(x₂, y₂)` over `k`, with independent generic points
and interalgebraic sums, satisfy additive coset equations with common nonzero additive
polynomials. `AddCorrSetup` records the hypotheses. The relocation, prime-curve and Hopf
arguments culminate in `exists_delta_gen_data` and `exists_coset_equations`.

**Status:** the two-pair core is proved with two explicitly supplied fresh elements.
The module `AdditiveThreePair` proves the full blueprint theorem as `AclGeom.addcorr`:
all three pairs and both sum constants, without a freshness
or ambient-rank hypothesis. The abstract subgroup and curve-coset statements remain on #5.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- The hypothesis block of the additive correspondence theorem
(blueprint Thm 8.8, two-pair core): finite correspondences over `k` with
independent generic points and interalgebraic sums.-/
structure AddCorrSetup (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] where
  /-- First coordinate of the first correspondence.-/
  x₁ : Ω
  /-- Second coordinate of the first correspondence.-/
  y₁ : Ω
  /-- First coordinate of the second correspondence.-/
  x₂ : Ω
  /-- Second coordinate of the second correspondence.-/
  y₂ : Ω
  /-- The generic points are independent.-/
  indep : AlgebraicIndependent k ![x₁, x₂]
  /-- The first pair is a finite correspondence: `y₁` is algebraic over `x₁`.-/
  y₁_mem : y₁ ∈ racl k {x₁}
  /-- … and `x₁` is algebraic over `y₁`.-/
  x₁_mem : x₁ ∈ racl k {y₁}
  /-- The second pair is a finite correspondence.-/
  y₂_mem : y₂ ∈ racl k {x₂}
  /-- … in both directions.-/
  x₂_mem : x₂ ∈ racl k {y₂}
  /-- The sums are interalgebraic: `y₁ + y₂` over `x₁ + x₂`.-/
  sum_mem : y₁ + y₂ ∈ racl k {x₁ + x₂}
  /-- … and conversely.-/
  sum_mem' : x₁ + x₂ ∈ racl k {y₁ + y₂}

namespace AddCorrSetup

variable (S : AddCorrSetup k Ω)

/-- The base field of the joint relocation: `k(x₁, y₁)`.-/
def base : IntermediateField k Ω :=
  adjoin k {S.x₁, S.y₁}

/-- The base is contained in the closure of `x₁`.-/
theorem base_le_racl : S.base ≤ racl k {S.x₁} := by
  refine adjoin_le_iff.2 ?_
  rintro z (rfl | rfl)
  · exact subset_racl k _ rfl
  · exact S.y₁_mem

/-- `x₂` is not algebraic over `x₁` (blueprint Lemma 4.2(a) applied to the
independence hypothesis).-/
theorem x₂_notMem : S.x₂ ∉ racl k {S.x₁} :=
  AlgebraicIndependent.notMem_racl_pair S.indep

/-- … and symmetrically.-/
theorem x₁_notMem : S.x₁ ∉ racl k {S.x₂} :=
  AlgebraicIndependent.notMem_racl_pair' S.indep

/-- `x₂` remains transcendental over the enlarged base `k(x₁, y₁)`
(first pregeometry count of the curve-coset chain).-/
theorem transcendental_x₂ : Transcendental ↥S.base S.x₂ := by
  intro halg
  refine S.x₂_notMem ((isRAC_racl {S.x₁}).mem_of_isAlgebraic ?_)
  exact isAlgebraic_of_le S.base_le_racl halg

/-- The second correspondence relation persists over the enlarged base.-/
theorem y₂_mem_baseRacl : S.y₂ ∈ racl ↥S.base {S.x₂} :=
  racl_subset_racl_base S.base {S.x₂} S.y₂_mem

/-- `x₂` is not algebraic over the base, in `racl` form.-/
theorem x₂_notMem_base : S.x₂ ∉ racl k {S.x₁, S.y₁} := fun hmem ↦
  S.transcendental_x₂ ((mem_racl_iff k).1 hmem)

section Relocation

open MvPolynomial

/-- The relation-preservation property produced by `exists_pair_relocation`:
`c₂'` satisfies exactly the joint `k`-polynomial relations with `(x₁, y₁)`
that `(x₂, y₂)` does.-/
def JointRel (c₂' : Fin 2 → Ω) : Prop :=
  ∀ f : MvPolynomial (Fin 2 ⊕ Fin 2) k,
    aeval (Sum.elim ![S.x₁, S.y₁] c₂') f = 0 ↔
      aeval (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂]) f = 0

/-- Joint relocation of the second pair (step 1 of the fused curve-coset
chain, instantiated to the `AddCorrSetup` data): given `s` transcendental over
the base `k(x₁, y₁)`, the pair `(x₂, y₂)` relocates to a pair `c₂'` satisfying
exactly the same joint `k`-polynomial relations with `(x₁, y₁)` and algebraic
over `k(x₁, y₁, s)`.-/
theorem exists_pair_relocation [IsAlgClosed Ω] {s : Ω}
    (hs : Transcendental ↥S.base s) :
    ∃ c₂' : Fin 2 → Ω, S.JointRel c₂' ∧
      ∀ j, IsAlgebraic ↥(adjoin ↥S.base ({s} : Set Ω)) (c₂' j) := by
  have hbase : S.base = adjoin k (Set.range ![S.x₁, S.y₁]) :=
    congrArg (adjoin k) (Matrix.range_cons_cons_empty S.x₁ S.y₁ ![]).symm
  have hx₂ : Transcendental ↥S.base S.x₂ := S.transcendental_x₂
  have hy₂ : S.y₂ ∈ racl ↥S.base {S.x₂} := S.y₂_mem_baseRacl
  rw [hbase] at hs hx₂ hy₂ ⊢
  -- The transcendence basis `![S.x₂]` of the pair over the base.
  have ht : AlgebraicIndependent ↥(adjoin k (Set.range ![S.x₁, S.y₁]))
      ![S.x₂] := algebraicIndependent_unique_type_iff.2 hx₂
  have hs' : AlgebraicIndependent ↥(adjoin k (Set.range ![S.x₁, S.y₁]))
      ![s] := algebraicIndependent_unique_type_iff.2 hs
  have hsub : (Set.range ![S.x₂] : Set Ω) ⊆ Set.range ![S.x₂, S.y₂] := by
    rw [Matrix.range_cons_empty, Matrix.range_cons_cons_empty]
    exact Set.singleton_subset_iff.2 (Set.mem_insert _ _)
  have hle : adjoin ↥(adjoin k (Set.range ![S.x₁, S.y₁])) (Set.range ![S.x₂]) ≤
      adjoin ↥(adjoin k (Set.range ![S.x₁, S.y₁])) (Set.range ![S.x₂, S.y₂]) :=
    adjoin.mono _ _ _ hsub
  -- Everything in the pair is algebraic over the basis.
  have hgen : ∀ x ∈ Set.range ![S.x₂, S.y₂], IsAlgebraic
      ↥(adjoin ↥(adjoin k (Set.range ![S.x₁, S.y₁])) (Set.range ![S.x₂])) x := by
    rw [Matrix.range_cons_empty, Matrix.range_cons_cons_empty]
    rintro x (rfl | rfl)
    · exact isAlgebraic_algebraMap
        (⟨S.x₂, subset_adjoin _ _ rfl⟩ :
          ↥(adjoin ↥(adjoin k (Set.range ![S.x₁, S.y₁])) {S.x₂}))
    · exact (mem_racl_iff _).1 hy₂
  obtain ⟨c₂', hrel, halg⟩ := exists_joint_relocation ![S.x₁, S.y₁] ht hle
    (isAlgebraic_extendScalars_adjoin hle hgen) hs'
  refine ⟨c₂', hrel, fun j ↦ ?_⟩
  have h := halg j
  rwa [Matrix.range_cons_empty] at h

variable {S} {c₂' : Fin 2 → Ω}

/-- A joint relocation has the same joint vanishing ideal.-/
theorem JointRel.idealOf_eq (hrel : S.JointRel c₂') :
    idealOf k (Sum.elim ![S.x₁, S.y₁] c₂') =
      idealOf k (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂]) :=
  idealOf_eq_of_aeval_iff k hrel

/-- The relocated first coordinate stays generic over the base `k(x₁, y₁)`.-/
theorem JointRel.fst_notMem_base (hrel : S.JointRel c₂') :
    c₂' 0 ∉ racl k {S.x₁, S.y₁} := by
  have hv : Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] (Sum.inr 0) ∉ racl k
      (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] '' {Sum.inl 0, Sum.inl 1}) := by
    simpa [Set.image_insert_eq, Set.image_singleton] using S.x₂_notMem_base
  have h := notMem_racl_image_of_idealOf_eq k hrel.idealOf_eq.symm hv
  simpa [Set.image_insert_eq, Set.image_singleton] using h

variable {s : Ω}

/-- Convert the algebraicity output of `exists_pair_relocation` to closure
form over `k`: the relocated coordinates lie in `racl k {x₁, s}` — the
generator `y₁` is absorbed by `y₁ ∈ racl k {x₁}`.-/
theorem racl_pair_of_relocation {z : Ω}
    (halg : IsAlgebraic ↥(adjoin ↥S.base ({s} : Set Ω)) z) :
    z ∈ racl k {S.x₁, s} := by
  have h1 : z ∈ racl k (insert s {S.x₁, S.y₁}) := mem_racl_insert_iff.2 halg
  have hy₁ : S.y₁ ∈ racl k {S.x₁, s} :=
    racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) S.y₁_mem
  have hins : (insert s {S.x₁, S.y₁} : Set Ω) = insert S.y₁ {S.x₁, s} := by
    rw [Set.insert_comm s S.x₁, Set.pair_comm s S.y₁, Set.insert_comm S.x₁ S.y₁]
  rw [hins, racl_insert_of_mem hy₁] at h1
  exact h1

/-- With `s` chosen independent from `{x₁, x₂}`, the relocated first
coordinate stays outside `racl k {x₁, x₂}`: by exchange it is
interalgebraic with `s` over `k(x₁)`.-/
theorem JointRel.fst_notMem_pair (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    c₂' 0 ∉ racl k {S.x₁, S.x₂} := by
  intro hmem
  have h0 : c₂' 0 ∉ racl k {S.x₁} := fun h ↦ hrel.fst_notMem_base
    (racl_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) h)
  have hexch : s ∈ racl k (insert (c₂' 0) {S.x₁}) := by
    refine racl_exchange ?_ h0
    rwa [Set.pair_comm S.x₁ s] at halg
  have hsub : (insert (c₂' 0) {S.x₁} : Set Ω) ⊆ racl k {S.x₁, S.x₂} := by
    rintro z (rfl | rfl)
    · exact hmem
    · exact subset_racl k _ (Set.mem_insert _ _)
  exact hs (racl_le_of_subset_racl hsub hexch)

/-- Triple independence, permuted: `x₁` is not algebraic over `{x₂, x₂'}`.-/
theorem JointRel.x₁_notMem_pair (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₁ ∉ racl k {S.x₂, c₂' 0} := by
  intro hmem
  have hexch : c₂' 0 ∈ racl k (insert S.x₁ {S.x₂}) := by
    refine racl_exchange ?_ S.x₁_notMem
    rwa [Set.pair_comm S.x₂ (c₂' 0)] at hmem
  exact hrel.fst_notMem_pair hs halg hexch

end Relocation

section SumLocus

open MvPolynomial

variable {S} {c₂' : Fin 2 → Ω}

end SumLocus

section TranslationIdentity

open MvPolynomial

/-- The field generated by the translation element `δ = c₂ − c₂'`.-/
def deltaField (S : AddCorrSetup k Ω) (c₂' : Fin 2 → Ω) :
    IntermediateField k Ω :=
  adjoin k {S.x₂ - c₂' 0, S.y₂ - c₂' 1}

/-- The translation element as a vector over `k(δ)`.-/
def deltaVec (S : AddCorrSetup k Ω) (c₂' : Fin 2 → Ω) :
    Fin 2 → ↥(deltaField S c₂') :=
  ![⟨S.x₂ - c₂' 0, subset_adjoin k _ (Set.mem_insert _ _)⟩,
    ⟨S.y₂ - c₂' 1, subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)⟩]

variable {S} {c₂' : Fin 2 → Ω} {s : Ω}

variable {c₂'' : Fin 2 → Ω} {s' : Ω}

/-- First-coordinate specialization of a bivariate polynomial.-/
theorem polynomial_aeval_fst (g : MvPolynomial (Fin 2) k) (u : Ω) :
    Polynomial.aeval u (aeval ![Polynomial.X, (0 : Polynomial k)] g) =
      aeval ![u, 0] g := by
  have hcomp : (Polynomial.aeval u).comp
      (aeval ![Polynomial.X, (0 : Polynomial k)] :
        MvPolynomial (Fin 2) k →ₐ[k] Polynomial k) =
      aeval ![u, (0 : Ω)] := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i <;> simp
  exact congrArg (fun (φ : MvPolynomial (Fin 2) k →ₐ[k] Ω) ↦ φ g) hcomp

/-- Second-coordinate specialization of a bivariate polynomial.-/
theorem polynomial_aeval_snd (g : MvPolynomial (Fin 2) k) (v : Ω) :
    Polynomial.aeval v (aeval ![(0 : Polynomial k), Polynomial.X] g) =
      aeval ![0, v] g := by
  have hcomp : (Polynomial.aeval v).comp
      (aeval ![(0 : Polynomial k), Polynomial.X] :
        MvPolynomial (Fin 2) k →ₐ[k] Polynomial k) =
      aeval ![(0 : Ω), v] := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i <;> simp
  exact congrArg (fun (φ : MvPolynomial (Fin 2) k →ₐ[k] Ω) ↦ φ g) hcomp

end TranslationIdentity

section Endgame

open MvPolynomial

end Endgame

end AddCorrSetup

end

end AclGeom
