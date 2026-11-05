/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Correspondence.GenericPoints
import Tengoku.AclGeom.AclGeom.Correspondence.CurveIdeal
import Tengoku.AclGeom.AclGeom.Correspondence.BaseChange
import Tengoku.AclGeom.AclGeom.Closure.ClosedLattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The multiplicative correspondence theorem: two-pair core

Two finite correspondences with independent generic points, interalgebraic products and
nonzero coordinates satisfy multiplicative coset equations. Relocation and product-locus
preservation lead to support comparison and `MulCorrSetup.exists_coset_equations`.

**Status:** the core is proved with an explicitly supplied fresh element.
`MultiplicativeLiteral` proves the full blueprint Theorem `mulcorr` as `AclGeom.mulcorr`,
with both nonzero exponents and constants, without a freshness or ambient-rank hypothesis.
The abstract subgroup and curve-coset statements remain separate obligations on #5.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- The hypothesis block of the multiplicative correspondence theorem
(blueprint Thm 8.9, two-pair core): finite correspondences over `k` with
independent generic points, nonzero coordinates, and interalgebraic
products.-/
structure MulCorrSetup (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] where
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
  /-- The second coordinates are nonzero.-/
  y₁_ne : y₁ ≠ 0
  /-- … both of them.-/
  y₂_ne : y₂ ≠ 0
  /-- The first pair is a finite correspondence.-/
  y₁_mem : y₁ ∈ racl k {x₁}
  /-- … in both directions.-/
  x₁_mem : x₁ ∈ racl k {y₁}
  /-- The second pair is a finite correspondence.-/
  y₂_mem : y₂ ∈ racl k {x₂}
  /-- … in both directions.-/
  x₂_mem : x₂ ∈ racl k {y₂}
  /-- The products are interalgebraic: `y₁y₂` over `x₁x₂`.-/
  mul_mem : y₁ * y₂ ∈ racl k {x₁ * x₂}
  /-- … and conversely.-/
  mul_mem' : x₁ * x₂ ∈ racl k {y₁ * y₂}

namespace MulCorrSetup

variable (S : MulCorrSetup k Ω)

/-- The base field of the joint relocation: `k(x₁, y₁)`.-/
def base : IntermediateField k Ω :=
  adjoin k {S.x₁, S.y₁}

/-- The base is contained in the closure of `x₁`.-/
theorem base_le_racl : S.base ≤ racl k {S.x₁} := by
  refine adjoin_le_iff.2 ?_
  rintro z (rfl | rfl)
  · exact subset_racl k _ rfl
  · exact S.y₁_mem

/-- The independence counts, exactly as in the additive setup.-/
theorem x₂_notMem : S.x₂ ∉ racl k {S.x₁} :=
  AlgebraicIndependent.notMem_racl_pair S.indep

/-- … and symmetrically.-/
theorem x₁_notMem : S.x₁ ∉ racl k {S.x₂} :=
  AlgebraicIndependent.notMem_racl_pair' S.indep

/-- The transcendental coordinates are nonzero.-/
theorem x₁_ne : S.x₁ ≠ 0 := by
  intro h
  refine S.x₁_notMem ?_
  rw [h]
  exact zero_mem _

/-- … both of them.-/
theorem x₂_ne : S.x₂ ≠ 0 := by
  intro h
  refine S.x₂_notMem ?_
  rw [h]
  exact zero_mem _

/-- `x₂` remains transcendental over the enlarged base `k(x₁, y₁)`.-/
theorem transcendental_x₂ : Transcendental ↥S.base S.x₂ := by
  intro halg
  refine S.x₂_notMem ((isRAC_racl {S.x₁}).mem_of_isAlgebraic ?_)
  exact isAlgebraic_of_le S.base_le_racl halg

/-- The second correspondence relation persists over the enlarged base.-/
theorem y₂_mem_baseRacl : S.y₂ ∈ racl ↥S.base {S.x₂} :=
  racl_subset_racl_base S.base {S.x₂} S.y₂_mem

/-- The first coordinate of the product correspondence is transcendental:
dividing by `x₁` would otherwise make `x₂` algebraic over `k(x₁)`.-/
theorem mul_fst_transcendental : Transcendental k (S.x₁ * S.x₂) := by
  intro halg
  have hmem : S.x₁ * S.x₂ ∈ racl k {S.x₁} :=
    (mem_racl_iff k).2 (halg.tower_top _)
  have hx₂ : S.x₂ ∈ racl k {S.x₁} := by
    have hdiv := div_mem hmem (subset_racl k ({S.x₁} : Set Ω) rfl)
    have hcancel : S.x₁ * S.x₂ / S.x₁ = S.x₂ := by
      rw [mul_comm, mul_div_assoc, div_self S.x₁_ne, mul_one]
    rwa [hcancel] at hdiv
  exact S.x₂_notMem hx₂

/-- The product pair is a two-way correspondence in the first coordinate.-/
theorem mul_fst_ne : S.x₁ * S.x₂ ≠ 0 :=
  mul_ne_zero S.x₁_ne S.x₂_ne

/-- … and in the second.-/
theorem mul_snd_ne : S.y₁ * S.y₂ ≠ 0 :=
  mul_ne_zero S.y₁_ne S.y₂_ne

section Relocation

open MvPolynomial

/-- The relation-preservation property for the multiplicative chain:
`c₂'` satisfies exactly the joint `k`-polynomial relations with `(x₁, y₁)`
that `(x₂, y₂)` does.-/
def JointRel (c₂' : Fin 2 → Ω) : Prop :=
  ∀ f : MvPolynomial (Fin 2 ⊕ Fin 2) k,
    aeval (Sum.elim ![S.x₁, S.y₁] c₂') f = 0 ↔
      aeval (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂]) f = 0

/-- Joint relocation of the second pair, exactly as in the additive chain:
the construction is independent of the group operation.-/
theorem exists_pair_relocation [IsAlgClosed Ω] {s : Ω}
    (hs : Transcendental ↥S.base s) :
    ∃ c₂' : Fin 2 → Ω, S.JointRel c₂' ∧
      ∀ j, IsAlgebraic ↥(adjoin ↥S.base ({s} : Set Ω)) (c₂' j) := by
  have hbase : S.base = adjoin k (Set.range ![S.x₁, S.y₁]) :=
    congrArg (adjoin k) (Matrix.range_cons_cons_empty S.x₁ S.y₁ ![]).symm
  have hx₂ : Transcendental ↥S.base S.x₂ := S.transcendental_x₂
  have hy₂ : S.y₂ ∈ racl ↥S.base {S.x₂} := S.y₂_mem_baseRacl
  rw [hbase] at hs hx₂ hy₂ ⊢
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

/-- The product pair of a joint relocation is a generic point of the same
product locus (the multiplicative step 2a, instantiated).-/
theorem JointRel.mul_idealOf_eq (hrel : S.JointRel c₂') :
    idealOf k (![S.x₁, S.y₁] * c₂') =
      idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) :=
  idealOf_mul_eq_of_joint hrel

/-- The relocated pair is still a finite correspondence.-/
theorem JointRel.snd_mem (hrel : S.JointRel c₂') : c₂' 1 ∈ racl k {c₂' 0} := by
  have hv : Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] (Sum.inr 1) ∈ racl k
      (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] '' {Sum.inr 0}) := by
    simpa [Set.image_singleton] using S.y₂_mem
  have h := mem_racl_image_of_idealOf_eq k hrel.idealOf_eq.symm hv
  simpa [Set.image_singleton] using h

/-- The relocated product pair is still a two-way correspondence.-/
theorem JointRel.mul_snd_mem (hrel : S.JointRel c₂') :
    S.y₁ * c₂' 1 ∈ racl k {S.x₁ * c₂' 0} := by
  have hv : (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) 1 ∈ racl k
      ((![S.x₁, S.y₁] * ![S.x₂, S.y₂]) '' {(0 : Fin 2)}) := by
    simpa [Set.image_singleton] using S.mul_mem
  have h := mem_racl_image_of_idealOf_eq k hrel.mul_idealOf_eq.symm hv
  simpa [Set.image_singleton] using h

/-- … and conversely.-/
theorem JointRel.mul_fst_mem (hrel : S.JointRel c₂') :
    S.x₁ * c₂' 0 ∈ racl k {S.y₁ * c₂' 1} := by
  have hv : (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) 0 ∈ racl k
      ((![S.x₁, S.y₁] * ![S.x₂, S.y₂]) '' {(1 : Fin 2)}) := by
    simpa [Set.image_singleton] using S.mul_mem'
  have h := mem_racl_image_of_idealOf_eq k hrel.mul_idealOf_eq.symm hv
  simpa [Set.image_singleton] using h

/-- The relocated product coordinate is transcendental.-/
theorem JointRel.mul_fst_transcendental (hrel : S.JointRel c₂') :
    Transcendental k (S.x₁ * c₂' 0) := by
  have hv : Transcendental k ((![S.x₁, S.y₁] * ![S.x₂, S.y₂]) 0) := by
    simpa using S.mul_fst_transcendental
  have h := transcendental_of_idealOf_eq k hrel.mul_idealOf_eq.symm hv
  simpa using h

/-- The relocated coordinates stay nonzero: vanishing is a joint relation.-/
theorem JointRel.fst_ne (hrel : S.JointRel c₂') : c₂' 0 ≠ 0 := by
  intro h0
  have h := (hrel (MvPolynomial.X (Sum.inr 0))).1 (by simp [h0])
  simp at h
  exact S.x₂_ne h

/-- … both of them.-/
theorem JointRel.snd_ne (hrel : S.JointRel c₂') : c₂' 1 ≠ 0 := by
  intro h0
  have h := (hrel (MvPolynomial.X (Sum.inr 1))).1 (by simp [h0])
  simp at h
  exact S.y₂_ne h

variable (S) in
/-- `x₂` is not algebraic over the base, in `racl` form.-/
theorem x₂_notMem_base : S.x₂ ∉ racl k {S.x₁, S.y₁} := fun hmem ↦
  S.transcendental_x₂ ((mem_racl_iff k).1 hmem)

/-- The relocated first coordinate stays generic over the base.-/
theorem JointRel.fst_notMem_base (hrel : S.JointRel c₂') :
    c₂' 0 ∉ racl k {S.x₁, S.y₁} := by
  have hv : Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] (Sum.inr 0) ∉ racl k
      (Sum.elim ![S.x₁, S.y₁] ![S.x₂, S.y₂] '' {Sum.inl 0, Sum.inl 1}) := by
    simpa [Set.image_insert_eq, Set.image_singleton] using S.x₂_notMem_base
  have h := notMem_racl_image_of_idealOf_eq k hrel.idealOf_eq.symm hv
  simpa [Set.image_insert_eq, Set.image_singleton] using h

variable {s : Ω}

variable (S) in
/-- Convert the algebraicity output of `exists_pair_relocation` to closure
form over `k`.-/
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

/-- With `s` independent from `{x₁, x₂}`, the relocated first coordinate
stays outside `racl k {x₁, x₂}`.-/
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

/-- Triple independence, permuted.-/
theorem JointRel.x₁_notMem_pair (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₁ ∉ racl k {S.x₂, c₂' 0} := by
  intro hmem
  have hexch : c₂' 0 ∈ racl k (insert S.x₁ {S.x₂}) := by
    refine racl_exchange ?_ S.x₁_notMem
    rwa [Set.pair_comm S.x₂ (c₂' 0)] at hmem
  exact hrel.fst_notMem_pair hs halg hexch

/-- The ρ-side genericity count: the relocated product coordinate is not
algebraic over the ratio element `ρ = c₂ / c₂'`.-/
theorem JointRel.mul_fst_notMem_rho (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₁ * c₂' 0 ∉ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} := by
  intro hmem
  have hx₂'mem : c₂' 0 ∈ racl k {S.x₂, c₂' 0} :=
    subset_racl k _ (Set.mem_insert_iff.2 (Or.inr rfl))
  have hy₂'mem : c₂' 1 ∈ racl k {S.x₂, c₂' 0} := by
    refine racl_le_of_subset_racl ?_ hrel.snd_mem
    rintro z rfl
    exact hx₂'mem
  have hy₂mem : S.y₂ ∈ racl k {S.x₂, c₂' 0} := by
    refine racl_le_of_subset_racl ?_ S.y₂_mem
    rintro z rfl
    exact subset_racl k _ (Set.mem_insert _ _)
  have hρsub : ({S.x₂ / c₂' 0, S.y₂ / c₂' 1} : Set Ω) ⊆
      racl k {S.x₂, c₂' 0} := by
    rintro z (rfl | rfl)
    · exact div_mem (subset_racl k _ (Set.mem_insert _ _)) hx₂'mem
    · exact div_mem hy₂mem hy₂'mem
  have hmul : S.x₁ * c₂' 0 ∈ racl k {S.x₂, c₂' 0} :=
    racl_le_of_subset_racl hρsub hmem
  have hx₁ : S.x₁ ∈ racl k {S.x₂, c₂' 0} := by
    have hdiv := div_mem hmul hx₂'mem
    have hcancel : S.x₁ * c₂' 0 / c₂' 0 = S.x₁ := by
      rw [mul_div_assoc, div_self hrel.fst_ne, mul_one]
    rwa [hcancel] at hdiv
  exact hrel.x₁_notMem_pair hs halg hx₁

end Relocation

section ProductLocus

open MvPolynomial

/-- The product locus is a plane curve: its vanishing ideal is generated by
a single prime polynomial (the curve-ideal brick applied to the product
pair).-/
theorem exists_prime_span_mul :
    ∃ F : MvPolynomial (Fin 2) k, Prime F ∧
      idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) = Ideal.span {F} := by
  have hconv : ![S.x₁, S.y₁] * ![S.x₂, S.y₂] = ![S.x₁ * S.x₂, S.y₁ * S.y₂] := by
    funext i
    fin_cases i <;> rfl
  rw [hconv]
  exact exists_prime_span_idealOf k S.mul_fst_transcendental S.mul_mem

variable {S} {c₂' : Fin 2 → Ω}

end ProductLocus

section ScalingIdentity

open MvPolynomial

/-- The field generated by the ratio element `ρ = c₂ / c₂'`.-/
def rhoField (S : MulCorrSetup k Ω) (c₂' : Fin 2 → Ω) :
    IntermediateField k Ω :=
  adjoin k {S.x₂ / c₂' 0, S.y₂ / c₂' 1}

/-- The ratio element as a vector over `k(ρ)`.-/
def rhoVec (S : MulCorrSetup k Ω) (c₂' : Fin 2 → Ω) :
    Fin 2 → ↥(rhoField S c₂') :=
  ![⟨S.x₂ / c₂' 0, subset_adjoin k _ (Set.mem_insert _ _)⟩,
    ⟨S.y₂ / c₂' 1, subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)⟩]

variable {S} {c₂' : Fin 2 → Ω} {s : Ω}

/-- The unrelocated product coordinate is also transcendental over `k(ρ)`
(dividing by `ρ₁` moves between the two product points).-/
theorem JointRel.mul_fst_notMem_rho' (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.x₁ * S.x₂ ∉ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} := by
  intro hmem
  have hρ₁ : S.x₂ / c₂' 0 ∈ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} :=
    subset_racl k _ (Set.mem_insert _ _)
  have h2 : S.x₁ * c₂' 0 ∈ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} := by
    have h3 := div_mem hmem hρ₁
    have h4 : S.x₁ * S.x₂ / (S.x₂ / c₂' 0) = S.x₁ * c₂' 0 := by
      rw [div_div_eq_mul_div, mul_right_comm, mul_div_assoc, div_self S.x₂_ne,
        mul_one]
    rwa [h4] at h3
  exact hrel.mul_fst_notMem_rho hs halg h2

/-- The unrelocated product's second coordinate is also transcendental over
`k(ρ)`.-/
theorem JointRel.mul_snd_notMem_rho' (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.y₁ * S.y₂ ∉ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} := fun hmem ↦
  hrel.mul_fst_notMem_rho' hs halg
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem) S.mul_mem')

/-- … and the relocated product's second coordinate.-/
theorem JointRel.mul_snd_notMem_rho (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s}) :
    S.y₁ * c₂' 1 ∉ racl k {S.x₂ / c₂' 0, S.y₂ / c₂' 1} := fun hmem ↦
  hrel.mul_fst_notMem_rho hs halg
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 hmem) hrel.mul_fst_mem)

/-- **The exact scaling identity** (the multiplicative chain assembled
through step 4): the extension to `k(ρ)` of the product-locus generator has
its span fixed by the scaling substitution by `ρ = c₂ / c₂'`, so by scaling
rigidity the monomial values of `ρ` agree across its support — the
`ρ^(m−m') = 1` relations feeding the exponent-lattice classification.-/
theorem JointRel.monomial_prod_rhoVec_eq [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hF0 : F ≠ 0)
    (hFspan : idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) = Ideal.span {F}) :
    ∀ m ∈ (MvPolynomial.map (algebraMap k ↥(rhoField S c₂')) F).support,
      ∀ m' ∈ (MvPolynomial.map (algebraMap k ↥(rhoField S c₂')) F).support,
        (m.prod fun j e ↦ rhoVec S c₂' j ^ e) =
          (m'.prod fun j e ↦ rhoVec S c₂' j ^ e) := by
  classical
  set FK := MvPolynomial.map (algebraMap k ↥(rhoField S c₂')) F with hFK
  -- Genericity of the original product point over `k(ρ)`.
  have hu : Transcendental ↥(rhoField S c₂') (S.x₁ * S.x₂) := fun h ↦
    hrel.mul_fst_notMem_rho' hs halg ((mem_racl_iff k).2 h)
  have hv' : Transcendental ↥(rhoField S c₂') (S.y₁ * S.y₂) := fun h ↦
    hrel.mul_snd_notMem_rho' hs halg ((mem_racl_iff k).2 h)
  -- The span at the clean product tuple.
  have hconv : ![S.x₁, S.y₁] * ![S.x₂, S.y₂] = ![S.x₁ * S.x₂, S.y₁ * S.y₂] := by
    funext i
    fin_cases i <;> rfl
  rw [hconv] at hFspan
  have hspan_d : idealOf ↥(rhoField S c₂') ![S.x₁ * S.x₂, S.y₁ * S.y₂] =
      Ideal.span {FK} :=
    idealOf_map_eq_span hu S.mul_mem hv' S.mul_mem' hF0 hFspan
  -- Genericity of the relocated product point over `k(ρ)`, and its span.
  have hud' : Transcendental ↥(rhoField S c₂') (S.x₁ * c₂' 0) := fun h ↦
    hrel.mul_fst_notMem_rho hs halg ((mem_racl_iff k).2 h)
  have hvd'' : Transcendental ↥(rhoField S c₂') (S.y₁ * c₂' 1) := fun h ↦
    hrel.mul_snd_notMem_rho hs halg ((mem_racl_iff k).2 h)
  have hFspan_d' : idealOf k ![S.x₁ * c₂' 0, S.y₁ * c₂' 1] = Ideal.span {F} := by
    have h1 := hrel.mul_idealOf_eq
    have hconv' : ![S.x₁, S.y₁] * c₂' = ![S.x₁ * c₂' 0, S.y₁ * c₂' 1] := by
      funext i
      fin_cases i <;> simp
    rw [hconv', hconv] at h1
    rw [h1, hFspan]
  have hspan_d' : idealOf ↥(rhoField S c₂') ![S.x₁ * c₂' 0, S.y₁ * c₂' 1] =
      Ideal.span {FK} :=
    idealOf_map_eq_span hud' hrel.mul_snd_mem hvd'' hrel.mul_fst_mem hF0
      hFspan_d'
  -- Transport the `d`-span along the scaling and compare with the `d'`-span.
  have hρne : ∀ j, rhoVec S c₂' j ≠ 0 := by
    intro j
    fin_cases j
    · exact fun h0 ↦
        div_ne_zero S.x₂_ne hrel.fst_ne (congrArg Subtype.val h0)
    · exact fun h0 ↦
        div_ne_zero S.y₂_ne hrel.snd_ne (congrArg Subtype.val h0)
  have htrans := idealOf_scale_span (c := rhoVec S c₂') hρne hspan_d
  have htuple : (fun j ↦ (![S.x₁ * S.x₂, S.y₁ * S.y₂] : Fin 2 → Ω) j /
      algebraMap ↥(rhoField S c₂') Ω (rhoVec S c₂' j)) =
      ![S.x₁ * c₂' 0, S.y₁ * c₂' 1] := by
    funext j
    fin_cases j
    · show S.x₁ * S.x₂ / (S.x₂ / c₂' 0) = S.x₁ * c₂' 0
      rw [div_div_eq_mul_div, mul_right_comm, mul_div_assoc, div_self S.x₂_ne,
        mul_one]
    · show S.y₁ * S.y₂ / (S.y₂ / c₂' 1) = S.y₁ * c₂' 1
      rw [div_div_eq_mul_div, mul_right_comm, mul_div_assoc, div_self S.y₂_ne,
        mul_one]
  rw [htuple, hspan_d'] at htrans
  have hFK0 : FK ≠ 0 := fun h ↦ hF0 (MvPolynomial.map_injective _
    (algebraMap k ↥(rhoField S c₂')).injective (by rw [map_zero]; exact h))
  exact monomial_prod_eq_of_span_scale_eq hρne hFK0 htrans.symm

/-- The Ω-level form of the exact scaling identity: at any two support
monomials of the generator, the ratio element satisfies the same monomial
value.-/
theorem JointRel.rho_pow_support_eq [IsAlgClosed k] (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hF0 : F ≠ 0)
    (hFspan : idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) = Ideal.span {F})
    {m m' : Fin 2 →₀ ℕ} (hm : m ∈ F.support) (hm' : m' ∈ F.support) :
    (S.x₂ / c₂' 0) ^ m 0 * (S.y₂ / c₂' 1) ^ m 1 =
      (S.x₂ / c₂' 0) ^ m' 0 * (S.y₂ / c₂' 1) ^ m' 1 := by
  have hsupmap : (MvPolynomial.map (algebraMap k ↥(rhoField S c₂')) F).support
      = F.support :=
    support_map_of_injective F (algebraMap k ↥(rhoField S c₂')).injective
  have hrelmon := hrel.monomial_prod_rhoVec_eq hs halg hF0 hFspan m
    (hsupmap ▸ hm) m' (hsupmap ▸ hm')
  have hval := congrArg (rhoField S c₂').val hrelmon
  have hconv : ∀ mm : Fin 2 →₀ ℕ,
      (rhoField S c₂').val (mm.prod fun j e ↦ rhoVec S c₂' j ^ e) =
        (S.x₂ / c₂' 0) ^ mm 0 * (S.y₂ / c₂' 1) ^ mm 1 := by
    intro mm
    rw [Finsupp.prod_fintype _ _ fun j ↦ pow_zero _, Fin.prod_univ_two,
      map_mul, map_pow, map_pow]
    rfl
  rwa [hconv, hconv] at hval

/-- The `ℤ`-exponent form: the support difference kills the ratio element,
`ρ^(m−m') = 1`.-/
theorem JointRel.zpow_rho_support_eq_one [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hF0 : F ≠ 0)
    (hFspan : idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) = Ideal.span {F})
    {m m' : Fin 2 →₀ ℕ} (hm : m ∈ F.support) (hm' : m' ∈ F.support) :
    (S.x₂ / c₂' 0) ^ ((m 0 : ℤ) - m' 0) *
      (S.y₂ / c₂' 1) ^ ((m 1 : ℤ) - m' 1) = 1 := by
  have hρ₀ : S.x₂ / c₂' 0 ≠ 0 := div_ne_zero S.x₂_ne hrel.fst_ne
  have hρ₁ : S.y₂ / c₂' 1 ≠ 0 := div_ne_zero S.y₂_ne hrel.snd_ne
  have h := hrel.rho_pow_support_eq hs halg hF0 hFspan hm hm'
  rw [zpow_sub₀ hρ₀, zpow_sub₀ hρ₁, zpow_natCast, zpow_natCast,
    zpow_natCast, zpow_natCast, div_mul_div_comm, h, div_self]
  exact mul_ne_zero (pow_ne_zero _ hρ₀) (pow_ne_zero _ hρ₁)

/-- Intermediate fields are closed under integer powers (helper avoiding a
slow instance search).-/
theorem zpow_mem_racl {A : Set Ω} {x : Ω} (hx : x ∈ racl k A)
    (n : ℤ) : x ^ n ∈ racl k A := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hx n
  · rw [zpow_negSucc]
    exact inv_mem (pow_mem hx (n + 1))

/-- **Relocation invariance of monomial values** (the coset-constant step):
any support-difference monomial value of the product point is fixed by the
relocation, hence algebraic over every side of the independence, hence in
`k`.-/
theorem JointRel.exists_algebraMap_eq_zpow_mul [IsAlgClosed k]
    (hrel : S.JointRel c₂')
    (hs : s ∉ racl k {S.x₁, S.x₂}) (halg : c₂' 0 ∈ racl k {S.x₁, s})
    {F : MvPolynomial (Fin 2) k} (hF0 : F ≠ 0)
    (hFspan : idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) = Ideal.span {F})
    {m m' : Fin 2 →₀ ℕ} (hm : m ∈ F.support) (hm' : m' ∈ F.support) :
    ∃ c : k, c ≠ 0 ∧
      (S.x₁ * S.x₂) ^ ((m 0 : ℤ) - m' 0) *
        (S.y₁ * S.y₂) ^ ((m 1 : ℤ) - m' 1) = algebraMap k Ω c := by
  set a : ℤ := (m 0 : ℤ) - m' 0 with ha
  set b : ℤ := (m 1 : ℤ) - m' 1 with hb
  set μ : Ω := (S.x₁ * S.x₂) ^ a * (S.y₁ * S.y₂) ^ b with hμ
  -- Nonvanishing of all the bases.
  have hx₂' : c₂' 0 ≠ 0 := hrel.fst_ne
  have hy₂' : c₂' 1 ≠ 0 := hrel.snd_ne
  have hμ0 : μ ≠ 0 := mul_ne_zero (zpow_ne_zero _ S.mul_fst_ne)
    (zpow_ne_zero _ S.mul_snd_ne)
  -- Invariance: μ is also the monomial value of the relocated product point.
  have hxconv : S.x₁ * c₂' 0 * (S.x₂ / c₂' 0) = S.x₁ * S.x₂ := by
    rw [mul_assoc, mul_comm (c₂' 0), div_mul_cancel₀ _ hx₂']
  have hyconv : S.y₁ * c₂' 1 * (S.y₂ / c₂' 1) = S.y₁ * S.y₂ := by
    rw [mul_assoc, mul_comm (c₂' 1), div_mul_cancel₀ _ hy₂']
  have hsplit : μ = ((S.x₁ * c₂' 0) ^ a * (S.y₁ * c₂' 1) ^ b) *
      ((S.x₂ / c₂' 0) ^ a * (S.y₂ / c₂' 1) ^ b) := by
    rw [hμ, mul_mul_mul_comm ((S.x₁ * c₂' 0) ^ a), ← mul_zpow, ← mul_zpow,
      hxconv, hyconv]
  have hinv : μ = (S.x₁ * c₂' 0) ^ a * (S.y₁ * c₂' 1) ^ b := by
    rw [hsplit, hrel.zpow_rho_support_eq_one hs halg hF0 hFspan hm hm',
      mul_one]
  -- μ is algebraic over both independent sides.
  have hmem₁ : μ ∈ racl k {S.x₂, S.x₁} := by
    have hx₁m : S.x₁ ∈ racl k {S.x₂, S.x₁} :=
      subset_racl k _ (Set.mem_insert_iff.2 (Or.inr rfl))
    have hx₂m : S.x₂ ∈ racl k {S.x₂, S.x₁} :=
      subset_racl k _ (Set.mem_insert _ _)
    have hx : S.x₁ * S.x₂ ∈ racl k {S.x₂, S.x₁} :=
      MulMemClass.mul_mem hx₁m hx₂m
    have hy : S.y₁ * S.y₂ ∈ racl k {S.x₂, S.x₁} := by
      refine MulMemClass.mul_mem ?_ ?_
      · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hx₁m) S.y₁_mem
      · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 hx₂m) S.y₂_mem
    exact MulMemClass.mul_mem (zpow_mem_racl hx a) (zpow_mem_racl hy b)
  have hmem₂ : μ ∈ racl k {s, S.x₁} := by
    have hx₂'r : c₂' 0 ∈ racl k {s, S.x₁} := by
      rwa [Set.pair_comm s S.x₁]
    have hy₂'r : c₂' 1 ∈ racl k {s, S.x₁} :=
      racl_le_of_subset_racl (Set.singleton_subset_iff.2 hx₂'r) hrel.snd_mem
    have hx₁r : S.x₁ ∈ racl k {s, S.x₁} :=
      subset_racl k _ (Set.mem_insert_iff.2 (Or.inr rfl))
    have hy₁r : S.y₁ ∈ racl k {s, S.x₁} :=
      racl_le_of_subset_racl (Set.singleton_subset_iff.2 hx₁r) S.y₁_mem
    rw [hinv]
    exact MulMemClass.mul_mem
      (zpow_mem_racl (MulMemClass.mul_mem hx₁r hx₂'r) a)
      (zpow_mem_racl (MulMemClass.mul_mem hy₁r hy₂'r) b)
  -- Descend to `racl k {x₁}`, then to `racl k ∅`, then to `k`.
  have hmemx₁ : μ ∈ racl k {S.x₁} := by
    refine mem_racl_of_mem_racl_insert (a := S.x₂) (b := s) hmem₁ hmem₂ ?_
    rwa [Set.pair_comm S.x₁ S.x₂] at hs
  have hins₁ : (insert S.x₁ (∅ : Set Ω)) = {S.x₁} := by simp
  have hins₂ : (insert (S.x₁ * S.x₂) (∅ : Set Ω)) = {S.x₁ * S.x₂} := by simp
  have hmemempty : μ ∈ racl k (∅ : Set Ω) := by
    -- `x₁x₂` is not algebraic over `x₁` alone …
    have hx₁x₂ : S.x₁ * S.x₂ ∉ racl k (insert S.x₁ (∅ : Set Ω)) := by
      rw [hins₁]
      intro hmem
      have hx₁m : S.x₁ ∈ racl k {S.x₁} := subset_racl k _ rfl
      have hdiv := div_mem hmem hx₁m
      rw [mul_div_cancel_left₀ _ S.x₁_ne] at hdiv
      exact S.x₂_notMem hdiv
    -- … and μ is algebraic over `x₁x₂` alone.
    have hμx₂ : μ ∈ racl k (insert (S.x₁ * S.x₂) (∅ : Set Ω)) := by
      rw [hins₂]
      have hxm : S.x₁ * S.x₂ ∈ racl k {S.x₁ * S.x₂} := subset_racl k _ rfl
      have hym : S.y₁ * S.y₂ ∈ racl k {S.x₁ * S.x₂} :=
        racl_le_of_subset_racl (Set.singleton_subset_iff.2 hxm) S.mul_mem
      exact MulMemClass.mul_mem (zpow_mem_racl hxm a) (zpow_mem_racl hym b)
    -- `x₁` transcendental keeps the two directions independent.
    have hx₁empty : S.x₁ ∉ racl k (∅ : Set Ω) := fun h ↦
      S.x₁_notMem (racl_mono (Set.empty_subset _) h)
    refine mem_racl_of_mem_racl_insert (a := S.x₁ * S.x₂) (b := S.x₁)
      hμx₂ ?_ ?_
    · rw [hins₁]
      exact hmemx₁
    · intro hmem
      exact hx₁x₂ (racl_exchange hmem hx₁empty)
  have halgμ : IsAlgebraic k μ := isAlgebraic_of_mem_racl_empty hmemempty
  obtain ⟨c, hc⟩ := mem_range_algebraMap_of_isAlgebraic halgμ
  refine ⟨c, fun h0 ↦ ?_, hc.symm⟩
  rw [h0, map_zero] at hc
  exact hμ0 hc.symm

end ScalingIdentity

section Endgame

open MvPolynomial

/-- **The multiplicative correspondence theorem** (blueprint Theorem 8.9):
two finite correspondences with independent generic points and
interalgebraic products satisfy multiplicative coset equations
`x_i^a y_i^b = c_i` with common nonzero integer exponents and nonzero
constants from `k`. The exponents arise as a support difference of the
product-locus generator; the constants are the relocation-invariant
monomial values, split along the independence of the two pairs.-/
theorem exists_coset_equations [IsAlgClosed k] [IsAlgClosed Ω] {s : Ω}
    (hs : s ∉ racl k {S.x₁, S.x₂}) :
    ∃ (a b : ℤ) (c₁ c₂ : k), a ≠ 0 ∧ b ≠ 0 ∧ c₁ ≠ 0 ∧ c₂ ≠ 0 ∧
      S.x₁ ^ a * S.y₁ ^ b = algebraMap k Ω c₁ ∧
      S.x₂ ^ a * S.y₂ ^ b = algebraMap k Ω c₂ := by
  classical
  -- The fresh element is transcendental over the base `k(x₁, y₁)`.
  have hsbase : s ∉ racl k {S.x₁, S.y₁} := by
    intro hmem
    refine hs (racl_le_of_subset_racl ?_ hmem)
    rintro z (rfl | rfl)
    · exact subset_racl k _ (Set.mem_insert _ _)
    · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2
        (subset_racl k _ (Set.mem_insert _ _))) S.y₁_mem
  have hstr : Transcendental ↥S.base s := fun halg ↦
    hsbase ((mem_racl_iff k).2 halg)
  -- Relocate, and pick up the product-locus generator.
  obtain ⟨c₂', hrel, halgrel⟩ := S.exists_pair_relocation hstr
  have halg : c₂' 0 ∈ racl k {S.x₁, s} :=
    S.racl_pair_of_relocation (halgrel 0)
  obtain ⟨F, hFp, hFspan⟩ := S.exists_prime_span_mul
  -- Two distinct support monomials give the exponents.
  have hFmem : F ∈ idealOf k (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) := by
    rw [hFspan]
    exact Ideal.subset_span rfl
  have hv0 : ∀ j, (![S.x₁, S.y₁] * ![S.x₂, S.y₂]) j ≠ 0 := by
    intro j
    fin_cases j
    · exact S.mul_fst_ne
    · exact S.mul_snd_ne
  obtain ⟨m, hm, m', hm', hmne⟩ := exists_support_pair_of_aeval_eq_zero hv0
    hFp.ne_zero ((mem_idealOf_iff _).1 hFmem)
  set a : ℤ := (m 0 : ℤ) - m' 0 with ha
  set b : ℤ := (m 1 : ℤ) - m' 1 with hb
  have hab : ¬(a = 0 ∧ b = 0) := by
    rintro ⟨ha0, hb0⟩
    rw [ha, sub_eq_zero] at ha0
    rw [hb, sub_eq_zero] at hb0
    exact hmne (Finsupp.ext (Fin.forall_fin_two.2
      ⟨by exact_mod_cast ha0, by exact_mod_cast hb0⟩))
  -- The invariant monomial value of the product point.
  obtain ⟨c, hc0, hc⟩ := hrel.exists_algebraMap_eq_zpow_mul hs halg
    hFp.ne_zero hFspan hm hm'
  -- Split along the independence of the two pairs.
  have hμν : (S.x₁ * S.x₂) ^ a * (S.y₁ * S.y₂) ^ b =
      (S.x₁ ^ a * S.y₁ ^ b) * (S.x₂ ^ a * S.y₂ ^ b) := by
    rw [mul_zpow, mul_zpow, mul_mul_mul_comm]
  have hν₁ne : S.x₁ ^ a * S.y₁ ^ b ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ S.x₁_ne) (zpow_ne_zero _ S.y₁_ne)
  have hν₂ne : S.x₂ ^ a * S.y₂ ^ b ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ S.x₂_ne) (zpow_ne_zero _ S.y₂_ne)
  have hx₁self : S.x₁ ∈ racl k {S.x₁} := subset_racl k _ rfl
  have hx₂self : S.x₂ ∈ racl k {S.x₂} := subset_racl k _ rfl
  have hν₁mem₁ : S.x₁ ^ a * S.y₁ ^ b ∈ racl k {S.x₁} :=
    MulMemClass.mul_mem (zpow_mem_racl hx₁self a) (zpow_mem_racl S.y₁_mem b)
  have hν₁eq : S.x₁ ^ a * S.y₁ ^ b =
      algebraMap k Ω c / (S.x₂ ^ a * S.y₂ ^ b) := by
    rw [eq_div_iff hν₂ne, ← hμν]
    exact hc
  have hν₁mem₂ : S.x₁ ^ a * S.y₁ ^ b ∈ racl k {S.x₂} := by
    rw [hν₁eq]
    refine div_mem (IntermediateField.algebraMap_mem _ c) ?_
    exact MulMemClass.mul_mem (zpow_mem_racl hx₂self a)
      (zpow_mem_racl S.y₂_mem b)
  -- Both directions are independent, so the value descends to `k`.
  have hins₁ : (insert S.x₁ (∅ : Set Ω)) = {S.x₁} := by simp
  have hins₂ : (insert S.x₂ (∅ : Set Ω)) = {S.x₂} := by simp
  have hν₁empty : S.x₁ ^ a * S.y₁ ^ b ∈ racl k (∅ : Set Ω) := by
    refine mem_racl_of_mem_racl_insert (a := S.x₁) (b := S.x₂) ?_ ?_ ?_
    · rw [hins₁]
      exact hν₁mem₁
    · rw [hins₂]
      exact hν₁mem₂
    · rw [hins₁]
      exact S.x₂_notMem
  obtain ⟨c₁, hc₁eq⟩ := mem_range_algebraMap_of_isAlgebraic
    (isAlgebraic_of_mem_racl_empty hν₁empty)
  have hc₁0 : c₁ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc₁eq
    exact hν₁ne hc₁eq.symm
  -- The second constant is the quotient.
  have hν₂eq : S.x₂ ^ a * S.y₂ ^ b = algebraMap k Ω (c / c₁) := by
    rw [map_div₀, hc₁eq, eq_div_iff hν₁ne, mul_comm, ← hμν]
    exact hc
  -- Nonzero exponents: a degenerate direction would make a transcendental
  -- coordinate algebraic.
  have hx₁tr : S.x₁ ∉ racl k (∅ : Set Ω) := fun h ↦
    S.x₁_notMem (racl_mono (Set.empty_subset _) h)
  have hy₁tr : S.y₁ ∉ racl k (∅ : Set Ω) := by
    intro h
    have hy₁racl : racl k ({S.y₁} : Set Ω) = racl k (∅ : Set Ω) := by
      have h2 := racl_insert_of_mem (S := (∅ : Set Ω)) h
      simpa using h2
    have hx₁m := S.x₁_mem
    rw [hy₁racl] at hx₁m
    exact hx₁tr hx₁m
  have ha0 : a ≠ 0 := by
    intro h0
    have hb0 : b ≠ 0 := fun hb' ↦ hab ⟨h0, hb'⟩
    have hyb : S.y₁ ^ b ∈ racl k (∅ : Set Ω) := by
      have h1 := hν₁empty
      rwa [h0, zpow_zero, one_mul] at h1
    exact hy₁tr (mem_racl_empty_of_zpow hb0 hyb)
  have hb0 : b ≠ 0 := by
    intro h0
    have ha0' : a ≠ 0 := fun ha' ↦ hab ⟨ha', h0⟩
    have hxa : S.x₁ ^ a ∈ racl k (∅ : Set Ω) := by
      have h1 := hν₁empty
      rwa [h0, zpow_zero, mul_one] at h1
    exact hx₁tr (mem_racl_empty_of_zpow ha0' hxa)
  exact ⟨a, b, c₁, c / c₁, ha0, hb0, hc₁0, div_ne_zero hc0 hc₁0,
    hc₁eq.symm, hν₂eq⟩

/-- The multiplicative coset equations with **coprime** exponents:
extracting the gcd only changes the constants, since the root of the
monomial value is itself algebraic over the algebraically closed base.-/
theorem exists_coset_equations_coprime [IsAlgClosed k] [IsAlgClosed Ω]
    {s : Ω} (hs : s ∉ racl k {S.x₁, S.x₂}) :
    ∃ (a b : ℤ) (c₁ c₂ : k), a ≠ 0 ∧ b ≠ 0 ∧ Int.gcd a b = 1 ∧
      c₁ ≠ 0 ∧ c₂ ≠ 0 ∧
      S.x₁ ^ a * S.y₁ ^ b = algebraMap k Ω c₁ ∧
      S.x₂ ^ a * S.y₂ ^ b = algebraMap k Ω c₂ := by
  classical
  obtain ⟨a, b, c₁, c₂, ha, hb, hc₁, hc₂, h₁, h₂⟩ :=
    S.exists_coset_equations hs
  have hdpos : 0 < Int.gcd a b := by
    rcases Nat.eq_zero_or_pos (Int.gcd a b) with h0 | h
    · exact absurd (Int.gcd_eq_zero_iff.1 h0).1 ha
    · exact h
  obtain ⟨a', b', hcop, ha', hb'⟩ := Int.exists_gcd_one hdpos
  have ha'0 : a' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at ha'
    exact ha ha'
  have hb'0 : b' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hb'
    exact hb hb'
  -- The gcd-th root of the monomial value is algebraic, hence in `k`.
  have hkey : ∀ (x y : Ω) (c : k), x ≠ 0 → y ≠ 0 →
      x ^ a * y ^ b = algebraMap k Ω c →
      ∃ c' : k, c' ≠ 0 ∧ x ^ a' * y ^ b' = algebraMap k Ω c' := by
    intro x y c hx hy h
    have hzd : (x ^ a' * y ^ b') ^ ((Int.gcd a b : ℤ)) =
        algebraMap k Ω c := by
      rw [mul_zpow, ← zpow_mul, ← zpow_mul, ← ha', ← hb']
      exact h
    have hzne : x ^ a' * y ^ b' ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ hx) (zpow_ne_zero _ hy)
    have hzmem : (x ^ a' * y ^ b') ^ ((Int.gcd a b : ℤ)) ∈
        racl k (∅ : Set Ω) := by
      rw [hzd]
      exact IntermediateField.algebraMap_mem _ _
    have hz : x ^ a' * y ^ b' ∈ racl k (∅ : Set Ω) := by
      refine mem_racl_empty_of_zpow ?_ hzmem
      exact_mod_cast hdpos.ne'
    obtain ⟨c', hc'⟩ := mem_range_algebraMap_of_isAlgebraic
      (isAlgebraic_of_mem_racl_empty hz)
    refine ⟨c', fun h0 ↦ hzne ?_, hc'.symm⟩
    rw [← hc', h0, map_zero]
  obtain ⟨c₁', hc₁'0, h₁'⟩ := hkey S.x₁ S.y₁ c₁ S.x₁_ne S.y₁_ne h₁
  obtain ⟨c₂', hc₂'0, h₂'⟩ := hkey S.x₂ S.y₂ c₂ S.x₂_ne S.y₂_ne h₂
  exact ⟨a', b', c₁', c₂', ha'0, hb'0, hcop, hc₁'0, hc₂'0, h₁', h₂'⟩

end Endgame

end MulCorrSetup

end

end AclGeom
