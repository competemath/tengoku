module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Lemma31.Picture.PermOrbits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Combinatorial maps and gluing at a vertex

A `CombMap` is a combinatorial map in the permutation (dart) representation:

* a finite type `D` of darts;
* a fixed-point-free involution `α` (the two ends of an edge);
* a permutation `σ` (the cyclic order of the darts around each vertex).

Vertices are the orbits of `σ`, edges the orbits of `α`, faces the orbits of `φ = σ * α`, and the
Euler characteristic is `χ = V - E + F`.  Unlike `BipartiteMap` (`EulerCounting.lean`), vertices
of a `CombMap` carry no kind; the kinds are recorded by labels (see `Raw.lean`).

## Results

* `CombMap.glue M₁ M₂ p₁ p₂` : the disjoint union of `M₁` and `M₂` with the vertex of `p₁` and the
  vertex of `p₂` merged into a single vertex (the darts of the vertex of `p₂` are inserted into the
  cyclic order at `p₁`).  This is `σ = swap p₁ p₂ * (σ₁ ⊕ σ₂)`, `α = α₁ ⊕ α₂`.
* `CombMap.glue_numVertices`, `glue_numEdges`, `glue_numFaces` : the merge loses one vertex and one
  face (the two corner faces are merged), keeps all edges; hence
  `CombMap.glue_euler : χ(glue) = χ(M₁) + χ(M₂) - 2`.  Gluing two spheres gives a sphere.
* `CombMap.glue_connected` : gluing two connected maps gives a connected map.
* `CombMap.triangle`, `CombMap.digon` : two explicit spherical connected maps (a triangle, and two
  vertices joined by two edges), with `χ = 2` computed from the definitions.
-/

@[expose] public section

namespace TheoremA.Picture

open Equiv Function

/-- A combinatorial map in the dart representation.-/
structure CombMap where
  /-- The darts.-/
  D : Type
  [instFintype : Fintype D]
  [instDecEq : DecidableEq D]
  /-- The rotation of darts around the vertices.-/
  σ : Perm D
  /-- The edge involution.-/
  α : Perm D
  α_α : ∀ d, α (α d) = d
  α_ne : ∀ d, α d ≠ d

attribute [instance] CombMap.instFintype CombMap.instDecEq

namespace CombMap

variable (M : CombMap)

/-- The face permutation `σ * α`.-/
def φ : Perm M.D := M.σ * M.α

/-- The number of vertices (`σ`-orbits).-/
noncomputable def numVertices : ℕ := numOrbits M.σ

/-- The number of edges (`α`-orbits).-/
noncomputable def numEdges : ℕ := numOrbits M.α

/-- The number of faces (`σ * α`-orbits).-/
noncomputable def numFaces : ℕ := numOrbits M.φ

/-- The Euler characteristic `V - E + F`.-/
noncomputable def euler : ℤ := (M.numVertices : ℤ) - M.numEdges + M.numFaces

/-- One step along the map: to the next dart at the same vertex, or to the other end of the
edge.-/
def Step (x y : M.D) : Prop := y = M.σ x ∨ y = M.α x

/-- The map is connected.-/
def Connected : Prop := ∀ x y, Relation.EqvGen M.Step x y

/--
@isnad1 id=eqvgen.1h3v.s4.ccea2e1c9d3b from=translated src=- shape=dbfd64fe vocab=f9a983e8
-/
theorem eqvGen_of_sameCycle {x y : M.D} (h : M.σ.SameCycle x y) : Relation.EqvGen M.Step x y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
    refine ih.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl ?_))
    rw [pow_succ', Perm.mul_apply]

/--
@isnad1 id=connecte.1h2v.s4.eaeac4347127 from=translated src=- shape=113dcabb vocab=403474c9
-/
theorem connected_of_base (d₀ : M.D) (h : ∀ x, Relation.EqvGen M.Step d₀ x) : M.Connected :=
  fun x y => ((h x).symm _ _).trans _ _ _ (h y)

/-! ### Gluing two maps at a vertex -/

/-- Glue `M₁` and `M₂` by merging the vertex of `p₁` with the vertex of `p₂`.-/
def glue (M₁ M₂ : CombMap) (p₁ : M₁.D) (p₂ : M₂.D) : CombMap where
  D := M₁.D ⊕ M₂.D
  σ := swap (Sum.inl p₁) (Sum.inr p₂) * Perm.sumCongr M₁.σ M₂.σ
  α := Perm.sumCongr M₁.α M₂.α
  α_α := by rintro (d | d) <;> simp [M₁.α_α, M₂.α_α]
  α_ne := by rintro (d | d) <;> simp [M₁.α_ne, M₂.α_ne]

variable (M₁ M₂ : CombMap) (p₁ : M₁.D) (p₂ : M₂.D)

/--
@isnad1 id=not.0h4v.s5.f8681185a521 from=translated src=- shape=7612a1ac vocab=eef52461
-/
theorem glue_not_sameCycle :
    ¬ (Perm.sumCongr M₁.σ M₂.σ).SameCycle (Sum.inl p₁) (Sum.inr p₂) :=
  not_sameCycle_sumCongr_inl_inr

/--
@isnad1 id=eq.0h4v.s5.646e743f8048 from=translated src=- shape=15e37719 vocab=0511dfad
-/
theorem glue_numVertices :
    (glue M₁ M₂ p₁ p₂).numVertices + 1 = M₁.numVertices + M₂.numVertices := by
  unfold numVertices
  rw [← numOrbits_sumCongr, numOrbits_swap_mul (glue_not_sameCycle M₁ M₂ p₁ p₂)]
  rfl

/--
@isnad1 id=eq.0h4v.s4.b9eb765de0e0 from=translated src=- shape=34d81c5b vocab=6b0d5c07
-/
theorem glue_numEdges : (glue M₁ M₂ p₁ p₂).numEdges = M₁.numEdges + M₂.numEdges :=
  numOrbits_sumCongr _ _

/-- The cycles of the rotation of a gluing.
@isnad1 id=iff.0h6v.s7.467c8f9082e3 from=translated src=- shape=1dabe80a vocab=62ac1070
-/
theorem glue_sameCycle_iff {x y : (glue M₁ M₂ p₁ p₂).D} :
    (glue M₁ M₂ p₁ p₂).σ.SameCycle x y ↔ (Perm.sumCongr M₁.σ M₂.σ).SameCycle x y ∨
      (((Perm.sumCongr M₁.σ M₂.σ).SameCycle (Sum.inl p₁) x ∨
          (Perm.sumCongr M₁.σ M₂.σ).SameCycle (Sum.inr p₂) x) ∧
        ((Perm.sumCongr M₁.σ M₂.σ).SameCycle (Sum.inl p₁) y ∨
          (Perm.sumCongr M₁.σ M₂.σ).SameCycle (Sum.inr p₂) y)) :=
  sameCycle_swap_mul_iff (glue_not_sameCycle M₁ M₂ p₁ p₂)

/--
@isnad1 id=eqvgen.1h6v.s5.16a8494278ec from=translated src=- shape=f11168c1 vocab=e12e0995
-/
theorem glue_eqvGen_inl {x y : M₁.D} (h : Relation.EqvGen M₁.Step x y) :
    Relation.EqvGen (glue M₁ M₂ p₁ p₂).Step (Sum.inl x) (Sum.inl y) := by
  induction h with
  | rel x y h =>
    rcases h with rfl | rfl
    · exact eqvGen_of_sameCycle _ ((glue_sameCycle_iff M₁ M₂ p₁ p₂).2
        (Or.inl (sameCycle_sumCongr_inl.2 ⟨1, by simp⟩)))
    · exact Relation.EqvGen.rel _ _ (Or.inr rfl)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/--
@isnad1 id=eqvgen.1h6v.s5.1599be9421ff from=translated src=- shape=ae06fd1f vocab=764a8287
-/
theorem glue_eqvGen_inr {x y : M₂.D} (h : Relation.EqvGen M₂.Step x y) :
    Relation.EqvGen (glue M₁ M₂ p₁ p₂).Step (Sum.inr x) (Sum.inr y) := by
  induction h with
  | rel x y h =>
    rcases h with rfl | rfl
    · exact eqvGen_of_sameCycle _ ((glue_sameCycle_iff M₁ M₂ p₁ p₂).2
        (Or.inl (sameCycle_sumCongr_inr.2 ⟨1, by simp⟩)))
    · exact Relation.EqvGen.rel _ _ (Or.inr rfl)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/-- **Gluing connected maps gives a connected map.**
@isnad1 id=connecte.2h4v.s4.74884bc1f01d from=translated src=- shape=df9514ce vocab=bffaa5a2
-/
theorem glue_connected (h₁ : M₁.Connected) (h₂ : M₂.Connected) :
    (glue M₁ M₂ p₁ p₂).Connected := by
  refine connected_of_base _ (Sum.inl p₁) ?_
  have hlink : Relation.EqvGen (glue M₁ M₂ p₁ p₂).Step (Sum.inl p₁) (Sum.inr p₂) :=
    eqvGen_of_sameCycle _ (sameCycle_swap_mul_left_right (glue_not_sameCycle M₁ M₂ p₁ p₂))
  rintro (x | x)
  · exact glue_eqvGen_inl M₁ M₂ p₁ p₂ (h₁ p₁ x)
  · exact hlink.trans _ _ _ (glue_eqvGen_inr M₁ M₂ p₁ p₂ (h₂ p₂ x))

end CombMap

/-! ### Explicit small maps -/

section Explicit

variable {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Counting orbits of an explicit permutation through an invariant with explicit witnesses of
reachability (all hypotheses are decidable for explicit data).
@isnad1 id=eq.3h5v.s6.5a4843995dca from=translated src=- shape=8b475d92 vocab=1fe322ff
-/
theorem numOrbits_eq_of_invariant {n N : ℕ} (π : Perm D) (f : D → Fin n) (hf : Surjective f)
    (hinv : ∀ x, f (π x) = f x) (hreach : ∀ x y, f x = f y → ∃ k : Fin N, (π ^ (k : ℕ)) x = y) :
    numOrbits π = n := by
  rw [numOrbits_eq_of_iff π f hf, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro x y
  constructor
  · intro h
    obtain ⟨k, hk⟩ := hreach x y h
    exact sameCycle_of_pow_eq k hk
  · exact SameCycle.eq_of_invariant hinv

omit [DecidableEq D] in
/-- The cycles of an explicit permutation, through an invariant with explicit witnesses of
reachability.
@isnad1 id=iff.2h7v.s6.2ca2e00fa3a3 from=translated src=- shape=d747db6e vocab=348071ed
-/
theorem sameCycle_iff_of_invariant {n N : ℕ} (π : Perm D) (f : D → Fin n)
    (hinv : ∀ x, f (π x) = f x) (hreach : ∀ x y, f x = f y → ∃ k : Fin N, (π ^ (k : ℕ)) x = y)
    (x y : D) : π.SameCycle x y ↔ f x = f y := by
  constructor
  · exact SameCycle.eq_of_invariant hinv
  · intro h
    obtain ⟨k, hk⟩ := hreach x y h
    exact sameCycle_of_pow_eq k hk

/-- Following a list of steps (`true` = rotate, `false` = cross the edge).-/
def walk (σ α : Perm D) : D → List Bool → D
  | d, [] => d
  | d, b :: l => walk σ α (if b then σ d else α d) l

/--
@isnad1 id=eqvgen.0h3v.s4.0464ca4b2382 from=translated src=- shape=b484d759 vocab=b34b8d91
-/
theorem CombMap.eqvGen_walk (M : CombMap) (d : M.D) (l : List Bool) :
    Relation.EqvGen M.Step d (walk M.σ M.α d l) := by
  induction l generalizing d with
  | nil => exact Relation.EqvGen.refl _
  | cons b l ih =>
    refine Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ?_) (ih _)
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl

/--
@isnad1 id=connecte.1h3v.s5.c66adae966fd from=translated src=- shape=1dc6eeb0 vocab=1570b7ed
-/
theorem CombMap.connected_of_walks (M : CombMap) (d₀ : M.D) (S : List (List Bool))
    (h : ∀ x, ∃ l ∈ S, walk M.σ M.α d₀ l = x) : M.Connected := by
  refine M.connected_of_base d₀ fun x => ?_
  obtain ⟨l, -, rfl⟩ := h x
  exact M.eqvGen_walk d₀ l

end Explicit

namespace CombMap

/-- The triangle: three vertices `b = {0, 5}`, `v = {1, 2}`, `t = {3, 4}` and three edges
`{0, 1}`, `{2, 3}`, `{4, 5}`.-/
def triangle : CombMap where
  D := Fin 6
  σ := swap 0 5 * swap 1 2 * swap 3 4
  α := swap 0 1 * swap 2 3 * swap 4 5
  α_α := by decide
  α_ne := by decide

/-- The digon: two vertices `b = {0, 3}`, `w = {1, 2}` joined by the edges `{0, 1}`, `{2, 3}`.-/
def digon : CombMap where
  D := Fin 4
  σ := swap 0 3 * swap 1 2
  α := swap 0 1 * swap 2 3
  α_α := by decide
  α_ne := by decide

/--
@isnad1 id=connecte.0h0v.s1.a772b99440cd from=translated src=- shape=49959d42 vocab=487f801a
-/
theorem triangle_connected : triangle.Connected :=
  triangle.connected_of_walks (0 : Fin 6)
    [[], [true], [false], [true, false], [false, true], [false, true, false]] (by decide)

/--
@isnad1 id=connecte.0h0v.s1.95a22ab2b7b5 from=translated src=- shape=49959d42 vocab=99692d15
-/
theorem digon_connected : digon.Connected :=
  digon.connected_of_walks (0 : Fin 4) [[], [true], [false], [true, false]] (by decide)

end CombMap

end TheoremA.Picture
