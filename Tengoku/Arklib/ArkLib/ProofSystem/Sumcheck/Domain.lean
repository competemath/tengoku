/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Tengoku.Seed.Data.Fintype.Pi
public import Tengoku.Seed.Data.Fintype.BigOperators
public import Tengoku.Seed.Data.Fin.VecNotation
public import Tengoku.Seed.Data.Fin.Tuple.Basic
public import Tengoku.Seed.Data.Fin.Tuple.Finset
public import Tengoku.Seed.Logic.Embedding.Basic
public import Tengoku.Seed.Algebra.Ring.Basic
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Sigma
public import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sum-check evaluation domains

The sum-check protocol reduces a claim about a sum of a polynomial over an evaluation domain. The
*domain* is, in general, a product `∏ᵢ Dᵢ` of per-coordinate evaluation sets `Dᵢ ⊆ R`, and —
crucially — **the `Dᵢ` may differ from one coordinate to the next**. This file defines that domain
abstraction once, so both the oracle-mode (`Sumcheck.Spec`) and witness-mode (`Sumcheck.Structured`)
sum-checks can consume it, so different protocols can pick the domain best suited to them on a
case-by-case basis (Boolean hypercube, SWIRL-style hyperprism, …).

## Main definitions

* `SumcheckDomain R k` — a per-coordinate evaluation-domain family over `k` coordinates: a size
  `mᵢ` and an injection `Fin mᵢ ↪ R` for each coordinate `i : Fin k`.
* `SumcheckDomain.points` / `SumcheckDomain.cube` — the per-coordinate domain as a `Finset R`, and
  the dependent product cube `∏ᵢ (univ.map (embed i))` as a `Finset (Fin k → R)`.
* `SumcheckDomain.uniform D₀ k` — the same `m`-point embedding in every coordinate. Its `cube` is
  *definitionally* the homogeneous `(univ.map D₀) ^ᶠ k` used today, so `Sumcheck.Spec` can migrate
  onto this abstraction with no semantic change.
* `SumcheckDomain.prepend` — prepend a coordinate (used to build heterogeneous domains).
* `boolDomain R k` — the Boolean hypercube `{0,1}^k` (the canonical `0 ↦ 0, 1 ↦ 1` embedding in
  every coordinate). The plain multilinear sum-check instance.
* `hyperprismDomain R Dskip k` — SWIRL's hyperprism `𝔻 = D × {0,1}^k`: coordinate `0` over a
  `2^ℓ`-point univariate "skip" domain `Dskip`, the remaining `k` coordinates Boolean.

The summation-domain abstraction is intentionally **degree-free**: the per-round polynomial degree
(`d`, or a per-variable / prismalinear bound) is a separate parameter, kept out of this module.
-/

@[expose] public section
namespace Tengoku.Arklib end Tengoku.Arklib open Tengoku.Arklib 
universe u

/-- A per-coordinate evaluation-domain family for a `k`-round sum-check. Each coordinate `i : Fin k`
has `size i` evaluation points, given as an injection `Fin (size i) ↪ R`; the points need not be the
same across coordinates (so this captures Boolean hypercubes, hyperprisms, and mixtures).-/
structure _root_.Tengoku.Arklib.SumcheckDomain (R : Type u) (k : ℕ) where
  /-- The number of evaluation points in coordinate `i`.-/
  size : Fin k → ℕ
  /-- The evaluation domain of coordinate `i`, as an injection `Fin (size i) ↪ R`.-/
  embed : (i : Fin k) → (Fin (size i) ↪ R)

namespace Tengoku.Arklib.SumcheckDomain

variable {R : Type u} {k m : ℕ}

/-- The evaluation points of coordinate `i`, as a `Finset R`.-/
def points (D : SumcheckDomain R k) (i : Fin k) : Finset R := Finset.univ.map (D.embed i)

/-- The evaluation cube: the dependent product of the per-coordinate domains, a `Finset` of points
`Fin k → R`. Generalises the homogeneous `(univ.map D₀) ^ᶠ k`.-/
def cube (D : SumcheckDomain R k) : Finset (Fin k → R) := Fintype.piFinset D.points

/-- The *uniform* domain: the same `m`-point embedding `D₀` in every one of the `k` coordinates.

Its `cube` is *definitionally* `Fintype.piFinset (fun _ : Fin k => univ.map D₀)`, which is exactly
the `(univ.map D₀) ^ᶠ k` used by `Sumcheck.Spec` today — so migrating `Spec` onto this abstraction
is a `rfl`-rename with no downstream change.-/
def uniform (D₀ : Fin m ↪ R) (k : ℕ) : SumcheckDomain R k where
  size := fun _ => m
  embed := fun _ => D₀

/--
@isnad1 id=eq.0h5v.s4.a9b20c1550e3 from=translated src=- shape=f5e2b8c4 vocab=48df9eca
-/
@[simp] lemma size_uniform (D₀ : Fin m ↪ R) (k : ℕ) (i : Fin k) :
    (uniform D₀ k).size i = m := rfl

/--
@isnad1 id=eq.0h5v.s5.4b6a9f9050ee from=translated src=- shape=a7725cae vocab=b2748fab
-/
@[simp] lemma embed_uniform (D₀ : Fin m ↪ R) (k : ℕ) (i : Fin k) :
    (uniform D₀ k).embed i = D₀ := rfl

/--
@isnad1 id=eq.0h5v.s5.dde676c6e408 from=translated src=- shape=f5430ee8 vocab=e8408374
-/
@[simp] lemma points_uniform (D₀ : Fin m ↪ R) (k : ℕ) (i : Fin k) :
    (uniform D₀ k).points i = Finset.univ.map D₀ := rfl

/-- The uniform cube is definitionally the homogeneous product `Fintype.piFinset (fun _ => univ.map
D₀)` (= the `(univ.map D₀) ^ᶠ k` notation used by `Sumcheck.Spec`).
@isnad1 id=eq.0h4v.s5.923ec02bef85 from=translated src=- shape=8109df01 vocab=4a009d98
-/
lemma cube_uniform (D₀ : Fin m ↪ R) (k : ℕ) :
    (uniform D₀ k).cube = Fintype.piFinset (fun _ : Fin k => Finset.univ.map D₀) := rfl

/-- Prepend a coordinate with domain `D₀` in front of an existing `k`-coordinate domain family,
yielding a `(k+1)`-coordinate family. Used to build heterogeneous domains (e.g. one univariate-skip
coordinate followed by Boolean coordinates).-/
def prepend (D₀ : Fin m ↪ R) (rest : SumcheckDomain R k) : SumcheckDomain R (k + 1) where
  size := Fin.cons m rest.size
  embed := Fin.cons D₀ rest.embed

/--
@isnad1 id=eq.0h5v.s6.7b41c016e708 from=translated src=- shape=c7deae0c vocab=df552179
-/
@[simp] lemma size_prepend_zero (D₀ : Fin m ↪ R) (rest : SumcheckDomain R k) :
    (prepend D₀ rest).size 0 = m := rfl

/--
@isnad1 id=eq.0h6v.s5.e7a445fd4799 from=translated src=- shape=7f51240f vocab=1fa72b76
-/
@[simp] lemma size_prepend_succ (D₀ : Fin m ↪ R) (rest : SumcheckDomain R k) (i : Fin k) :
    (prepend D₀ rest).size i.succ = rest.size i := rfl

/-- Drop the first coordinate of a `(k+1)`-coordinate domain family.-/
def tail (D : SumcheckDomain R (k + 1)) : SumcheckDomain R k where
  size := fun i => D.size i.succ
  embed := fun i => D.embed i.succ

/--
@isnad1 id=eq.0h4v.s5.5809a69c5665 from=translated src=- shape=a830d961 vocab=0d1dd5d5
-/
@[simp] lemma points_tail (D : SumcheckDomain R (k + 1)) (i : Fin k) :
    D.tail.points i = D.points i.succ := rfl

/-- Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates:
coordinate `i` of `D.drop j` is coordinate `j + i` of `D`. This is the *suffix* that per-round
sum-check needs — round `j` sums over coordinates `j … k-1`.-/
def drop (D : SumcheckDomain R k) (j : ℕ) : SumcheckDomain R (k - j) where
  size := fun i => D.size ⟨j + i, by omega⟩
  embed := fun i => D.embed ⟨j + i, by omega⟩

/--
@isnad1 id=eq.0h5v.s6.b34b32cd9a83 from=translated src=- shape=d299fb2f vocab=eb908dd0
-/
@[simp] lemma points_drop (D : SumcheckDomain R k) (j : ℕ) (i : Fin (k - j)) :
    (D.drop j).points i = D.points ⟨j + i, by omega⟩ := rfl

/-- Dropping coordinates from a uniform domain is again uniform. So the per-round suffix cube
`((uniform D₀ N).drop j).cube` reduces *definitionally* to today's `(univ.map D₀) ^ᶠ (N - j)` — the
`rfl` hook that lets `Sumcheck.Spec`'s round-`i` sum migrate onto `drop` with no semantic change.
@isnad1 id=eq.0h5v.s5.799529b12908 from=translated src=- shape=62b589ec vocab=a5e16e0c
-/
@[simp] lemma drop_uniform (D₀ : Fin m ↪ R) (N j : ℕ) :
    (uniform D₀ N).drop j = uniform D₀ (N - j) := rfl

/-- Membership in the cube: a point lies in the cube iff each coordinate lies in its domain.
@isnad1 id=iff.0h4v.s6.4ebeb941b6ca from=translated src=- shape=a1ec08b5 vocab=0ac371f9
-/
@[simp] lemma mem_cube {D : SumcheckDomain R k} {x : Fin k → R} :
    x ∈ D.cube ↔ ∀ i, x i ∈ D.points i := Fintype.mem_piFinset

/-- A point lies in coordinate `i`'s domain iff it is the image of some index under `embed i`.
@isnad1 id=iff.0h5v.s6.1a042d0b1d86 from=translated src=- shape=017686ca vocab=1c3fc3ee
-/
@[simp] lemma mem_points {D : SumcheckDomain R k} {i : Fin k} {x : R} :
    x ∈ D.points i ↔ ∃ j, D.embed i j = x := by simp [points]

/-- Coordinate `i` has exactly `size i` evaluation points.
@isnad1 id=eq.0h4v.s4.1d6b74712f8e from=translated src=- shape=cdca0775 vocab=93693ca2
-/
@[simp] lemma card_points (D : SumcheckDomain R k) (i : Fin k) :
    (D.points i).card = D.size i := by
  simp [points]

/-- The cube has `∏ᵢ (size i)` points — the size of the heterogeneous evaluation product. Used for
the Schwartz–Zippel soundness bound `d / ∏ᵢ (size i)`.
@isnad1 id=eq.0h3v.s5.090a500f3f78 from=translated src=- shape=f47362c1 vocab=54ea842f
-/
@[simp] lemma card_cube (D : SumcheckDomain R k) : D.cube.card = ∏ i, D.size i := by
  simp only [cube, Fintype.card_piFinset, card_points]

/-- Telescoping identity (the core sum-check completeness step): summing over the `(k+1)`-coordinate
cube equals summing coordinate `0` over its domain, then the rest over the tail cube. This is the
`piFinset` "cons decomposition" `𝔻^{k+1} ↔ 𝔻₀ × 𝔻^k`.
@isnad1 id=eq.0h5v.s7.23e953f7ce5d from=translated src=- shape=8fe55df8 vocab=ef33cbbd
-/
theorem sum_cube_succ {M : Type*} [AddCommMonoid M] (D : SumcheckDomain R (k + 1))
    (f : (Fin (k + 1) → R) → M) :
    ∑ x ∈ D.cube, f x = ∑ b ∈ D.points 0, ∑ y ∈ D.tail.cube, f (Fin.cons b y) := by
  rw [← Finset.sum_product']
  have htail : D.tail.cube = Fintype.piFinset (Fin.tail D.points) := by
    congr 1
  have hcube : D.cube
      = (D.points 0 ×ˢ D.tail.cube).map (Fin.consEquiv (fun _ : Fin (k + 1) => R)).toEmbedding := by
    rw [htail]
    simpa [cube] using
      Finset.filter_piFinset_eq_map_consEquiv (S := D.points) (fun _ => True)
  rw [hcube, Finset.sum_map]
  rfl

end Tengoku.Arklib.SumcheckDomain

/-- The canonical Boolean embedding `Fin 2 ↪ R`, `0 ↦ (0 : R)`, `1 ↦ (1 : R)`. Injective because
`R` is nontrivial.-/
def _root_.Tengoku.Arklib.boolEmbedding (R : Type u) [CommSemiring R] [Nontrivial R] : Fin 2 ↪ R where
  toFun := ![0, 1]
  inj' a b hab := by
    have h01 : (0 : R) ≠ 1 := zero_ne_one
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact (h01 hab).elim | exact (h01 hab.symm).elim

/--
@isnad1 id=eq.0h1v.s6.0d1a70dbe6f5 from=translated src=- shape=dabe8cfc vocab=9ecb35a4
-/
@[simp] lemma _root_.Tengoku.Arklib.boolEmbedding_zero (R : Type u) [CommSemiring R] [Nontrivial R] :
    boolEmbedding R 0 = (0 : R) := rfl

/--
@isnad1 id=eq.0h1v.s6.d8784630f6ba from=translated src=- shape=dabe8cfc vocab=9ecb35a4
-/
@[simp] lemma _root_.Tengoku.Arklib.boolEmbedding_one (R : Type u) [CommSemiring R] [Nontrivial R] :
    boolEmbedding R 1 = (1 : R) := rfl

/-- The Boolean hypercube `{0,1}^k` as a `SumcheckDomain`: the canonical `0 ↦ 0, 1 ↦ 1` embedding in
every coordinate. This is the plain multilinear sum-check domain (Binius, Hachi, …).-/
def _root_.Tengoku.Arklib.boolDomain (R : Type u) [CommSemiring R] [Nontrivial R] (k : ℕ) : SumcheckDomain R k :=
  SumcheckDomain.uniform (boolEmbedding R) k

/--
@isnad1 id=eq.0h3v.s5.b8d2a0baa2bb from=translated src=- shape=e4d37c98 vocab=69b620b7
-/
@[simp] lemma _root_.Tengoku.Arklib.points_boolDomain (R : Type u) [CommSemiring R] [Nontrivial R] {k : ℕ}
    (i : Fin k) : (boolDomain R k).points i = Finset.univ.map (boolEmbedding R) := rfl

/-- A *hyperprism* domain `𝔻 = D × {0,1}^k` (SWIRL): coordinate `0` ranges over a given `2^ℓ`-point
univariate "skip" domain `Dskip`, and the remaining `k` coordinates are Boolean.

`Dskip` is taken as a parameter here; constructing the concrete smooth multiplicative coset of order
`2^ℓ` (which needs the `2^ℓ ∣ |R×|` smoothness assumption and a chosen generator) is deferred.-/
def _root_.Tengoku.Arklib.hyperprismDomain (R : Type u) [CommSemiring R] [Nontrivial R] {ℓ : ℕ}
    (Dskip : Fin (2 ^ ℓ) ↪ R) (k : ℕ) : SumcheckDomain R (k + 1) :=
  SumcheckDomain.prepend Dskip (boolDomain R k)
-- Tengoku: root names of this library moved to Tengoku.Arklib so they do not collide with other libraries (generated)
