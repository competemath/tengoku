/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite sparse-Fock occupation patterns

Three local levels define fresh, light, and heavy sites, their row subsets, and the exact total occupation grade.
Ported from `SparseFockFormal.Pattern` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch

/-- The three local orthogonal-polynomial levels used by the sparse-Fock model.

Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
inductive Level where
  | zero
  | one
  | two
  deriving DecidableEq, Repr

/-- A concrete enumeration: local pattern states really form a finite type.

Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
instance : Fintype Level where
  elems := {.zero, .one, .two}
  complete x := by
    cases x <;> simp

/-- There are exactly three local occupation levels.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h0v.s3.5bc050227515 from=translated src=- shape=b0ae1d2b vocab=faeb6727
-/
@[simp] theorem card_level : Fintype.card Level = 3 := by
  decide

/-- Occupation weight in the total-grade decomposition.

Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def Level.weight : Level → ℕ
  | .zero => 0
  | .one => 1
  | .two => 2

/-- A site is an incidence `(row, column)`.

Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
abbrev Site (m n : ℕ) := Fin m × Fin n

/-- A finite sparse-Fock pattern.

Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
abbrev Pattern (m n : ℕ) := Site m n → Level

namespace Pattern

variable {m n : ℕ}

/-- Total particle grade.

Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def grade (p : Pattern m n) : ℕ := ∑ s, (p s).weight

/-- Fresh sites are exactly the sites at occupation level zero.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def fresh (p : Pattern m n) : Finset (Site m n) :=
  Finset.univ.filter fun s => p s = .zero

/-- Light sites are exactly the sites at occupation level one.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def light (p : Pattern m n) : Finset (Site m n) :=
  Finset.univ.filter fun s => p s = .one

/-- Heavy sites are exactly the sites at occupation level two.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def heavy (p : Pattern m n) : Finset (Site m n) :=
  Finset.univ.filter fun s => p s = .two

/-- The fresh-site columns in one physical row are selected by level zero.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def freshInRow (p : Pattern m n) (r : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => p (r, i) = .zero

/-- The light-site columns in one physical row are selected by level one.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def lightInRow (p : Pattern m n) (r : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => p (r, i) = .one

/-- The heavy-site columns in one physical row are selected by level two.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def heavyInRow (p : Pattern m n) (r : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => p (r, i) = .two

/-- Membership in the fresh-site set is occupation level zero.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=iff.0h4v.s5.7d7f10615ec9 from=translated src=- shape=467877c9 vocab=69fbbba7
-/
@[simp] theorem mem_fresh {p : Pattern m n} {s : Site m n} :
    s ∈ p.fresh ↔ p s = .zero := by
  simp [fresh]

/-- Membership in the light-site set is occupation level one.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=iff.0h4v.s5.59d73142fb99 from=translated src=- shape=467877c9 vocab=d3cd297e
-/
@[simp] theorem mem_light {p : Pattern m n} {s : Site m n} :
    s ∈ p.light ↔ p s = .one := by
  simp [light]

/-- Membership in the heavy-site set is occupation level two.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=iff.0h4v.s5.e0b3d0c2fc4f from=translated src=- shape=467877c9 vocab=8c4a9a82
-/
@[simp] theorem mem_heavy {p : Pattern m n} {s : Site m n} :
    s ∈ p.heavy ↔ p s = .two := by
  simp [heavy]

/-- Membership in a row's fresh-site set is level zero at that row-column site.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=iff.0h5v.s5.ca68a731e629 from=translated src=- shape=04d751ce vocab=d697d6d3
-/
@[simp] theorem mem_freshInRow {p : Pattern m n} {r : Fin m} {i : Fin n} :
    i ∈ p.freshInRow r ↔ p (r, i) = .zero := by
  simp [freshInRow]

/-- Membership in a row's light-site set is level one at that row-column site.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=iff.0h5v.s5.3453a29f6be1 from=translated src=- shape=04d751ce vocab=399ea2d6
-/
@[simp] theorem mem_lightInRow {p : Pattern m n} {r : Fin m} {i : Fin n} :
    i ∈ p.lightInRow r ↔ p (r, i) = .one := by
  simp [lightInRow]

/-- Membership in a row's heavy-site set is level two at that row-column site.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=iff.0h5v.s5.05de8a7688d8 from=translated src=- shape=04d751ce vocab=22879e78
-/
@[simp] theorem mem_heavyInRow {p : Pattern m n} {r : Fin m} {i : Fin n} :
    i ∈ p.heavyInRow r ↔ p (r, i) = .two := by
  simp [heavyInRow]

/-- A pattern's fresh and light site sets are disjoint.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=disjoint.0h3v.s4.a67d7d406533 from=translated src=- shape=b4ecab76 vocab=0197b19c
-/
theorem fresh_disjoint_light (p : Pattern m n) : Disjoint p.fresh p.light := by
  refine Finset.disjoint_left.mpr ?_
  intro s hs0 hs1
  simp only [mem_fresh] at hs0
  simp only [mem_light] at hs1
  cases hs0.symm.trans hs1

/-- A pattern's fresh and heavy site sets are disjoint.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=disjoint.0h3v.s4.ff52f7183287 from=translated src=- shape=b4ecab76 vocab=8da673f9
-/
theorem fresh_disjoint_heavy (p : Pattern m n) : Disjoint p.fresh p.heavy := by
  refine Finset.disjoint_left.mpr ?_
  intro s hs0 hs2
  simp only [mem_fresh] at hs0
  simp only [mem_heavy] at hs2
  cases hs0.symm.trans hs2

/-- A pattern's light and heavy site sets are disjoint.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=disjoint.0h3v.s4.c55950a1bd06 from=translated src=- shape=b4ecab76 vocab=15ee1830
-/
theorem light_disjoint_heavy (p : Pattern m n) : Disjoint p.light p.heavy := by
  refine Finset.disjoint_left.mpr ?_
  intro s hs1 hs2
  simp only [mem_light] at hs1
  simp only [mem_heavy] at hs2
  cases hs1.symm.trans hs2

/-- Every site is in exactly one of the three occupation classes.

Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s6.e3bc3e4f4f7b from=translated src=- shape=6b367359 vocab=9fc89e98
-/
theorem fresh_union_light_union_heavy (p : Pattern m n) :
    (p.fresh ∪ p.light) ∪ p.heavy = Finset.univ := by
  ext s
  cases h : p s <;> simp [h]

/-- The row-local light counts sum to the global light count.

Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s5.bc4605a371dd from=translated src=- shape=88bc5115 vocab=f0af6bc7
-/
theorem card_light_eq_sum_card_lightInRow (p : Pattern m n) :
    p.light.card = ∑ r, (p.lightInRow r).card := by
  classical
  simp only [light, lightInRow, Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- The row-local heavy counts sum to the global heavy count.

Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s5.887c6571207f from=translated src=- shape=88bc5115 vocab=e3afd047
-/
theorem card_heavy_eq_sum_card_heavyInRow (p : Pattern m n) :
    p.heavy.card = ∑ r, (p.heavyInRow r).card := by
  classical
  simp only [heavy, heavyInRow, Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- The pattern grade is its light count plus twice its heavy count.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s5.b05892c73b18 from=translated src=- shape=19df206f vocab=c29bd985
-/
theorem grade_eq_card_light_add_two_mul_card_heavy (p : Pattern m n) :
    p.grade = p.light.card + 2 * p.heavy.card := by
  classical
  simp only [grade, light, heavy, Finset.card_filter]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  cases h : p s <;> simp [Level.weight]

/-- The light-site count is bounded by the pattern grade.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h3v.s4.4ded46c858e0 from=translated src=- shape=4ef563f4 vocab=056c054c
-/
theorem card_light_le_grade (p : Pattern m n) : p.light.card ≤ p.grade := by
  rw [grade_eq_card_light_add_two_mul_card_heavy]
  omega

/-- Twice the heavy-site count is bounded by the pattern grade.
Source: ported from `SparseFockFormal.Pattern`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h3v.s5.01aa87bf8d44 from=translated src=- shape=9f07de73 vocab=c4aa1d04
-/
theorem two_mul_card_heavy_le_grade (p : Pattern m n) :
    2 * p.heavy.card ≤ p.grade := by
  rw [grade_eq_card_light_add_two_mul_card_heavy]
  omega

end Pattern

end NLAlib.SparseSketch
