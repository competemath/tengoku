import Tengoku.PaperCLean.PaperC.Combinatorics.LargePrimeOccurrences
import Tengoku.Seed.Combinatorics.SimpleGraph.Paths

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1200000

/-!
# The concrete graph of large-prime occurrences

This module turns the local occurrence theorem into the graph used in
Section 6 of Paper C.  Its vertices are the two complete start boundaries.
Two distinct vertices are adjacent when one prime above the cutoff occurs
with odd valuation at both vertices.  A singleton occurrence is a pin.

The subspace `largePrimeSolution` is the space denoted `W_{>B}(x,y)` in the
paper, written directly in complete-boundary coordinates.  The main local
results below identify its equations with the two graph rules:

* values agree across every edge;
* values vanish at every pinned vertex.

The resolution by connected components is kept in the separate generic
module `PinnedGraphResolution`.
-/

namespace PaperC
namespace LargePrimeGraph

open LargePrimeOccurrences

noncomputable section

/-- A genuine prime strictly above the complete-boundary length.-/
def IsLargePrime (L p : ℕ) : Prop :=
  p.Prime ∧ L + 1 < p

/--
The graph whose edges are the two-element odd-occurrence sets of primes
above `L+1`.-/
def largePrimeGraph (x y L : ℕ) :
    SimpleGraph (Occurrence L) where
  Adj v w :=
    v ≠ w ∧
      ∃ p : ℕ, IsLargePrime L p ∧
        v ∈ primeOccurrences x y L p ∧
        w ∈ primeOccurrences x y L p
  symm := by
    constructor
    rintro v w ⟨hvw, p, hp, hv, hw⟩
    exact ⟨hvw.symm, p, hp, hw, hv⟩
  loopless := by
    constructor
    intro v hv
    exact hv.1 rfl

/--
@isnad1 id=iff.0h5v.s6.568177241385 from=translated src=- shape=f32c552f vocab=1b0a4d85
-/
@[simp]
theorem largePrimeGraph_adj
    {x y L : ℕ} {v w : Occurrence L} :
    (largePrimeGraph x y L).Adj v w ↔
      v ≠ w ∧
        ∃ p : ℕ, IsLargePrime L p ∧
          v ∈ primeOccurrences x y L p ∧
          w ∈ primeOccurrences x y L p :=
  Iff.rfl

/-- A vertex is pinned when some large prime occurs there and nowhere else.-/
def IsPinned
    (x y L : ℕ) (v : Occurrence L) : Prop :=
  ∃ p : ℕ, IsLargePrime L p ∧
    primeOccurrences x y L p = {v}

/-- A defective vertex carries no odd valuation at any prime above `L+1`.-/
def IsDefective
    (x y L : ℕ) (v : Occurrence L) : Prop :=
  ∀ p : ℕ, IsLargePrime L p →
    v ∉ primeOccurrences x y L p

/--
The complete-boundary version of `W_{>B}(x,y)`: every equation belonging to
a prime above `L+1` has zero sum.-/
def largePrimeSolution
    (x y L : ℕ) : Submodule F₂ (Occurrence L → F₂) where
  carrier := {u |
    ∀ p : ℕ, IsLargePrime L p →
      ∑ v ∈ primeOccurrences x y L p, u v = 0}
  zero_mem' := by
    intro p hp
    simp
  add_mem' := by
    intro u v hu hv p hp
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, hu p hp, hv p hp, add_zero]
  smul_mem' := by
    intro c u hu p hp
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hu p hp, mul_zero]

/--
@isnad1 id=iff.0h4v.s8.4f00f045bc3c from=translated src=- shape=2401bdfb vocab=477f8856
-/
@[simp]
theorem mem_largePrimeSolution
    {x y L : ℕ} {u : Occurrence L → F₂} :
    u ∈ largePrimeSolution x y L ↔
      ∀ p : ℕ, IsLargePrime L p →
        ∑ v ∈ primeOccurrences x y L p, u v = 0 :=
  Iff.rfl

/--
The boundary prime equation is exactly the sum over the occurrence finset.
@isnad1 id=eq.0h5v.s7.9a3d7b8a3e6e from=translated src=- shape=1af9c4aa vocab=2eb4b9cf
-/
theorem sum_mul_parityVec_eq_sum_primeOccurrences
    (x y L p : ℕ) (u : Occurrence L → F₂) :
    (∑ v : Occurrence L,
        u v *
          parityVec
            (Affine.twoStartCompleteVertexLabel x y L v) p) =
      ∑ v ∈ primeOccurrences x y L p, u v := by
  classical
  change
    (∑ v : Occurrence L,
        u v *
          parityVec
            (Affine.twoStartCompleteVertexLabel x y L v) p) =
      ∑ v ∈
        Finset.univ.filter
          (fun v : Occurrence L ↦
            parityVec
              (Affine.twoStartCompleteVertexLabel x y L v) p = 1),
        u v
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hparity :
      parityVec
        (Affine.twoStartCompleteVertexLabel x y L v) p = 1
  · rw [ite_eq_left hparity, hparity, mul_one]
  · have hzero :
        parityVec
          (Affine.twoStartCompleteVertexLabel x y L v) p = 0 := by
      have hbinary : ∀ z : F₂, z ≠ 1 → z = 0 := by
        decide
      exact hbinary _ hparity
    rw [ite_eq_right hparity, hzero, mul_zero]

/--
Equivalent prime-coordinate formulation of `largePrimeSolution`.
@isnad1 id=iff.0h4v.s8.9706ff638a95 from=translated src=- shape=a28ee5c3 vocab=db37f7bb
-/
theorem mem_largePrimeSolution_iff_boundary_prime_equations
    {x y L : ℕ} {u : Occurrence L → F₂} :
    u ∈ largePrimeSolution x y L ↔
      ∀ p : ℕ, IsLargePrime L p →
        ∑ v : Occurrence L,
          u v *
            parityVec
              (Affine.twoStartCompleteVertexLabel x y L v) p = 0 := by
  constructor
  · intro hu p hp
    rw [sum_mul_parityVec_eq_sum_primeOccurrences]
    exact hu p hp
  · intro hu p hp
    rw [← sum_mul_parityVec_eq_sum_primeOccurrences]
    exact hu p hp

/-- Two prescribed distinct members exhaust a large-prime occurrence set.
@isnad1 id=eq.6h6v.s7.853ab12ab634 from=translated src=- shape=9ef72887 vocab=d8be10fc
-/
theorem primeOccurrences_eq_pair_of_mem
    {x y L p : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : IsLargePrime L p)
    {v w : Occurrence L}
    (hv : v ∈ primeOccurrences x y L p)
    (hw : w ∈ primeOccurrences x y L p)
    (hvw : v ≠ w) :
    primeOccurrences x y L p = {v, w} := by
  classical
  have hsubset :
      ({v, w} : Finset (Occurrence L)) ⊆
        primeOccurrences x y L p := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hv
    · exact hw
  have hpairCard : ({v, w} : Finset (Occurrence L)).card = 2 := by
    simp [hvw]
  have hcardUpper :
      (primeOccurrences x y L p).card ≤ 2 :=
    card_primeOccurrences_le_two hx hy hp.1 hp.2
  have hcardLower :
      2 ≤ (primeOccurrences x y L p).card := by
    rw [← hpairCard]
    exact Finset.card_le_card hsubset
  have hcard :
      (primeOccurrences x y L p).card = 2 :=
    Nat.le_antisymm hcardUpper hcardLower
  have hreverseCard :
      (primeOccurrences x y L p).card ≤
        ({v, w} : Finset (Occurrence L)).card := by
    rw [hcard, hpairCard]
  exact
    (Finset.eq_of_subset_of_card_le hsubset
      hreverseCard).symm

/-- A solution of the large-prime equations has equal values across an edge.-/
theorem eq_on_adj_of_mem
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {u : Occurrence L → F₂}
    (hu : u ∈ largePrimeSolution x y L)
    {v w : Occurrence L}
    (hvw : (largePrimeGraph x y L).Adj v w) :
    u v = u w := by
  obtain ⟨hne, p, hp, hv, hw⟩ := hvw
  have hset :=
    primeOccurrences_eq_pair_of_mem hx hy hp hv hw hne
  have hsum := hu p hp
  rw [hset] at hsum
  simp only [Finset.sum_pair hne] at hsum
  have hneg : u v = -u w :=
    eq_neg_of_add_eq_zero_left hsum
  have hself : -u w = u w :=
    ZMod.neg_eq_self_mod_two (u w)
  exact hneg.trans hself

/-- A solution of the large-prime equations vanishes at every pin.-/
theorem eq_zero_of_isPinned_of_mem
    {x y L : ℕ}
    {u : Occurrence L → F₂}
    (hu : u ∈ largePrimeSolution x y L)
    {v : Occurrence L}
    (hv : IsPinned x y L v) :
    u v = 0 := by
  obtain ⟨p, hp, hset⟩ := hv
  have hsum := hu p hp
  rw [hset] at hsum
  simpa using hsum

/--
Conversely, equality across graph edges and vanishing at pins solve every
large-prime equation.
@isnad1 id=mem.4h4v.s8.26d7fa669e29 from=translated src=- shape=b79283f2 vocab=058fd919
-/
theorem mem_largePrimeSolution_of_graph_rules
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {u : Occurrence L → F₂}
    (hedge :
      ∀ ⦃v w : Occurrence L⦄,
        (largePrimeGraph x y L).Adj v w →
          u v = u w)
    (hpin :
      ∀ ⦃v : Occurrence L⦄,
        IsPinned x y L v → u v = 0) :
    u ∈ largePrimeSolution x y L := by
  intro p hp
  have hcard :=
    card_primeOccurrences_le_two hx hy hp.1 hp.2
  have hcases :
      (primeOccurrences x y L p).card = 0 ∨
        (primeOccurrences x y L p).card = 1 ∨
        (primeOccurrences x y L p).card = 2 := by
    omega
  rcases hcases with hc | hc | hc
  · have hempty :
        primeOccurrences x y L p = ∅ :=
      Finset.card_eq_zero.mp hc
    simp [hempty]
  · obtain ⟨v, hset⟩ :=
      Finset.card_eq_one.mp hc
    have hvpin : IsPinned x y L v :=
      ⟨p, hp, hset⟩
    rw [hset]
    simp [hpin hvpin]
  · obtain ⟨v, w, hvw, hset⟩ :=
      Finset.card_eq_two.mp hc
    have hadj :
        (largePrimeGraph x y L).Adj v w := by
      refine ⟨hvw, p, hp, ?_, ?_⟩ <;>
        rw [hset] <;> simp
    rw [hset]
    simp only [Finset.sum_pair hvw]
    rw [hedge hadj]
    exact ZModModule.add_self (u w)

/--
Exact graph-rule characterization of `W_{>B}(x,y)`.
@isnad1 id=iff.2h4v.s8.e7e053659fe6 from=translated src=- shape=0e171f63 vocab=058fd919
-/
theorem mem_largePrimeSolution_iff_graph_rules
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {u : Occurrence L → F₂} :
    u ∈ largePrimeSolution x y L ↔
      (∀ ⦃v w : Occurrence L⦄,
          (largePrimeGraph x y L).Adj v w →
            u v = u w) ∧
      (∀ ⦃v : Occurrence L⦄,
          IsPinned x y L v → u v = 0) := by
  constructor
  · intro hu
    exact
      ⟨fun _ _ hvw ↦ eq_on_adj_of_mem hx hy hu hvw,
        fun _ hv ↦ eq_zero_of_isPinned_of_mem hu hv⟩
  · rintro ⟨hedge, hpin⟩
    exact mem_largePrimeSolution_of_graph_rules hx hy hedge hpin

/-- Defective vertices are unpinned.
@isnad1 id=not.1h4v.s4.d80ccd40a216 from=translated src=- shape=26e02f44 vocab=53e29ef9
-/
theorem not_isPinned_of_isDefective
    {x y L : ℕ} {v : Occurrence L}
    (hv : IsDefective x y L v) :
    ¬ IsPinned x y L v := by
  rintro ⟨p, hp, hset⟩
  exact hv p hp (by simp [hset])

/-- Defective vertices are isolated in the large-prime graph.
@isnad1 id=not.1h5v.s4.cf02eaed4c3f from=translated src=- shape=e3389d5d vocab=10c51b60
-/
theorem not_adj_of_isDefective
    {x y L : ℕ} {v : Occurrence L}
    (hv : IsDefective x y L v)
    (w : Occurrence L) :
    ¬ (largePrimeGraph x y L).Adj v w := by
  rintro ⟨_hne, p, hp, hvp, _hwp⟩
  exact hv p hp hvp

/--
An unpinned isolated vertex is defective.  This is the converse needed to
identify the `D` free singleton components in Lemma 6.1.
@isnad1 id=isdefect.4h4v.s5.6214a5fdf929 from=translated src=- shape=81e8af88 vocab=f8a69305
-/
theorem isDefective_of_not_isPinned_of_isolated
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v : Occurrence L}
    (hpin : ¬ IsPinned x y L v)
    (hisolated :
      ∀ w : Occurrence L,
        ¬ (largePrimeGraph x y L).Adj v w) :
    IsDefective x y L v := by
  intro p hp hvp
  have hcard :=
    card_primeOccurrences_le_two hx hy hp.1 hp.2
  have hpositive :
      0 < (primeOccurrences x y L p).card :=
    Finset.card_pos.mpr ⟨v, hvp⟩
  have hcases :
      (primeOccurrences x y L p).card = 1 ∨
        (primeOccurrences x y L p).card = 2 := by
    omega
  rcases hcases with hc | hc
  · obtain ⟨w, hset⟩ :=
      Finset.card_eq_one.mp hc
    have hvw : v = w := by
      have : v ∈ ({w} : Finset (Occurrence L)) := by
        simpa [hset] using hvp
      simpa using this
    apply hpin
    subst w
    exact ⟨p, hp, hset⟩
  · obtain ⟨w, z, hwz, hset⟩ :=
      Finset.card_eq_two.mp hc
    have hvCases : v = w ∨ v = z := by
      have : v ∈ ({w, z} : Finset (Occurrence L)) := by
        simpa [hset] using hvp
      simpa using this
    rcases hvCases with rfl | rfl
    · exact hisolated z
        ⟨hwz, p, hp,
          (by rw [hset]; simp),
          (by rw [hset]; simp)⟩
    · exact hisolated w
        ⟨hwz.symm, p, hp,
          (by rw [hset]; simp),
          (by rw [hset]; simp)⟩

end

end LargePrimeGraph
end PaperC
