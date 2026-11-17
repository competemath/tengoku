import Tengoku.PaperCLean.PaperC.Arithmetic.IntervalCongruence
import Tengoku.PaperCLean.PaperC.Probability.BadStartCount
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Combinatorics.SimpleGraph.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1200000

/-!
# The large-prime dependency graph

This module formalizes the finite combinatorial core of Lemmas 13.5--13.6.
For a start at `x`, the complete tree support is

`Vₓ = {x - 1, x, ..., x + L - 1}`.

The set `largePrimeCoordinates x L Y` is the manuscript's `Πₓ(Y)`: the
large odd-prime coordinates occurring on at least one vertex of `Vₓ`.
The good starts are the starts in the dyadic block which do not belong to
the terminal bad-start set `D_Y`.

Two distinct good starts are joined when their large-prime coordinate sets
intersect.  We prove:

* symmetry and the explicit absence of loops;
* every local pair of good starts at distance at most `L` is joined;
* an exact finite cover of all ordered edges by a first shared prime;
* the concrete pre-analytic edge bound

`E_Y ≤ (L+1)² ∑_{Y < p ≤ 3N, p prime} (N/p + 1)²`.

The last inequality is stated over `ℚ`, matching the interval-congruence
count used in its proof.  It is precisely the finite estimate preceding the
prime-sum estimates in Lemma 13.6.  The conditional-independence assertion
of Lemma 13.5 is deliberately not asserted here: it belongs to the
probability-space interface, whereas every result in this file is a proved
finite arithmetic or finset statement.
-/

namespace PaperC
namespace LargePrimeDependencyGraph

open scoped BigOperators

open BadStartCount
open LargeOddKernel

noncomputable section

/-! ## Start supports and their large-prime coordinates -/

/-- The non-root vertices `Uₓ = {x, ..., x+L-1}` of a start tree.-/
def startRunSupport (x L : ℕ) : Finset ℕ :=
  (Finset.range L).image fun j ↦ x + j

/--
@isnad1 id=iff.0h3v.s5.1512636b1deb from=translated src=- shape=69ed5c06 vocab=1640af99
-/
@[simp]
theorem mem_startRunSupport {x L n : ℕ} :
    n ∈ startRunSupport x L ↔
      ∃ j < L, x + j = n := by
  simp [startRunSupport]

/-- The complete start-tree support `Vₓ = {x-1} ∪ Uₓ`.-/
def startTreeSupport (x L : ℕ) : Finset ℕ :=
  insert (x - 1) (startRunSupport x L)

/--
@isnad1 id=iff.0h3v.s5.bd9f56b50aa1 from=translated src=- shape=a4ee16ab vocab=428c2cc5
-/
@[simp]
theorem mem_startTreeSupport {x L n : ℕ} :
    n ∈ startTreeSupport x L ↔
      n = x - 1 ∨ ∃ j < L, x + j = n := by
  simp [startTreeSupport, eq_comm]

/--
The set `Πₓ(Y)` of prime coordinates above `Y` occurring to odd order on
some vertex of the complete start tree.-/
def largePrimeCoordinates (x L Y : ℕ) : Finset ℕ :=
  (startTreeSupport x L).biUnion fun n ↦
    largeOddPrimeSupport Y n

/--
@isnad1 id=iff.0h4v.s5.40776b6b6cf6 from=translated src=- shape=4c7f3950 vocab=e39c2e31
-/
@[simp]
theorem mem_largePrimeCoordinates {x L Y p : ℕ} :
    p ∈ largePrimeCoordinates x L Y ↔
      ∃ n ∈ startTreeSupport x L,
        p ∈ largeOddPrimeSupport Y n := by
  simp [largePrimeCoordinates]

/-- Good starts: dyadic starts outside the terminal bad set `D_Y`.-/
def goodStarts (N L Y : ℕ) : Finset ℕ :=
  dyadicBlock N \ terminalBadStarts N L Y

/--
@isnad1 id=iff.0h4v.s5.6bc67598044e from=translated src=- shape=e631d21a vocab=cd927e34
-/
@[simp]
theorem mem_goodStarts {N L Y x : ℕ} :
    x ∈ goodStarts N L Y ↔
      x ∈ dyadicBlock N ∧ x ∉ terminalBadStarts N L Y := by
  simp [goodStarts]

/--
Adjacency before restricting the vertex set: distinct starts share at least
one large-prime coordinate.-/
def LargePrimeAdjacent (L Y x y : ℕ) : Prop :=
  x ≠ y ∧
    (largePrimeCoordinates x L Y ∩
      largePrimeCoordinates y L Y).Nonempty

/--
@isnad1 id=largepri.1h4v.s4.6140a8e022ac from=translated src=- shape=8ddedaae vocab=1f63405b
-/
theorem largePrimeAdjacent_symm
    {L Y x y : ℕ} :
    LargePrimeAdjacent L Y x y →
      LargePrimeAdjacent L Y y x := by
  rintro ⟨hxy, ⟨p, hp⟩⟩
  have hp' := Finset.mem_inter.mp hp
  exact ⟨hxy.symm,
    ⟨p, Finset.mem_inter.mpr ⟨hp'.2, hp'.1⟩⟩⟩

/--
@isnad1 id=not.0h3v.s3.b8ffe28531ac from=translated src=- shape=627c77a1 vocab=1f63405b
-/
theorem not_largePrimeAdjacent_self
    (L Y x : ℕ) :
    ¬LargePrimeAdjacent L Y x x := by
  intro h
  exact h.1 rfl

/-- The literal simple graph on the finite subtype of good starts.-/
def largePrimeDependencyGraph (N L Y : ℕ) :
    SimpleGraph {x : ℕ // x ∈ goodStarts N L Y} where
  Adj x y := LargePrimeAdjacent L Y x.1 y.1
  symm := ⟨fun _ _ h ↦ largePrimeAdjacent_symm h⟩
  loopless := ⟨fun x h ↦ not_largePrimeAdjacent_self L Y x.1 h⟩

/--
@isnad1 id=iff.0h5v.s6.511bc8a5b64f from=translated src=- shape=b5037e6a vocab=e1441411
-/
@[simp]
theorem largePrimeDependencyGraph_adj
    {N L Y : ℕ}
    {x y : {z : ℕ // z ∈ goodStarts N L Y}} :
    (largePrimeDependencyGraph N L Y).Adj x y ↔
      LargePrimeAdjacent L Y x.1 y.1 :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s5.8e37dde8a942 from=translated src=- shape=114a3e77 vocab=e2b031e4
-/
theorem largePrimeAdjacent_iff
    {L Y x y : ℕ} :
    LargePrimeAdjacent L Y x y ↔
      x ≠ y ∧
        ∃ p,
          p ∈ largePrimeCoordinates x L Y ∧
          p ∈ largePrimeCoordinates y L Y := by
  constructor
  · rintro ⟨hxy, ⟨p, hp⟩⟩
    exact ⟨hxy, p, Finset.mem_inter.mp hp⟩
  · rintro ⟨hxy, p, hpx, hpy⟩
    exact ⟨hxy, ⟨p, Finset.mem_inter.mpr ⟨hpx, hpy⟩⟩⟩

/-! ## Local good pairs are edges -/

/--
A good start supplies a large prime at each of its non-root vertices.
@isnad1 id=ex.2h5v.s6.780c4bec4508 from=translated src=- shape=a36b8c86 vocab=468340ae
-/
theorem exists_largePrime_of_mem_runSupport_of_good
    {N L Y x n : ℕ}
    (hx : x ∈ goodStarts N L Y)
    (hn : n ∈ startRunSupport x L) :
    ∃ p,
      p ∈ largeOddPrimeSupport Y n ∧
        p ∈ largePrimeCoordinates x L Y := by
  obtain ⟨j, hj, rfl⟩ := mem_startRunSupport.mp hn
  have hkernel :
      largeOddKernel Y (x + j) ≠ 1 := by
    intro h
    exact (mem_goodStarts.mp hx).2
      (mem_terminalBadStarts.mpr
        ⟨(mem_goodStarts.mp hx).1, j, hj, h⟩)
  have hsupport :
      (largeOddPrimeSupport Y (x + j)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact hkernel
      ((largeOddKernel_eq_one_iff_support_eq_empty Y (x + j)).mpr
        hempty)
  obtain ⟨p, hp⟩ := hsupport
  refine ⟨p, hp, mem_largePrimeCoordinates.mpr ?_⟩
  exact ⟨x + j, mem_startTreeSupport.mpr
    (Or.inr ⟨j, hj, rfl⟩), hp⟩

/--
If a non-root vertex of one good start belongs to the complete support of a
second start, the same large prime witnesses an edge.
@isnad1 id=largepri.4h6v.s6.99819d1ee78d from=translated src=- shape=66edff44 vocab=3cca0ba0
-/
theorem largePrimeAdjacent_of_common_run_tree_vertex
    {N L Y x y n : ℕ}
    (hxy : x ≠ y)
    (hx : x ∈ goodStarts N L Y)
    (hnx : n ∈ startRunSupport x L)
    (hny : n ∈ startTreeSupport y L) :
    LargePrimeAdjacent L Y x y := by
  obtain ⟨p, hpn, hpx⟩ :=
    exists_largePrime_of_mem_runSupport_of_good hx hnx
  refine (largePrimeAdjacent_iff.mpr
    ⟨hxy, p, hpx, ?_⟩)
  exact mem_largePrimeCoordinates.mpr ⟨n, hny, hpn⟩

/--
Oriented local-pair statement.  The common vertex is `y-1`: it is a
non-root vertex of the earlier start and the root of the later start.
@isnad1 id=largepri.3h5v.s5.90ea97881ff6 from=translated src=- shape=14553f71 vocab=b5b01e26
-/
theorem largePrimeAdjacent_of_lt_of_sub_le
    {N L Y x y : ℕ}
    (hx : x ∈ goodStarts N L Y)
    (hxy : x < y)
    (hgap : y - x ≤ L) :
    LargePrimeAdjacent L Y x y := by
  have hrun : y - 1 ∈ startRunSupport x L := by
    apply mem_startRunSupport.mpr
    refine ⟨(y - 1) - x, ?_, ?_⟩
    · omega
    · omega
  have htree : y - 1 ∈ startTreeSupport y L :=
    mem_startTreeSupport.mpr (Or.inl rfl)
  exact largePrimeAdjacent_of_common_run_tree_vertex
    (Nat.ne_of_lt hxy) hx hrun htree

/--
Symmetric local-pair form used in Lemma 13.5: two distinct good starts whose
natural-number distance is at most `L` are adjacent.
@isnad1 id=largepri.4h5v.s5.dc65066d6b44 from=translated src=- shape=838e6dd9 vocab=7d440359
-/
theorem largePrimeAdjacent_of_good_of_dist_le
    {N L Y x y : ℕ}
    (hx : x ∈ goodStarts N L Y)
    (hy : y ∈ goodStarts N L Y)
    (hxy : x ≠ y)
    (hdist : Nat.dist x y ≤ L) :
    LargePrimeAdjacent L Y x y := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · rw [Nat.dist_eq_sub_of_le hlt.le] at hdist
    exact largePrimeAdjacent_of_lt_of_sub_le hx hlt hdist
  · rw [Nat.dist_eq_sub_of_le_right hgt.le] at hdist
    exact largePrimeAdjacent_symm
      (largePrimeAdjacent_of_lt_of_sub_le hy hgt hdist)

/--
The shared coordinate in a local good pair is a genuine prime strictly above
the conditioning cutoff.
@isnad1 id=ex.4h5v.s6.a6de972faa9c from=translated src=- shape=1ecafbfc vocab=7ebe03d0
-/
theorem exists_shared_largePrime_of_good_of_dist_le
    {N L Y x y : ℕ}
    (hx : x ∈ goodStarts N L Y)
    (hy : y ∈ goodStarts N L Y)
    (hxy : x ≠ y)
    (hdist : Nat.dist x y ≤ L) :
    ∃ p,
      p.Prime ∧ Y < p ∧
        p ∈ largePrimeCoordinates x L Y ∧
        p ∈ largePrimeCoordinates y L Y := by
  have hadj :=
    largePrimeAdjacent_of_good_of_dist_le hx hy hxy hdist
  obtain ⟨p, hpx, hpy⟩ :=
    (largePrimeAdjacent_iff.mp hadj).2
  obtain ⟨n, _hnTree, hpn⟩ :=
    mem_largePrimeCoordinates.mp hpx
  have hpData :=
    prime_and_large_of_mem_largeOddPrimeSupport hpn
  exact ⟨p, hpData.1, hpData.2, hpx, hpy⟩

/-- Overlapping distinct good starts share a prime coordinate above `Y`.
@isnad1 id=ex.4h5v.s6.7041f93a624a from=translated src=- shape=d0835835 vocab=8e56473c
-/
theorem exists_shared_largePrime_of_good_of_dist_lt
    {N L Y x y : ℕ}
    (hx : x ∈ goodStarts N L Y)
    (hy : y ∈ goodStarts N L Y)
    (hxy : x ≠ y)
    (hdist : Nat.dist x y < L) :
    ∃ p,
      p.Prime ∧ Y < p ∧
        p ∈ largePrimeCoordinates x L Y ∧
        p ∈ largePrimeCoordinates y L Y :=
  exists_shared_largePrime_of_good_of_dist_le
    hx hy hxy hdist.le

/-- Touching distinct good starts share a prime coordinate above `Y`.
@isnad1 id=ex.4h5v.s6.09a80740b707 from=translated src=- shape=1ecafbfc vocab=8e56473c
-/
theorem exists_shared_largePrime_of_good_of_dist_eq
    {N L Y x y : ℕ}
    (hx : x ∈ goodStarts N L Y)
    (hy : y ∈ goodStarts N L Y)
    (hxy : x ≠ y)
    (hdist : Nat.dist x y = L) :
    ∃ p,
      p.Prime ∧ Y < p ∧
        p ∈ largePrimeCoordinates x L Y ∧
        p ∈ largePrimeCoordinates y L Y :=
  exists_shared_largePrime_of_good_of_dist_le
    hx hy hxy hdist.le

/-! ## Ordered edges and the first-shared-prime cover -/

/-- Ordered distinct edges among the good starts.-/
def orderedDependencyEdges (N L Y : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    ((goodStarts N L Y).product (goodStarts N L Y)).filter
      fun xy ↦ LargePrimeAdjacent L Y xy.1 xy.2

/--
@isnad1 id=iff.0h4v.s6.6e5496c2fd87 from=translated src=- shape=eae28b95 vocab=c0a81d74
-/
@[simp]
theorem mem_orderedDependencyEdges
    {N L Y : ℕ} {xy : ℕ × ℕ} :
    xy ∈ orderedDependencyEdges N L Y ↔
      xy.1 ∈ goodStarts N L Y ∧
        xy.2 ∈ goodStarts N L Y ∧
          LargePrimeAdjacent L Y xy.1 xy.2 := by
  classical
  rcases xy with ⟨x, y⟩
  simp [orderedDependencyEdges, and_assoc]

/-- Reversing an ordered edge gives an ordered edge.
@isnad1 id=mem.1h5v.s6.3fbd741705ff from=translated src=- shape=4f848001 vocab=d72864fa
-/
theorem swap_mem_orderedDependencyEdges
    {N L Y x y : ℕ}
    (hxy : (x, y) ∈ orderedDependencyEdges N L Y) :
    (y, x) ∈ orderedDependencyEdges N L Y := by
  rw [mem_orderedDependencyEdges] at hxy ⊢
  exact ⟨hxy.2.1, hxy.1,
    largePrimeAdjacent_symm hxy.2.2⟩

/-- Ordered dependency edges have explicitly distinct endpoints.
@isnad1 id=ne.1h5v.s5.a9da6d939f4e from=translated src=- shape=3c96f106 vocab=d72864fa
-/
theorem ne_of_mem_orderedDependencyEdges
    {N L Y x y : ℕ}
    (hxy : (x, y) ∈ orderedDependencyEdges N L Y) :
    x ≠ y :=
  (mem_orderedDependencyEdges.mp hxy).2.2.1

/-- There are no diagonal ordered dependency edges.
@isnad1 id=not.0h4v.s5.0678a4fde248 from=translated src=- shape=025c2de6 vocab=d72864fa
-/
theorem pair_self_not_mem_orderedDependencyEdges
    (N L Y x : ℕ) :
    (x, x) ∉ orderedDependencyEdges N L Y := by
  intro h
  exact ne_of_mem_orderedDependencyEdges h rfl

/-- The finite set of primes in the range used in Lemma 13.6.-/
def largePrimesInRange (Y X : ℕ) : Finset ℕ :=
  (Finset.Ioc Y X).filter Nat.Prime

/--
@isnad1 id=iff.0h3v.s5.0e18945b01b9 from=translated src=- shape=79037f53 vocab=35aa90fe
-/
@[simp]
theorem mem_largePrimesInRange {Y X p : ℕ} :
    p ∈ largePrimesInRange Y X ↔
      p.Prime ∧ Y < p ∧ p ≤ X := by
  simp only [largePrimesInRange, Finset.mem_filter,
    Finset.mem_Ioc]
  tauto

/-- Good starts whose complete support uses the prime coordinate `p`.-/
def startsUsingPrime (N L Y p : ℕ) : Finset ℕ :=
  (goodStarts N L Y).filter fun x ↦
    p ∈ largePrimeCoordinates x L Y

/--
@isnad1 id=iff.0h5v.s5.edb09ca01019 from=translated src=- shape=62d80dd4 vocab=6e106d5c
-/
@[simp]
theorem mem_startsUsingPrime {N L Y p x : ℕ} :
    x ∈ startsUsingPrime N L Y p ↔
      x ∈ goodStarts N L Y ∧
        p ∈ largePrimeCoordinates x L Y := by
  simp [startsUsingPrime]

/-- Ordered pairs of good starts sharing one prescribed prime.-/
def orderedPairsUsingPrime
    (N L Y p : ℕ) : Finset (ℕ × ℕ) :=
  (startsUsingPrime N L Y p).product
    (startsUsingPrime N L Y p)

/--
@isnad1 id=iff.0h5v.s6.6cc2138d9361 from=translated src=- shape=943b0878 vocab=812f8491
-/
@[simp]
theorem mem_orderedPairsUsingPrime
    {N L Y p : ℕ} {xy : ℕ × ℕ} :
    xy ∈ orderedPairsUsingPrime N L Y p ↔
      xy.1 ∈ startsUsingPrime N L Y p ∧
        xy.2 ∈ startsUsingPrime N L Y p := by
  simp [orderedPairsUsingPrime]

/-- Union of all ordered-pair covers, indexed by the first shared prime.-/
def orderedPrimeWitnessCover
    (N L Y : ℕ) : Finset (ℕ × ℕ) :=
  (largePrimesInRange Y (3 * N)).biUnion fun p ↦
    orderedPairsUsingPrime N L Y p

/--
A prime coordinate used by a dyadic start lies at most at `3N`, provided
`L ≤ N`.  This is the support cutoff used in Lemma 13.6.
@isnad1 id=mem.4h5v.s6.8d0f15cf8a2b from=translated src=- shape=00195984 vocab=970a9d92
-/
theorem mem_largePrimesInRange_of_mem_coordinates
    {N L Y x p : ℕ}
    (hN : 2 ≤ N)
    (hL : L ≤ N)
    (hx : x ∈ goodStarts N L Y)
    (hp : p ∈ largePrimeCoordinates x L Y) :
    p ∈ largePrimesInRange Y (3 * N) := by
  obtain ⟨n, hnTree, hpn⟩ :=
    mem_largePrimeCoordinates.mp hp
  have hpData :=
    prime_and_large_of_mem_largeOddPrimeSupport hpn
  have hxBlock := (mem_goodStarts.mp hx).1
  have hxBounds :
      N ≤ x ∧ x < 2 * N := by
    simpa [dyadicBlock] using
      (Finset.mem_Ico.mp
        (by simpa [dyadicBlock] using hxBlock))
  have hnPos : 0 < n := by
    rcases mem_startTreeSupport.mp hnTree with
      hroot | ⟨j, hj, hlabel⟩
    · rw [hroot]
      omega
    · rw [← hlabel]
      omega
  have hnUpper : n ≤ 3 * N := by
    rcases mem_startTreeSupport.mp hnTree with
      hroot | ⟨j, hj, hlabel⟩
    · rw [hroot]
      omega
    · rw [← hlabel]
      omega
  have hpDvd : p ∣ n :=
    Nat.dvd_of_mem_primeFactors
      (largeOddPrimeSupport_subset_primeFactors Y n hpn)
  exact mem_largePrimesInRange.mpr
    ⟨hpData.1, hpData.2,
      (Nat.le_of_dvd hnPos hpDvd).trans hnUpper⟩

/-- Every ordered edge is covered by at least one shared-prime pair set.
@isnad1 id=le.2h3v.s5.4ad00a05615a from=translated src=- shape=5652f827 vocab=86928ccf
-/
theorem orderedDependencyEdges_subset_primeWitnessCover
    {N L Y : ℕ}
    (hN : 2 ≤ N)
    (hL : L ≤ N) :
    orderedDependencyEdges N L Y ⊆
      orderedPrimeWitnessCover N L Y := by
  intro xy hxy
  have hedge := mem_orderedDependencyEdges.mp hxy
  obtain ⟨p, hpx, hpy⟩ :=
    (largePrimeAdjacent_iff.mp hedge.2.2).2
  rw [orderedPrimeWitnessCover, Finset.mem_biUnion]
  refine ⟨p,
    mem_largePrimesInRange_of_mem_coordinates
      hN hL hedge.1 hpx, ?_⟩
  exact mem_orderedPairsUsingPrime.mpr
    ⟨mem_startsUsingPrime.mpr ⟨hedge.1, hpx⟩,
      mem_startsUsingPrime.mpr ⟨hedge.2.1, hpy⟩⟩

/--
First-shared-prime overcount: the number of ordered edges is at most the sum
of the squares of the numbers of starts using each prime.
@isnad1 id=le.2h3v.s6.30212bfe1b1a from=translated src=- shape=ea10867d vocab=f15bade0
-/
theorem card_orderedDependencyEdges_le_sum_sq
    {N L Y : ℕ}
    (hN : 2 ≤ N)
    (hL : L ≤ N) :
    (orderedDependencyEdges N L Y).card ≤
      ∑ p ∈ largePrimesInRange Y (3 * N),
        (startsUsingPrime N L Y p).card ^ 2 := by
  calc
    (orderedDependencyEdges N L Y).card ≤
        (orderedPrimeWitnessCover N L Y).card :=
      Finset.card_le_card
        (orderedDependencyEdges_subset_primeWitnessCover hN hL)
    _ ≤ ∑ p ∈ largePrimesInRange Y (3 * N),
          (orderedPairsUsingPrime N L Y p).card := by
      exact Finset.card_biUnion_le
    _ = ∑ p ∈ largePrimesInRange Y (3 * N),
          (startsUsingPrime N L Y p).card ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp [orderedPairsUsingPrime, pow_two]

/-! ## Counting the starts which use one prime -/

/--
Dyadic starts for which the vertex at complete-tree offset `j` is divisible
by `p`.-/
def startsWithDivisibleOffset
    (N p j : ℕ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦
    p ∣ x - 1 + j

/--
@isnad1 id=iff.0h4v.s5.9ef0a46a9383 from=translated src=- shape=12899a3c vocab=b9f5f0ee
-/
@[simp]
theorem mem_startsWithDivisibleOffset
    {N p j x : ℕ} :
    x ∈ startsWithDivisibleOffset N p j ↔
      x ∈ dyadicBlock N ∧ p ∣ x - 1 + j := by
  simp [startsWithDivisibleOffset]

/--
Divisibility of the offset vertex is a single residue class in the start
variable.  The positivity assumption prevents truncated subtraction at zero.
@isnad1 id=iff.2h3v.s6.ea604c55744f from=translated src=- shape=097512da vocab=6c186314
-/
theorem dvd_sub_one_add_iff_modEq
    {p x j : ℕ}
    (hx : 1 ≤ x)
    (hj : j ≤ p + 1) :
    p ∣ x - 1 + j ↔
      x ≡ p + 1 - j [MOD p] := by
  rw [Nat.modEq_iff_dvd]
  have hleftCast :
      ((x - 1 + j : ℕ) : ℤ) =
        (x : ℤ) - 1 + (j : ℤ) := by
    push_cast
    omega
  have hrightCast :
      ((p + 1 - j : ℕ) : ℤ) =
        (p : ℤ) + 1 - (j : ℤ) := by
    omega
  constructor
  · intro h
    have h' : (p : ℤ) ∣ ((x - 1 + j : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [hleftCast] at h'
    rw [hrightCast]
    convert Int.dvd_sub (dvd_refl (p : ℤ)) h' using 1
    all_goals ring
  · intro h
    rw [hrightCast] at h
    have h' :
        (p : ℤ) ∣ (x : ℤ) - 1 + (j : ℤ) := by
      convert Int.dvd_sub (dvd_refl (p : ℤ)) h using 1
      all_goals ring
    rw [← hleftCast] at h'
    exact_mod_cast h'

/--
For a fixed complete-tree offset, a prime divides at most `N/p+1` labels as
the start ranges over the dyadic interval of length `N`.
@isnad1 id=le.3h3v.s6.2675245b1810 from=translated src=- shape=a5daeda3 vocab=48714ff2
-/
theorem card_startsWithDivisibleOffset_cast_le
    {N p j : ℕ}
    (hN : 1 ≤ N)
    (hp : 0 < p)
    (hj : j ≤ p + 1) :
    ((startsWithDivisibleOffset N p j).card : ℚ) ≤
      (N : ℚ) / (p : ℚ) + 1 := by
  have hset :
      startsWithDivisibleOffset N p j =
        (Finset.Ico N (2 * N)).filter
          fun x ↦ x ≡ p + 1 - j [MOD p] := by
    ext x
    simp only [mem_startsWithDivisibleOffset, dyadicBlock,
      Finset.mem_Ico, Finset.mem_filter]
    constructor
    · rintro ⟨hxInterval, hdiv⟩
      exact ⟨hxInterval,
        (dvd_sub_one_add_iff_modEq
          (hN.trans hxInterval.1) hj).mp hdiv⟩
    · rintro ⟨hxInterval, hmod⟩
      exact ⟨hxInterval,
        (dvd_sub_one_add_iff_modEq
          (hN.trans hxInterval.1) hj).mpr hmod⟩
  rw [hset]
  have hinterval :=
    card_nat_Ico_modEq_cast_le_div_add_one
      N (2 * N) (p + 1 - j) p hp (by omega)
  have hlength :
      (((2 * N : ℕ) : ℤ) - (N : ℤ)) = (N : ℤ) := by
    push_cast
    ring
  norm_num [hlength] at hinterval
  convert hinterval using 1
  all_goals ring

/--
Starts using `p` are covered by the union over the `L+1` possible vertices
of their complete support.
@isnad1 id=le.1h4v.s5.fdda61be15c7 from=translated src=- shape=6c69121d vocab=35708430
-/
theorem startsUsingPrime_subset_offsetUnion
    {N L Y p : ℕ}
    (hN : 1 ≤ N) :
    startsUsingPrime N L Y p ⊆
      (Finset.range (L + 1)).biUnion fun j ↦
        startsWithDivisibleOffset N p j := by
  intro x hx
  have hxData := mem_startsUsingPrime.mp hx
  obtain ⟨n, hnTree, hpn⟩ :=
    mem_largePrimeCoordinates.mp hxData.2
  have hpDvd : p ∣ n :=
    Nat.dvd_of_mem_primeFactors
      (largeOddPrimeSupport_subset_primeFactors Y n hpn)
  have hxBlock := (mem_goodStarts.mp hxData.1).1
  rw [Finset.mem_biUnion]
  rcases mem_startTreeSupport.mp hnTree with
    hroot | ⟨j, hj, hlabel⟩
  · refine ⟨0, by simp, ?_⟩
    rw [mem_startsWithDivisibleOffset]
    simpa [hroot] using And.intro hxBlock hpDvd
  · refine ⟨j + 1, by simpa using Nat.succ_lt_succ hj, ?_⟩
    rw [mem_startsWithDivisibleOffset]
    have hvertex : x - 1 + (j + 1) = n := by
      rw [← hlabel]
      have hxPos : 1 ≤ x := by
        have hxLower :
            N ≤ x := by
          exact
            (Finset.mem_Ico.mp
              (by simpa [dyadicBlock] using hxBlock)).1
        exact hN.trans hxLower
      omega
    exact ⟨hxBlock, hvertex ▸ hpDvd⟩

/--
Concrete one-prime start count.  The factor `L+1` is the number of vertices
of the complete start tree.
@isnad1 id=le.3h4v.s6.726df0f82b7e from=translated src=- shape=4e3fb6bf vocab=fb430e8a
-/
theorem card_startsUsingPrime_cast_le
    {N L Y p : ℕ}
    (hN : 1 ≤ N)
    (hLY : L ≤ Y)
    (hpY : Y < p) :
    ((startsUsingPrime N L Y p).card : ℚ) ≤
      (L + 1 : ℚ) * ((N : ℚ) / (p : ℚ) + 1) := by
  have hp : 0 < p := by omega
  calc
    ((startsUsingPrime N L Y p).card : ℚ) ≤
        (((Finset.range (L + 1)).biUnion fun j ↦
          startsWithDivisibleOffset N p j).card : ℚ) := by
      exact_mod_cast
        Finset.card_le_card
          (startsUsingPrime_subset_offsetUnion hN)
    _ ≤ ∑ j ∈ Finset.range (L + 1),
          ((startsWithDivisibleOffset N p j).card : ℚ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (L + 1),
          ((N : ℚ) / (p : ℚ) + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      apply card_startsWithDivisibleOffset_cast_le hN hp
      have hj' : j < L + 1 := by simpa using hj
      omega
    _ = (L + 1 : ℚ) * ((N : ℚ) / (p : ℚ) + 1) := by
      simp
      ring

/-! ## The finite edge estimate of Lemma 13.6 -/

/--
Exact pre-analytic form of the edge estimate in Lemma 13.6:

`E_Y ≤ (L+1)² ∑_{Y<p≤3N} (N/p+1)²`.

The sum is restricted to primes by `largePrimesInRange`.
@isnad1 id=le.3h3v.s7.046f91a00e34 from=translated src=- shape=12122ce6 vocab=58421cea
-/
theorem card_orderedDependencyEdges_cast_le_prime_sum
    {N L Y : ℕ}
    (hN : 2 ≤ N)
    (hLN : L ≤ N)
    (hLY : L ≤ Y) :
    ((orderedDependencyEdges N L Y).card : ℚ) ≤
      (L + 1 : ℚ) ^ 2 *
        ∑ p ∈ largePrimesInRange Y (3 * N),
          ((N : ℚ) / (p : ℚ) + 1) ^ 2 := by
  have hedge :=
    card_orderedDependencyEdges_le_sum_sq
      (N := N) (L := L) (Y := Y) hN hLN
  calc
    ((orderedDependencyEdges N L Y).card : ℚ) ≤
        ∑ p ∈ largePrimesInRange Y (3 * N),
          ((startsUsingPrime N L Y p).card : ℚ) ^ 2 := by
      exact_mod_cast hedge
    _ ≤ ∑ p ∈ largePrimesInRange Y (3 * N),
          ((L + 1 : ℚ) *
            ((N : ℚ) / (p : ℚ) + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply pow_le_pow_left₀
      · positivity
      · exact card_startsUsingPrime_cast_le
          (le_trans (by omega : 1 ≤ 2) hN)
          hLY (mem_largePrimesInRange.mp hp).2.1
    _ = (L + 1 : ℚ) ^ 2 *
        ∑ p ∈ largePrimesInRange Y (3 * N),
          ((N : ℚ) / (p : ℚ) + 1) ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]

end

end LargePrimeDependencyGraph
end PaperC
