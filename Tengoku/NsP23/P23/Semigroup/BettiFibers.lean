import Tengoku.NsP23.P23.Semigroup.FourGenerated
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite factorization fibers and their overlap components

This module is purely combinatorial.  It does not identify component counts
with generators of a toric or polynomial ideal.
-/

namespace P23.Semigroup

open scoped BigOperators

noncomputable section

namespace FourGeneratedNumericalSemigroup

variable (D : FourGeneratedNumericalSemigroup)

/-- The stable vertex type of the factorization fiber of degree `d`.-/
abbrev FactorizationAt (d : ℕ) := {u : Fin 4 →₀ ℕ // u ∈ D.factorizations d}

instance factorizationAtFintype (d : ℕ) : Fintype (D.FactorizationAt d) :=
  Fintype.ofFinset (D.factorizations d) (fun _ => Iff.rfl)

/--
@isnad1 id=eq.0h3v.s6.e69ca1723805 from=translated src=- shape=2fc74067 vocab=3ad2a69f
-/
@[simp] theorem factorizationAt_degree {d : ℕ} (u : D.FactorizationAt d) :
    D.weightedDegree u.1 = d :=
  D.mem_factorizations.mp u.2

/-- Variables occurring with positive exponent in a factorization.-/
def factorizationSupport {d : ℕ} (u : D.FactorizationAt d) : Finset (Fin 4) :=
  u.1.support

/--
@isnad1 id=iff.0h4v.s7.161d97d94ed9 from=translated src=- shape=1ee00799 vocab=c90f9839
-/
@[simp] theorem mem_factorizationSupport {d : ℕ} (u : D.FactorizationAt d)
    (j : Fin 4) :
    j ∈ D.factorizationSupport u ↔ 0 < u.1 j := by
  simp [factorizationSupport, Nat.pos_iff_ne_zero]

/-- Two factorizations overlap when they use a common generator.-/
def FactorizationOverlap {d : ℕ} (u v : D.FactorizationAt d) : Prop :=
  ∃ j : Fin 4, 0 < u.1 j ∧ 0 < v.1 j

/--
@isnad1 id=iff.0h4v.s4.e001ffed8ed9 from=translated src=- shape=f19b9d55 vocab=829a173f
-/
theorem factorizationOverlap_comm {d : ℕ} (u v : D.FactorizationAt d) :
    D.FactorizationOverlap u v ↔ D.FactorizationOverlap v u := by
  constructor <;> rintro ⟨j, hu, hv⟩ <;> exact ⟨j, hv, hu⟩

/-- The overlap graph on a fixed factorization fiber.-/
def factorizationGraph (d : ℕ) : SimpleGraph (D.FactorizationAt d) :=
  SimpleGraph.fromRel D.FactorizationOverlap

noncomputable instance factorizationGraphAdjDecidable (d : ℕ) :
    DecidableRel (D.factorizationGraph d).Adj := by
  classical
  exact Classical.decRel _

/--
@isnad1 id=iff.0h4v.s5.f14edc93d7d5 from=translated src=- shape=38cf086b vocab=3e9ad9d0
-/
@[simp] theorem factorizationGraph_adj {d : ℕ} (u v : D.FactorizationAt d) :
    (D.factorizationGraph d).Adj u v ↔
      u ≠ v ∧ D.FactorizationOverlap u v := by
  simp only [factorizationGraph, SimpleGraph.fromRel_adj]
  rw [D.factorizationOverlap_comm v u, or_self]

abbrev BettiComponent (d : ℕ) := (D.factorizationGraph d).ConnectedComponent

noncomputable instance bettiComponentFintype (d : ℕ) :
    Fintype (D.BettiComponent d) := by
  classical
  infer_instance

abbrev componentOf {d : ℕ} (u : D.FactorizationAt d) : D.BettiComponent d :=
  (D.factorizationGraph d).connectedComponentMk u

/-- Number `c_d` of overlap-connected components.-/
def componentCount (d : ℕ) : ℕ := Fintype.card (D.BettiComponent d)

/-- A Betti degree is a fiber with at least two overlap components.-/
def IsBettiDegree (d : ℕ) : Prop := 2 ≤ D.componentCount d

/--
@isnad1 id=iff.0h4v.s5.552d5f256330 from=translated src=- shape=3bfaa05a vocab=7ba75021
-/
theorem componentOf_eq_iff_reachable {d : ℕ} (u v : D.FactorizationAt d) :
    D.componentOf u = D.componentOf v ↔ (D.factorizationGraph d).Reachable u v :=
  SimpleGraph.ConnectedComponent.eq

/-- Support of one connected component.-/
def componentSupport {d : ℕ} (C : D.BettiComponent d) : Finset (Fin 4) :=
  by
    classical
    exact (Finset.univ.filter fun u : D.FactorizationAt d => D.componentOf u = C).biUnion
      (fun u => D.factorizationSupport u)

/-- Combined support `V_d` of the whole factorization fiber.-/
def combinedSupport (d : ℕ) : Finset (Fin 4) :=
  by
    classical
    exact Finset.univ.biUnion (fun u : D.FactorizationAt d => D.factorizationSupport u)

/-- Cardinality `v_d` of the combined fiber support.-/
def supportCard (d : ℕ) : ℕ := (D.combinedSupport d).card

/--
@isnad1 id=iff.0h4v.s7.ff2527893e8a from=translated src=- shape=1468f630 vocab=9ebecb5e
-/
theorem mem_componentSupport_iff {d : ℕ} {C : D.BettiComponent d} {j : Fin 4} :
    j ∈ D.componentSupport C ↔
      ∃ u : D.FactorizationAt d, D.componentOf u = C ∧ 0 < u.1 j := by
  classical
  constructor
  · intro hj
    obtain ⟨u, hu, hj⟩ := Finset.mem_biUnion.mp hj
    exact ⟨u, (Finset.mem_filter.mp hu).2, (D.mem_factorizationSupport u j).mp hj⟩
  · rintro ⟨u, huC, huj⟩
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huC⟩,
      (D.mem_factorizationSupport u j).mpr huj⟩

/--
@isnad1 id=iff.0h3v.s7.575e3a44dce4 from=translated src=- shape=164a957b vocab=831607d5
-/
theorem mem_combinedSupport_iff {d : ℕ} {j : Fin 4} :
    j ∈ D.combinedSupport d ↔ ∃ u : D.FactorizationAt d, 0 < u.1 j := by
  classical
  constructor
  · intro hj
    obtain ⟨u, _, hj⟩ := Finset.mem_biUnion.mp hj
    exact ⟨u, (D.mem_factorizationSupport u j).mp hj⟩
  · rintro ⟨u, huj⟩
    exact Finset.mem_biUnion.mpr
      ⟨u, Finset.mem_univ _, (D.mem_factorizationSupport u j).mpr huj⟩

/--
@isnad1 id=le.0h3v.s5.c67344cd126c from=translated src=- shape=941142ac vocab=9b0b6a4e
-/
theorem componentSupport_subset_combinedSupport {d : ℕ} (C : D.BettiComponent d) :
    D.componentSupport C ⊆ D.combinedSupport d := by
  intro j hj
  rw [D.mem_componentSupport_iff] at hj
  rw [D.mem_combinedSupport_iff]
  exact ⟨hj.choose, hj.choose_spec.2⟩

/--
@isnad1 id=eq.0h2v.s5.8852d3e81645 from=translated src=- shape=2357e844 vocab=3062c533
-/
theorem biUnion_componentSupport (d : ℕ) :
    Finset.univ.biUnion (fun C : D.BettiComponent d => D.componentSupport C) =
      D.combinedSupport d := by
  classical
  ext j
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨C, hj⟩
    exact D.componentSupport_subset_combinedSupport C hj
  · intro hj
    obtain ⟨u, hu⟩ := D.mem_combinedSupport_iff.mp hj
    exact ⟨D.componentOf u, D.mem_componentSupport_iff.mpr ⟨u, rfl, hu⟩⟩

/-- Distinct overlap components use disjoint generator sets.
@isnad1 id=disjoint.1h4v.s5.ddb5d67ad4c5 from=translated src=- shape=6dc67563 vocab=e315766c
-/
theorem componentSupport_disjoint {d : ℕ} {C E : D.BettiComponent d}
    (hCE : C ≠ E) : Disjoint (D.componentSupport C) (D.componentSupport E) := by
  classical
  rw [Finset.disjoint_left]
  intro j hjC hjE
  obtain ⟨u, huC, huj⟩ := D.mem_componentSupport_iff.mp hjC
  obtain ⟨v, hvE, hvj⟩ := D.mem_componentSupport_iff.mp hjE
  apply hCE
  rw [← huC, ← hvE]
  by_cases huv : u = v
  · exact congrArg D.componentOf huv
  · exact SimpleGraph.ConnectedComponent.sound
      ((D.factorizationGraph_adj u v).2 ⟨huv, ⟨j, huj, hvj⟩⟩).reachable

/--
@isnad1 id=pairwise.0h2v.s5.91b55bb6331f from=translated src=- shape=4d02e199 vocab=a22a1da8
-/
theorem componentSupport_pairwiseDisjoint (d : ℕ) :
    (Set.univ : Set (D.BettiComponent d)).PairwiseDisjoint D.componentSupport := by
  intro C _ E _ hCE
  exact D.componentSupport_disjoint hCE

/--
@isnad1 id=eq.1h3v.s7.96d886417536 from=translated src=- shape=6a6831aa vocab=62cb20bb
-/
theorem factorization_eq_zero_of_degree_eq_zero {d : ℕ} (hd : d = 0)
    (u : D.FactorizationAt d) : u.1 = 0 := by
  apply Finsupp.ext
  intro j
  have hle := D.factorization_coordinate_le
    (⟨u.1, D.factorizationAt_degree u⟩ : D.Factorization d) j
  simp [hd] at hle
  exact hle

/--
@isnad1 id=eq.0h3v.s5.3952e390d57b from=translated src=- shape=5a8b4ac5 vocab=48dad74c
-/
@[simp] theorem weightedDegree_single (j : Fin 4) (m : ℕ) :
    D.weightedDegree (Finsupp.single j m) = m * D.n j := by
  classical
  simp only [weightedDegreeOf]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Finsupp.single_apply, hkj]
  · simp

/--
@isnad1 id=nonempty.1h3v.s4.a292dd5801ba from=translated src=- shape=c5967874 vocab=36233bdd
-/
theorem componentSupport_nonempty_of_isBetti {d : ℕ} (hd : D.IsBettiDegree d)
    (C : D.BettiComponent d) : (D.componentSupport C).Nonempty := by
  classical
  obtain ⟨u, huC⟩ := SimpleGraph.ConnectedComponent.nonempty_supp C
  by_contra hempty
  have husupp : D.factorizationSupport u = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hsupp
    obtain ⟨j, hj⟩ := hsupp
    apply hempty
    exact ⟨j, D.mem_componentSupport_iff.mpr
      ⟨u, (SimpleGraph.ConnectedComponent.mem_supp_iff C u).mp huC,
        (D.mem_factorizationSupport u j).mp hj⟩⟩
  have hu0 : u.1 = 0 := Finsupp.support_eq_empty.mp husupp
  have hd0 : d = 0 := by simpa [hu0] using (D.factorizationAt_degree u).symm
  letI : Subsingleton (D.FactorizationAt d) :=
    ⟨fun x y => Subtype.ext (by
      rw [D.factorization_eq_zero_of_degree_eq_zero hd0 x,
        D.factorization_eq_zero_of_degree_eq_zero hd0 y])⟩
  have hcard : D.componentCount d ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  unfold IsBettiDegree at hd
  omega

/-- A component supported on exactly one generator.-/
def IsSingletonSupportComponent {d : ℕ} (C : D.BettiComponent d) : Prop :=
  (D.componentSupport C).card = 1

/-- Number `ell_d` of singleton-support components.-/
def singletonComponentCount (d : ℕ) : ℕ :=
  by
    classical
    exact (Finset.univ.filter fun C : D.BettiComponent d =>
      D.IsSingletonSupportComponent C).card

/-- The unique support variable of a singleton component (arbitrary only when
the support is empty, a branch never used by singleton theorems).-/
def singletonSupportVariable {d : ℕ} (C : D.BettiComponent d) : Fin 4 :=
  if h : (D.componentSupport C).Nonempty then h.choose else 0

/--
@isnad1 id=mem.1h3v.s5.b9d021027191 from=translated src=- shape=154279ea vocab=0af7f144
-/
theorem singletonSupportVariable_mem {d : ℕ} {C : D.BettiComponent d}
    (hC : D.IsSingletonSupportComponent C) :
    D.singletonSupportVariable C ∈ D.componentSupport C := by
  have hn : (D.componentSupport C).Nonempty := Finset.card_pos.mp (by
    unfold IsSingletonSupportComponent at hC
    omega)
  simp [singletonSupportVariable, hn, hn.choose_spec]

/--
@isnad1 id=eq.1h3v.s5.25f8f9eb005e from=translated src=- shape=74b4d9f0 vocab=10ae198c
-/
theorem componentSupport_eq_singleton {d : ℕ} {C : D.BettiComponent d}
    (hC : D.IsSingletonSupportComponent C) :
    D.componentSupport C = {D.singletonSupportVariable C} := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hC
  have hvar := D.singletonSupportVariable_mem hC
  rw [hj] at hvar
  have heq : D.singletonSupportVariable C = j := by simpa using hvar
  simpa [heq] using hj

/--
@isnad1 id=le.1h4v.s5.b6cc4a10036f from=translated src=- shape=769b03ae vocab=56ab6b6d
-/
theorem factorizationSupport_subset_componentSupport {d : ℕ}
    {C : D.BettiComponent d} {u : D.FactorizationAt d}
    (hu : D.componentOf u = C) :
    D.factorizationSupport u ⊆ D.componentSupport C := by
  intro j hj
  exact D.mem_componentSupport_iff.mpr
    ⟨u, hu, (D.mem_factorizationSupport u j).mp hj⟩

/--
@isnad1 id=eq.2h4v.s8.881388204731 from=translated src=- shape=4af7e269 vocab=89b0bc84
-/
theorem factorization_eq_single_of_singleton_component {d : ℕ}
    {C : D.BettiComponent d} (hC : D.IsSingletonSupportComponent C)
    {u : D.FactorizationAt d} (hu : D.componentOf u = C) :
    u.1 = Finsupp.single (D.singletonSupportVariable C)
      (u.1 (D.singletonSupportVariable C)) := by
  classical
  apply Finsupp.ext
  intro j
  by_cases hj : j = D.singletonSupportVariable C
  · subst j
    simp
  · have hjnot : j ∉ D.factorizationSupport u := by
      intro hmem
      have := D.factorizationSupport_subset_componentSupport hu hmem
      rw [D.componentSupport_eq_singleton hC] at this
      simpa [hj] using this
    have hz : u.1 j = 0 := by
      simpa [factorizationSupport] using hjnot
    simp [Finsupp.single_apply, hj, hz]

/--
@isnad1 id=eq.3h5v.s5.ec099b47089f from=translated src=- shape=98b78738 vocab=de877edd
-/
theorem singleton_component_vertex_unique {d : ℕ} {C : D.BettiComponent d}
    (hC : D.IsSingletonSupportComponent C)
    {u v : D.FactorizationAt d} (hu : D.componentOf u = C)
    (hv : D.componentOf v = C) : u = v := by
  apply Subtype.ext
  rw [D.factorization_eq_single_of_singleton_component hC hu,
    D.factorization_eq_single_of_singleton_component hC hv]
  apply congrArg (Finsupp.single (D.singletonSupportVariable C))
  have hdu := D.factorizationAt_degree u
  have hdv := D.factorizationAt_degree v
  rw [D.factorization_eq_single_of_singleton_component hC hu] at hdu
  rw [D.factorization_eq_single_of_singleton_component hC hv] at hdv
  simp only [D.weightedDegree_single] at hdu hdv
  have hn : 0 < D.n (D.singletonSupportVariable C) := D.positive _
  exact Nat.mul_right_cancel hn (hdu.trans hdv.symm)

/-- The fiber at `d` has a singleton-support component on variable `j`.-/
def HasSingletonComponentAt (j : Fin 4) (d : ℕ) : Prop :=
  ∃ C : D.BettiComponent d,
    D.IsSingletonSupportComponent C ∧ D.singletonSupportVariable C = j

private theorem singleton_degree_lt_impossible {j : Fin 4} {d₁ d₂ : ℕ}
    (h₁ : D.IsBettiDegree d₁) (h₂ : D.IsBettiDegree d₂)
    {C₁ : D.BettiComponent d₁} (hC₁ : D.IsSingletonSupportComponent C₁)
    (hj₁ : D.singletonSupportVariable C₁ = j)
    {C₂ : D.BettiComponent d₂} (hC₂ : D.IsSingletonSupportComponent C₂)
    (hj₂ : D.singletonSupportVariable C₂ = j)
    {u₁ : D.FactorizationAt d₁} (hu₁ : D.componentOf u₁ = C₁)
    {u₂ : D.FactorizationAt d₂} (hu₂ : D.componentOf u₂ = C₂)
    (hm : u₁.1 j < u₂.1 j) : False := by
  classical
  have hc₁gt : 1 < Fintype.card (D.BettiComponent d₁) := by
    unfold IsBettiDegree componentCount at h₁
    omega
  obtain ⟨E, hEC⟩ := Fintype.exists_ne_of_one_lt_card hc₁gt C₁
  have hEn : (D.componentSupport E).Nonempty :=
    D.componentSupport_nonempty_of_isBetti h₁ E
  obtain ⟨k, hkE⟩ := hEn
  obtain ⟨v, hvE, hvk⟩ := D.mem_componentSupport_iff.mp hkE
  have hC₁support : D.componentSupport C₁ = {j} := by
    rw [D.componentSupport_eq_singleton hC₁, hj₁]
  have hC₂support : D.componentSupport C₂ = {j} := by
    rw [D.componentSupport_eq_singleton hC₂, hj₂]
  have hjC₁ : j ∈ D.componentSupport C₁ := by simp [hC₁support]
  have hvj : v.1 j = 0 := by
    by_contra hvj0
    have hjE : j ∈ D.componentSupport E :=
      D.mem_componentSupport_iff.mpr ⟨v, hvE, Nat.pos_of_ne_zero hvj0⟩
    exact (Finset.disjoint_left.mp (D.componentSupport_disjoint hEC) hjE hjC₁)
  have hkj : k ≠ j := by
    intro h
    subst k
    exact (Nat.ne_of_gt hvk) hvj
  have hu₁pure := D.factorization_eq_single_of_singleton_component hC₁ hu₁
  have hu₂pure := D.factorization_eq_single_of_singleton_component hC₂ hu₂
  rw [hj₁] at hu₁pure
  rw [hj₂] at hu₂pure
  have hd₁ : d₁ = u₁.1 j * D.n j :=
    (D.factorizationAt_degree u₁).symm.trans
      ((congrArg D.weightedDegree hu₁pure).trans (D.weightedDegree_single j _))
  have hd₂ : d₂ = u₂.1 j * D.n j :=
    (D.factorizationAt_degree u₂).symm.trans
      ((congrArg D.weightedDegree hu₂pure).trans (D.weightedDegree_single j _))
  let shift : Fin 4 →₀ ℕ := Finsupp.single j (u₂.1 j - u₁.1 j)
  have hshiftDegree : D.weightedDegree (v.1 + shift) = d₂ := by
    rw [show D.weightedDegree (v.1 + shift) =
      D.weightedDegree v.1 + D.weightedDegree shift from weightedDegreeOf_add D.n v.1 shift]
    rw [show D.weightedDegree shift = (u₂.1 j - u₁.1 j) * D.n j by
      exact D.weightedDegree_single j _]
    rw [D.factorizationAt_degree v]
    calc
      d₁ + (u₂.1 j - u₁.1 j) * D.n j =
          u₁.1 j * D.n j + (u₂.1 j - u₁.1 j) * D.n j :=
        congrArg (fun z => z + (u₂.1 j - u₁.1 j) * D.n j) hd₁
      _ = (u₁.1 j + (u₂.1 j - u₁.1 j)) * D.n j := (Nat.add_mul ..).symm
      _ = u₂.1 j * D.n j :=
        congrArg (fun z => z * D.n j) (Nat.add_sub_of_le (Nat.le_of_lt hm))
      _ = d₂ := hd₂.symm
  let w : D.FactorizationAt d₂ :=
    ⟨v.1 + shift, D.mem_factorizations.mpr hshiftDegree⟩
  have hwj : 0 < w.1 j := by
    change 0 < (v.1 + shift) j
    simp [shift, hvj]
    omega
  have hu₂j : 0 < u₂.1 j := by omega
  have hwu : w ≠ u₂ := by
    intro heq
    have hkEq := congrArg (fun z : D.FactorizationAt d₂ => z.1 k) heq
    change (v.1 + shift) k = u₂.1 k at hkEq
    rw [hu₂pure] at hkEq
    simp [shift, Finsupp.single_apply, hkj] at hkEq
    omega
  have hcompw : D.componentOf w = C₂ := by
    rw [← hu₂]
    exact SimpleGraph.ConnectedComponent.sound
      ((D.factorizationGraph_adj w u₂).2 ⟨hwu, ⟨j, hwj, hu₂j⟩⟩).reachable
  exact hwu (D.singleton_component_vertex_unique hC₂ hcompw hu₂)

/-- A fixed generator can support a singleton Betti component in at most one
degree.  The proof shifts the smaller pure-power relation symbolically.
@isnad1 id=eq.4h4v.s5.9c2383d746b4 from=translated src=- shape=456fab4a vocab=bb074504
-/
theorem singletonComponent_degree_unique {j : Fin 4} {d₁ d₂ : ℕ}
    (h₁ : D.IsBettiDegree d₁) (h₂ : D.IsBettiDegree d₂)
    (hs₁ : D.HasSingletonComponentAt j d₁)
    (hs₂ : D.HasSingletonComponentAt j d₂) : d₁ = d₂ := by
  classical
  obtain ⟨C₁, hC₁, hj₁⟩ := hs₁
  obtain ⟨C₂, hC₂, hj₂⟩ := hs₂
  obtain ⟨u₁, hu₁⟩ := SimpleGraph.ConnectedComponent.nonempty_supp C₁
  obtain ⟨u₂, hu₂⟩ := SimpleGraph.ConnectedComponent.nonempty_supp C₂
  have hu₁C : D.componentOf u₁ = C₁ :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C₁ u₁).mp hu₁
  have hu₂C : D.componentOf u₂ = C₂ :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C₂ u₂).mp hu₂
  have hpure₁ := D.factorization_eq_single_of_singleton_component hC₁ hu₁C
  have hpure₂ := D.factorization_eq_single_of_singleton_component hC₂ hu₂C
  rw [hj₁] at hpure₁
  rw [hj₂] at hpure₂
  have hd₁ : d₁ = u₁.1 j * D.n j :=
    (D.factorizationAt_degree u₁).symm.trans
      ((congrArg D.weightedDegree hpure₁).trans (D.weightedDegree_single j _))
  have hd₂ : d₂ = u₂.1 j * D.n j :=
    (D.factorizationAt_degree u₂).symm.trans
      ((congrArg D.weightedDegree hpure₂).trans (D.weightedDegree_single j _))
  rcases lt_trichotomy (u₁.1 j) (u₂.1 j) with hlt | heq | hgt
  · exact False.elim (D.singleton_degree_lt_impossible h₁ h₂ hC₁ hj₁ hC₂ hj₂
      hu₁C hu₂C hlt)
  · simpa [hd₁, hd₂, heq]
  · exact False.elim (D.singleton_degree_lt_impossible h₂ h₁ hC₂ hj₂ hC₁ hj₁
      hu₂C hu₁C hgt)

/-- A singleton component at a Betti degree, retained with its degree.-/
structure SingletonBettiOccurrence where
  degree : ℕ
  isBetti : D.IsBettiDegree degree
  component : D.BettiComponent degree
  singleton : D.IsSingletonSupportComponent component

/-- The unique variable supporting a singleton occurrence.-/
def singletonOccurrenceVariable (o : D.SingletonBettiOccurrence) : Fin 4 :=
  D.singletonSupportVariable o.component

/--
@isnad1 id=injectiv.0h1v.s3.477b7bde22d0 from=translated src=- shape=dcea802f vocab=0a691138
-/
theorem singletonOccurrenceVariable_injective :
    Function.Injective D.singletonOccurrenceVariable := by
  intro a b hab
  rcases a with ⟨d₁, hd₁, C₁, hC₁⟩
  rcases b with ⟨d₂, hd₂, C₂, hC₂⟩
  dsimp [singletonOccurrenceVariable] at hab
  have hdeg : d₁ = d₂ := D.singletonComponent_degree_unique hd₁ hd₂
    ⟨C₁, hC₁, rfl⟩ ⟨C₂, hC₂, hab.symm⟩
  subst d₂
  have hcomp : C₁ = C₂ := by
    by_contra hne
    have hmem₁ := D.singletonSupportVariable_mem hC₁
    have hmem₂ := D.singletonSupportVariable_mem hC₂
    rw [hab] at hmem₁
    exact Finset.disjoint_left.mp (D.componentSupport_disjoint hne) hmem₁ hmem₂
  subst C₂
  rfl

/--
@isnad1 id=finite.0h1v.s2.f3a58e111526 from=translated src=- shape=76a08d12 vocab=078d3f95
-/
noncomputable instance singletonBettiOccurrenceFinite :
    Finite (D.SingletonBettiOccurrence) :=
  Finite.of_injective D.singletonOccurrenceVariable D.singletonOccurrenceVariable_injective

noncomputable instance singletonBettiOccurrenceFintype :
    Fintype (D.SingletonBettiOccurrence) := Fintype.ofFinite _

/--
@isnad1 id=le.0h1v.s3.081f8b4b8df2 from=translated src=- shape=f6b6ad72 vocab=0f06c9f4
-/
theorem singletonBettiOccurrence_card_le_four :
    Fintype.card (D.SingletonBettiOccurrence) ≤ 4 := by
  simpa using Fintype.card_le_of_injective D.singletonOccurrenceVariable
    D.singletonOccurrenceVariable_injective

end FourGeneratedNumericalSemigroup

end

end P23.Semigroup
