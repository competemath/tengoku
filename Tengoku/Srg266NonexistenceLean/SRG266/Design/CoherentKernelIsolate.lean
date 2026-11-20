/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.ArcDegree
import Tengoku.Srg266NonexistenceLean.SRG266.Design.CherryRecut
import Tengoku.Srg266NonexistenceLean.SRG266.Design.CoherentTripleLinks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.QuasiSymmetric

open scoped BigOperators

structure CoherentK11System (P : Type*) [DecidableEq P] where

  coordinate : ∀ p : P, {q : P // q ≠ p} ≃ Edge11

  coherent : ∀ {p q r : P} (hqp : q ≠ p) (hrp : r ≠ p) (hrq : r ≠ q),
    Edge11.vmeet (coordinate p ⟨q, hqp⟩) (coordinate p ⟨r, hrp⟩) = 1 ↔
      Edge11.vmeet (coordinate q ⟨p, hqp.symm⟩) (coordinate q ⟨r, hrq⟩) = 1

namespace CoherentK11System

variable {P : Type*} [DecidableEq P] (K : CoherentK11System P)

def localEdges (S : Finset P) (p : P) : Finset Edge11 :=
  Finset.univ.filter fun e => ((K.coordinate p).symm e : P) ∈ S

@[simp] theorem coordinate_mem_localEdges (S : Finset P) (p : P)
    (q : {q : P // q ≠ p}) :
    K.coordinate p q ∈ K.localEdges S p ↔ (q : P) ∈ S := by
  simp [localEdges]

theorem card_localEdges (S : Finset P) (p : P) :
    (K.localEdges S p).card = (S.erase p).card := by
  classical
  refine Finset.card_bij
    (fun e _ => ((K.coordinate p).symm e : P)) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_erase]
    exact ⟨((K.coordinate p).symm e).property,
      (Finset.mem_filter.mp he).2⟩
  · intro e₁ he₁ e₂ he₂ h
    have hsub : (K.coordinate p).symm e₁ = (K.coordinate p).symm e₂ :=
      Subtype.ext h
    exact (K.coordinate p).symm.injective hsub
  · intro q hq
    let q' : {r : P // r ≠ p} := ⟨q, (Finset.mem_erase.mp hq).1⟩
    refine ⟨K.coordinate p q', ?_, ?_⟩
    · rw [K.coordinate_mem_localEdges]
      exact (Finset.mem_erase.mp hq).2
    · exact congrArg Subtype.val ((K.coordinate p).symm_apply_apply q')

def IsLocallyEulerian (S : Finset P) : Prop :=
  ∀ p : P, ∀ v : Fin 11, Even (arcDegree (K.localEdges S p) v)

def IsInLineKernel (S : Finset P) : Prop :=
  ∀ p : P, ∀ e : Edge11,
    Even (∑ f ∈ K.localEdges S p, Edge11.vmeet e f)

def IsInAdjacencyKernel (S : Finset P) : Prop :=
  ∀ p : P, ∀ e : Edge11,
    Even ((K.localEdges S p).filter fun f => Edge11.vmeet e f = 1).card

theorem odd_vmeet_iff_eq_one (e f : Edge11) :
    Odd (Edge11.vmeet e f) ↔ Edge11.vmeet e f = 1 := by
  by_cases hef : e = f
  · subst f
    rw [Edge11.vmeet_self]
    norm_num
  · have hle := Edge11.vmeet_le_one hef
    constructor
    · rintro ⟨k, hk⟩
      omega
    · intro h
      rw [h]
      norm_num

theorem IsInAdjacencyKernel.isInLineKernel {S : Finset P}
    (hS : K.IsInAdjacencyKernel S) : K.IsInLineKernel S := by
  intro p e
  rw [Finset.even_sum_iff_even_card_odd]
  simpa [odd_vmeet_iff_eq_one] using hS p e

theorem IsInLineKernel.isLocallyEulerian {S : Finset P}
    (hS : K.IsInLineKernel S) : K.IsLocallyEulerian S := by
  classical
  intro p v
  let T := K.localEdges S p
  have hsumEven : Even (∑ u : Fin 11, arcDegree T u) := by
    rw [sum_arcDegree]
    exact ⟨T.card, by omega⟩
  by_contra hv
  have hvodd : Odd (arcDegree T v) := Nat.not_even_iff_odd.mp hv
  have hallOdd : ∀ u : Fin 11, Odd (arcDegree T u) := by
    intro u
    by_cases huv : u = v
    · simpa [huv] using hvodd
    · have hpairsum : Even (arcDegree T u + arcDegree T v) := by
        have hline := hS p (Edge11.mk' huv)
        rw [sum_vmeet_left, Edge11.vertices_mk',
          Finset.sum_pair huv] at hline
        exact hline
      have hparity : Even (arcDegree T u) ↔ Even (arcDegree T v) :=
        Nat.even_add.mp hpairsum
      exact Nat.not_even_iff_odd.mp fun hu => hv (hparity.mp hu)
  have hoddSet :
      ((Finset.univ : Finset (Fin 11)).filter fun u =>
        Odd (arcDegree T u)).card = 11 := by
    simp [hallOdd, Finset.card_univ, Fintype.card_fin]
  have hoddCardEven : Even
      (((Finset.univ : Finset (Fin 11)).filter fun u =>
        Odd (arcDegree T u)).card) := by
    rw [← Finset.even_sum_iff_even_card_odd]
    simpa using hsumEven
  rw [hoddSet] at hoddCardEven
  obtain ⟨k, hk⟩ := hoddCardEven
  omega

theorem exists_companion_of_even_degree {T : Finset Edge11} {e : Edge11}
    {v : Fin 11} (he : e ∈ T) (hv : v ∈ e.vertices)
    (heven : Even (arcDegree T v)) :
    ∃ f ∈ T, f ≠ e ∧ v ∈ f.vertices := by
  have hefilter : e ∈ T.filter fun f => v ∈ f.vertices :=
    Finset.mem_filter.mpr ⟨he, hv⟩
  have hpos : 0 < arcDegree T v := by
    rw [arcDegree]
    exact Finset.card_pos.mpr ⟨e, hefilter⟩
  obtain ⟨k, hk⟩ := heven
  have htwo : 2 ≤ arcDegree T v := by omega
  have hcard : 1 < (T.filter fun f => v ∈ f.vertices).card := by
    rw [arcDegree] at htwo
    omega
  obtain ⟨f, hf, hfe⟩ := Finset.exists_mem_ne hcard e
  exact ⟨f, (Finset.mem_filter.mp hf).1, hfe, (Finset.mem_filter.mp hf).2⟩

theorem vmeet_eq_zero_of_endpoint_degrees_zero {T : Finset Edge11}
    {u v : Fin 11} (huv : u ≠ v)
    (hu : arcDegree T u = 0) (hv : arcDegree T v = 0) {f : Edge11}
    (hf : f ∈ T) : Edge11.vmeet (Edge11.mk' huv) f = 0 := by
  by_contra hne
  have hpos : 0 < Edge11.vmeet (Edge11.mk' huv) f := Nat.pos_of_ne_zero hne
  have hinter : 0 < ((Edge11.mk' huv).vertices ∩ f.vertices).card := by
    simpa [Edge11.vmeet] using hpos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hinter
  rw [Finset.mem_inter, Edge11.vertices_mk'] at hw
  have hwdeg : 0 < arcDegree T w := by
    rw [arcDegree]
    exact Finset.card_pos.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, hw.2⟩⟩
  rcases Finset.mem_insert.mp hw.1 with rfl | hwv
  · omega
  · have : w = v := Finset.mem_singleton.mp hwv
    subst this
    omega

theorem unusedVertices_card_le_one {S : Finset P}
    (hS : K.IsLocallyEulerian S) {p : P} (hp : p ∈ S) :
    ((Finset.univ : Finset (Fin 11)).filter fun v =>
      arcDegree (K.localEdges S p) v = 0).card ≤ 1 := by
  classical
  by_contra hcard
  have htwo : 1 < ((Finset.univ : Finset (Fin 11)).filter fun v =>
      arcDegree (K.localEdges S p) v = 0).card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp htwo
  have hu0 : arcDegree (K.localEdges S p) u = 0 :=
    (Finset.mem_filter.mp hu).2
  have hv0 : arcDegree (K.localEdges S p) v = 0 :=
    (Finset.mem_filter.mp hv).2

  let e : Edge11 := Edge11.mk' huv
  let x' : {q : P // q ≠ p} := (K.coordinate p).symm e
  let x : P := x'
  have hxp : x ≠ p := x'.property
  have hxcoord : K.coordinate p x' = e := (K.coordinate p).apply_symm_apply e

  have hxS : x ∉ S := by
    intro hxmem
    have hemem : e ∈ K.localEdges S p := by
      rw [← hxcoord, K.coordinate_mem_localEdges]
      exact hxmem
    have hupos : 0 < arcDegree (K.localEdges S p) u := by
      rw [arcDegree]
      exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨hemem, by
        simp [e, Edge11.vertices_mk']⟩⟩
    omega

  let p' : {q : P // q ≠ x} := ⟨p, hxp.symm⟩
  let ep : Edge11 := K.coordinate x p'
  have hepmem : ep ∈ K.localEdges S x := by
    change K.coordinate x p' ∈ K.localEdges S x
    rw [K.coordinate_mem_localEdges]
    exact hp
  obtain ⟨w, hw⟩ := Edge11.exists_mem_vertices ep
  obtain ⟨f, hfmem, hfne, hwf⟩ :=
    exists_companion_of_even_degree hepmem hw (hS x w)

  let r' : {q : P // q ≠ x} := (K.coordinate x).symm f
  let r : P := r'
  have hrx : r ≠ x := r'.property
  have hrcoord : K.coordinate x r' = f := (K.coordinate x).apply_symm_apply f
  have hrS : r ∈ S := by
    rw [← K.coordinate_mem_localEdges S x r', hrcoord]
    exact hfmem
  have hrp : r ≠ p := by
    intro hrp
    apply hfne
    rw [← hrcoord]
    exact congrArg (K.coordinate x) (Subtype.ext hrp)

  let rAtP : {q : P // q ≠ p} := ⟨r, hrp⟩
  have hrmem : K.coordinate p rAtP ∈ K.localEdges S p := by
    rw [K.coordinate_mem_localEdges]
    exact hrS
  have hxmeet : Edge11.vmeet ep f = 1 :=
    Edge11.vmeet_eq_one hfne.symm hw hwf
  have hpmeet : Edge11.vmeet e (K.coordinate p rAtP) = 1 := by
    have hr'eq : (⟨r, hrx⟩ : {q : P // q ≠ x}) = r' := Subtype.ext rfl
    have hxmeet' :
        Edge11.vmeet (K.coordinate x ⟨p, hxp.symm⟩)
          (K.coordinate x ⟨r, hrx⟩) = 1 := by
      simpa [ep, p', hr'eq, hrcoord] using hxmeet
    have hcoh := (K.coherent hxp.symm hrx hrp).mp hxmeet'
    have hx'eq : (⟨x, hxp⟩ : {q : P // q ≠ p}) = x' := Subtype.ext rfl
    simpa [rAtP, hx'eq, hxcoord] using hcoh
  have hpzero : Edge11.vmeet e (K.coordinate p rAtP) = 0 :=
    vmeet_eq_zero_of_endpoint_degrees_zero huv hu0 hv0 hrmem
  omega

theorem ten_le_card_localEdges {S : Finset P}
    (hS : K.IsLocallyEulerian S) {p : P} (hp : p ∈ S) :
    10 ≤ (K.localEdges S p).card := by
  classical
  let used : Finset (Fin 11) :=
    Finset.univ.filter fun v => arcDegree (K.localEdges S p) v ≠ 0
  let unused : Finset (Fin 11) :=
    Finset.univ.filter fun v => arcDegree (K.localEdges S p) v = 0
  have hunused : unused.card ≤ 1 := by
    simpa [unused] using K.unusedVertices_card_le_one hS hp
  have hsplit : unused.card + used.card = 11 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 11)))
      (p := fun v => arcDegree (K.localEdges S p) v = 0)
    simpa [unused, used, Finset.card_univ, Fintype.card_fin] using h
  have hused : 10 ≤ used.card := by omega
  have hdegree : ∀ v ∈ used, 2 ≤ arcDegree (K.localEdges S p) v := by
    intro v hv
    have hne : arcDegree (K.localEdges S p) v ≠ 0 :=
      (Finset.mem_filter.mp hv).2
    obtain ⟨k, hk⟩ := hS p v
    omega
  have hsumUsed : 2 * used.card ≤
      ∑ v ∈ used, arcDegree (K.localEdges S p) v := by
    calc
      2 * used.card = ∑ v ∈ used, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ used, arcDegree (K.localEdges S p) v :=
        Finset.sum_le_sum fun v hv => hdegree v hv
  have hsumAll : (∑ v ∈ used, arcDegree (K.localEdges S p) v) ≤
      ∑ v : Fin 11, arcDegree (K.localEdges S p) v := by
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hincidence := sum_arcDegree (K.localEdges S p)
  rw [hincidence] at hsumAll
  omega

theorem eleven_le_card {S : Finset P} (hS : K.IsLocallyEulerian S)
    {p : P} (hp : p ∈ S) : 11 ≤ S.card := by
  have hlocal := K.ten_le_card_localEdges hS hp
  rw [K.card_localEdges, Finset.card_erase_of_mem hp] at hlocal
  omega

end CoherentK11System

namespace ConcreteQSD56

variable (Q : ConcreteQSD56)

def neEquivPunctured (p : Fin 56) : {q : Fin 56 // q ≠ p} ≃ Punctured p where
  toFun q := ⟨q, Finset.mem_erase.mpr
    ⟨q.property, Finset.mem_univ (q : Fin 56)⟩⟩
  invFun q := ⟨q, (Finset.mem_erase.mp q.property).1⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

noncomputable def toCoherentK11System : CoherentK11System (Fin 56) where
  coordinate p := (neEquivPunctured p).trans (Q.derived45 p).edgeEquiv
  coherent := by
    intro p q r hqp hrp hrq
    let qp : Punctured p := neEquivPunctured p ⟨q, hqp⟩
    let rp : Punctured p := neEquivPunctured p ⟨r, hrp⟩
    let pq : Punctured q := neEquivPunctured q ⟨p, hqp.symm⟩
    let rq : Punctured q := neEquivPunctured q ⟨r, hrq⟩
    change Edge11.vmeet ((Q.derived45 p).edgeEquiv qp)
        ((Q.derived45 p).edgeEquiv rp) = 1 ↔
      Edge11.vmeet ((Q.derived45 q).edgeEquiv pq)
        ((Q.derived45 q).edgeEquiv rq) = 1
    calc
      _ ↔ (Q.derived45 p).blockGraph.Adj qp rp :=
        ((Q.derived45 p).adj_iff_vmeet_edgeEquiv qp rp).symm
      _ ↔ Q.sparseTriple p q r := by
        change (Q.tripleLink p).Adj qp rp ↔ Q.sparseTriple p q r
        exact Q.tripleLink_adj_iff_sparseTriple
      _ ↔ Q.sparseTriple q p r := Q.sparseTriple_swap p q r
      _ ↔ (Q.derived45 q).blockGraph.Adj pq rq := by
        change Q.sparseTriple q p r ↔ (Q.tripleLink q).Adj pq rq
        simpa [pq, rq, neEquivPunctured] using
          (@Q.tripleLink_adj_iff_sparseTriple q pq rq).symm
      _ ↔ _ := (Q.derived45 q).adj_iff_vmeet_edgeEquiv pq rq

theorem coordinate_vmeet_iff_sparse (p : Fin 56)
    (q r : {x : Fin 56 // x ≠ p}) :
    Edge11.vmeet (Q.toCoherentK11System.coordinate p q)
        (Q.toCoherentK11System.coordinate p r) = 1 ↔
      Q.sparseTriple p q r := by
  let qp : Punctured p := neEquivPunctured p q
  let rp : Punctured p := neEquivPunctured p r
  change Edge11.vmeet ((Q.derived45 p).edgeEquiv qp)
      ((Q.derived45 p).edgeEquiv rp) = 1 ↔ Q.sparseTriple p q r
  calc
    _ ↔ (Q.derived45 p).blockGraph.Adj qp rp :=
      ((Q.derived45 p).adj_iff_vmeet_edgeEquiv qp rp).symm
    _ ↔ _ := by
      change (Q.tripleLink p).Adj qp rp ↔ Q.sparseTriple p q r
      simpa [qp, rp, neEquivPunctured] using
        (@Q.tripleLink_adj_iff_sparseTriple p qp rp)

noncomputable def sparseCompletionCount (S : Finset (Fin 56))
    (p q : Fin 56) : ℕ := by
  classical
  exact (S.filter fun r => Q.sparseTriple p q r).card

def IsSparseKernelSupport (S : Finset (Fin 56)) : Prop :=
  ∀ p q : Fin 56,
    Even (Q.sparseCompletionCount S p q)

def puncturedEmbedding (p : Fin 56) : Punctured p ↪ Fin 56 :=
  Function.Embedding.subtype _

noncomputable abbrev ambientTripleLink (p : Fin 56) : SimpleGraph (Fin 56) :=
  (Q.tripleLink p).map (puncturedEmbedding p)

noncomputable instance instDecidableTripleLinkAdj (p : Fin 56) :
    DecidableRel (Q.tripleLink p).Adj :=
  (Q.derived45 p).instDecidableRelAdjBlockGraph

noncomputable instance instDecidableAmbientTripleLinkAdj (p : Fin 56) :
    DecidableRel (Q.ambientTripleLink p).Adj := inferInstance

theorem ambientTripleLink_adj_iff_sparseTriple {p q r : Fin 56} :
    (Q.ambientTripleLink p).Adj q r ↔ Q.sparseTriple p q r := by
  constructor
  · rw [ambientTripleLink, SimpleGraph.map_adj]
    rintro ⟨q', r', hqr, rfl, rfl⟩
    exact Q.tripleLink_adj_iff_sparseTriple.mp hqr
  · intro h
    have hqp : q ≠ p := h.1.symm
    have hrp : r ≠ p := h.2.1.symm
    let q' : Punctured p :=
      ⟨q, Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ q⟩⟩
    let r' : Punctured p :=
      ⟨r, Finset.mem_erase.mpr ⟨hrp, Finset.mem_univ r⟩⟩
    have hlink : (Q.tripleLink p).Adj q' r' := by
      apply Q.tripleLink_adj_iff_sparseTriple.mpr
      simpa [q', r'] using h
    rw [ambientTripleLink, SimpleGraph.map_adj]
    exact ⟨q', r', hlink, rfl, rfl⟩

theorem card_tripleLink_edgeFinset (p : Fin 56) :
    (Q.tripleLink p).edgeFinset.card = 495 := by
  have hdegree := (Q.tripleLink_isSRGWith p).regular
  have hsum := (Q.tripleLink p).sum_degrees_eq_twice_card_edges
  simp_rw [hdegree.degree_eq] at hsum
  simp at hsum
  omega

theorem card_ambientTripleLink_edgeFinset (p : Fin 56) :
    (Q.ambientTripleLink p).edgeFinset.card = 495 := by
  change ((Q.tripleLink p).map (puncturedEmbedding p)).edgeFinset.card = 495
  rw [SimpleGraph.card_edgeFinset_map, Q.card_tripleLink_edgeFinset]

noncomputable def sparsePairColumnCount (S : Finset (Fin 56))
    (e : Sym2 (Fin 56)) : ℕ := by
  classical
  exact (S.filter fun p => e ∈ (Q.ambientTripleLink p).edgeFinset).card

theorem sparsePairColumnCount_mk (S : Finset (Fin 56)) (q r : Fin 56) :
    Q.sparsePairColumnCount S s(q, r) =
      Q.sparseCompletionCount S q r := by
  classical
  unfold sparsePairColumnCount sparseCompletionCount
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter]
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Q.ambientTripleLink_adj_iff_sparseTriple]
  exact and_congr_right fun _ => Q.sparseTriple_rotate p q r

theorem sparseKernel_column_even {S : Finset (Fin 56)}
    (hS : Q.IsSparseKernelSupport S) (e : Sym2 (Fin 56)) :
    Even (Q.sparsePairColumnCount S e) := by
  induction e using Sym2.inductionOn with
  | _ q r =>
      rw [Q.sparsePairColumnCount_mk]
      exact hS q r

theorem sum_sparsePairColumnCount (S : Finset (Fin 56)) :
    (∑ e : Sym2 (Fin 56), Q.sparsePairColumnCount S e) =
      495 * S.card := by
  classical
  let rel : Sym2 (Fin 56) → Fin 56 → Prop := fun e p =>
    e ∈ (Q.ambientTripleLink p).edgeFinset
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := (Finset.univ : Finset (Sym2 (Fin 56)))) (t := S)
  calc
    _ = ∑ p ∈ S,
        ((Finset.univ : Finset (Sym2 (Fin 56))).filter fun e =>
          rel e p).card := by
      simpa only [sparsePairColumnCount, rel,
        Finset.bipartiteAbove, Finset.bipartiteBelow] using hdouble
    _ = ∑ p ∈ S, (Q.ambientTripleLink p).edgeFinset.card := by
      apply Finset.sum_congr rfl
      intro p hp
      apply congrArg Finset.card
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, rel]
    _ = 495 * S.card := by
      simp [card_tripleLink_edgeFinset Q, mul_comm]

theorem sparseKernelSupport_card_even {S : Finset (Fin 56)}
    (hS : Q.IsSparseKernelSupport S) : Even S.card := by
  have htotal : Even
      (∑ e : Sym2 (Fin 56), Q.sparsePairColumnCount S e) := by
    exact Finset.even_sum _ fun e _ => Q.sparseKernel_column_even hS e
  rw [Q.sum_sparsePairColumnCount] at htotal
  obtain ⟨k, hk⟩ := htotal
  use k - 247 * S.card
  omega

noncomputable def pairThirdMatrix :
    Matrix (Fin 56) (Sym2 (Fin 56)) (ZMod 2) := fun p e =>
  if e ∈ (Q.ambientTripleLink p).edgeFinset then 1 else 0

noncomputable def supportVector (S : Finset (Fin 56)) : Fin 56 → ZMod 2 :=
  fun p => if p ∈ S then 1 else 0

theorem pairThirdMatrix_transpose_mulVec_support_apply
    (S : Finset (Fin 56)) (e : Sym2 (Fin 56)) :
    Matrix.mulVec (Matrix.transpose Q.pairThirdMatrix) (supportVector S) e =
      (Q.sparsePairColumnCount S e : ZMod 2) := by
  classical
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.transpose_apply, pairThirdMatrix, supportVector]
  calc
    (∑ p : Fin 56,
        (if e ∈ (Q.ambientTripleLink p).edgeFinset then 1 else 0) *
          if p ∈ S then 1 else 0) =
        ∑ p : Fin 56,
          if p ∈ S ∧ e ∈ (Q.ambientTripleLink p).edgeFinset
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpS : p ∈ S <;> simp [hpS]
    _ = (((Finset.univ : Finset (Fin 56)).filter fun p =>
          p ∈ S ∧
            e ∈ (Q.ambientTripleLink p).edgeFinset).card : ZMod 2) := by
      rw [Finset.sum_boole]
    _ = (Q.sparsePairColumnCount S e : ZMod 2) := by
      congr 1
      unfold sparsePairColumnCount
      apply congrArg Finset.card
      ext p
      simp

def IsPairThirdKernelSupport (S : Finset (Fin 56)) : Prop :=
  Matrix.mulVec (Matrix.transpose Q.pairThirdMatrix) (supportVector S) = 0

theorem isPairThirdKernelSupport_iff_columns_even
    (S : Finset (Fin 56)) :
    Q.IsPairThirdKernelSupport S ↔
      ∀ e : Sym2 (Fin 56), Even (Q.sparsePairColumnCount S e) := by
  constructor
  · intro h e
    have he := congrFun h e
    rw [Q.pairThirdMatrix_transpose_mulVec_support_apply] at he
    simpa using (ZMod.natCast_eq_zero_iff_even.mp he)
  · intro h
    funext e
    rw [Q.pairThirdMatrix_transpose_mulVec_support_apply]
    exact ZMod.natCast_eq_zero_iff_even.mpr (h e)

theorem isPairThirdKernelSupport_iff_sparseKernelSupport
    (S : Finset (Fin 56)) :
    Q.IsPairThirdKernelSupport S ↔ Q.IsSparseKernelSupport S := by
  rw [Q.isPairThirdKernelSupport_iff_columns_even]
  constructor
  · intro h p q
    rw [← Q.sparsePairColumnCount_mk]
    exact h s(p, q)
  · intro h e
    exact Q.sparseKernel_column_even h e

theorem card_filter_vmeet_eq_card_filter_sparse (S : Finset (Fin 56))
    (p : Fin 56) (e : Edge11) :
    ((Q.toCoherentK11System.localEdges S p).filter fun f =>
      Edge11.vmeet e f = 1).card =
      Q.sparseCompletionCount S p
        ((Q.toCoherentK11System.coordinate p).symm e : Fin 56) := by
  classical
  unfold sparseCompletionCount
  let q' : {q : Fin 56 // q ≠ p} :=
    (Q.toCoherentK11System.coordinate p).symm e
  have hqcoord : Q.toCoherentK11System.coordinate p q' = e :=
    (Q.toCoherentK11System.coordinate p).apply_symm_apply e
  refine Finset.card_bij
    (fun f _ => ((Q.toCoherentK11System.coordinate p).symm f : Fin 56)) ?_ ?_ ?_
  · intro f hf
    let r' : {r : Fin 56 // r ≠ p} :=
      (Q.toCoherentK11System.coordinate p).symm f
    have hrcoord : Q.toCoherentK11System.coordinate p r' = f :=
      (Q.toCoherentK11System.coordinate p).apply_symm_apply f
    have hfparts := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact (Finset.mem_filter.mp hfparts.1).2
    · apply (Q.coordinate_vmeet_iff_sparse p q' r').mp
      simpa [hqcoord, hrcoord] using hfparts.2
  · intro f₁ hf₁ f₂ hf₂ hval
    have hsub :
        (Q.toCoherentK11System.coordinate p).symm f₁ =
          (Q.toCoherentK11System.coordinate p).symm f₂ := Subtype.ext hval
    exact (Q.toCoherentK11System.coordinate p).symm.injective hsub
  · intro r hr
    have hrp : r ≠ p := by
      have hsparse := (Finset.mem_filter.mp hr).2
      exact hsparse.2.1.symm
    let r' : {x : Fin 56 // x ≠ p} := ⟨r, hrp⟩
    refine ⟨Q.toCoherentK11System.coordinate p r', ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [Q.toCoherentK11System.coordinate_mem_localEdges]
        exact (Finset.mem_filter.mp hr).1
      · rw [← hqcoord]
        apply (Q.coordinate_vmeet_iff_sparse p q' r').mpr
        simpa [q'] using (Finset.mem_filter.mp hr).2
    · exact congrArg Subtype.val
        ((Q.toCoherentK11System.coordinate p).symm_apply_apply r')

theorem sparseKernel_isInAdjacencyKernel {S : Finset (Fin 56)}
    (hS : Q.IsSparseKernelSupport S) :
    Q.toCoherentK11System.IsInAdjacencyKernel S := by
  intro p e
  rw [Q.card_filter_vmeet_eq_card_filter_sparse S p e]
  exact hS p ((Q.toCoherentK11System.coordinate p).symm e : Fin 56)

def IsEulerianKernelSupport (S : Finset (Fin 56)) : Prop :=
  Q.toCoherentK11System.IsLocallyEulerian S

def IsCoordinateKernelSupport (S : Finset (Fin 56)) : Prop :=
  Q.toCoherentK11System.IsInAdjacencyKernel S

theorem coordinateKernel_isEulerian {S : Finset (Fin 56)}
    (hS : Q.IsCoordinateKernelSupport S) : Q.IsEulerianKernelSupport S :=
  hS.isInLineKernel.isLocallyEulerian

theorem sparseKernel_isCoordinateKernel {S : Finset (Fin 56)}
    (hS : Q.IsSparseKernelSupport S) : Q.IsCoordinateKernelSupport S :=
  Q.sparseKernel_isInAdjacencyKernel hS

theorem kernelSupport_unusedVertices_card_le_one {S : Finset (Fin 56)}
    (hS : Q.IsEulerianKernelSupport S) {p : Fin 56} (hp : p ∈ S) :
    ((Finset.univ : Finset (Fin 11)).filter fun v =>
      arcDegree (Q.toCoherentK11System.localEdges S p) v = 0).card ≤ 1 :=
  Q.toCoherentK11System.unusedVertices_card_le_one hS hp

theorem eleven_le_card_kernelSupport {S : Finset (Fin 56)}
    (hS : Q.IsEulerianKernelSupport S) {p : Fin 56} (hp : p ∈ S) :
    11 ≤ S.card :=
  Q.toCoherentK11System.eleven_le_card hS hp

theorem twelve_le_card_kernelSupport {S : Finset (Fin 56)}
    (hS : Q.IsEulerianKernelSupport S) (heven : Even S.card)
    {p : Fin 56} (hp : p ∈ S) : 12 ≤ S.card := by
  have heleven := Q.eleven_le_card_kernelSupport hS hp
  obtain ⟨k, hk⟩ := heven
  omega

theorem twelve_le_card_coordinateKernelSupport {S : Finset (Fin 56)}
    (hS : Q.IsCoordinateKernelSupport S) (heven : Even S.card)
    {p : Fin 56} (hp : p ∈ S) : 12 ≤ S.card :=
  Q.twelve_le_card_kernelSupport (Q.coordinateKernel_isEulerian hS) heven hp

theorem twelve_le_card_sparseKernelSupport {S : Finset (Fin 56)}
    (hS : Q.IsSparseKernelSupport S) {p : Fin 56} (hp : p ∈ S) :
    12 ≤ S.card :=
  Q.twelve_le_card_coordinateKernelSupport
    (Q.sparseKernel_isCoordinateKernel hS)
    (Q.sparseKernelSupport_card_even hS) hp

theorem twelve_le_card_pairThirdKernelSupport {S : Finset (Fin 56)}
    (hS : Q.IsPairThirdKernelSupport S) {p : Fin 56} (hp : p ∈ S) :
    12 ≤ S.card :=
  Q.twelve_le_card_sparseKernelSupport
    ((Q.isPairThirdKernelSupport_iff_sparseKernelSupport S).mp hS) hp

theorem weightTwelve_local_constraints {S : Finset (Fin 56)}
    (hS : Q.IsEulerianKernelSupport S) (hcard : S.card = 12)
    {p : Fin 56} (hp : p ∈ S) :
    (Q.toCoherentK11System.localEdges S p).card = 11 ∧
    ((Finset.univ : Finset (Fin 11)).filter fun v =>
      arcDegree (Q.toCoherentK11System.localEdges S p) v = 0).card ≤ 1 ∧
    (∑ v : Fin 11,
      arcDegree (Q.toCoherentK11System.localEdges S p) v) = 22 ∧
    ∀ v : Fin 11,
      Even (arcDegree (Q.toCoherentK11System.localEdges S p) v) := by
  have hedgecard : (Q.toCoherentK11System.localEdges S p).card = 11 := by
    rw [Q.toCoherentK11System.card_localEdges,
      Finset.card_erase_of_mem hp, hcard]
  refine ⟨hedgecard, Q.kernelSupport_unusedVertices_card_le_one hS hp, ?_, hS p⟩
  rw [sum_arcDegree, hedgecard]

theorem sparseKernel_weightTwelve_local_constraints
    {S : Finset (Fin 56)} (hS : Q.IsSparseKernelSupport S)
    (hcard : S.card = 12) {p : Fin 56} (hp : p ∈ S) :
    (Q.toCoherentK11System.localEdges S p).card = 11 ∧
    ((Finset.univ : Finset (Fin 11)).filter fun v =>
      arcDegree (Q.toCoherentK11System.localEdges S p) v = 0).card ≤ 1 ∧
    (∑ v : Fin 11,
      arcDegree (Q.toCoherentK11System.localEdges S p) v) = 22 ∧
    ∀ v : Fin 11,
      Even (arcDegree (Q.toCoherentK11System.localEdges S p) v) :=
  Q.weightTwelve_local_constraints
    (Q.coordinateKernel_isEulerian (Q.sparseKernel_isCoordinateKernel hS))
    hcard hp

end ConcreteQSD56

end SRG266.QuasiSymmetric
