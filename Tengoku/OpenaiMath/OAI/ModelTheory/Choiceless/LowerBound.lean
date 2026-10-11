import Tengoku.OpenaiMath.OAI.ModelTheory.Choiceless.Traces

namespace OAI

noncomputable section

namespace CPTSeparation

end CPTSeparation

namespace CPTSeparation.Operational.Machine

open Classical Hereditary Counting HFCoding Finset

variable {R ι L : Type} {A : ι → Type} [finiteFamilyA : ∀ i, Fintype (A i)]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (P : Machine R)

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool)

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

include hd hp ha hmem hset hinput in
lemma uniform_runActive (ss : ∀ i, ℕ → P.Store (A := A i)) (h K J : ℕ)
    (hr : ∀ i j, j ≤ h → P.run (rel i) j = some (ss i j))
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (ht : ∀ i j, j < h → ∀ x ∈ P.rule.trace (rel i) (ss i j) Fin.elim0,
      x ∈ d i ∧ (elements x).card ≤ J)
    (hs : ∀ i j, j ≤ h → ∀ x ∈ (ss i j).active, x ∈ d i)
    (hK : ∀ i j, j ≤ h → (ss i j).active.card ≤ K) :
    UniformDefinable S m 1 (fun i v => (v 0).val ∈ P.runActive (rel i) h) := by
  let := P.finiteFunctions
  have hstage (j : ℕ) (hj : j ∈ range (h+1)) :
      UniformDefinable S m 1 (fun i v => (v 0).val ∈ (ss i j).active) := by
    have hjh : j ≤ h := by simpa using hj
    have hst := P.uniform_run d S hd hp ha hmem hset rel hinput ss j J
      (fun i k hk => hr i k (by omega)) hm hroom (fun i k hk => ht i k (by omega))
    exact State.uniform_active d S hd hp ha hmem hset (fun i => ss i j) hst hroom
      (fun f => by have := hm f; omega) (fun i => hs i j hjh) K (fun i => hK i j hjh)
  apply (UniformDefinable.exists_finset (range (h+1)) hstage).congr
  intro i v
  simp only [runActive,mem_biUnion]
  constructor
  · rintro ⟨j,hj,hv⟩
    exact ⟨j,hj,by simpa only [hr i j (by simpa using hj)] using hv⟩
  · rintro ⟨j,hj,hv⟩
    exact ⟨j,hj,by simpa only [hr i j (by simpa using hj)] using hv⟩

omit ι L A d S m in
lemma uniform_finite_family_card
    {ι : Type}
    {L : Type}
    {A : ι → Type}
    [(i : ι) → Fintype (A i)]
    (d : (i : ι) → Set (Hereditary.HF (A i)))
    (S : (i : ι) → Counting.Structure L (HFCoding.Domain (d i)))
    {m : ℕ} (t : ∀ i, Finset (HF (A i)))
    (ht : UniformDefinable S m 1 (fun i v => (v 0).val ∈ t i))
    (hs : ∀ i x, x ∈ t i → x ∈ d i) (hm : 1 ≤ m) (k : ℕ) :
    UniformDefinable S m 0 (fun i _ => (t i).card = k) := by
  apply (ht.exact (by omega) k).congr
  intro i v
  change Nonempty ({x : Domain (d i) // x.val ∈ t i} ≃ Fin k) ↔ _
  let e : {x : Domain (d i) // x.val ∈ t i} ≃ {x // x ∈ t i} :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      invFun := fun x => ⟨⟨x.val,hs i x.val x.property⟩,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  constructor
  · rintro ⟨f⟩
    have h := Fintype.card_congr (e.symm.trans f)
    simpa using h
  · intro h
    exact ⟨e.trans ((Fintype.equivFin _).trans (finCongr (by simpa using h)))⟩

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable {n m M N : ℕ} (P : Operational.Machine Symbol) (vstar : Vertex n)

lemma op_cumulative_agrees (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (ss : ∀ i : Bool, ℕ → P.Store (A := Atom (twoCharges vstar i)))
    (hr : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j))
    (ha : ∀ i j, j ≤ h → (ss i j).active.card ≤ K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+P.rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    (P.runActive (atomInput (twoCharges vstar false)).rel h).card =
      (P.runActive (atomInput (twoCharges vstar true)).rel h).card := by
  let s := ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊
  let D := programDomain (twoCharges vstar) (s := s)
  let C := programHF (twoCharges vstar) (s := s)
  have hbound (i : Bool) : ∀ j ≤ h, ∀ st, P.run (atomInput (twoCharges vstar i)).rel j = some st → st.active.card ≤ K := by
    intro j hj st hh
    have he : st = ss i j := Option.some.inj (hh.symm.trans (hr i j hj))
    exact he ▸ ha i j hj
  have hfamily (i : Bool) : ∀ x ∈ P.runTrace (atomInput (twoCharges vstar i)).rel h, x ∈ D i :=
    opTrace_supported (twoCharges vstar i) P hn h K N hN (hbound i) q hq hb
  have ht : ∀ i j, j < h → ∀ x ∈ P.rule.trace (atomInput (twoCharges vstar i)).rel (ss i j) Fin.elim0,
      x ∈ D i ∧ (elements x).card ≤ (h+1)*(K+P.rule.bound.eval K) := by
    intro i j hj x hx
    have hx' := P.rule_trace_subset (h := h) (atomInput (twoCharges vstar i)).rel (by omega) (hr i j (by omega)) hx
    refine ⟨hfamily i x hx',?_⟩
    have he : elements x ⊆ P.runTrace (atomInput (twoCharges vstar i)).rel h := by
      intro y hy
      exact P.runTrace_closed _ h x hx' y hy
    exact (card_le_card he).trans (P.card_runTrace_le _ h K (hbound i))
  have hdef := P.uniform_runActive D C (program_domain_transitive (twoCharges vstar))
    (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
    (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
    (fun i => (atomInput (twoCharges vstar i)).rel) (op_input_uniform (twoCharges vstar))
    ss h K ((h+1)*(K+P.rule.bound.eval K)) hr hm hroom ht
    (fun i j hj x hx => hfamily i x (P.active_subset_trace _ hj (hr i j hj) hx)) ha
  have hc := Operational.Machine.uniform_finite_family_card D C
    (fun i => P.runActive (atomInput (twoCharges vstar i)).rel h) hdef
    (fun i x hx => hfamily i x (mem_union_left _ hx)) (by omega)
    (P.runActive (atomInput (twoCharges vstar false)).rel h).card
  obtain ⟨φ,hφ,hφsem⟩ := hc (Fin.elim0 : Fin 0 → Fin m)
  have hfree : φ.free = ∅ := subset_empty.mp (by simpa using hφ)
  let v : Fin m → Domain (D false) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn false 0⟩
  let w : Fin m → Domain (D true) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn true 0⟩
  let := atom_nonempty hn (0 : Vertex n → Scalar)
  let := atom_nonempty hn (Pi.single vstar 1)
  have he := (hφsem false v).symm.trans ((grid_hf_transfer hn hs (by omega) vstar
    hwidth hhom hgiant φ hfree v w).trans (hφsem true w))
  exact (he.mp rfl).symm

end CPTSeparation.Grid

namespace CPTSeparation.Operational.Machine

section

open Classical Hereditary Finset

variable {A R : Type} [Fintype A]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (P : Machine R)

def cumulativeAccepts (rel : R → A → A → Bool) (time space : ℕ) : Prop :=
  ∃ h st, h ≤ time ∧ P.run rel h = some st ∧ P.flag st .halt ∧ P.flag st .accept ∧
    (P.runActive rel h).card ≤ space

lemma cumulative_implies_bounded (rel : R → A → A → Bool) {time space : ℕ}
    (ha : P.cumulativeAccepts rel time space) : P.boundedAccepts rel time space := by
  obtain ⟨h,st,hht,hhr,hhf,hha,hbudget⟩ := ha
  refine ⟨h,st,hht,hhr,hhf,hha,?_⟩
  intro j hj t ht
  exact (card_le_card (P.state_active_subset rel hj ht)).trans hbudget

lemma bounded_active_all (rel : R → A → A → Bool) {time space : ℕ}
    (ha : P.boundedAccepts rel time space) :
    ∀ j, ∃ st, P.run rel j = some st ∧ st.active.card ≤ space := by
  obtain ⟨h,st,hht,hhr,hhf,hha,hbudget⟩ := ha
  intro j
  by_cases hj : j ≤ h
  · obtain ⟨t,ht⟩ := P.run_prefix_exists rel hhr hj
    exact ⟨t,ht,hbudget j hj t ht⟩
  · exact ⟨st,P.halted_persists rel hhr hhf j (by omega),hbudget h (le_refl h) st hhr⟩

variable {B : Bool → Type} [∀ i, Fintype (B i)]

variable (rel : ∀ i, R → B i → B i → Bool)

lemma cumulative_accept_transfer (time space K : ℕ) (hS : space ≤ K)
    (hnext : space+P.rule.bound.eval space ≤ K)
    (hroot : ∀ i, (State.initial : P.Store (A := B i)).active.card ≤ K)
    (hobs : ∀ h, h ≤ time → P.PrefixBound rel h K → P.ObservationsAt rel h)
    (hcum : ∀ h, h ≤ time → P.PrefixBound rel h K →
      (P.runActive (rel false) h).card = (P.runActive (rel true) h).card)
    (i j : Bool) (hacc : P.cumulativeAccepts (rel i) time space) :
    P.cumulativeAccepts (rel j) time space := by
  by_cases hij : i = j
  · subst j; exact hacc
  have hcases (b : Bool) : b = i ∨ b = j := by cases i <;> cases j <;> cases b <;> simp_all
  obtain ⟨h,st,hht,hhr,hhf,hha,hbudget⟩ := hacc
  have hsource : P.cumulativeAccepts (rel i) h space := ⟨h,st,le_refl _,hhr,hhf,hha,hbudget⟩
  have htarget := P.bounded_accept_transfer rel h space K hS hnext hroot
    (fun k hk => hobs k (by omega)) i j (P.cumulative_implies_bounded (rel i) hsource)
  have hsource' := P.bounded_active_all (rel i) (P.cumulative_implies_bounded (rel i) hsource)
  have htarget' := P.bounded_active_all (rel j) htarget
  have hp : P.PrefixBound rel h K := by
    intro b k hk
    rcases hcases b with rfl | rfl
    · obtain ⟨t,ht,hb⟩ := hsource' k
      exact ⟨t,ht,hb.trans hS⟩
    · obtain ⟨t,ht,hb⟩ := htarget' k
      exact ⟨t,ht,hb.trans hS⟩
  obtain ⟨t,ht,hbt⟩ := htarget' h
  have ho := hobs h hht hp i j st t hhr ht
  have he : (P.runActive (rel i) h).card = (P.runActive (rel j) h).card := by
    have he := hcum h hht hp
    cases i <;> cases j <;> simp_all
  exact ⟨h,t,hht,ht,(ho.1 .halt).mp hhf,(ho.1 .accept).mp hha,he ▸ hbudget⟩

lemma cumulative_accept_iff (time space K : ℕ) (hS : space ≤ K)
    (hnext : space+P.rule.bound.eval space ≤ K)
    (hroot : ∀ i, (State.initial : P.Store (A := B i)).active.card ≤ K)
    (hobs : ∀ h, h ≤ time → P.PrefixBound rel h K → P.ObservationsAt rel h)
    (hcum : ∀ h, h ≤ time → P.PrefixBound rel h K →
      (P.runActive (rel false) h).card = (P.runActive (rel true) h).card) :
    P.cumulativeAccepts (rel false) time space ↔ P.cumulativeAccepts (rel true) time space :=
  ⟨P.cumulative_accept_transfer rel time space K hS hnext hroot hobs hcum false true,
   P.cumulative_accept_transfer rel time space K hS hnext hroot hobs hcum true false⟩

end

def cumulativeCutoffAccepts {A R : Type} [Fintype A] (P : Machine R) (c d : ℕ)
    (rel : R → A → A → Bool) : Prop :=
  P.cumulativeAccepts rel (c*(Fintype.card A+1)^d) (c*(Fintype.card A+1)^d)

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable {n m M N : ℕ} (P : Operational.Machine Symbol) (vstar : Vertex n)

lemma op_prefix_cumulative (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (hr : P.PrefixBound (fun i => (atomInput (twoCharges vstar i)).rel) h K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+P.rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    (P.runActive (atomInput (twoCharges vstar false)).rel h).card =
      (P.runActive (atomInput (twoCharges vstar true)).rel h).card := by
  let ss := fun i j => (P.run (atomInput (twoCharges vstar i)).rel j).getD State.initial
  have hrs : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j) := by
    intro i j hj
    obtain ⟨st,hst,hb⟩ := hr i j hj
    simp only [ss,hst,Option.getD_some]
  have hact : ∀ i j, j ≤ h → (ss i j).active.card ≤ K := by
    intro i j hj
    obtain ⟨st,hst,hb⟩ := hr i j hj
    simpa only [ss,hst,Option.getD_some] using hb
  exact op_cumulative_agrees P vstar hn h K hN ss hrs hact q hq hb hm hroom hs hwidth hhom hgiant

end CPTSeparation.Grid

namespace CPTSeparation.Operational.Machine

lemma cumulativeAccepts_fintype {A R : Type} (t u : Fintype A) (P : Machine R)
    (rel : R → A → A → Bool) (T S : ℕ) :
    @cumulativeAccepts A R t P rel T S ↔ @cumulativeAccepts A R u P rel T S := by
  have h : t = u := Subsingleton.elim _ _
  cases h
  rfl

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Quantitative Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

end CPTSeparation.Grid

namespace CPTSeparation

end CPTSeparation

namespace CPTSeparation.Operational.Machine

def polynomialCumulativeAccepts {A R : Type} [Fintype A] (P : Machine R)
    (time space : Polynomial ℕ) (rel : R → A → A → Bool) : Prop :=
  P.cumulativeAccepts rel (time.eval (Fintype.card A)) (space.eval (Fintype.card A))

end CPTSeparation.Operational.Machine

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Operational Quantitative Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

end CPTSeparation.Grid

namespace CPTSeparation

end CPTSeparation

end

end OAI
