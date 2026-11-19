import Tengoku.Linearhadwiger.HadwigerLean.Graph.CliqueDensity.RandomBranches
import Tengoku.Linearhadwiger.HadwigerLean.Graph.CliqueDensity.Endpoint
import Tengoku.Linearhadwiger.HadwigerLean.Graph.InducedFinsetLift
import Tengoku.Linearhadwiger.HadwigerLean.Graph.CliqueDensity.FinsetBranchMinor
import Tengoku.Linearhadwiger.HadwigerLean.Graph.MinorFree
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Branch construction for the quantitative clique-minor bound
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The residual graph has the expected order after deleting a finite set.
@isnad1 id=eq.0h3v.s6.dfddf6953ed0 from=translated src=- shape=9db53b9b vocab=092d68ba
-/
theorem card_induce_compl_eq_sub (G : SimpleGraph V) (U : Finset V) :
    Fintype.card ↥((U : Set V)ᶜ) = Fintype.card V - U.card := by
  classical
  calc
    Fintype.card ↥((U : Set V)ᶜ) = Uᶜ.card := by
      apply Fintype.card_of_subtype
      intro v
      simp
    _ = Fintype.card V - U.card := Finset.card_compl U

/-- Residual degree and order bounds in core case (I).
@isnad1 id=and.3h4v.s9.120245228525 from=translated src=- shape=50430819 vocab=e89d0951
-/
theorem residual_bounds_caseI
    (F : SimpleGraph V) [DecidableRel F.Adj] (d : ℕ) (U : Finset V)
    (horder : Fintype.card V ≤ 2 * d)
    (hdegree : ∀ v : V, d ≤ F.degree v)
    (hb : 3 * U.card < d) :
    (∀ v : ↥((U : Set V)ᶜ),
      d - U.card ≤ (F.induce (U : Set V)ᶜ).degree v) ∧
    2 * Fintype.card ↥((U : Set V)ᶜ) < 5 * (d - U.card) := by
  classical
  have hcard := card_induce_compl_eq_sub F U
  constructor
  · intro v
    have h : F.degree v.1 ≤
        (F.induce (U : Set V)ᶜ).degree v + U.card := by
      simpa using degree_le_degree_induce_compl_add_card F U v.1 v.property
    have hd := hdegree v.1
    omega
  · rw [hcard]
    exact residual_ratio_case_one d (Fintype.card V) U.card horder hb

/-- Residual degree and order bounds in core case (II).
@isnad1 id=and.4h5v.s9.b03edc05881e from=translated src=- shape=1d51a545 vocab=e89d0951
-/
theorem residual_bounds_caseII
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (d δ : ℕ) (U : Finset V)
    (horder : Fintype.card V ≤ d)
    (hdegree : ∀ v : V, δ ≤ F.degree v)
    (hδ : 2 * d < 3 * δ) (hb : 3 * U.card < d) :
    (∀ v : ↥((U : Set V)ᶜ),
      δ - U.card ≤ (F.induce (U : Set V)ᶜ).degree v) ∧
    2 * Fintype.card ↥((U : Set V)ᶜ) < 5 * (δ - U.card) := by
  classical
  have hcard := card_induce_compl_eq_sub F U
  constructor
  · intro v
    have h : F.degree v.1 ≤
        (F.induce (U : Set V)ᶜ).degree v + U.card := by
      simpa using degree_le_degree_induce_compl_add_card F U v.1 v.property
    have hd := hdegree v.1
    omega
  · rw [hcard]
    exact residual_ratio_case_two d δ (Fintype.card V) U.card horder hδ hb

/-- The one-step sampling conclusion from a numerical endpoint estimate.
@isnad1 id=ex.7h8v.s9.e2fdf979c76f from=translated src=- shape=7f5a1c2d vocab=a9e5a0ba
-/
theorem exists_good_sample_of_endpoint_bound
    (R : SimpleGraph V) [DecidableRel R.Adj]
    {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (A : ι → Finset V) (s δ : ℕ) (η : ℝ)
    (hV : Nonempty V) (hδ : δ ≤ Fintype.card V)
    (hmin : ∀ v : V, δ ≤ R.degree v)
    (hratio : 2 * Fintype.card V < 5 * δ)
    (hη : 0 < η)
    (hendpoint : (Fintype.card V : ℝ) *
      Real.exp (-(s : ℝ) * (δ : ℝ) / (Fintype.card V : ℝ)) ≤ η)
    (hold : 8 * (Finset.univ.filter (fun ω : Fin s → V =>
      ∃ j ∈ J, sampleRange ω ⊆ A j)).card <
      Fintype.card (Fin s → V)) :
    ∃ ω : Fin s → V,
      (undominatedCount R ω : ℝ) ≤ 4 * η ∧
      Fintype.card (R.induce (sampleRange ω : Set V)).ConnectedComponent ≤ 3 ∧
      ∀ j ∈ J, ¬ sampleRange ω ⊆ A j := by
  have hm : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hV
  have hsum := sum_undominatedCount_le_exp R s δ hm hδ hmin
  have hNnonneg : (0 : ℝ) ≤ (Fintype.card (Fin s → V) : ℝ) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hendpoint hNnonneg
  have hdom :
      4 * (∑ ω : Fin s → V, (undominatedCount R ω : ℝ)) ≤
        (Fintype.card (Fin s → V) : ℝ) * (4 * η) := by
    nlinarith [hsum, hstep]
  exact exists_good_sample_of_count_bounds R J A s δ (4 * η) hV
    hmin hratio (by linarith) hdom hold
/-- Convert the real endpoint estimate to the residual graph in case (I).
@isnad1 id=le.5h5v.s8.dc5c1b98bec3 from=translated src=- shape=683ba5e1 vocab=8401f647
-/
theorem residual_endpoint_caseI
    (F : SimpleGraph V) (d s : ℕ) (U : Finset V)
    (hd : 0 < d) (hmlo : d < Fintype.card V)
    (hmhi : Fintype.card V ≤ 2 * d)
    (hb : 3 * U.card < d) (hs : 7 ≤ s) :
    (Fintype.card ↥((U : Set V)ᶜ) : ℝ) *
      Real.exp (-(s : ℝ) * ((d - U.card : ℕ) : ℝ) /
        (Fintype.card ↥((U : Set V)ᶜ) : ℝ)) ≤
      ((Fintype.card V : ℝ) - (d : ℝ) / 3) *
        Real.exp (-(2 : ℝ) * (s : ℝ) / 5) := by
  have hb₁ : U.card ≤ d := by omega
  have hb₂ : U.card ≤ Fintype.card V := by omega
  have hreal := CliqueDensity.endpoint_exponential_bound_caseI
    (d : ℝ) (Fintype.card V : ℝ) (U.card : ℝ) (s : ℝ) (d : ℝ)
    (by exact_mod_cast hd)
    (by exact_mod_cast hmlo)
    (by exact_mod_cast hmhi)
    (le_refl _)
    (by positivity)
    (by have h : 3 * (U.card : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast (by omega : 3 * U.card ≤ d)
        linarith)
    (by exact_mod_cast hs)
  rw [card_induce_compl_eq_sub F U]
  rw [Nat.cast_sub hb₁, Nat.cast_sub hb₂]
  convert hreal using 1 <;> ring
/-- Convert the real endpoint estimate to the residual graph in case (II).
@isnad1 id=le.6h6v.s8.7b7b409081d2 from=translated src=- shape=bb230c0d vocab=8401f647
-/
theorem residual_endpoint_caseII
    (F : SimpleGraph V) (d δ s : ℕ) (U : Finset V)
    (hd : 0 < d) (hmlo : 2 * d < 3 * Fintype.card V)
    (hmhi : Fintype.card V ≤ d)
    (hδ : 2 * d < 3 * δ)
    (hb : 3 * U.card < d) (hs : 7 ≤ s) :
    (Fintype.card ↥((U : Set V)ᶜ) : ℝ) *
      Real.exp (-(s : ℝ) * ((δ - U.card : ℕ) : ℝ) /
        (Fintype.card ↥((U : Set V)ᶜ) : ℝ)) ≤
      ((Fintype.card V : ℝ) - (d : ℝ) / 3) *
        Real.exp (-(2 : ℝ) * (s : ℝ) / 5) := by
  have hb₁ : U.card ≤ δ := by omega
  have hb₂ : U.card ≤ Fintype.card V := by omega
  have hreal := CliqueDensity.endpoint_exponential_bound_caseII
    (d : ℝ) (Fintype.card V : ℝ) (U.card : ℝ) (s : ℝ) (δ : ℝ)
    (by exact_mod_cast hd)
    (by have h : (2 : ℝ) * (d : ℝ) < 3 * (Fintype.card V : ℝ) := by
          exact_mod_cast hmlo
        linarith)
    (by exact_mod_cast hmhi)
    (by have h : (2 : ℝ) * (d : ℝ) < 3 * (δ : ℝ) := by
          exact_mod_cast hδ
        linarith)
    (by positivity)
    (by have h : 3 * (U.card : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast (by omega : 3 * U.card ≤ d)
        linarith)
    (by exact_mod_cast hs)
  rw [card_induce_compl_eq_sub F U]
  rw [Nat.cast_sub hb₁, Nat.cast_sub hb₂]
  convert hreal using 1 <;> ring
/-- Vertices occupied by a finite family of branch sets.-/
def branchFamilyUsed (S : Finset (Finset V)) : Finset V :=
  S.biUnion id

/-- Remaining vertices with no edge into one branch set.-/
def branchAvoid (F : SimpleGraph V) [DecidableRel F.Adj]
    (S : Finset (Finset V)) (Q : Finset V) : Finset V :=
  (branchFamilyUsed S)ᶜ.filter (fun v => ∀ q ∈ Q, ¬ F.Adj v q)

/-- Inductive certificate for a partially built complete-minor model.-/
structure CliqueBranchState (F : SimpleGraph V) [DecidableRel F.Adj]
    (s i : ℕ) (θ : ℝ) where
  branches : Finset (Finset V)
  card_branches : branches.card = i
  connected : ∀ Q ∈ branches, (F.induce (Q : Set V)).Connected
  disjoint : Set.Pairwise (branches : Set (Finset V)) (fun Q T => Disjoint Q T)
  adjacent : Set.Pairwise (branches : Set (Finset V))
    (fun Q T => ∃ x ∈ Q, ∃ y ∈ T, F.Adj x y)
  size_bound : ∀ Q ∈ branches, Q.card ≤ s + 8
  used_bound : (branchFamilyUsed branches).card ≤ i * (s + 8)
  avoid_bound : ∀ Q ∈ branches, (branchAvoid F branches Q).card ≤ θ

/-- Empty branch families satisfy every invariant.-/
def CliqueBranchState.empty (F : SimpleGraph V) [DecidableRel F.Adj]
    (s : ℕ) (θ : ℝ) : CliqueBranchState F s 0 θ where
  branches := ∅
  card_branches := rfl
  connected := by simp
  disjoint := by simp
  adjacent := by simp
  size_bound := by simp
  used_bound := by simp [branchFamilyUsed]
  avoid_bound := by simp
/-- Adding branch sets can only shrink each old forbidden set.
@isnad1 id=le.1h5v.s6.ebd47de489e2 from=translated src=- shape=09262903 vocab=9fd8c22b
-/
theorem branchAvoid_mono
    (F : SimpleGraph V) [DecidableRel F.Adj]
    {S T : Finset (Finset V)} (hST : S ⊆ T) (Q : Finset V) :
    branchAvoid F T Q ⊆ branchAvoid F S Q := by
  classical
  have hused : branchFamilyUsed S ⊆ branchFamilyUsed T := by
    intro x hx
    obtain ⟨R, hR, hxR⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨R, hST hR, hxR⟩
  intro x hx
  obtain ⟨hxout, hxnon⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_compl.mpr
    intro hxS
    exact (Finset.mem_compl.mp hxout) (hused hxS)
  · exact hxnon

/-- Avoiding every sampled neighbor is the undominated-vertex predicate.
@isnad1 id=eq.0h4v.s7.b5a282f2e2f0 from=translated src=- shape=2870a5b0 vocab=208e571a
-/
theorem undominatedCount_eq_no_sample_neighbor
    (R : SimpleGraph V) [DecidableRel R.Adj]
    {s : ℕ} (ω : Fin s → V) :
    undominatedCount R ω =
      (Finset.univ.filter (fun v : V =>
        ∀ w ∈ sampleRange ω, ¬ R.Adj v w)).card := by
  unfold undominatedCount
  congr 1
  ext v
  simp [Finset.subset_iff, Finset.mem_compl, SimpleGraph.mem_neighborFinset]
/-- The new branch's forbidden set is controlled by vertices
undominated by its sampled subset.
@isnad1 id=le.1h6v.s9.796463d853f5 from=translated src=- shape=f49bd690 vocab=342fef83
-/
theorem new_branch_avoid_card_le_undominated
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (S : Finset (Finset V))
    {s : ℕ}
    (ω : Fin s → ↥((branchFamilyUsed S : Set V)ᶜ))
    (Q : Finset ↥((branchFamilyUsed S : Set V)ᶜ))
    (hBQ : sampleRange ω ⊆ Q) :
    (branchAvoid F (insert (Q.image Subtype.val) S)
      (Q.image Subtype.val)).card ≤
      undominatedCount (F.induce (branchFamilyUsed S : Set V)ᶜ) ω := by
  classical
  let U := branchFamilyUsed S
  let R := F.induce (U : Set V)ᶜ
  let T := Q.image Subtype.val
  let N : Finset ↥((U : Set V)ᶜ) :=
    Finset.univ.filter (fun v =>
      ∀ w ∈ sampleRange ω, ¬ R.Adj v w)
  have hsubset : branchAvoid F (insert T S) T ⊆ N.image Subtype.val := by
    intro x hx
    have hxold : x ∈ branchAvoid F S T :=
      branchAvoid_mono F (Finset.subset_insert T S) T hx
    obtain ⟨hxU, hxnon⟩ := Finset.mem_filter.mp hxold
    let y : ↥((U : Set V)ᶜ) := ⟨x, Finset.mem_compl.mp hxU⟩
    apply Finset.mem_image.mpr
    refine ⟨y, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro w hw
    have hwQ : w ∈ Q := hBQ hw
    have hwT : w.1 ∈ T := Finset.mem_image.mpr ⟨w, hwQ, rfl⟩
    have hnot := hxnon w.1 hwT
    exact hnot
  have hcardN : (N.image Subtype.val).card = N.card :=
    Finset.card_image_of_injective N Subtype.val_injective
  calc
    (branchAvoid F (insert T S) T).card ≤ (N.image Subtype.val).card :=
      Finset.card_le_card hsubset
    _ = N.card := hcardN
    _ = undominatedCount R ω := by
      exact (undominatedCount_eq_no_sample_neighbor R ω).symm
/-- A sample that escapes an old forbidden set supplies the required
edge from the new branch to that old branch.
@isnad1 id=ex.2h7v.s9.1a9634f05def from=translated src=- shape=0dce21b6 vocab=d5e75ea5
-/
theorem adjacent_new_branch_of_sample_escape
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (U T : Finset V)
    {s : ℕ} (ω : Fin s → ↥((U : Set V)ᶜ))
    (Q : Finset ↥((U : Set V)ᶜ))
    (hBQ : sampleRange ω ⊆ Q)
    (hescape : ¬ sampleRange ω ⊆
      Finset.univ.filter (fun x : ↥((U : Set V)ᶜ) =>
        ∀ y ∈ T, ¬ F.Adj x.1 y)) :
    ∃ x ∈ Q.image Subtype.val, ∃ y ∈ T, F.Adj x y := by
  classical
  obtain ⟨x, hxB, hxnot⟩ := Finset.not_subset.mp hescape
  have hxQ : x.1 ∈ Q.image Subtype.val :=
    Finset.mem_image.mpr ⟨x, hBQ hxB, rfl⟩
  have hsome : ∃ y ∈ T, F.Adj x.1 y := by
    simpa using hxnot
  obtain ⟨y, hy, hxy⟩ := hsome
  exact ⟨x.1, hxQ, y, hy, hxy⟩
/-- Extend a certified branch family by one sampled and connected branch.-/
noncomputable def CliqueBranchState.extend
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (s i : ℕ) (θ : ℝ) (st : CliqueBranchState F s i θ)
    (ω : Fin s → ↥((branchFamilyUsed st.branches : Set V)ᶜ))
    (Q : Finset ↥((branchFamilyUsed st.branches : Set V)ᶜ))
    (hBQ : sampleRange ω ⊆ Q)
    (hQconn : ((F.induce (branchFamilyUsed st.branches : Set V)ᶜ).induce
      (Q : Set ↥((branchFamilyUsed st.branches : Set V)ᶜ))).Connected)
    (hQsize : Q.card ≤ s + 8)
    (hdom : (undominatedCount
      (F.induce (branchFamilyUsed st.branches : Set V)ᶜ) ω : ℝ) ≤ θ)
    (hescape : ∀ T ∈ st.branches,
      ¬ sampleRange ω ⊆ Finset.univ.filter
        (fun x : ↥((branchFamilyUsed st.branches : Set V)ᶜ) =>
          ∀ y ∈ T, ¬ F.Adj x.1 y)) :
    CliqueBranchState F s (i + 1) θ := by
  classical
  let S := st.branches
  let U := branchFamilyUsed S
  let T := Q.image Subtype.val
  let S' := insert T S
  have hUQ : Disjoint T U := disjoint_induced_compl_finset_image U Q
  have hTnonempty : T.Nonempty := by
    obtain ⟨x, hx⟩ := hQconn.nonempty
    exact ⟨x.1, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hTnotS : T ∉ S := by
    intro hTS
    obtain ⟨x, hxT⟩ := hTnonempty
    have hxU : x ∈ U := Finset.mem_biUnion.mpr ⟨T, hTS, hxT⟩
    exact (Finset.disjoint_left.mp hUQ) hxT hxU
  have hTconn : (F.induce (T : Set V)).Connected :=
    connected_induced_finset_image F (U : Set V)ᶜ Q hQconn
  have hTsize : T.card ≤ s + 8 := by
    rw [card_induced_finset_image (U : Set V)ᶜ Q]
    exact hQsize
  have hToldDisj (R : Finset V) (hR : R ∈ S) : Disjoint T R := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxR
    have hxU : x ∈ U := Finset.mem_biUnion.mpr ⟨R, hR, hxR⟩
    exact (Finset.disjoint_left.mp hUQ) hxT hxU
  have hToldAdj (R : Finset V) (hR : R ∈ S) :
      ∃ x ∈ T, ∃ y ∈ R, F.Adj x y :=
    adjacent_new_branch_of_sample_escape F U R ω Q hBQ (hescape R hR)
  have hUsedEq : branchFamilyUsed S' = U ∪ T := by
    simp [branchFamilyUsed, S', U, Finset.union_comm]
  refine {
    branches := S'
    card_branches := by
      change (insert T S).card = i + 1
      simpa [hTnotS, S] using st.card_branches
    connected := ?_
    disjoint := ?_
    adjacent := ?_
    size_bound := ?_
    used_bound := ?_
    avoid_bound := ?_
  }
  · intro R hR
    rcases Finset.mem_insert.mp hR with rfl | hR
    · exact hTconn
    · exact st.connected R hR
  · intro R hR R' hR' hne
    rcases Finset.mem_insert.mp hR with rfl | hR
    · rcases Finset.mem_insert.mp hR' with heq | hR'
      · exact False.elim (hne heq.symm)
      · exact hToldDisj R' hR'
    · rcases Finset.mem_insert.mp hR' with rfl | hR'
      · exact (hToldDisj R hR).symm
      · exact st.disjoint hR hR' hne
  · intro R hR R' hR' hne
    rcases Finset.mem_insert.mp hR with rfl | hR
    · rcases Finset.mem_insert.mp hR' with heq | hR'
      · exact False.elim (hne heq.symm)
      · exact hToldAdj R' hR'
    · rcases Finset.mem_insert.mp hR' with rfl | hR'
      · obtain ⟨x, hx, y, hy, hxy⟩ := hToldAdj R hR
        exact ⟨y, hy, x, hx, hxy.symm⟩
      · exact st.adjacent hR hR' hne
  · intro R hR
    rcases Finset.mem_insert.mp hR with rfl | hR
    · exact hTsize
    · exact st.size_bound R hR
  · rw [hUsedEq]
    calc
      (U ∪ T).card ≤ U.card + T.card := Finset.card_union_le U T
      _ ≤ i * (s + 8) + (s + 8) := by
        have hbound : U.card ≤ i * (s + 8) := st.used_bound
        omega
      _ = (i + 1) * (s + 8) := by ring
  · intro R hR
    rcases Finset.mem_insert.mp hR with rfl | hR
    · have hcard := new_branch_avoid_card_le_undominated F S ω Q hBQ
      have hreal : ((branchAvoid F S' T).card : ℝ) ≤
          (undominatedCount (F.induce (U : Set V)ᶜ) ω : ℝ) := by
        exact_mod_cast hcard
      exact hreal.trans hdom
    · have hsubset : branchAvoid F S' R ⊆ branchAvoid F S R :=
        branchAvoid_mono F (Finset.subset_insert T S) R
      have hcard := Finset.card_le_card hsubset
      have hcardReal : ((branchAvoid F S' R).card : ℝ) ≤
          ((branchAvoid F S R).card : ℝ) := by exact_mod_cast hcard
      exact hcardReal.trans (st.avoid_bound R hR)
/-- The numerical E.7 bound applies to every unfinished branch family.
@isnad1 id=lt.3h3v.s7.9030c46c7c06 from=translated src=- shape=e77cf390 vocab=71436e0e
-/
theorem branch_old_numeric_bound
    (r s i : ℕ) (hr : 13 ≤ r)
    (hs : s = Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ))))
    (hi : i ≤ r) :
    8 * (i : ℝ) *
      (4 * Real.exp (-(2 : ℝ) * (s : ℝ) / 5)) ^ s < 1 := by
  subst s
  let α := 4 * Real.exp (-(2 : ℝ) *
    (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ))) : ℝ) / 5)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hpow : 0 ≤ α ^ (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ)))) :=
    pow_nonneg hα _
  have hreal : (i : ℝ) ≤ r := by exact_mod_cast hi
  have h₀ := clique_branch_old_set_failure_bound r hr
  have h₁ : 8 * (r : ℝ) * α ^
      (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ)))) < 1 := by
    dsimp [α] at h₀ ⊢
    linarith
  have h₂ : 8 * (i : ℝ) * α ^
      (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ)))) ≤
      8 * (r : ℝ) * α ^
      (Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ)))) := by
    nlinarith [mul_le_mul_of_nonneg_right hreal hpow]
  exact h₂.trans_lt h₁
/-- The branch budget leaves strictly fewer than `d/3` vertices used
before every one of the `r` stages.
@isnad1 id=and.3h5v.s6.b9ed9d803359 from=translated src=- shape=75e55e87 vocab=ef4726aa
-/
theorem branch_used_lt_third
    (d r s i b : ℕ) (hi : i < r)
    (hbudget : 3 * r * (s + 8) ≤ d)
    (hused : b ≤ i * (s + 8)) :
    b < d / 3 ∧ 3 * b < d := by
  have hstep : (i + 1) * (s + 8) ≤ r * (s + 8) :=
    Nat.mul_le_mul_right (s + 8) hi
  have hgap : 3 * b + 3 * (s + 8) ≤ d := by
    nlinarith
  constructor <;> omega
/-- The large-order sample length is at least seven.
@isnad1 id=le.1h1v.s5.94269928101a from=translated src=- shape=1078488e vocab=4ea8baaa
-/
theorem clique_sample_size_ge_seven (r : ℕ) (hr : 13 ≤ r) :
    7 ≤ Nat.ceil (4 * Real.sqrt (Real.log (r : ℝ))) := by
  let L : ℝ := Real.log (r : ℝ)
  let x : ℝ := Real.sqrt L
  let s : ℕ := Nat.ceil (4 * x)
  have hrreal : (12 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 12 ≤ r)
  have hlog : (9 / 4 : ℝ) < L :=
    lt_of_lt_of_le log_twelve_gt_nine_fourths
      (Real.log_le_log (by norm_num) hrreal)
  have hLnonneg : 0 ≤ L := by linarith
  have hxsq : x ^ 2 = L := Real.sq_sqrt hLnonneg
  have hxnonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hx : (3 / 2 : ℝ) < x := by nlinarith
  have hceil : 4 * x ≤ (s : ℝ) := Nat.le_ceil _
  have hsreal : (6 : ℝ) < (s : ℝ) := by linarith
  have hs : 6 < s := by exact_mod_cast hsreal
  exact hs
/-- The fixed forbidden-set threshold is at most the current
order times the E.7 avoidance factor.
@isnad1 id=le.2h5v.s8.24133caf1c07 from=translated src=- shape=271d0a2a vocab=8401f647
-/
theorem branch_threshold_le_current_order
    (F : SimpleGraph V) (d s : ℕ) (U : Finset V)
    (hb : 3 * U.card < d)
    (horder : U.card ≤ Fintype.card V) :
    4 * (((Fintype.card V : ℝ) - (d : ℝ) / 3) *
      Real.exp (-(2 : ℝ) * (s : ℝ) / 5)) ≤
      (Fintype.card ↥((U : Set V)ᶜ) : ℝ) *
        (4 * Real.exp (-(2 : ℝ) * (s : ℝ) / 5)) := by
  have hbReal : (U.card : ℝ) ≤ (d : ℝ) / 3 := by
    have h : (3 : ℝ) * (U.card : ℝ) < (d : ℝ) := by
      exact_mod_cast hb
    linarith
  rw [card_induce_compl_eq_sub F U, Nat.cast_sub horder]
  have he : (0 : ℝ) ≤ 4 * Real.exp (-(2 : ℝ) * (s : ℝ) / 5) := by
    positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith :
    0 ≤ ((Fintype.card V : ℝ) - (U.card : ℝ)) -
      ((Fintype.card V : ℝ) - (d : ℝ) / 3))) he]
/-- The two correlated core cases yield the same residual sampling data.
@isnad1 id=ex.5h5v.s9.a1f14887d338 from=translated src=- shape=b6ede2ce vocab=88357e99
-/
theorem residual_parameters_of_core_case
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (d s : ℕ) (U : Finset V)
    (hd : 0 < d) (hpositive : 0 < Fintype.card V)
    (hcase :
      (Fintype.card V ≤ 2 * d ∧ ∀ v : V, d ≤ F.degree v) ∨
      (Fintype.card V ≤ d ∧ ∀ v : V, 2 * d < 3 * F.degree v))
    (hb : 3 * U.card < d) (hs : 7 ≤ s) :
    ∃ δ : ℕ,
      (∀ v : ↥((U : Set V)ᶜ),
        δ ≤ (F.induce (U : Set V)ᶜ).degree v) ∧
      2 * Fintype.card ↥((U : Set V)ᶜ) < 5 * δ ∧
      (Fintype.card ↥((U : Set V)ᶜ) : ℝ) *
        Real.exp (-(s : ℝ) * (δ : ℝ) /
          (Fintype.card ↥((U : Set V)ᶜ) : ℝ)) ≤
        ((Fintype.card V : ℝ) - (d : ℝ) / 3) *
          Real.exp (-(2 : ℝ) * (s : ℝ) / 5) := by
  classical
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpositive
  rcases hcase with ⟨hmhi, hdegree⟩ | ⟨hmhi, hstrong⟩
  · have hmlo : d < Fintype.card V :=
      lt_of_le_of_lt (hdegree v) (F.degree_lt_card_verts v)
    obtain ⟨hmin, hratio⟩ := residual_bounds_caseI F d U hmhi hdegree hb
    exact ⟨d - U.card, hmin, hratio,
      residual_endpoint_caseI F d s U hd hmlo hmhi hb hs⟩
  · let δ := 2 * d / 3 + 1
    have hδ : 2 * d < 3 * δ := by dsimp [δ]; omega
    have hdegree : ∀ v : V, δ ≤ F.degree v := by
      intro w
      have h := hstrong w
      dsimp [δ]
      omega
    have hmlo : 2 * d < 3 * Fintype.card V := by
      have h := hstrong v
      have hlt := F.degree_lt_card_verts v
      omega
    obtain ⟨hmin, hratio⟩ :=
      residual_bounds_caseII F d δ U hmhi hdegree hδ hb
    exact ⟨δ - U.card, hmin, hratio,
      residual_endpoint_caseII F d δ s U hd hmlo hmhi hδ hb hs⟩

end HadwigerLean
