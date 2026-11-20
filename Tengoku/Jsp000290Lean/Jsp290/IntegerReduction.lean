import Tengoku.Jsp000290Lean.Jsp290.Reindex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Jsp290

open Finset

def negateAt (a : Sequence) (j : ℕ) : Sequence := Function.update a j (-a j)

/--
@isnad1 id=eq.0h2v.s3.2f5b6be759e2 from=translated src=- shape=e2610455 vocab=5ff57cc1
-/
theorem negateAt_involutive (a : Sequence) (j : ℕ) :
    negateAt (negateAt a j) j = a := by
  funext i
  by_cases h : i = j
  · subst i; simp [negateAt]
  · simp [negateAt, h]

/--
@isnad1 id=represen.2h4v.s5.8f6e7d29403e from=translated src=- shape=b14b243f vocab=c2db46d5
-/
theorem representsAfter_negateAt {a : Sequence} {D : Finset ℕ} {j : ℕ}
    (hj : j ∉ D) {x : ℤ} (h : RepresentsAfter a D x) :
    RepresentsAfter (negateAt a j) D (x - a j) := by
  classical
  obtain ⟨s, hs, hx⟩ := h
  by_cases hjs : j ∈ s
  · refine ⟨s.erase j, hs.mono_left (Finset.erase_subset _ _), ?_⟩
    calc
      ∑ i ∈ s.erase j, negateAt a j i = ∑ i ∈ s.erase j, a i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
      _ = x - a j := by
        have he := Finset.sum_erase_add s a hjs
        rw [hx] at he
        omega
  · refine ⟨insert j s, ?_, ?_⟩
    · simp only [Finset.disjoint_insert_left]
      exact ⟨hj, hs⟩
    · rw [Finset.sum_insert hjs]
      have he : ∑ i ∈ s, negateAt a j i = ∑ i ∈ s, a i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i ≠ j := by intro hij; exact hjs (hij ▸ hi)
        exact Function.update_of_ne hij _ _
      rw [he, hx]
      simp [negateAt, sub_eq_add_neg, add_comm]

/--
@isnad1 id=complete.1h3v.s4.92c812f17448 from=translated src=- shape=83ed05ce vocab=6f1338d3
-/
theorem completeAfter_negateAt {a : Sequence} {D : Finset ℕ} (j : ℕ)
    (h : CompleteAfter a D) : CompleteAfter (negateAt a j) D := by
  classical
  obtain ⟨T, hT⟩ := h
  by_cases hj : j ∈ D
  · refine ⟨T, ?_⟩
    intro x hx
    obtain ⟨s, hs, hsum⟩ := hT x hx
    refine ⟨s, hs, ?_⟩
    calc
      ∑ i ∈ s, negateAt a j i = ∑ i ∈ s, a i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i ≠ j := by
          intro hij
          exact Finset.disjoint_left.mp hs hi (hij ▸ hj)
        exact Function.update_of_ne hij _ _
      _ = x := hsum
  · refine ⟨T - a j, ?_⟩
    intro x hx
    have hrep := representsAfter_negateAt hj (hT (x + a j) (by omega))
    simpa using hrep

/--
@isnad1 id=iff.0h3v.s4.d33633f9f35e from=translated src=- shape=64db9841 vocab=6f1338d3
-/
theorem completeAfter_negateAt_iff (a : Sequence) (D : Finset ℕ) (j : ℕ) :
    CompleteAfter (negateAt a j) D ↔ CompleteAfter a D := by
  constructor
  · intro h
    simpa only [negateAt_involutive] using completeAfter_negateAt j h
  · exact completeAfter_negateAt j

def flipSigns (a : Sequence) (S : Finset ℕ) : Sequence :=
  fun i => if i ∈ S then -a i else a i

/--
@isnad1 id=iff.0h3v.s4.0562a70b92c3 from=translated src=- shape=91684bb6 vocab=c7011f13
-/
theorem completeAfter_flipSigns_iff (a : Sequence) (D S : Finset ℕ) :
    CompleteAfter (flipSigns a S) D ↔ CompleteAfter a D := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : flipSigns a ∅ = a := by
      funext i
      simp only [flipSigns, Finset.notMem_empty, ↓reduceIte]
    rw [he]
  | @insert j S hj ih =>
    have he : flipSigns a (insert j S) = negateAt (flipSigns a S) j := by
      funext i
      by_cases hi : i = j
      · subst i; simp [flipSigns, negateAt, hj]
      · simp [flipSigns, negateAt, hi]
    rw [he, completeAfter_negateAt_iff, ih]

/--
@isnad1 id=iff.1h3v.s5.2e3d1f57aacb from=translated src=- shape=8b3f57e2 vocab=7ce774df
-/
theorem completeAfter_abs_iff (a : Sequence) (K : ℕ)
    (hK : ∀ i, K ≤ i → 0 ≤ a i) (D : Finset ℕ) :
    CompleteAfter (fun i => |a i|) D ↔ CompleteAfter a D := by
  classical
  let S := (range K).filter (fun i => a i < 0)
  have he : (fun i => |a i|) = flipSigns a S := by
    funext i
    by_cases hi : a i < 0
    · have hiK : i < K := by
        by_contra hn
        have := hK i (by omega)
        omega
      simp [flipSigns, S, hi, hiK, abs_of_neg hi]
    · simp [flipSigns, S, hi, abs_of_nonneg (by omega : 0 ≤ a i)]
  rw [he]
  exact completeAfter_flipSigns_iff a D S

/--
@isnad1 id=iff.2h4v.s5.69c6adb6dc8d from=translated src=- shape=781bce5d vocab=24df2f8c
-/
theorem representsAfter_reindex_iff (a : Sequence) (f : ℕ → ℕ)
    (hf : Function.Injective f) (hz : ∀ i, i ∉ Set.range f → a i = 0)
    (D : Finset ℕ) (x : ℤ) :
    RepresentsAfter (fun i => a (f i)) D x ↔ RepresentsAfter a (D.image f) x := by
  classical
  constructor
  · rintro ⟨s, hs, hsum⟩
    refine ⟨s.image f, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi hD
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hD
      have hkj' := hf hkj
      exact Finset.disjoint_left.mp hs hj (hkj' ▸ hk)
    · rw [Finset.sum_image]
      · exact hsum
      · exact fun _ _ _ _ h => hf h
  · rintro ⟨s, hs, hsum⟩
    refine ⟨s.preimage f hf.injOn, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi hD
      exact Finset.disjoint_left.mp hs (Finset.mem_preimage.mp hi)
        (Finset.mem_image.mpr ⟨i, hD, rfl⟩)
    · calc
        ∑ i ∈ s.preimage f hf.injOn, a (f i) =
            ∑ i ∈ (s.preimage f hf.injOn).image f, a i := by
          rw [Finset.sum_image]
          exact fun _ _ _ _ h => hf h
        _ = ∑ i ∈ s with i ∈ Set.range f, a i := by rw [Finset.image_preimage]
        _ = ∑ i ∈ s, a i := by
          apply Finset.sum_filter_of_ne
          intro i _ hi
          by_contra h
          exact hi (hz i h)
        _ = x := hsum

/--
@isnad1 id=iff.2h3v.s5.31292b80a2ea from=translated src=- shape=161d1ed2 vocab=1d0960b1
-/
theorem completeAfter_reindex_iff (a : Sequence) (f : ℕ → ℕ)
    (hf : Function.Injective f) (hz : ∀ i, i ∉ Set.range f → a i = 0)
    (D : Finset ℕ) :
    CompleteAfter (fun i => a (f i)) D ↔ CompleteAfter a (D.image f) := by
  simp only [CompleteAfter, representsAfter_reindex_iff a f hf hz]

/--
@isnad1 id=ex.2h1v.s6.03e48fdabe8a from=translated src=- shape=adcda8c4 vocab=d232ca67
-/
theorem exists_positive_model (a : Sequence) (ha : Monotone a)
    (hu : ∀ C : ℤ, ∃ i : ℕ, C < a i) :
    ∃ b : Sequence, Monotone b ∧ (∀ i, 0 < b i) ∧
      ∀ D : Finset ℕ, ∃ E : Finset ℕ, E.card = D.card ∧
        (CompleteAfter b D ↔ CompleteAfter a E) := by
  classical
  obtain ⟨K, hK⟩ := hu (|a 0| + 1)
  have hKpos : 0 < a K := by have := abs_nonneg (a 0); omega
  have htail : ∀ i, K ≤ i → 0 < a i := fun i hi => hKpos.trans_le (ha hi)
  let c : Sequence := fun i => |a i|
  have hfront : ∀ i, i < K → c i ≤ a K := by
    intro i hi
    apply abs_le.mpr
    constructor
    · have h₀ := ha (Nat.zero_le i)
      have habs := neg_abs_le (a 0)
      omega
    · exact ha hi.le
  let f : Fin K → ℤ := fun i => c i
  let σ : Equiv.Perm ℕ := (Tuple.sort f).viaEmbedding Fin.valEmbedding
  have hσfront : ∀ (i : ℕ) (hi : i < K),
      σ i = ((Tuple.sort f) ⟨i, hi⟩ : ℕ) := by
    intro i hi
    exact Equiv.Perm.viaEmbedding_apply (Tuple.sort f) Fin.valEmbedding (⟨i, hi⟩ : Fin K)
  have hσtail : ∀ i, K ≤ i → σ i = i := by
    intro i hi
    apply Equiv.Perm.viaEmbedding_apply_of_notMem
    rintro ⟨j, hj⟩
    change (j : ℕ) = i at hj
    have := j.isLt
    omega
  let q : Sequence := fun i => c (σ i)
  have hqtail : ∀ i, K ≤ i → q i = a i := by
    intro i hi
    dsimp [q]
    rw [hσtail i hi]
    exact abs_of_pos (htail i hi)
  have hqnonneg : ∀ i, 0 ≤ q i := fun i => abs_nonneg (a (σ i))
  have hqmono : Monotone q := by
    intro i j hij
    by_cases hj : j < K
    · have hi : i < K := hij.trans_lt hj
      change c (σ i) ≤ c (σ j)
      rw [hσfront i hi, hσfront j hj]
      exact Tuple.monotone_sort f (show (⟨i, hi⟩ : Fin K) ≤ ⟨j, hj⟩ from hij)
    · have hjK : K ≤ j := by omega
      rw [hqtail j hjK]
      by_cases hi : i < K
      · change c (σ i) ≤ a j
        rw [hσfront i hi]
        exact (hfront _ (Tuple.sort f ⟨i, hi⟩).isLt).trans (ha hjK)
      · rw [hqtail i (by omega)]
        exact ha hij
  let Z := (range K).filter (fun i => q i = 0)
  have hZ : ∀ i, i ∈ Z ↔ q i = 0 := by
    intro i
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hi
      have hiK : i < K := by
        by_contra hn
        have hpos := htail i (by omega)
        rw [hqtail i (by omega)] at hi
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiK, hi⟩
  let b := erase q Z
  have hbpos : ∀ i, 0 < b i := by
    intro i
    have hz := survivor_not_mem Z i
    have hn := hqnonneg (survivor Z i)
    have hne : q (survivor Z i) ≠ 0 := fun h => hz ((hZ _).mpr h)
    change 0 < q (survivor Z i)
    omega
  refine ⟨b, monotone_erase hqmono Z, hbpos, ?_⟩
  intro D
  let F := D.image (survivor Z)
  let E := F.image σ
  have hcard : E.card = D.card := by
    dsimp [E, F]
    rw [Finset.card_image_of_injective _ σ.injective,
      Finset.card_image_of_injective _ (survivor_strictMono Z).injective]
  refine ⟨E, hcard, ?_⟩
  have hzero : ∀ i, i ∉ Set.range (survivor Z) → q i = 0 := by
    intro i hi
    apply (hZ i).mp
    by_contra hiZ
    exact hi ⟨Nat.count (fun j => j ∉ Z) i, survivor_count Z hiZ⟩
  have hperm : ∀ i, i ∉ Set.range σ → c i = 0 := by
    intro i hi
    exact False.elim (hi (σ.surjective i))
  calc
    CompleteAfter b D ↔ CompleteAfter q F :=
      completeAfter_reindex_iff q (survivor Z) (survivor_strictMono Z).injective hzero D
    _ ↔ CompleteAfter c E := completeAfter_reindex_iff c σ σ.injective hperm F
    _ ↔ CompleteAfter a E := completeAfter_abs_iff a K (fun i hi => (htail i hi).le) E

end Jsp290
