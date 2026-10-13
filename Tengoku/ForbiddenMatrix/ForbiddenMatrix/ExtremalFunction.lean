module

public import Tengoku.ForbiddenMatrix.ForbiddenMatrix.Containment
public import Tengoku

@[expose] public section

open Finset

variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] {m n : ℕ}
  {P : α → β → Prop}

open scoped Classical in
noncomputable def density (M : Fin m → Fin n → Prop) : ℕ := #{(i, j) : Fin m × Fin n | M i j}

/--
@isnad1 id=eq.0h2v.s6.8bc62fed3de4 from=translated src=- shape=2d6cd005 vocab=19e34945
-/
lemma density_def {n : ℕ} (M : Fin n → Fin n → Prop) [DecidableRel M] :
    density M = #{(i, j) : Fin n × Fin n | M i j} := by unfold density; convert rfl

/--
@isnad1 id=le.0h5v.s5.c05c2307d6a2 from=translated src=- shape=c729f2b9 vocab=9a3ecca5
-/
@[gcongr] lemma density_mono {M N : Fin m → Fin n → Prop} (h : ∀ i j, M i j → N i j) :
    density M ≤ density N := card_le_card fun _ ↦ by aesop

open scoped Classical in noncomputable
def row_density {n : ℕ} (M : Fin n → Fin n → Prop) (i : Fin n) : ℕ := #{j | M i j}

open scoped Classical in noncomputable
def col_density {n : ℕ} (M : Fin n → Fin n → Prop) (j : Fin n) : ℕ := #{i | M i j}

open scoped Classical in noncomputable
def ex (P : α → β → Prop) (n : ℕ) : ℕ := sup {M : Fin n → Fin n → Prop | ¬ Contains P M} density

/--
@isnad1 id=eq.0h3v.s5.98868b631d5c from=translated src=- shape=5c51c657 vocab=e0a4489c
-/
@[simp] lemma ex_zero (P : α → β → Prop) : ex P 0 = 0 := by simp [ex, density]

/--
@isnad1 id=iff.0h5v.s6.779c71918b51 from=translated src=- shape=7d783327 vocab=78884a70
-/
theorem ex_le_iff {P : α → β → Prop} {m n : ℕ} :
    ex P n ≤ m ↔ ∀ (M : Fin n → Fin n → Prop), ¬ Contains P M → density M ≤ m:= by
  simp [ex]

/--
@isnad1 id=iff.1h5v.s6.ab1f232ae08c from=translated src=- shape=03a1a26b vocab=78884a70
-/
theorem le_ex_iff (P : α → β → Prop) (P_nonempty : ∃ a b, P a b) {m n : ℕ} :
    m ≤ ex P n ↔ ∃ (M : Fin n → Fin n → Prop), ¬ Contains P M ∧ m ≤ density M := by
  obtain rfl | hm := eq_zero_or_pos m
  · simpa using ⟨_, not_contains_false P P_nonempty⟩
  · simp [ex, Finset.le_sup_iff hm]

/--
@isnad1 id=le.0h4v.s5.67928e095881 from=translated src=- shape=5eeef0fb vocab=53511f5b
-/
lemma ex_le_sq {P : α → β → Prop} (n : ℕ) : ex P n ≤ n ^ 2 := by
  simpa [ex, density, sq] using fun M _ ↦ Finset.card_le_univ (α := Fin n × Fin n) _

/--
@isnad1 id=le.1h5v.s5.115a67e1d1d6 from=translated src=- shape=6d32c309 vocab=78884a70
-/
lemma density_le_ex_of_not_contains (M : Fin n → Fin n → Prop) (AvoidP : ¬ Contains P M) :
    density M ≤ ex P n := by
  rw [ex]
  apply le_sup
  simpa only [mem_filter, Finset.mem_univ, true_and]

/--
@isnad1 id=eq.0h2v.s5.fb2afb573b74 from=translated src=- shape=814c2cb6 vocab=daf53fb5
-/
theorem split_density_to_rows {n : ℕ} (M : Fin n → Fin n → Prop) :
    density M = ∑ i, row_density M i := by
  simpa [density, row_density, card_eq_sum_ones, -sum_const] using
    Finset.sum_finset_product _ _ _ (by simp)

/--
@isnad1 id=le.1h3v.s5.c733b2dc4f62 from=translated src=- shape=ece2be8d vocab=c5089f38
-/
theorem density_by_rows_ub {n c : ℕ} (M : Fin n → Fin n → Prop)
    (h_row_density_bounded : ∀ i, row_density M i ≤ c) : density M ≤ n * c := calc
    density M
  _ = ∑ i, row_density M i := split_density_to_rows M
  _ ≤ ∑ _, c := by gcongr; exact h_row_density_bounded _
  _ = n * c := by simp

/--
@isnad1 id=eq.0h2v.s5.dfd5137cfcf2 from=translated src=- shape=814c2cb6 vocab=e8b2f847
-/
theorem split_density_to_cols {n : ℕ} (M : Fin n → Fin n → Prop) :
    density M = ∑ i, col_density M i := by
  simpa [density, col_density, card_eq_sum_ones, -sum_const]
    using Finset.sum_finset_product_right _ _ _ (by simp)

/--
@isnad1 id=le.1h3v.s5.1000ba57637b from=translated src=- shape=ece2be8d vocab=be971a18
-/
theorem density_by_cols_ub {n c : ℕ} (M : Fin n → Fin n → Prop)
    (h_col_bounded : ∀ i, col_density M i ≤ c) : density M ≤ n * c := calc
      density M
  _ = ∑ i, col_density M i := split_density_to_cols M
  _ ≤ ∑ _, c := by gcongr; exact h_col_bounded _
  _ = n * c := by simp

def rectPtset (n a₁ b₁ a₂ b₂ : ℕ) : Finset (Fin n × Fin n) :=
  ({a | ↑a ∈ Finset.Ico a₁ b₁} : Finset (Fin n)) ×ˢ ({a | ↑a ∈ Finset.Ico a₂ b₂} : Finset (Fin n))

open scoped Classical in noncomputable
def rectPtsetMatrix {n : ℕ} (M : Fin n → Fin n → Prop) (a₁ b₁ a₂ b₂ : ℕ) : Finset (Fin n × Fin n) :=
  {(a, b) | M a b ∧ (a, b) ∈ rectPtset n a₁ b₁ a₂ b₂}

open scoped Classical in noncomputable
def rectPtsetSubsetMatrix {n : ℕ} (M : Fin n → Fin n → Prop) (R C : Finset (Fin n)) :
    Finset (Fin n × Fin n) := {(a, b) | M a b ∧ (a, b) ∈ R ×ˢ C}

/--
@isnad1 id=eq.1h3v.s6.474ac0819b12 from=translated src=- shape=470bb449 vocab=a3160db6
-/
lemma card_interval {n : ℕ} (x y : ℕ) (hy : y ≤ n) :
    #{a : Fin n | ↑a ∈ Finset.Ico x y} = #(.Ico x y) := by
  apply Finset.card_bij (fun (a : Fin n) _ ↦ ↑a) (by aesop) (by aesop) ?_
  intro b hb
  simp at hb
  exact ⟨⟨b, by omega⟩, by simpa⟩

/--
@isnad1 id=eq.1h5v.s5.2be8fc45035d from=translated src=- shape=1e30d755 vocab=dd486b46
-/
@[simp] lemma card_rectPtSet (n a₁ b₁ a₂ b₂ : ℕ) (h : b₁ ≤ n ∧ b₂ ≤ n) :
    #(rectPtset n a₁ b₁ a₂ b₂) = (b₁ - a₁) * (b₂ - a₂) := by
  simp only [rectPtset, card_product]
  suffices claim : ∀ x y, y ≤ n → #{a : Fin n | ↑a ∈ Finset.Ico x y} = #(.Ico x y) by aesop
  intro x y hy
  exact card_interval x y hy

/--
@isnad1 id=le.0h4v.s5.a4dd924c8335 from=translated src=- shape=42dd5f36 vocab=3f434d87
-/
@[simp] lemma card_rectPtsetSubsetMatrix {n : ℕ} (M : Fin n → Fin n → Prop) (R C : Finset (Fin n)) :
    #(rectPtsetSubsetMatrix M R C) ≤ #R * #C := by
  calc
    #(rectPtsetSubsetMatrix M R C)
      ≤ #(R ×ˢ C) := ?_
    _ = #R * #C := card_product R C
  gcongr
  simp only [rectPtsetSubsetMatrix, Prod.mk.eta, mem_product]
  intro a ha
  aesop

/--
@isnad1 id=eq.0h3v.s6.43ab6f742b2a from=translated src=- shape=6b698898 vocab=413ddff2
-/
lemma density_mk_mem_product {n : ℕ} (I J : Finset (Fin n)) :
    density (fun i j ↦ (i, j) ∈ I ×ˢ J) = #I * #J := by simp [density_def, -mem_product]

/--
@isnad1 id=other.0h2v.s6.2e029ff6fb78 from=translated src=- shape=7835d24b vocab=9fca5c08
-/
theorem den_all1_matrix_row_subset {n : ℕ} (I : Finset (Fin n)) :
    let M (i j : Fin n) : Prop := (i, j) ∈ I ×ˢ Finset.univ
    density M = n * #I := by
  simp only [density, Prod.mk.eta]
  convert (Finset.card_product I (.univ : Finset <| Fin n)).trans _
  · ext
    simp
  · simp [mul_comm]

/--
@isnad1 id=other.0h2v.s6.4b103e9ccb88 from=translated src=- shape=77c41f7c vocab=9fca5c08
-/
theorem den_all1_matrix_col_subset {n : ℕ} (I : Finset (Fin n)) :
    let M (i j : Fin n) : Prop := (i, j) ∈ Finset.univ ×ˢ I
    density M = n * #I := by
  simpa using density_mk_mem_product .univ I

/--
@isnad1 id=other.0h3v.s7.f9866e3e540e from=translated src=- shape=c8c44a18 vocab=24bf1b5f
-/
theorem den_all1_matrix_column_interval {n : ℕ} (a b : Fin n) :
    let I := ({x | ↑x ∈ Finset.Icc a.1 b.1} : Finset (Fin n))
    let M (i j : Fin n) : Prop := (i, j) ∈ Finset.univ ×ˢ I
    density M = n * (b + 1 - a) := by
  extract_lets I M
  have h1 : #I = #(.Icc a.1 b.1) := by
    apply card_interval
    exact b.2
  observe h2 : #(.Icc a.1 b.1) = b.1 +1 - a.1
  calc
    density M = n * #I := by exact den_all1_matrix_col_subset I
    _ = n * #(.Icc a.1 b.1) := by exact congrArg (HMul.hMul n) h1
    _ = n * (b + 1 - a) := by exact congrArg (HMul.hMul n) h2

/--
@isnad1 id=other.0h3v.s7.728b18d7db7d from=translated src=- shape=36dee1be vocab=24bf1b5f
-/
theorem den_all1_matrix_row_interval {n : ℕ} (a b : Fin n) :
    let I := ({x | ↑x ∈ Finset.Icc a.1 b.1} : Finset (Fin n))
    let M (i j : Fin n) : Prop := (i, j) ∈ I ×ˢ Finset.univ
    density M = n * (b + 1 - a) := by
  extract_lets I M
  have h1 : #I = #(.Icc a.1 b.1) := by
    apply card_interval
    exact b.2
  observe h2 : #(.Icc a.1 b.1) = b.1 +1- a.1
  calc
    density M = n * #I := by exact den_all1_matrix_row_subset I
    _ = n * #(.Icc a.1 b.1) := by exact congrArg (HMul.hMul n) h1
    _ = n * (b + 1 - a) := by exact congrArg (HMul.hMul n) h2

/--
@isnad1 id=other.0h2v.s4.fe990cd30a2b from=translated src=- shape=2bd3dcdd vocab=c38ae5f1
-/
theorem den_all1_matrix_single_row {n : ℕ} (x : Fin n) :
    let M (i _ : Fin n) : Prop := i = x
    density M = n := by
  extract_lets M
  have := den_all1_matrix_row_interval x x
  simp only [density, Icc_self, mem_singleton, Prod.mk.eta, mem_product, mem_filter, mem_univ,
    true_and, and_true, add_tsub_cancel_left, mul_one] at this
  simp only [density, M]
  convert this
  aesop

/--
@isnad1 id=other.0h2v.s4.1c9c6559e230 from=translated src=- shape=f7d26cbc vocab=c38ae5f1
-/
theorem den_all1_matrix_single_col {n : ℕ} (x : Fin n) :
    let M (_ j : Fin n) : Prop := j = x
    density M = n := by
  extract_lets M
  have := den_all1_matrix_column_interval x x
  simp only [density, Icc_self, mem_singleton, Prod.mk.eta, mem_product, mem_univ, mem_filter,
    true_and, add_tsub_cancel_left, mul_one] at this
  simp only [density, M]
  convert this
  aesop

/--
@isnad1 id=le.1h4v.s6.32e19bc49c67 from=translated src=- shape=c979e245 vocab=748dc6ff
-/
theorem le_ex_self_of_two_points (P : α → β → Prop) (n : ℕ)
    (hP : ∃ x y : (α × β), P x.1 x.2 ∧ P y.1 y.2 ∧ x ≠ y) : n ≤ ex P n := by
  obtain rfl | n_pos := eq_zero_or_neZero n
  · simp
  simp only [ne_eq, Prod.ext_iff, not_and_or] at hP
  obtain ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩, h₁, h₂, ha | hb⟩ := hP
  · refine (le_ex_iff _ ⟨_, _, h₁⟩).2 ⟨fun i j ↦ i = 0, ?_, by simp [den_all1_matrix_single_row]⟩
    rintro ⟨f, hf, g, hg, hfg⟩
    exact ha <| hf.injective <| (hfg _ _ h₁).trans (hfg _ _ h₂).symm
  · refine (le_ex_iff _ ⟨_, _, h₁⟩).2 ⟨fun i j ↦ j = 0, ?_, by simp [den_all1_matrix_single_col]⟩
    rintro ⟨f, hf, g, hg, hfg⟩
    exact hb <| hg.injective <| (hfg _ _ h₁).trans (hfg _ _ h₂).symm

/--
@isnad1 id=ex.1h4v.s6.e60f24e2fd44 from=translated src=- shape=03898574 vocab=86cb6180
-/
lemma exists_av_and_ex_eq {n : ℕ} {P : α → β → Prop} (P_nonempty : ∃ a b, P a b) :
    ∃ M : Fin n → Fin n → Prop, ¬ Contains P M ∧ ex P n = density M := by
  classical
  simpa [ex] using Finset.exists_mem_eq_sup {M : Fin n → Fin n → Prop | ¬ Contains P M}
    ⟨_, by simpa using not_contains_false P P_nonempty⟩ density

/--
@isnad1 id=other.0h3v.s6.02b8044e561f from=translated src=- shape=45b19234 vocab=1b91619b
-/
theorem split_density {n : ℕ} (M : Fin n → Fin n → Prop) (Pred : Fin n → Fin n → Prop) :
    let M1 (i j : Fin n) : Prop := M i j ∧  (Pred i j);
    let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
    density M = density M1 + density M2 := by
  classical
  let M1 (i j : Fin n) : Prop := M i j ∧  (Pred i j);
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
  let s1 : Finset (Fin n × Fin n) := {(i, j) | M1 i j}
  let s2 : Finset (Fin n × Fin n) := {(i, j) | M2 i j}
  let s : Finset (Fin n × Fin n) := {(i, j) | M  i j}
  have seqs1s2 : s = s1 ∪ s2 := by
    ext x
    constructor
    · -- (->)
      intro xins
      simp [s] at xins
      simp [s1, s2, M1, M2]
      tauto
    · -- (<-)
      intro xins1s2
      simp [s1, s2, M1, M2] at xins1s2
      simp [s]
      tauto
  have dm : density M = s.card := by simp [density, s]
  have dm1 : density M1 = #s1 := by simp [density_def, s1]
  have dm2 : density M2 = #s2 := by simp [density_def, s2]
  have s1eqs2card : (s1 ∪ s2).card = s1.card + s2.card := by
    apply card_union_of_disjoint
    rw [disjoint_left]
    aesop
  rw [← seqs1s2] at s1eqs2card
  aesop
