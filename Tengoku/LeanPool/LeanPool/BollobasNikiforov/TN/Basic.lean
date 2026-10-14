/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Tengoku

/-!
# Total nonnegativity

A real matrix is totally nonnegative when every square minor formed by
strictly increasing index maps is nonnegative. The empty (`k = 0`) minor is
the determinant of a `Matrix (Fin 0) (Fin 0)`, which Mathlib sets to `1`.

Cauchy–Binet is proved only for a product with middle dimension `3`, by
enumerating the `C(3, r)` strictly increasing maps `Fin r → Fin 3`
(`r = 0,1,2,3`) and using rank for `r > 3`.
-/

@[expose] public section

open Function Matrix

namespace BollobasNikiforov

/-! ### TN01: definition -/

variable {m n : Type*} [LinearOrder m] [LinearOrder n]

/-- A matrix is totally nonnegative if every square minor with strictly
increasing row and column index maps has nonnegative determinant. The
`k = 0` case is included: `Matrix.det_fin_zero` says the empty minor equals
`1`. -/
def IsTotallyNonneg (A : Matrix m n ℝ) : Prop :=
  ∀ k : ℕ, ∀ I : Fin k → m, ∀ J : Fin k → n,
    StrictMono I → StrictMono J → 0 ≤ (A.submatrix I J).det

/-! ### TN02: size-one minors and nondecreasing index maps -/

/-- A monotone injective map out of a linear order is strictly increasing.
@isnad1 id=strictmo.2h3v.s5.22b1611dfd2c from=translated src=- shape=9c6ecd3f vocab=115db13a
-/
lemma strictMono_of_monotone_injective {α β : Type*}
    [LinearOrder α] [PartialOrder β] {f : α → β}
    (hmono : Monotone f) (hinj : Injective f) : StrictMono f :=
  hmono.strictMono_of_injective hinj

/-- Totally nonnegative matrices are entrywise nonnegative (the `k = 1`
minors).
@isnad1 id=le.1h5v.s5.acd2174d09a7 from=translated src=- shape=6634da39 vocab=b7799c82
-/
lemma IsTotallyNonneg.apply {A : Matrix m n ℝ} (hA : IsTotallyNonneg A)
    (i : m) (j : n) : 0 ≤ A i j := by
  simpa [det_fin_one, submatrix_apply] using
    hA 1 (fun _ ↦ i) (fun _ ↦ j) (Subsingleton.strictMono _) (Subsingleton.strictMono _)

omit [LinearOrder m] [LinearOrder n] in
/--
@isnad1 id=eq.1h6v.s5.005d330cace3 from=translated src=- shape=6df3f667 vocab=900c2ea4
-/
lemma det_submatrix_eq_zero_of_not_injective {k : ℕ}
    (A : Matrix m n ℝ) {I : Fin k → m} {J : Fin k → n}
    (h : ¬ Injective I ∨ ¬ Injective J) : (A.submatrix I J).det = 0 := by
  rcases h with hI | hJ
  · obtain ⟨i, j, hf, hij⟩ := not_injective_iff.mp hI
    exact det_zero_of_row_eq hij (funext fun _ ↦ by simp [hf])
  · obtain ⟨i, j, hg, hij⟩ := not_injective_iff.mp hJ
    exact det_zero_of_column_eq hij (fun _ ↦ by simp [hg])

/-- If `A` is totally nonnegative and `I`, `J` are merely nondecreasing, the
corresponding minor is still nonnegative: a repeated index forces determinant
`0` when `k ≥ 2`, and an injective monotone map is strictly increasing.
@isnad1 id=le.3h6v.s6.f6e5a0289838 from=translated src=- shape=1fe04b34 vocab=efae6c6a
-/
lemma IsTotallyNonneg.det_submatrix_monotone {A : Matrix m n ℝ}
    (hA : IsTotallyNonneg A) {k : ℕ} {I : Fin k → m} {J : Fin k → n}
    (hI : Monotone I) (hJ : Monotone J) : 0 ≤ (A.submatrix I J).det := by
  by_cases hIinj : Injective I
  · by_cases hJinj : Injective J
    · exact hA k I J (strictMono_of_monotone_injective hI hIinj)
        (strictMono_of_monotone_injective hJ hJinj)
    · simp [det_submatrix_eq_zero_of_not_injective A (Or.inr hJinj)]
  · simp [det_submatrix_eq_zero_of_not_injective A (Or.inl hIinj)]

/-! ### TN03: Cauchy–Binet of width 3 -/

/-- Strictly increasing maps `Fin r → Fin 3`. There are `C(3, r)` of them
for `r ≤ 3`, and none when `r > 3`. -/
abbrev StrictMonoFin3 (r : ℕ) := {f : Fin r → Fin 3 // StrictMono f}

instance decidablePredStrictMonoFin3 {r : ℕ} :
    DecidablePred fun f : Fin r → Fin 3 ↦ StrictMono f := by
  classical
  infer_instance

noncomputable instance {r : ℕ} : Fintype (StrictMonoFin3 r) :=
  Subtype.fintype _

/--
@isnad1 id=eq.1h2v.s5.4fa671624849 from=translated src=- shape=e7450bd6 vocab=33edd9a9
-/
lemma det_eq_zero_of_rank_lt {r : ℕ} {A : Matrix (Fin r) (Fin r) ℝ}
    (h : A.rank < r) : A.det = 0 := by
  by_contra h0
  have hli := linearIndependent_rows_of_det_ne_zero h0
  have hr := hli.rank_matrix
  simp only [Fintype.card_fin] at hr
  omega

/--
@isnad1 id=eq.1h3v.s6.ba58c74eef6e from=translated src=- shape=964474ee vocab=f7536138
-/
lemma det_mul_eq_zero_of_three_lt {r : ℕ} (hr : 3 < r)
    (P : Matrix (Fin r) (Fin 3) ℝ) (Q : Matrix (Fin 3) (Fin r) ℝ) :
    (P * Q).det = 0 := by
  refine det_eq_zero_of_rank_lt ?_
  have hle : (P * Q).rank ≤ 3 :=
    (rank_mul_le_left P Q).trans P.rank_le_width
  omega

/--
@isnad1 id=isempty.1h1v.s3.526aeda69acd from=translated src=- shape=c1538fc1 vocab=002f6273
-/
lemma isEmpty_strictMonoFin3_of_three_lt {r : ℕ} (hr : 3 < r) :
    IsEmpty (StrictMonoFin3 r) :=
  ⟨fun ⟨f, hf⟩ ↦
    Fintype.not_injective_of_card_lt f (by simpa [Fintype.card_fin] using hr) hf.injective⟩

/--
@isnad1 id=eq.1h2v.s5.4b2528d8f492 from=translated src=- shape=7333a306 vocab=3d95bad8
-/
lemma strictMono_eq_id {k : ℕ} {f : Fin k → Fin k} (hf : StrictMono f) : f = id := by
  ext i
  exact le_antisymm hf.apply_le hf.le_apply

/--
@isnad1 id=ex.1h1v.s6.8a22c8d4da8a from=translated src=- shape=ba96133e vocab=9789a292
-/
lemma exists_eq_succAbove_of_strictMono {f : Fin 2 → Fin 3} (hf : StrictMono f) :
    ∃ k : Fin 3, f = Fin.succAbove k := by
  have hinj := hf.injective
  have hcard : (Finset.univ.image f).card = 2 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hex : ∃ k, k ∉ Finset.univ.image f := by
    by_contra! h
    have : Finset.univ.image f = Finset.univ := Finset.eq_univ_of_forall h
    rw [this, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  obtain ⟨k, hk⟩ := hex
  have himg : Finset.univ.image f = ({k}ᶜ : Finset (Fin 3)) := by
    rw [Finset.compl_singleton]
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      exact hk hx
    · simp [hcard, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin]
  have hfmem : ∀ x, f x ∈ ({k}ᶜ : Finset (Fin 3)) := by
    intro x
    rw [← himg]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have huniq :=
    Finset.orderEmbOfFin_unique
      (by simp [Finset.card_compl] : ({k}ᶜ : Finset (Fin 3)).card = 2) hfmem hf
  refine ⟨k, huniq.trans ?_⟩
  rw [Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb]
  rfl

/-- The three strictly increasing maps `Fin 2 → Fin 3` are `Fin.succAbove k`
for `k : Fin 3` (skip one of `{0,1,2}`). -/
def succAboveStrictMono (k : Fin 3) : StrictMonoFin3 2 :=
  ⟨Fin.succAbove k, Fin.strictMono_succAbove k⟩

/--
@isnad1 id=bijectiv.0h0v.s3.946fe1fc50be from=translated src=- shape=37e7d28e vocab=85702163
-/
lemma succAboveStrictMono_bijective : Bijective succAboveStrictMono := by
  refine ⟨fun a b h ↦ ?_, fun S ↦ ?_⟩
  · simpa [succAboveStrictMono, Fin.succAbove_left_inj] using congrArg Subtype.val h
  · obtain ⟨k, hk⟩ := exists_eq_succAbove_of_strictMono S.2
    exact ⟨k, Subtype.ext hk.symm⟩

/-- All maps `Fin 1 → Fin 3` are strictly monotone (the domain is a
subsingleton). -/
def constStrictMono (k : Fin 3) : StrictMonoFin3 1 :=
  ⟨fun _ ↦ k, Subsingleton.strictMono _⟩

/--
@isnad1 id=bijectiv.0h0v.s3.6aea6f7da2c6 from=translated src=- shape=37e7d28e vocab=e3f1ab34
-/
lemma constStrictMono_bijective : Bijective constStrictMono := by
  refine ⟨fun a b h ↦ ?_, fun S ↦ ?_⟩
  · simpa [constStrictMono] using congrArg (fun t : StrictMonoFin3 1 ↦ t.1 0) h
  · refine ⟨S.1 0, Subtype.ext (funext fun i ↦ ?_)⟩
    simp [constStrictMono, Subsingleton.elim i 0]

private lemma succAbove_fin3_zero_zero :
    Fin.succAbove (0 : Fin 3) (0 : Fin 2) = 1 := by decide
private lemma succAbove_fin3_zero_one :
    Fin.succAbove (0 : Fin 3) (1 : Fin 2) = 2 := by decide
private lemma succAbove_fin3_one_zero :
    Fin.succAbove (1 : Fin 3) (0 : Fin 2) = 0 := by decide
private lemma succAbove_fin3_one_one :
    Fin.succAbove (1 : Fin 3) (1 : Fin 2) = 2 := by decide
private lemma succAbove_fin3_two_zero :
    Fin.succAbove (2 : Fin 3) (0 : Fin 2) = 0 := by decide
private lemma succAbove_fin3_two_one :
    Fin.succAbove (2 : Fin 3) (1 : Fin 2) = 1 := by decide

/-- Direct expansion of a `2 × 2` determinant of a product through width `3`.
@isnad1 id=eq.0h2v.s9.2b74e87f373f from=translated src=- shape=598d663b vocab=5f8ad368
-/
lemma det_mul_width3_two (P : Matrix (Fin 2) (Fin 3) ℝ)
    (Q : Matrix (Fin 3) (Fin 2) ℝ) :
    (P * Q).det =
      (P.submatrix id (Fin.succAbove 0)).det * (Q.submatrix (Fin.succAbove 0) id).det +
      (P.submatrix id (Fin.succAbove 1)).det * (Q.submatrix (Fin.succAbove 1) id).det +
      (P.submatrix id (Fin.succAbove 2)).det * (Q.submatrix (Fin.succAbove 2) id).det := by
  simp only [det_fin_two, mul_apply, submatrix_apply, Fin.sum_univ_three, id_eq,
    succAbove_fin3_zero_zero, succAbove_fin3_zero_one, succAbove_fin3_one_zero,
    succAbove_fin3_one_one, succAbove_fin3_two_zero, succAbove_fin3_two_one]
  ring

/-- Cauchy–Binet for `P * Q` with middle index `Fin 3`.
@isnad1 id=eq.0h3v.s8.18cc3e2c1bec from=translated src=- shape=67e047f5 vocab=c49f9781
-/
lemma det_mul_eq_sum_strictMono_width3 {r : ℕ}
    (P : Matrix (Fin r) (Fin 3) ℝ) (Q : Matrix (Fin 3) (Fin r) ℝ) :
    (P * Q).det =
      ∑ S : StrictMonoFin3 r, (P.submatrix id S.1).det * (Q.submatrix S.1 id).det := by
  match r with
  | 0 =>
    have : Unique (StrictMonoFin3 0) :=
      { default := ⟨isEmptyElim, Subsingleton.strictMono _⟩
        uniq := fun ⟨_, _⟩ ↦ Subtype.ext (Subsingleton.elim _ _) }
    rw [Fintype.sum_unique, det_fin_zero, det_fin_zero, det_fin_zero, mul_one]
  | 1 =>
    rw [← constStrictMono_bijective.sum_comp fun S ↦
      (P.submatrix id S.1).det * (Q.submatrix S.1 id).det]
    simp [constStrictMono, mul_apply, submatrix_apply, Fin.sum_univ_three]
  | 2 =>
    rw [← succAboveStrictMono_bijective.sum_comp fun S ↦
      (P.submatrix id S.1).det * (Q.submatrix S.1 id).det]
    simpa [succAboveStrictMono, Fin.sum_univ_three] using det_mul_width3_two P Q
  | 3 =>
    have : Subsingleton (StrictMonoFin3 3) :=
      ⟨fun ⟨f, hf⟩ ⟨g, hg⟩ ↦ Subtype.ext ((strictMono_eq_id hf).trans (strictMono_eq_id hg).symm)⟩
    rw [Fintype.sum_subsingleton _ ⟨id, strictMono_id⟩]
    simp [det_mul]
  | r + 4 =>
    have hr : 3 < r + 4 := by omega
    have := isEmpty_strictMonoFin3_of_three_lt hr
    rw [det_mul_eq_zero_of_three_lt hr, Fintype.sum_empty]

variable {ι κ : Type*}

/--
@isnad1 id=eq.0h7v.s7.d7b07d127fb1 from=translated src=- shape=729cc50a vocab=70b718ee
-/
lemma submatrix_mul_transpose {r : ℕ}
    (X : Matrix ι (Fin 3) ℝ) (Y : Matrix κ (Fin 3) ℝ)
    (I : Fin r → ι) (J : Fin r → κ) :
    (X * Yᵀ).submatrix I J = X.submatrix I id * (Y.submatrix J id)ᵀ := by
  ext a b
  simp [submatrix_apply, mul_apply, transpose_apply]

/-- Square minors of size greater than `3` of a product `X * Yᵀ` vanish,
since the factors have only three columns (rank at most `3`).
@isnad1 id=eq.1h7v.s6.06714862e81c from=translated src=- shape=df734ad1 vocab=c372fdef
-/
lemma det_submatrix_mul_transpose_eq_zero_of_lt {r : ℕ} (hr : 3 < r)
    (X : Matrix ι (Fin 3) ℝ) (Y : Matrix κ (Fin 3) ℝ)
    (I : Fin r → ι) (J : Fin r → κ) :
    ((X * Yᵀ).submatrix I J).det = 0 := by
  rw [submatrix_mul_transpose]
  exact det_mul_eq_zero_of_three_lt hr _ _

/-- Cauchy–Binet for a product of two three-column real matrices. The sum
runs over the strictly increasing maps `Fin r → Fin 3` (equivalently, the
`C(3, r)` increasing embeddings, enumerated as the unique empty map, the
three constants, `Fin.succAbove`, and `id`). For `r > 3` both sides are
zero.
@isnad1 id=eq.0h7v.s8.aaa021db96fe from=translated src=- shape=1a90ed7a vocab=33afe857
-/
lemma det_submatrix_mul_transpose_eq_sum_strictMono {r : ℕ}
    (X : Matrix ι (Fin 3) ℝ) (Y : Matrix κ (Fin 3) ℝ)
    (I : Fin r → ι) (J : Fin r → κ) :
    ((X * Yᵀ).submatrix I J).det =
      ∑ S : StrictMonoFin3 r,
        (X.submatrix I S.1).det * (Y.submatrix J S.1).det := by
  rw [submatrix_mul_transpose, det_mul_eq_sum_strictMono_width3]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [submatrix_submatrix, Function.comp_id, ← transpose_submatrix, det_transpose,
    submatrix_submatrix, Function.id_comp, Function.comp_id]

/-! ### TN04: product of two 3-column TN matrices -/

/-- The product `X * Yᵀ` of two three-column totally nonnegative matrices is
totally nonnegative. Size `r > 3` minors vanish by rank; smaller minors are
nonnegative sums of products of TN minors via Cauchy–Binet.
@isnad1 id=istotall.2h4v.s6.59466a2c529f from=translated src=- shape=341821ce vocab=b7f77ecc
-/
lemma IsTotallyNonneg.mul_transpose [LinearOrder ι] [LinearOrder κ]
    {X : Matrix ι (Fin 3) ℝ} {Y : Matrix κ (Fin 3) ℝ}
    (hX : IsTotallyNonneg X) (hY : IsTotallyNonneg Y) :
    IsTotallyNonneg (X * Yᵀ) := by
  intro r I J hI hJ
  by_cases hr : 3 < r
  · simp [det_submatrix_mul_transpose_eq_zero_of_lt hr]
  · rw [det_submatrix_mul_transpose_eq_sum_strictMono]
    exact Finset.sum_nonneg fun S _ ↦
      mul_nonneg (hX r I S.1 hI S.2) (hY r J S.1 hJ S.2)

end BollobasNikiforov
