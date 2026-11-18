import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

namespace LocalCartan

open Matrix

variable {K : Type*} [Field K] (O : ValuationSubring K)

def IsInt (k : GL (Fin 2) K) : Prop :=
  (∀ i j, (k : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
    (∀ i j, ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O)

/--
@isnad1 id=mem.2h6v.s7.b6db6c93f4c6 from=translated src=- shape=2b9383e4 vocab=d415588a
-/
theorem mul_entry_mem {A B : Matrix (Fin 2) (Fin 2) K} (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O)
    (i j : Fin 2) : (A * B) i j ∈ O := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact O.add_mem _ _ (O.mul_mem _ _ (hA _ _) (hB _ _)) (O.mul_mem _ _ (hA _ _) (hB _ _))

/--
@isnad1 id=isint.2h4v.s7.56cae645a500 from=translated src=- shape=78170625 vocab=6641d6e4
-/
theorem IsInt.mul {k k' : GL (Fin 2) K} (hk : IsInt O k) (hk' : IsInt O k') : IsInt O (k * k') := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]
    exact mul_entry_mem O hk.1 hk'.1 i j
  · rw [_root_.mul_inv_rev, Units.val_mul]
    exact mul_entry_mem O hk'.2 hk.2 i j

def mkGL (A B : Matrix (Fin 2) (Fin 2) K) (h1 : A * B = 1) (h2 : B * A = 1) : GL (Fin 2) K :=
  ⟨A, B, h1, h2⟩

def lower (c : K) : GL (Fin 2) K :=
  mkGL !![1, 0; c, 1] !![1, 0; -c, 1]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

def upper (b : K) : GL (Fin 2) K :=
  mkGL !![1, b; 0, 1] !![1, -b; 0, 1]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

def swap : GL (Fin 2) K :=
  mkGL !![0, 1; 1, 0] !![0, 1; 1, 0]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

omit O in
/--
@isnad1 id=eq.0h2v.s8.a1a7fd61dd91 from=translated src=- shape=ca907116 vocab=620a764d
-/
@[scoped simp] theorem coe_lower (c : K) : ((lower c : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl
omit O in
/--
@isnad1 id=eq.0h2v.s8.d66bf772c949 from=translated src=- shape=9c1ed21a vocab=8b5d5594
-/
@[scoped simp] theorem coe_lower_inv (c : K) :
    (((lower c)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; -c, 1] := rfl
omit O in
/--
@isnad1 id=eq.0h2v.s8.c5d479dfeaa1 from=translated src=- shape=91de8ec8 vocab=87f3ef5a
-/
@[scoped simp] theorem coe_upper (b : K) : ((upper b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, b; 0, 1] := rfl
omit O in
/--
@isnad1 id=eq.0h2v.s8.9c70d7c35b43 from=translated src=- shape=5f4db9d9 vocab=ff0c17c8
-/
@[scoped simp] theorem coe_upper_inv (b : K) :
    (((upper b)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, -b; 0, 1] := rfl
omit O in
/--
@isnad1 id=eq.0h1v.s8.1ee3d9412f4d from=translated src=- shape=9c464ae8 vocab=8697e2bb
-/
@[scoped simp] theorem coe_swap : ((swap : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl
omit O in
/--
@isnad1 id=eq.0h1v.s8.087efaa4c55b from=translated src=- shape=e110b0f8 vocab=262c2056
-/
@[scoped simp] theorem coe_swap_inv : ((swap⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

/--
@isnad1 id=isint.1h3v.s5.f49427accafd from=translated src=- shape=50217b26 vocab=d79de369
-/
theorem isInt_lower {c : K} (hc : c ∈ O) : IsInt O (lower c) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_lower]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem, hc]
  · rw [coe_lower_inv]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem, O.neg_mem _ hc]

/--
@isnad1 id=isint.1h3v.s5.3bcd57c59696 from=translated src=- shape=50217b26 vocab=da7d3f12
-/
theorem isInt_upper {b : K} (hb : b ∈ O) : IsInt O (upper b) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_upper]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem, hb]
  · rw [coe_upper_inv]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem, O.neg_mem _ hb]

/--
@isnad1 id=isint.0h2v.s4.7053206d379b from=translated src=- shape=fa25e355 vocab=03a8bd17
-/
theorem isInt_swap : IsInt O (swap : GL (Fin 2) K) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_swap]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem]
  · rw [coe_swap_inv]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem]

/--
@isnad1 id=isint.0h2v.s6.80d2e101f8b6 from=translated src=- shape=7ef7fef7 vocab=7ca6ae71
-/
theorem isInt_one : IsInt O (1 : GL (Fin 2) K) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem]
  · rw [inv_one, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem]

def Concl (A : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ (s t : K) (k₁ k₂ : GL (Fin 2) K), s ≠ 0 ∧ t ≠ 0 ∧ t ∈ O ∧ IsInt O k₁ ∧ IsInt O k₂ ∧
    A = s • ((k₁ : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal ![(1 : K), t] * (k₂ : Matrix (Fin 2) (Fin 2) K))

/--
@isnad1 id=concl.5h6v.s8.5cd0b71a0ce3 from=translated src=- shape=e78054a3 vocab=fd3bb329
-/
theorem base (a b c d : K) (ha : a ≠ 0) (hb : b / a ∈ O) (hc : c / a ∈ O) (hd : d / a ∈ O)
    (hdet : a * d - b * c ≠ 0) : Concl O !![a, b; c, d] := by
  refine ⟨a, d / a - (c / a) * (b / a), lower (c / a), upper (b / a), ha, ?_, ?_,
    isInt_lower O hc, isInt_upper O hb, ?_⟩
  · have h : d / a - (c / a) * (b / a) = (a * d - b * c) / a ^ 2 := by
      field_simp
    rw [h]
    exact div_ne_zero hdet (pow_ne_zero 2 ha)
  · exact O.toSubring.sub_mem hd (O.mul_mem _ _ hc hb)
  · have hD : Matrix.diagonal ![(1 : K), d / a - c / a * (b / a)] = !![1, 0; 0, d / a - c / a * (b / a)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [coe_lower, coe_upper, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp; try (field_simp; try ring))

/--
@isnad1 id=concl.4h6v.s8.308a3dc4209f from=translated src=- shape=6d2b319a vocab=4b77429b
-/
theorem of_conj {H A : Matrix (Fin 2) (Fin 2) K} {P Q : GL (Fin 2) K} (hP : IsInt O P) (hQ : IsInt O Q)
    (hHA : H = (P : Matrix (Fin 2) (Fin 2) K) * A * (Q : Matrix (Fin 2) (Fin 2) K)) (hA : Concl O A) :
    Concl O H := by
  obtain ⟨s, t, k₁, k₂, hs, ht, htO, hk₁, hk₂, hAeq⟩ := hA
  refine ⟨s, t, P * k₁, k₂ * Q, hs, ht, htO, hP.mul O hk₁, hk₂.mul O hQ, ?_⟩
  rw [hHA, hAeq, Units.val_mul, Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc]

/--
@isnad1 id=ex.1h3v.s7.8d3e9492eaa2 from=translated src=- shape=9fc40549 vocab=e6849836
-/
theorem exists_entry_dvd (A : Matrix (Fin 2) (Fin 2) K) (hA : ∃ i j, A i j ≠ 0) :
    ∃ i₀ j₀, A i₀ j₀ ≠ 0 ∧ ∀ i j, A i j / A i₀ j₀ ∈ O := by
  classical
  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun ij => O.valuation (A ij.1 ij.2)) Finset.univ_nonempty
  have h0 : A i₀ j₀ ≠ 0 := by
    obtain ⟨i, j, hij⟩ := hA
    intro h0
    have h := hmax (i, j) (Finset.mem_univ _)
    simp only [h0, map_zero, le_zero_iff] at h
    exact hij ((Valuation.zero_iff _).mp h)
  refine ⟨i₀, j₀, h0, fun i j => ?_⟩
  rw [← O.valuation_le_one_iff, map_div₀]
  have hpos : 0 < O.valuation (A i₀ j₀) := (Valuation.pos_iff _).mpr h0
  rw [div_le_one₀ hpos]
  exact hmax (i, j) (Finset.mem_univ _)

/--
@isnad1 id=concl.0h3v.s6.152928c5ac11 from=translated src=- shape=8aa67d3c vocab=e8ef63c5
-/
theorem concl (H : GL (Fin 2) K) : Concl O (H : Matrix (Fin 2) (Fin 2) K) := by
  set A : Matrix (Fin 2) (Fin 2) K := (H : Matrix (Fin 2) (Fin 2) K) with hAdef
  have hdet : A.det ≠ 0 := by
    rw [hAdef, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [Matrix.det_fin_two] at hdet
  have hne : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    simp [h]
  obtain ⟨i₀, j₀, h0, hdiv⟩ := exists_entry_dvd O A hne
  have hA : A = !![A 0 0, A 0 1; A 1 0, A 1 1] := Matrix.eta_fin_two A
  fin_cases i₀ <;> fin_cases j₀
  ·
    simp only [Fin.zero_eta, Fin.isValue] at h0 hdiv
    rw [hA]
    exact base O _ _ _ _ h0 (hdiv 0 1) (hdiv 1 0) (hdiv 1 1) hdet
  ·
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at h0 hdiv
    refine of_conj O (P := 1) (Q := swap) (isInt_one O) (isInt_swap O) (A := !![A 0 1, A 0 0; A 1 1, A 1 0]) ?_ ?_
    · rw [hA]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · refine base O _ _ _ _ h0 (hdiv 0 0) (hdiv 1 1) (hdiv 1 0) ?_
      intro h; apply hdet; linear_combination -h
  ·
    simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue] at h0 hdiv
    refine of_conj O (P := swap) (Q := 1) (isInt_swap O) (isInt_one O) (A := !![A 1 0, A 1 1; A 0 0, A 0 1]) ?_ ?_
    · rw [hA]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · refine base O _ _ _ _ h0 (hdiv 1 1) (hdiv 0 0) (hdiv 0 1) ?_
      intro h; apply hdet; linear_combination -h
  ·
    simp only [Fin.mk_one, Fin.isValue] at h0 hdiv
    refine of_conj O (P := swap) (Q := swap) (isInt_swap O) (isInt_swap O) (A := !![A 1 1, A 1 0; A 0 1, A 0 0]) ?_ ?_
    · rw [hA]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · refine base O _ _ _ _ h0 (hdiv 1 0) (hdiv 0 1) (hdiv 0 0) ?_
      intro h; apply hdet; linear_combination h

end LocalCartan
open scoped _root_.P2MW.S_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring.LocalCartan

/--
@isnad1 id=ex.0h3v.s10.e1aa9352cd89 from=translated src=- shape=f7d4d9ad vocab=a3ca62bf
-/
theorem solution
    {K : Type*} [Field K] (O : ValuationSubring K) (H : GL (Fin 2) K) :
    ∃ (s t : K) (k₁ k₂ : GL (Fin 2) K), s ≠ 0 ∧ t ≠ 0 ∧ t ∈ O ∧
      (∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, ((k₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, ((k₂⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (H : Matrix (Fin 2) (Fin 2) K) =
        s • ((k₁ : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal ![(1 : K), t] * (k₂ : Matrix (Fin 2) (Fin 2) K)) := by
  obtain ⟨s, t, k₁, k₂, hs, ht, htO, hk₁, hk₂, heq⟩ := LocalCartan.concl O H
  exact ⟨s, t, k₁, k₂, hs, ht, htO, hk₁.1, hk₁.2, hk₂.1, hk₂.2, heq⟩
