import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix

open scoped Classical

namespace AutomorphicForm

section DetOneSubgroup

variable (K : Type*) [NormedField K]

def rowIsometrySubgroup₀ : Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.det).ker ⊓ rowIsometrySubgroup K

/--
@isnad1 id=iff.0h2v.s8.c35516726ff7 from=translated src=- shape=32f48a79 vocab=a70bee35
-/
theorem mem_rowIsometrySubgroup₀_iff {k : GL (Fin 2) K} :
    k ∈ rowIsometrySubgroup₀ K ↔
      (k : Matrix (Fin 2) (Fin 2) K).det = 1 ∧ IsRowIsometry k := by
  unfold rowIsometrySubgroup₀
  constructor
  · rintro ⟨hd, hi⟩
    exact ⟨Units.val_eq_one.mpr hd, hi⟩
  · rintro ⟨hd, hi⟩
    refine ⟨?_, hi⟩
    ext; exact hd

/--
@isnad1 id=le.0h1v.s8.6e72d1ed0455 from=translated src=- shape=d088da8d vocab=fbcbd6a1
-/
theorem rowIsometrySubgroup₀_le :
    rowIsometrySubgroup₀ K ≤ rowIsometrySubgroup K := inf_le_right

/--
@isnad1 id=mem.0h1v.s9.f09d05ffb720 from=translated src=- shape=3735c667 vocab=bb111e66
-/
theorem weyl_mem_rowIsometrySubgroup₀ :
    (Matrix.GeneralLinearGroup.mk'' (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K)
      (by rw [Matrix.det_fin_two_of]; norm_num) : GL (Fin 2) K)
      ∈ rowIsometrySubgroup₀ K := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨?_, weyl_mem_rowIsometrySubgroup⟩
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1
  rw [Matrix.det_fin_two_of]; ring

end DetOneSubgroup

section WeightChar

/--
@isnad1 id=other.1h1v.s9.1e8d66fc3585 from=translated src=- shape=03554f68 vocab=86ba990b
-/
theorem entries_of_mem_rowIsometrySubgroup₀ {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    let a := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0
    let b := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1
    (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -b ∧
      (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = a ∧ a ^ 2 + b ^ 2 = 1 := by
  obtain ⟨hd, hdn, hiso⟩ := (mem_rowIsometrySubgroup₀_iff ℝ).mp hk
  set a := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  set b := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  set c := (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set d := (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1
  have h10 : a ^ 2 + b ^ 2 = 1 := by
    have := hiso 1 0
    simp only [one_mul, zero_mul, add_zero, Real.norm_eq_abs, sq_abs, norm_one,
      one_pow, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    linarith
  have h01 : c ^ 2 + d ^ 2 = 1 := by
    have := hiso 0 1
    simp only [zero_mul, one_mul, zero_add, Real.norm_eq_abs, sq_abs, norm_one,
      one_pow, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    linarith
  have h11 : a * c + b * d = 0 := by
    have h1 := hiso 1 1
    simp only [one_mul, Real.norm_eq_abs, sq_abs, norm_one, one_pow] at h1
    nlinarith [h10, h01]
  have hdet : a * d - b * c = 1 := by
    have := hd; rw [Matrix.det_fin_two] at this; linarith

  refine ⟨?_, ?_, h10⟩
  · nlinarith [sq_nonneg (a - d), sq_nonneg (b + c), h10, h01, h11, hdet]
  · nlinarith [sq_nonneg (a - d), sq_nonneg (b + c), h10, h01, h11, hdet]

def firstRowℂ (k : GL (Fin 2) ℝ) : ℂ :=
  ⟨(k : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1⟩

/--
@isnad1 id=eq.1h1v.s8.9a25f22c89b5 from=translated src=- shape=1a0c1568 vocab=08a3c39b
-/
theorem normSq_firstRowℂ_of_mem {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    Complex.normSq (firstRowℂ k) = 1 := by
  obtain ⟨_, _, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ hk
  simp only [firstRowℂ, Complex.normSq_mk]
  nlinarith

/--
@isnad1 id=ne.1h1v.s8.674a521ff3be from=translated src=- shape=0e85e2e8 vocab=a3dff7d4
-/
theorem firstRowℂ_ne_zero_of_mem {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    firstRowℂ k ≠ 0 := fun h0 => by
  have h := normSq_firstRowℂ_of_mem hk
  rw [h0, map_zero] at h
  exact one_ne_zero h.symm

/--
@isnad1 id=eq.1h2v.s9.29c3199bb035 from=translated src=- shape=ca3caa3f vocab=eddf0a0a
-/
theorem firstRowℂ_mul_of_mem {k k' : GL (Fin 2) ℝ}
    (hk' : k' ∈ rowIsometrySubgroup₀ ℝ) :
    firstRowℂ (k * k') = firstRowℂ k * firstRowℂ k' := by
  obtain ⟨hc', hd', _⟩ := entries_of_mem_rowIsometrySubgroup₀ hk'
  apply Complex.ext
  · show ((k * k' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = _
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hc',
      Complex.mul_re, firstRowℂ, firstRowℂ]
    ring
  · show ((k * k' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = _
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hd',
      Complex.mul_im, firstRowℂ, firstRowℂ]

noncomputable def archWeightOneℝ : rowIsometrySubgroup₀ ℝ →* ℂˣ where
  toFun k := Units.mk0 (firstRowℂ (k : GL (Fin 2) ℝ))
    (firstRowℂ_ne_zero_of_mem k.2)
  map_one' := Units.ext <| Complex.ext (by simp [firstRowℂ]) (by simp [firstRowℂ])
  map_mul' k k' := by
    ext
    exact firstRowℂ_mul_of_mem k'.2

noncomputable def archWeightCharℝ (n : ℤ) : rowIsometrySubgroup₀ ℝ →* ℂˣ :=
  (zpowGroupHom n).comp archWeightOneℝ

/--
@isnad1 id=eq.0h0v.s12.1b59b9eb829d from=translated src=- shape=c0dd6fcc vocab=297434ab
-/
theorem archWeightOneℝ_weyl :
    (archWeightOneℝ
      ⟨_, weyl_mem_rowIsometrySubgroup₀ ℝ⟩ : ℂ) = ⟨0, 1⟩ := by
  show firstRowℂ _ = (⟨0, 1⟩ : ℂ)
  apply Complex.ext <;> simp [firstRowℂ]

/--
@isnad1 id=ne.0h0v.s12.6cda3d362219 from=translated src=- shape=babb3023 vocab=94d9cad8
-/
theorem archWeightOneℝ_ne_one :
    archWeightOneℝ ⟨_, weyl_mem_rowIsometrySubgroup₀ ℝ⟩ ≠ 1 := by
  intro h
  have : (⟨0, 1⟩ : ℂ) = 1 := archWeightOneℝ_weyl ▸ (Units.val_eq_one.mpr h)
  simp [Complex.ext_iff] at this

end WeightChar

section PredicateZero

variable (F : Type) [Field F] [NumberField F]

def HasArchCharacterAt₀ (w : InfinitePlace F) (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ g : AdelicGL2 (𝓞 F) F,
    φ (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))
      = (χ k : ℂ) * φ g

def HasArchType₀ (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, HasArchCharacterAt₀ F w (χ w) φ

end PredicateZero

section Ed9Witness

end Ed9Witness

end AutomorphicForm
