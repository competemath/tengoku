import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Ihara

open Matrix CongruenceSubgroup

open scoped MatrixGroups

section Inclusion

/--
@isnad1 id=le.0h2v.s7.b740bb6fb88d from=translated src=- shape=fcc802a3 vocab=ae3ecfa8
-/
theorem Gamma0_mul_le (N q : ℕ) : Gamma0 (N * q) ≤ Gamma0 N := by
  intro γ hγ
  rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod (N * q)) (N * q)] at hγ
  rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod N) N]
  exact dvd_trans (Int.natCast_dvd_natCast.mpr (dvd_mul_right N q)) hγ

def ι₀ (N q : ℕ) : Gamma0 (N * q) →* Gamma0 N :=
  Subgroup.inclusion (Gamma0_mul_le N q)

/--
@isnad1 id=eq.0h3v.s12.ac770e8c2a18 from=translated src=- shape=5f50cb9e vocab=2a7e1dbd
-/
@[simp]
theorem coe_iota0 (N q : ℕ) (γ : Gamma0 (N * q)) :
    ((ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) = (γ : SL(2, ℤ)) :=
  rfl

/--
@isnad1 id=injectiv.0h2v.s12.c83423951842 from=translated src=- shape=d85d2504 vocab=2b13c501
-/
theorem iota0_injective (N q : ℕ) : Function.Injective (ι₀ N q) :=
  Subgroup.inclusion_injective _

end Inclusion

section Conjugation

/--
@isnad1 id=dvd.0h3v.s9.3e8c9ef09a93 from=translated src=- shape=ac398a03 vocab=6a0f5611
-/
theorem dvd_entry (N q : ℕ) (γ : Gamma0 (N * q)) :
    ((N * q : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  have h := γ.2
  rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod (N * q)) (N * q)] at h
  exact h

/--
@isnad1 id=dvd.0h3v.s9.8b1300fd7099 from=translated src=- shape=b393eb0b vocab=6a0f5611
-/
theorem q_dvd_entry (N q : ℕ) (γ : Gamma0 (N * q)) : (q : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
  dvd_trans (Int.natCast_dvd_natCast.mpr (dvd_mul_left q N)) (dvd_entry N q γ)

def iota1Mat (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![g 0 0, g 0 1 * (q : ℤ); g 1 0 / (q : ℤ), g 1 1]

/--
@isnad1 id=eq.0h2v.s6.bbd5170d7286 from=translated src=- shape=6e5b346e vocab=5855fef5
-/
@[simp] theorem iota1Mat_apply_zero_zero (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    iota1Mat q g 0 0 = g 0 0 := rfl

/--
@isnad1 id=eq.0h2v.s6.642da6978441 from=translated src=- shape=a9bef9cd vocab=7ac7877d
-/
@[simp] theorem iota1Mat_apply_zero_one (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    iota1Mat q g 0 1 = g 0 1 * (q : ℤ) := rfl

/--
@isnad1 id=eq.0h2v.s6.287d023c3027 from=translated src=- shape=a9bef9cd vocab=9b01b37e
-/
@[simp] theorem iota1Mat_apply_one_zero (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    iota1Mat q g 1 0 = g 1 0 / (q : ℤ) := rfl

/--
@isnad1 id=eq.0h2v.s6.bf4932aa1cd0 from=translated src=- shape=6e5b346e vocab=5855fef5
-/
@[simp] theorem iota1Mat_apply_one_one (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    iota1Mat q g 1 1 = g 1 1 := rfl

/--
@isnad1 id=eq.1h2v.s9.24cd678b5a40 from=translated src=- shape=27520a8a vocab=d03e9d7d
-/
theorem w_mul_iota1Mat {q : ℕ} {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (q : ℤ) ∣ g 1 0) :
    !![(1 : ℤ), 0; 0, (q : ℤ)] * iota1Mat q g = g * !![(1 : ℤ), 0; 0, (q : ℤ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iota1Mat, Matrix.mul_apply, Fin.sum_univ_two, Int.mul_ediv_cancel' hg, mul_comm]

/--
@isnad1 id=eq.0h1v.s7.b6dc0bb11e16 from=translated src=- shape=13d30a65 vocab=5855fef5
-/
theorem iota1Mat_one (q : ℕ) : iota1Mat q (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [iota1Mat]

/--
@isnad1 id=eq.1h2v.s6.4447835bd71b from=translated src=- shape=90e06f91 vocab=80557d07
-/
theorem det_iota1Mat {q : ℕ} {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (q : ℤ) ∣ g 1 0) :
    (iota1Mat q g).det = g.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, iota1Mat_apply_zero_zero, iota1Mat_apply_zero_one,
    iota1Mat_apply_one_zero, iota1Mat_apply_one_one, mul_assoc, Int.mul_ediv_cancel' hg]

/--
@isnad1 id=eq.2h3v.s8.73cc1d587f30 from=translated src=- shape=83b27b3c vocab=34eb43e0
-/
theorem iota1Mat_mul {q : ℕ} {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (q : ℤ) ∣ g 1 0) (hh : (q : ℤ) ∣ h 1 0) :
    iota1Mat q (g * h) = iota1Mat q g * iota1Mat q h := by
  obtain ⟨k, hk⟩ := hg
  obtain ⟨k', hk'⟩ := hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [iota1Mat, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, hk, hk'] <;>
    by_cases hq : (q : ℤ) = 0
  · simp [hq]
  · rw [Int.mul_ediv_cancel_left _ hq]; ring
  · simp [hq]
  · ring
  · simp [hq]
  · rw [show (q : ℤ) * k * h 0 0 + g 1 1 * ((q : ℤ) * k') = (q : ℤ) * (k * h 0 0 + g 1 1 * k') by ring,
      Int.mul_ediv_cancel_left _ hq, Int.mul_ediv_cancel_left _ hq, Int.mul_ediv_cancel_left _ hq]
  · simp [hq]
  · rw [Int.mul_ediv_cancel_left _ hq]; ring

def iota1SL (N q : ℕ) (γ : Gamma0 (N * q)) : SL(2, ℤ) :=
  ⟨iota1Mat q (γ : SL(2, ℤ)), by
    rw [det_iota1Mat (q_dvd_entry N q γ)]
    exact (γ : SL(2, ℤ)).det_coe⟩

/--
@isnad1 id=eq.0h3v.s9.6e97a9c29830 from=translated src=- shape=4fa86425 vocab=8733bef8
-/
@[simp]
theorem coe_iota1SL (N q : ℕ) (γ : Gamma0 (N * q)) :
    (iota1SL N q γ : Matrix (Fin 2) (Fin 2) ℤ) = iota1Mat q (γ : SL(2, ℤ)) :=
  rfl

/--
@isnad1 id=mem.0h3v.s8.8c28d25960a7 from=translated src=- shape=a7388c4f vocab=90189562
-/
theorem iota1SL_mem (N q : ℕ) (γ : Gamma0 (N * q)) : iota1SL N q γ ∈ Gamma0 N := by
  rw [Gamma0_mem, coe_iota1SL, iota1Mat_apply_one_zero, CharP.intCast_eq_zero_iff (ZMod N) N]
  obtain ⟨k, hk⟩ := dvd_entry N q γ
  rw [hk]
  by_cases hq : (q : ℤ) = 0
  · simp [hq]
  · rw [show ((N * q : ℕ) : ℤ) * k = (q : ℤ) * ((N : ℤ) * k) by push_cast; ring,
      Int.mul_ediv_cancel_left _ hq]
    exact dvd_mul_right (N : ℤ) k

def ι₁ (N q : ℕ) : Gamma0 (N * q) →* Gamma0 N where
  toFun γ := ⟨iota1SL N q γ, iota1SL_mem N q γ⟩
  map_one' := Subtype.ext <| Subtype.ext <| by
    simpa using iota1Mat_one q
  map_mul' γ δ := Subtype.ext <| Subtype.ext <| by
    simpa using iota1Mat_mul (q_dvd_entry N q γ) (q_dvd_entry N q δ)

/--
@isnad1 id=eq.0h3v.s12.2d3419bb7e4f from=translated src=- shape=afa8739d vocab=2a540afe
-/
@[simp]
theorem coe_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    ((ι₁ N q γ : Gamma0 N) : SL(2, ℤ)) = iota1SL N q γ :=
  rfl

/--
@isnad1 id=eq.0h3v.s12.e738d3ce1077 from=translated src=- shape=b5edd320 vocab=71aa5105
-/
theorem coe_coe_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    (((ι₁ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = iota1Mat q (γ : SL(2, ℤ)) :=
  rfl

/--
@isnad1 id=eq.0h3v.s12.1cd8f6d833e4 from=translated src=- shape=239fb459 vocab=18891fb6
-/
theorem w_mul_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    !![(1 : ℤ), 0; 0, (q : ℤ)] * (((ι₁ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * !![(1 : ℤ), 0; 0, (q : ℤ)] :=
  w_mul_iota1Mat (q_dvd_entry N q γ)

/--
@isnad1 id=injectiv.1h2v.s12.1e5560fe3bab from=translated src=- shape=7504ac4d vocab=31ab267c
-/
theorem iota1_injective (N : ℕ) {q : ℕ} (hq : q ≠ 0) : Function.Injective (ι₁ N q) := by
  intro γ δ h
  have hq' : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq
  have hmat : iota1Mat q (γ : SL(2, ℤ)) = iota1Mat q (δ : SL(2, ℤ)) :=
    congrArg (fun x : Gamma0 N => ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) h
  refine Subtype.ext (Subtype.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using congrFun (congrFun hmat 0) 0
  · simpa [hq] using congrFun (congrFun hmat 0) 1
  · have h10 := congrFun (congrFun hmat 1) 0
    simp only [iota1Mat_apply_one_zero, Fin.isValue] at h10
    have := congrArg (fun x : ℤ => (q : ℤ) * x) h10
    simp only [Int.mul_ediv_cancel' (q_dvd_entry N q γ), Int.mul_ediv_cancel' (q_dvd_entry N q δ)]
      at this
    exact this
  · simpa using congrFun (congrFun hmat 1) 1

/--
@isnad1 id=iff.1h3v.s11.fab25a8ea2e8 from=translated src=- shape=4be51388 vocab=f9b16a94
-/
theorem mem_range_iota1_iff (N : ℕ) {q : ℕ} (hq : q ≠ 0) (δ : Gamma0 N) :
    δ ∈ (ι₁ N q).range ↔ (q : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 := by
  have hq' : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨(γ : SL(2, ℤ)) 0 1, by simp [mul_comm]⟩
  · rintro ⟨b, hb⟩

    have hN : ((N : ℕ) : ℤ) ∣ (δ : SL(2, ℤ)) 1 0 := by
      have h := δ.2
      rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod N) N] at h
      exact h
    let M : Matrix (Fin 2) (Fin 2) ℤ :=
      !![(δ : SL(2, ℤ)) 0 0, b; (δ : SL(2, ℤ)) 1 0 * (q : ℤ), (δ : SL(2, ℤ)) 1 1]
    have hdet : M.det = 1 := by
      have h1 := (δ : SL(2, ℤ)).det_coe
      rw [Matrix.det_fin_two] at h1 ⊢
      simp only [M, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        Fin.isValue]
      rw [hb] at h1
      linear_combination h1
    have hmem : (⟨M, hdet⟩ : SL(2, ℤ)) ∈ Gamma0 (N * q) := by
      show (((⟨M, hdet⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod (N * q)) = 0
      rw [CharP.intCast_eq_zero_iff (ZMod (N * q)) (N * q)]
      show ((N * q : ℕ) : ℤ) ∣ (δ : SL(2, ℤ)) 1 0 * (q : ℤ)
      push_cast
      exact mul_dvd_mul hN dvd_rfl
    refine ⟨⟨⟨M, hdet⟩, hmem⟩, Subtype.ext (Subtype.ext ?_)⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [iota1Mat, M]
    · simp [iota1Mat, M, hb, mul_comm]
    · show (δ : SL(2, ℤ)) 1 0 * (q : ℤ) / (q : ℤ) = (δ : SL(2, ℤ)) 1 0
      exact Int.mul_ediv_cancel _ hq'
    · simp [iota1Mat, M]

end Conjugation

end Ihara
