import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries

set_option autoImplicit false

namespace HeckeEis
export _root_.HeckeEis (heckeConjMat heckeConjMat_apply_zero_one heckeConjMat_apply_one_zero heckeUpper mem_heckeUpper heckeConj transferAux coeffCocycles coeffCoboundaries coeffHeckeFun coeffHeckeFun_apply sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries coeffHeckeFun_mem_coeffCoboundaries)
open _root_.HeckeEis
namespace R2CompTT

open CongruenceSubgroup Matrix
open scoped MatrixGroups

section Entries

variable (N ℓ : ℕ) [NeZero ℓ]

/--
@isnad1 id=eq.0h3v.s14.0ff1229c10ab from=translated src=- shape=11df7d9a vocab=d2b9b1b9
-/
theorem conj_apply01 (u : ↥(heckeUpper N ℓ)) :
    ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 0 1 = ((u : Gamma0 N) : SL(2, ℤ)) 0 1 / (ℓ : ℤ) := rfl

end Entries

section Levels

variable (N ℓ ℓ' m : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero m]

omit [NeZero ℓ] [NeZero ℓ'] [NeZero m] in
/--
@isnad1 id=le.1h4v.s10.890545591c2b from=translated src=- shape=a6c2da2d vocab=4a3de591
-/
theorem heckeUpper_le_left (hm : m = ℓ * ℓ') : heckeUpper N m ≤ heckeUpper N ℓ := by
  intro w hw
  rw [mem_heckeUpper] at hw ⊢
  have h : (ℓ : ℤ) ∣ (m : ℤ) := ⟨(ℓ' : ℤ), by rw [hm]; push_cast; ring⟩
  exact h.trans hw

/--
@isnad1 id=iff.1h5v.s14.b62c7288ea43 from=translated src=- shape=e25a2bea vocab=422712ab
-/
theorem mem_heckeUpper_mul_iff (hm : m = ℓ * ℓ') (u : ↥(heckeUpper N ℓ)) :
    (u : Gamma0 N) ∈ heckeUpper N m ↔ heckeConj N ℓ u ∈ heckeUpper N ℓ' := by
  rw [mem_heckeUpper, mem_heckeUpper, conj_apply01]
  obtain ⟨b', hb'⟩ := (mem_heckeUpper N ℓ).mp u.2
  have hℓ0 : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne ℓ)
  rw [hb', Int.mul_ediv_cancel_left _ hℓ0, hm, Nat.cast_mul]
  exact mul_dvd_mul_iff_left hℓ0

def toLeft (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) : ↥(heckeUpper N ℓ) :=
  ⟨w, heckeUpper_le_left N ℓ ℓ' m hm w.2⟩

/--
@isnad1 id=mem.1h5v.s14.3662ccb7914f from=translated src=- shape=bec4b83f vocab=940572e1
-/
theorem conj_toLeft_mem (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) :
    heckeConj N ℓ (toLeft N ℓ ℓ' m hm w) ∈ heckeUpper N ℓ' :=
  (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mp w.2

/--
@isnad1 id=eq.1h5v.s16.e426a9b09691 from=translated src=- shape=7ef784fb vocab=a7df2179
-/
theorem heckeConj_mul (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) :
    heckeConj N m w =
      heckeConj N ℓ' ⟨heckeConj N ℓ (toLeft N ℓ ℓ' m hm w), conj_toLeft_mem N ℓ ℓ' m hm w⟩ := by
  have hm' : ((m : ℕ) : ℤ) = (ℓ : ℤ) * (ℓ' : ℤ) := by rw [hm, Nat.cast_mul]
  refine Subtype.ext (Subtype.ext ?_)
  change heckeConjMat m (((w : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    = heckeConjMat ℓ' (heckeConjMat ℓ (((w : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
  set A : Matrix (Fin 2) (Fin 2) ℤ := (((w : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simp only [heckeConjMat_apply_zero_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    rw [Int.ediv_ediv_of_nonneg (by positivity), hm']
  · simp only [heckeConjMat_apply_one_zero, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    rw [hm', mul_assoc]
  · rfl

/--
@isnad1 id=eq.3h7v.s16.b4a5cbc2f257 from=translated src=- shape=ecc50230 vocab=422712ab
-/
theorem heckeConj_mul_eq (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) (u : ↥(heckeUpper N ℓ))
    (u' : ↥(heckeUpper N ℓ')) (hwu : (w : Gamma0 N) = u) (huu' : heckeConj N ℓ u = (u' : Gamma0 N)) :
    heckeConj N m w = heckeConj N ℓ' u' := by
  rw [heckeConj_mul N ℓ ℓ' m hm w]
  congr 1
  refine Subtype.ext ?_
  rw [← huu']
  change heckeConj N ℓ (toLeft N ℓ ℓ' m hm w) = heckeConj N ℓ u
  congr 1
  exact Subtype.ext hwu

end Levels

section Coset

variable (N ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

/--
@isnad1 id=ex.3h3v.s14.4747c7595785 from=translated src=- shape=7606c430 vocab=a58d1d7c
-/
theorem exists_heckeConj_eq (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (x : Gamma0 N)
    (hx : (ℓ : ℤ) ∣ (x : SL(2, ℤ)) 1 0) : ∃ u : ↥(heckeUpper N ℓ), heckeConj N ℓ u = x := by
  obtain ⟨c', hc'⟩ := hx
  have hℓ0 : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne ℓ)
  set A : Matrix (Fin 2) (Fin 2) ℤ := ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hA
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two, hA]; exact (x : SL(2, ℤ)).2
  have hc'' : A 1 0 = (ℓ : ℤ) * c' := hc'

  let B : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0, A 0 1 * (ℓ : ℤ); c', A 1 1]
  have hB00 : B 0 0 = A 0 0 := rfl
  have hB01 : B 0 1 = A 0 1 * (ℓ : ℤ) := rfl
  have hB10 : B 1 0 = c' := rfl
  have hB11 : B 1 1 = A 1 1 := rfl
  have hBdet : B.det = 1 := by
    rw [Matrix.det_fin_two, hB00, hB01, hB10, hB11, ← hdet, hc'']; ring

  have hNc : ((A 1 0 : ℤ) : ZMod N) = 0 := by
    have := Gamma0_mem.mp x.2
    simpa [hA] using this
  have hNc' : ((c' : ℤ) : ZMod N) = 0 := by
    have hcop : IsCoprime (N : ℤ) (ℓ : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
    have hdvd : (N : ℤ) ∣ (ℓ : ℤ) * c' := by
      rw [← hc'']; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hNc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr (hcop.dvd_of_dvd_mul_left hdvd)
  let uSL : SL(2, ℤ) := ⟨B, hBdet⟩
  have huG : uSL ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact hNc'
  have huU : (⟨uSL, huG⟩ : Gamma0 N) ∈ heckeUpper N ℓ := by
    rw [mem_heckeUpper]
    exact Dvd.intro_left _ rfl
  refine ⟨⟨⟨uSL, huG⟩, huU⟩, Subtype.ext (Subtype.ext ?_)⟩
  change heckeConjMat ℓ B = A
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simp only [heckeConjMat_apply_zero_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, hB01]
    exact Int.mul_ediv_cancel _ hℓ0
  · simp only [heckeConjMat_apply_one_zero, Fin.zero_eta, Fin.mk_one, Fin.isValue, hB10, hc'']
    ring
  · rfl

/--
@isnad1 id=ex.3h5v.s12.ce0c6d1f604f from=translated src=- shape=4dc5c2a2 vocab=08a0da1c
-/
theorem exists_mul_mem_dvd (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (γ : Gamma0 N) (k : ℤ)
    (he : ¬ (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 * k * (ℓ' : ℤ) + (γ : SL(2, ℤ)) 1 1) :
    ∃ u'' : ↥(heckeUpper N ℓ'), (ℓ : ℤ) ∣ ((γ : Gamma0 N) * u'' : SL(2, ℤ)) 1 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set c : ℤ := (γ : SL(2, ℤ)) 1 0 with hc
  set d : ℤ := (γ : SL(2, ℤ)) 1 1 with hd
  set e : ℤ := c * k * (ℓ' : ℤ) + d with he_def
  have heZ : ((e : ℤ) : ZMod ℓ) ≠ 0 := fun h => he ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp h)
  have hNZ : ((N : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h
    rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h
    exact hℓN h
  set Y : ZMod ℓ := -(c : ZMod ℓ) * (((N : ℤ) : ZMod ℓ) * (e : ZMod ℓ))⁻¹ with hY
  let z₁ : ℕ := Y.val
  let zz : ℤ := (N : ℤ) * (z₁ : ℤ)
  have hz₁ : ((z₁ : ℤ) : ZMod ℓ) = Y := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val Y
  have hzz : ((zz : ℤ) : ZMod ℓ) = ((N : ℤ) : ZMod ℓ) * Y := by
    change (((N : ℤ) * (z₁ : ℤ) : ℤ) : ZMod ℓ) = _
    rw [Int.cast_mul, hz₁]
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![1 + k * (ℓ' : ℤ) * zz, k * (ℓ' : ℤ); zz, 1]
  have hB00 : B 0 0 = 1 + k * (ℓ' : ℤ) * zz := rfl
  have hB01 : B 0 1 = k * (ℓ' : ℤ) := rfl
  have hB10 : B 1 0 = zz := rfl
  have hB11 : B 1 1 = 1 := rfl
  have hBdet : B.det = 1 := by rw [Matrix.det_fin_two, hB00, hB01, hB10, hB11]; ring
  let uSL : SL(2, ℤ) := ⟨B, hBdet⟩
  have huG : uSL ∈ Gamma0 N := by
    rw [Gamma0_mem]
    change ((B 1 0 : ℤ) : ZMod N) = 0
    rw [hB10]
    change (((N : ℤ) * (z₁ : ℤ) : ℤ) : ZMod N) = 0
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  have huU : (⟨uSL, huG⟩ : Gamma0 N) ∈ heckeUpper N ℓ' := by
    rw [mem_heckeUpper]
    change (ℓ' : ℤ) ∣ B 0 1
    rw [hB01]; exact dvd_mul_left _ _
  refine ⟨⟨⟨uSL, huG⟩, huU⟩, ?_⟩

  have hentry : ((γ : Gamma0 N) * (⟨⟨uSL, huG⟩, huU⟩ : ↥(heckeUpper N ℓ')) : SL(2, ℤ)) 1 0
      = c * (1 + k * (ℓ' : ℤ) * zz) + d * zz := by
    change (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * B) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two, hB00, hB10]
  rw [hentry, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_one, hzz]
  have hNe : ((N : ℤ) : ZMod ℓ) * (e : ZMod ℓ) ≠ 0 := mul_ne_zero hNZ heZ
  have hX : (((N : ℤ) : ZMod ℓ) * (e : ZMod ℓ)) * Y = -(c : ZMod ℓ) := by
    rw [hY, mul_comm, mul_assoc, inv_mul_cancel₀ hNe, mul_one]
  have he' : ((e : ℤ) : ZMod ℓ) = (c : ZMod ℓ) * (k : ZMod ℓ) * ((ℓ' : ℤ) : ZMod ℓ) + (d : ZMod ℓ) := by
    rw [he_def, Int.cast_add, Int.cast_mul, Int.cast_mul]
  linear_combination hX - (((N : ℤ) : ZMod ℓ) * Y) * he'

/--
@isnad1 id=ex.3h4v.s15.c77c4ac7455c from=translated src=- shape=7aaebc26 vocab=cb76f337
-/
theorem exists_conj_mul_eq (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓℓ' : ¬ ℓ ∣ ℓ') (γ : Gamma0 N) :
    ∃ (u : ↥(heckeUpper N ℓ)) (u' : ↥(heckeUpper N ℓ')),
      (heckeConj N ℓ u : Gamma0 N) * u' = γ := by

  have hk : ∃ k : ℤ, ¬ (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 * k * (ℓ' : ℤ) + (γ : SL(2, ℤ)) 1 1 := by
    by_cases hd : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 1
    · refine ⟨1, fun h => ?_⟩
      rw [mul_one] at h
      have hc : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 * (ℓ' : ℤ) := (dvd_add_left hd).mp h
      have hℓp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
      rcases hℓp.dvd_or_dvd hc with h1 | h1
      ·
        have hdet := Matrix.det_fin_two ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        rw [(γ : SL(2, ℤ)).2] at hdet
        have : (ℓ : ℤ) ∣ 1 := by
          rw [hdet]
          exact dvd_sub (hd.mul_left _) (h1.mul_left _)
        exact hℓ.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
      · exact hℓℓ' (by exact_mod_cast h1)
    · exact ⟨0, by simpa using hd⟩
  obtain ⟨k, hk⟩ := hk
  obtain ⟨u'', hu''⟩ := exists_mul_mem_dvd N ℓ ℓ' hℓ hℓN γ k hk
  obtain ⟨u, hu⟩ := exists_heckeConj_eq N ℓ hℓ hℓN ((γ : Gamma0 N) * u'') hu''
  refine ⟨u, u''⁻¹, ?_⟩
  rw [hu, Subgroup.coe_inv, mul_inv_cancel_right]

/--
@isnad1 id=ex.3h3v.s14.174a2d3d51ca from=translated src=- shape=8e65ba56 vocab=b53936ce
-/
theorem exists_section (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓℓ' : ¬ ℓ ∣ ℓ') :
    ∃ σ : Gamma0 N ⧸ heckeUpper N ℓ' → ↥(heckeUpper N ℓ),
      ∀ q', ((heckeConj N ℓ (σ q') : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q' := by
  have h : ∀ q' : Gamma0 N ⧸ heckeUpper N ℓ', ∃ u : ↥(heckeUpper N ℓ),
      ((heckeConj N ℓ u : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q' := by
    intro q'
    obtain ⟨u, u', huu'⟩ := exists_conj_mul_eq N ℓ ℓ' hℓ hℓN hℓℓ' q'.out
    refine ⟨u, ?_⟩
    rw [← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.mpr ?_
    rw [← huu', inv_mul_cancel_left]
    exact u'.2
  choose σ hσ using h
  exact ⟨σ, hσ⟩

end Coset

section Main

variable {N ℓ ℓ' m : ℕ} [NeZero ℓ] [NeZero ℓ'] [NeZero m]
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (ρ : Representation K (Gamma0 N) V) (a a' : V →ₗ[K] V)
variable (σ : Gamma0 N ⧸ heckeUpper N ℓ' → ↥(heckeUpper N ℓ))
variable (hσ : ∀ q', ((heckeConj N ℓ (σ q') : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q')

def sP (q' : Gamma0 N ⧸ heckeUpper N ℓ') : Gamma0 N := heckeConj N ℓ (σ q')

include hσ in
/--
@isnad1 id=eq.1h5v.s14.125ae645e8a1 from=translated src=- shape=c729be31 vocab=8b714901
-/
theorem sP_coe (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((sP σ q' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q' := hσ q'

def tP (h : Gamma0 N) (q' : Gamma0 N ⧸ heckeUpper N ℓ') : ↥(heckeUpper N ℓ') :=
  ⟨(sP σ (h • q'))⁻¹ * (h * sP σ q'), by
    refine QuotientGroup.eq.mp ?_
    rw [sP_coe σ hσ]
    change h • q' = h • ((sP σ q' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ')
    rw [sP_coe σ hσ]⟩

/--
@isnad1 id=eq.1h6v.s15.25691268d321 from=translated src=- shape=6e8d7ab5 vocab=3a82aa19
-/
@[scoped simp] theorem coe_tP (h : Gamma0 N) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((tP σ hσ h q' : ↥(heckeUpper N ℓ')) : Gamma0 N) = (sP σ (h • q'))⁻¹ * (h * sP σ q') := rfl

/--
@isnad1 id=eq.1h6v.s15.d01d0cdb3de4 from=translated src=- shape=067eb01b vocab=0ec533c5
-/
theorem sP_mul_tP (h : Gamma0 N) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    sP σ (h • q') * (tP σ hσ h q' : Gamma0 N) = h * sP σ q' := by
  rw [coe_tP, mul_inv_cancel_left]

noncomputable def Ty (z : Gamma0 N → V) : Gamma0 N → V := fun h =>
  letI := (heckeUpper N ℓ').fintypeQuotientOfFiniteIndex
  ∑ q' : Gamma0 N ⧸ heckeUpper N ℓ', ρ (sP σ (h • q')) (a' (z (heckeConj N ℓ' (tP σ hσ h q'))))

/--
@isnad1 id=mem.3h9v.s16.822d805b4d7f from=translated src=- shape=bf1b92bc vocab=f1039774
-/
theorem Ty_sub_mem
    (ha' : ∀ u : ↥(heckeUpper N ℓ'), a' ∘ₗ ρ (heckeConj N ℓ' u) = ρ (u : Gamma0 N) ∘ₗ a')
    {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) :
    Ty ρ a' σ hσ z - coeffHeckeFun N ℓ' ρ a' z ∈ coeffCoboundaries ρ :=
  sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries N ℓ' ρ a' ha' (sP σ) (tP σ hσ)
    (sP_coe σ hσ) (sP_mul_tP σ hσ) hz

noncomputable def PsiFun (x : (Gamma0 N ⧸ heckeUpper N ℓ) × (Gamma0 N ⧸ heckeUpper N ℓ')) :
    Gamma0 N ⧸ heckeUpper N m :=
  ((x.1.out * ((σ x.2 : ↥(heckeUpper N ℓ)) : Gamma0 N) : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m)

variable (hm : m = ℓ * ℓ')

include hσ hm in
/--
@isnad1 id=injectiv.2h5v.s14.e50bd95c2d13 from=translated src=- shape=56884b22 vocab=7da9aac7
-/
theorem PsiFun_injective : Function.Injective (PsiFun (m := m) σ) := by
  rintro ⟨q₁, q₁'⟩ ⟨q₂, q₂'⟩ h
  have hW : (q₁.out * ((σ q₁' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹
      * (q₂.out * ((σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N)) ∈ heckeUpper N m :=
    QuotientGroup.eq.mp h

  have hU : q₁.out⁻¹ * q₂.out ∈ heckeUpper N ℓ := by
    have h1 : (q₁.out * ((σ q₁' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹
        * (q₂.out * ((σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N)) ∈ heckeUpper N ℓ :=
      heckeUpper_le_left N ℓ ℓ' m hm hW
    rw [_root_.mul_inv_rev, mul_assoc, ← mul_assoc (q₁.out⁻¹)] at h1
    have h2 := (Subgroup.mul_mem_cancel_left _ ((heckeUpper N ℓ).inv_mem (σ q₁').2)).mp h1
    exact (Subgroup.mul_mem_cancel_right _ (σ q₂').2).mp h2
  have hq : q₁ = q₂ := by
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    exact QuotientGroup.eq.mpr hU
  subst hq
  have hW' : (((σ q₁')⁻¹ * σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N) ∈ heckeUpper N m := by
    have : (q₁.out * ((σ q₁' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹
        * (q₁.out * ((σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N))
        = (((σ q₁')⁻¹ * σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
      push_cast; group
    rw [← this]; exact hW
  have hU' : heckeConj N ℓ ((σ q₁')⁻¹ * σ q₂') ∈ heckeUpper N ℓ' :=
    (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mp hW'
  rw [map_mul, map_inv] at hU'
  have hq' : ((sP σ q₁' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = (sP σ q₂' : Gamma0 N) :=
    QuotientGroup.eq.mpr hU'
  rw [sP_coe σ hσ, sP_coe σ hσ] at hq'
  rw [hq']

include hσ hm in
/--
@isnad1 id=surjecti.2h5v.s14.054272232525 from=translated src=- shape=56884b22 vocab=3d30e2c1
-/
theorem PsiFun_surjective : Function.Surjective (PsiFun (m := m) σ) := by
  intro Q
  induction Q using QuotientGroup.induction_on with
  | H γ =>
    set q : Gamma0 N ⧸ heckeUpper N ℓ := (γ : Gamma0 N ⧸ heckeUpper N ℓ) with hq
    have hu₀ : q.out⁻¹ * γ ∈ heckeUpper N ℓ := QuotientGroup.eq.mp (by rw [QuotientGroup.out_eq'])
    set u₀ : ↥(heckeUpper N ℓ) := ⟨q.out⁻¹ * γ, hu₀⟩ with hu₀_def
    set q' : Gamma0 N ⧸ heckeUpper N ℓ' :=
      ((heckeConj N ℓ u₀ : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') with hq'
    refine ⟨(q, q'), ?_⟩
    change ((q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N) : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m)
      = (γ : Gamma0 N ⧸ heckeUpper N m)
    refine QuotientGroup.eq.mpr ?_
    have hmem : (((σ q')⁻¹ * u₀ : ↥(heckeUpper N ℓ)) : Gamma0 N) ∈ heckeUpper N m := by
      refine (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mpr ?_
      rw [map_mul, map_inv]
      refine QuotientGroup.eq.mp ?_
      change ((sP σ q' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q'
      exact sP_coe σ hσ q'
    have : (q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹ * γ
        = (((σ q')⁻¹ * u₀ : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
      rw [hu₀_def]; push_cast; group
    rw [this]; exact hmem

noncomputable def Psi : (Gamma0 N ⧸ heckeUpper N ℓ) × (Gamma0 N ⧸ heckeUpper N ℓ') ≃
    Gamma0 N ⧸ heckeUpper N m :=
  Equiv.ofBijective (PsiFun σ) ⟨PsiFun_injective σ hσ hm, PsiFun_surjective σ hσ hm⟩

/--
@isnad1 id=eq.2h6v.s15.5912dd5ffba1 from=translated src=- shape=df87d1ac vocab=6d53bbed
-/
theorem Psi_apply (x : (Gamma0 N ⧸ heckeUpper N ℓ) × (Gamma0 N ⧸ heckeUpper N ℓ')) :
    Psi σ hσ hm x =
      ((x.1.out * ((σ x.2 : ↥(heckeUpper N ℓ)) : Gamma0 N) : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m) :=
  rfl

noncomputable def wU (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ↥(heckeUpper N ℓ) :=
  (σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q'))⁻¹
    * transferAux (heckeUpper N ℓ) g q * σ q'

/--
@isnad1 id=eq.1h7v.s16.4700c5951415 from=translated src=- shape=b62830e7 vocab=e04bc3cf
-/
theorem heckeConj_wU (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ)
    (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    heckeConj N ℓ (wU σ g q q') =
      (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) q' : Gamma0 N) := by
  rw [wU, map_mul, map_mul, map_inv, coe_tP, mul_assoc]
  rfl

include hσ hm in
/--
@isnad1 id=mem.2h8v.s14.46b1c803a4e9 from=translated src=- shape=667de4f6 vocab=7ead5cfd
-/
theorem wU_mem (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) ∈ heckeUpper N m := by
  refine (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mpr ?_
  rw [heckeConj_wU σ hσ]
  exact (tP σ hσ _ q').2

/--
@isnad1 id=eq.0h7v.s15.f03bd28c407f from=translated src=- shape=6743096a vocab=af6330fc
-/
theorem coe_wU (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) =
      ((σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') :
          ↥(heckeUpper N ℓ)) : Gamma0 N)⁻¹
        * ((g • q).out⁻¹ * (g * q.out)) * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := rfl

/--
@isnad1 id=eq.2h8v.s16.ee87b5140abf from=translated src=- shape=fd052bd3 vocab=cbf52069
-/
theorem smul_Psi (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    g • Psi σ hσ hm (q, q') =
      Psi σ hσ hm (g • q, (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') := by
  rw [Psi_apply, Psi_apply]
  change (((g * (q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N))) : Gamma0 N) :
      Gamma0 N ⧸ heckeUpper N m) = _
  refine QuotientGroup.eq.mpr ?_
  have key : ((g • q).out *
        ((σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') :
          ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹ * (g * (q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N)))
      = ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
    rw [coe_wU]; group
  have hmem := (heckeUpper N m).inv_mem (wU_mem σ hσ hm g q q')
  rw [← key, _root_.mul_inv_rev, inv_inv] at hmem
  exact hmem

noncomputable def SS (Q : Gamma0 N ⧸ heckeUpper N m) : Gamma0 N :=
  ((Psi σ hσ hm).symm Q).1.out * (((σ ((Psi σ hσ hm).symm Q).2) : ↥(heckeUpper N ℓ)) : Gamma0 N)

/--
@isnad1 id=eq.2h7v.s15.0e1827f3f349 from=translated src=- shape=2145958e vocab=ba2e5354
-/
theorem SS_Psi (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    SS σ hσ hm (Psi σ hσ hm (q, q')) = q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
  rw [SS, Equiv.symm_apply_apply]

/--
@isnad1 id=eq.2h6v.s14.aa09374ae69d from=translated src=- shape=70c5bcee vocab=94bd58c0
-/
theorem SS_coe (Q : Gamma0 N ⧸ heckeUpper N m) :
    ((SS σ hσ hm Q : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m) = Q := by
  conv_rhs => rw [← (Psi σ hσ hm).apply_symm_apply Q]
  unfold SS
  rw [Psi_apply]

noncomputable def TT (g : Gamma0 N) (Q : Gamma0 N ⧸ heckeUpper N m) : ↥(heckeUpper N m) :=
  ⟨(SS σ hσ hm (g • Q))⁻¹ * (g * SS σ hσ hm Q), by
    refine QuotientGroup.eq.mp ?_
    rw [SS_coe]
    change g • Q = g • ((SS σ hσ hm Q : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m)
    rw [SS_coe]⟩

/--
@isnad1 id=eq.2h7v.s15.cf43f6bf43a6 from=translated src=- shape=65717d67 vocab=003c635c
-/
@[scoped simp] theorem coe_TT (g : Gamma0 N) (Q : Gamma0 N ⧸ heckeUpper N m) :
    ((TT σ hσ hm g Q : ↥(heckeUpper N m)) : Gamma0 N) = (SS σ hσ hm (g • Q))⁻¹ * (g * SS σ hσ hm Q) :=
  rfl

/--
@isnad1 id=eq.2h7v.s15.05416316c4b9 from=translated src=- shape=8c28b2e9 vocab=9fa9f60c
-/
theorem SS_mul_TT (g : Gamma0 N) (Q : Gamma0 N ⧸ heckeUpper N m) :
    SS σ hσ hm (g • Q) * (TT σ hσ hm g Q : Gamma0 N) = g * SS σ hσ hm Q := by
  rw [coe_TT, mul_inv_cancel_left]

/--
@isnad1 id=eq.2h8v.s15.e4f904ec10eb from=translated src=- shape=fe570ccd vocab=01f28744
-/
theorem coe_TT_Psi (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((TT σ hσ hm g (Psi σ hσ hm (q, q')) : ↥(heckeUpper N m)) : Gamma0 N)
      = ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
  rw [coe_TT, smul_Psi, SS_Psi, SS_Psi, coe_wU]
  group

/--
@isnad1 id=eq.2h8v.s16.d6fe7e1d08c8 from=translated src=- shape=42613a36 vocab=7d4ea17a
-/
theorem heckeConj_TT_Psi (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ)
    (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    heckeConj N m (TT σ hσ hm g (Psi σ hσ hm (q, q'))) =
      heckeConj N ℓ' (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) q') :=
  heckeConj_mul_eq N ℓ ℓ' m hm _ (wU σ g q q') _ (coe_TT_Psi σ hσ hm g q q') (heckeConj_wU σ hσ g q q')

noncomputable def TmS (z : Gamma0 N → V) : Gamma0 N → V := fun g =>
  letI := (heckeUpper N m).fintypeQuotientOfFiniteIndex
  ∑ Q : Gamma0 N ⧸ heckeUpper N m, ρ (SS σ hσ hm (g • Q)) ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm g Q))))

include hm in

/--
@isnad1 id=eq.3h10v.s16.38b0935908f8 from=translated src=- shape=b958877c vocab=92a16965
-/
theorem compat_mul
    (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(heckeUpper N ℓ'), a' ∘ₗ ρ (heckeConj N ℓ' u) = ρ (u : Gamma0 N) ∘ₗ a')
    (w : ↥(heckeUpper N m)) :
    (a ∘ₗ a') ∘ₗ ρ (heckeConj N m w) = ρ (w : Gamma0 N) ∘ₗ (a ∘ₗ a') := by
  rw [heckeConj_mul N ℓ ℓ' m hm w, LinearMap.comp_assoc, ha', ← LinearMap.comp_assoc]
  change (a ∘ₗ ρ (heckeConj N ℓ (toLeft N ℓ ℓ' m hm w))) ∘ₗ a' = _
  rw [ha, LinearMap.comp_assoc]
  rfl

/--
@isnad1 id=mem.5h11v.s16.a8ade33aa75f from=translated src=- shape=03e472c4 vocab=baa21196
-/
theorem TmS_sub_mem
    (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(heckeUpper N ℓ'), a' ∘ₗ ρ (heckeConj N ℓ' u) = ρ (u : Gamma0 N) ∘ₗ a')
    {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) :
    TmS ρ a a' σ hσ hm z - coeffHeckeFun N m ρ (a ∘ₗ a') z ∈ coeffCoboundaries ρ :=
  sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries N m ρ (a ∘ₗ a') (compat_mul ρ a a' hm ha ha')
    (SS σ hσ hm) (TT σ hσ hm) (SS_coe σ hσ hm) (SS_mul_TT σ hσ hm) hz

/--
@isnad1 id=eq.3h11v.s15.02b319270aa2 from=translated src=- shape=0337766f vocab=a1643af9
-/
theorem coeffHeckeFun_Ty
    (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (z : Gamma0 N → V) :
    coeffHeckeFun N ℓ ρ a (Ty ρ a' σ hσ z) = TmS ρ a a' σ hσ hm z := by
  letI iU := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  letI iU' := (heckeUpper N ℓ').fintypeQuotientOfFiniteIndex
  letI iW := (heckeUpper N m).fintypeQuotientOfFiniteIndex
  funext g
  rw [coeffHeckeFun_apply]
  change ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, ρ (g • q).out (a (Ty ρ a' σ hσ z _)) =
    ∑ Q : Gamma0 N ⧸ heckeUpper N m, ρ (SS σ hσ hm (g • Q)) ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm g Q))))

  rw [← Fintype.sum_equiv (Psi σ hσ hm) (fun x => ρ (SS σ hσ hm (g • Psi σ hσ hm x))
      ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm g (Psi σ hσ hm x))))))
      (fun Q => ρ (SS σ hσ hm (g • Q)) ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm g Q)))))
      (fun x => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_

  simp only [Ty, map_sum]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have hpush : a (ρ (sP σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q'))
      (a' (z (heckeConj N ℓ' (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) q')))))
      = ρ ((σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') :
          ↥(heckeUpper N ℓ)) : Gamma0 N)
        (a (a' (z (heckeConj N ℓ' (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) q'))))) :=
    LinearMap.congr_fun (ha _) _
  rw [hpush, smul_Psi, SS_Psi, heckeConj_TT_Psi, map_mul, Module.End.mul_apply, LinearMap.comp_apply]

/--
@isnad1 id=eq.0h8v.s12.54efebc8151f from=translated src=- shape=661f4ca3 vocab=04390d93
-/
theorem coeffHeckeFun_sub (ℓ₀ : ℕ) [NeZero ℓ₀] (b : V →ₗ[K] V) (z w : Gamma0 N → V) :
    coeffHeckeFun N ℓ₀ ρ b (z - w) = coeffHeckeFun N ℓ₀ ρ b z - coeffHeckeFun N ℓ₀ ρ b w := by
  letI := (heckeUpper N ℓ₀).fintypeQuotientOfFiniteIndex
  funext g
  simp only [coeffHeckeFun_apply, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

end Main

end R2CompTT
open scoped _root_.P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.HeckeEis.R2CompTT
end HeckeEis
open scoped _root_.P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.HeckeEis.R2CompTT _root_.P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.HeckeEis

open scoped MatrixGroups in
/--
@isnad1 id=mem.7h10v.s16.60ae3f1f29f4 from=translated src=- shape=2afceba2 vocab=217ae6e1
-/
theorem solution
    (N ℓ ℓ' m : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero m] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hℓℓ' : ¬ ℓ ∣ ℓ') (hm : m = ℓ * ℓ')
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a a' : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(HeckeEis.heckeUpper N ℓ'),
      a' ∘ₗ ρ (HeckeEis.heckeConj N ℓ' u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a')
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a (HeckeEis.coeffHeckeFun N ℓ' ρ a' z)
      - HeckeEis.coeffHeckeFun N m ρ (a ∘ₗ a') z ∈ HeckeEis.coeffCoboundaries ρ := by
  open _root_.HeckeEis _root_.P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.HeckeEis HeckeEis.R2CompTT in
  obtain ⟨σ, hσ⟩ := exists_section N ℓ ℓ' hℓ hℓN hℓℓ'

  have h1 : coeffHeckeFun N ℓ ρ a (Ty ρ a' σ hσ z - coeffHeckeFun N ℓ' ρ a' z) ∈ coeffCoboundaries ρ :=
    coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha (Ty_sub_mem ρ a' σ hσ ha' hz)
  have h2 : coeffHeckeFun N ℓ ρ a (Ty ρ a' σ hσ z) - coeffHeckeFun N m ρ (a ∘ₗ a') z
      ∈ coeffCoboundaries ρ := by
    rw [coeffHeckeFun_Ty ρ a a' σ hσ hm ha]
    exact TmS_sub_mem ρ a a' σ hσ hm ha ha' hz
  have h3 := (coeffCoboundaries ρ).sub_mem h2 h1
  rw [coeffHeckeFun_sub] at h3
  convert h3 using 1
  abel
