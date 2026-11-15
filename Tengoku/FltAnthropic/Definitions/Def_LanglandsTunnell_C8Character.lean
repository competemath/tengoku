import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_Lift48

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2

open NumberField IsDedekindDomain FLT.ExplicitLift LanglandsTunnell.Lift48

def C8 : List Mat := (List.range 8).map (pw Tlift)

/--
@isnad1 id=mem.0h0v.s5.aeb7348a7303 from=translated src=- shape=d52416c9 vocab=56e6f186
-/
theorem one_mem_C8 : (1 : Mat) ∈ C8 := by decide

/--
@isnad1 id=mem.0h0v.s4.221b3a0fcae1 from=translated src=- shape=81ae8f40 vocab=ae7d1c4a
-/
theorem Tlift_mem_C8 : Tlift ∈ C8 := by decide

/--
@isnad1 id=mem.2h2v.s7.5b6fb9200ad5 from=translated src=- shape=bf7dc4ab vocab=4220ab89
-/
theorem C8_mul_closed : ∀ M ∈ C8, ∀ N ∈ C8, M * N ∈ C8 := by decide

/--
@isnad1 id=mem.1h1v.s4.1ffad29db598 from=translated src=- shape=b9e58cf8 vocab=6d2ca180
-/
theorem C8_pw_seven_mem : ∀ M ∈ C8, pw M 7 ∈ C8 := by decide

/--
@isnad1 id=eq.1h1v.s7.867c8017dfe4 from=translated src=- shape=3d8bd509 vocab=0f6fd0d7
-/
theorem C8_mul_pw_seven : ∀ M ∈ C8, M * pw M 7 = 1 := by decide

/--
@isnad1 id=eq.0h0v.s6.e0309965d1cf from=translated src=- shape=5b7a9bf7 vocab=46cccb4f
-/
theorem Tlift_det_eq_neg_one : Tlift.det = -1 := by
  rw [Matrix.det_fin_two]; decide

/--
@isnad1 id=eq.0h0v.s8.4b7a61ec3f4e from=translated src=- shape=9f32ea33 vocab=101e1549
-/
theorem Tlift_pow_four_eq_neg_one : Tlift ^ 4 = -1 := by
  rw [← pw_eq_pow]; decide

/--
@isnad1 id=eq.0h0v.s8.d784941135c2 from=translated src=- shape=fd4f0788 vocab=101e1549
-/
theorem Tlift_pow_eight_eq_one : Tlift ^ 8 = 1 := by
  rw [← pw_eq_pow]; decide

section C8Sub

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

def c8H : Subgroup (L ≃ₐ[ℚ] L) where
  carrier := {γ | ∃ M ∈ C8,
    M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))}
  one_mem' := ⟨1, one_mem_C8, by rw [map_one, Units.val_one, Matrix.map_one _ (map_zero red) (map_one red)]⟩
  mul_mem' := by
    rintro a b ⟨M, hM, hMa⟩ ⟨N, hN, hNb⟩
    exact ⟨M * N, C8_mul_closed M hM N hN, by rw [Matrix.map_mul, hMa, hNb, map_mul, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨M, hM, hMa⟩
    refine ⟨pw M 7, C8_pw_seven_mem M hM, ?_⟩
    rw [map_inv]
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    rw [← hMa, ← Matrix.map_mul, C8_mul_pw_seven M hM, Matrix.map_one _ (map_zero red) (map_one red)]

/--
@isnad1 id=iff.0h3v.s11.9b5d0bf90a57 from=translated src=- shape=986b49af vocab=99cbf1db
-/
theorem mem_c8H_iff (γ : L ≃ₐ[ℚ] L) :
    γ ∈ c8H e ↔ ∃ M ∈ C8,
      M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  Iff.rfl

def tbarGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Tlift.map red) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Tlift_det_eq_neg_one, map_neg, map_one]; decide)

/--
@isnad1 id=eq.0h0v.s9.9b1e1d776b46 from=translated src=- shape=1d713665 vocab=37e70580
-/
theorem val_tbarGL : ((tbarGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    = red.mapMatrix Tlift := rfl

/--
@isnad1 id=eq.0h1v.s10.636181018c0f from=translated src=- shape=9c26f937 vocab=02f78b6b
-/
theorem val_tbarGL_pow (k : ℕ) :
    ((tbarGL ^ k : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
      = red.mapMatrix (Tlift ^ k) := by
  rw [Units.val_pow_eq_pow_val, val_tbarGL, map_pow]

/--
@isnad1 id=ne.0h0v.s9.2a4d1f7b4cbb from=translated src=- shape=89b92624 vocab=eb10e15b
-/
theorem tbarGL_pow_four_ne_one : tbarGL ^ 4 ≠ 1 := by
  intro h
  have h' := congrArg Units.val h
  rw [val_tbarGL_pow, Tlift_pow_four_eq_neg_one, map_neg, map_one, Units.val_one] at h'
  exact absurd h' (by decide)

/--
@isnad1 id=eq.0h0v.s9.b09c6a844c3d from=translated src=- shape=89b92624 vocab=eb10e15b
-/
theorem tbarGL_pow_eight : tbarGL ^ 8 = 1 :=
  Units.ext (by rw [val_tbarGL_pow, Tlift_pow_eight_eq_one, map_one, Units.val_one])

/--
@isnad1 id=eq.0h0v.s7.a93f47aca1fd from=translated src=- shape=fa3a62ad vocab=049038b1
-/
theorem orderOf_tbarGL : orderOf tbarGL = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := tbarGL) tbarGL_pow_four_ne_one tbarGL_pow_eight
  norm_num at h
  exact h

def gammaT : L ≃ₐ[ℚ] L := e.symm tbarGL

/--
@isnad1 id=eq.0h2v.s10.98cf6fac0052 from=translated src=- shape=947712a6 vocab=d84e4dd4
-/
theorem e_gammaT : e (gammaT e) = tbarGL := MulEquiv.apply_symm_apply e _

/--
@isnad1 id=mem.0h2v.s9.1d2aee77443c from=translated src=- shape=83797f98 vocab=174bcc95
-/
theorem gammaT_mem : gammaT e ∈ c8H e :=
  ⟨Tlift, Tlift_mem_C8, by rw [e_gammaT]; rfl⟩

/--
@isnad1 id=eq.0h2v.s8.1beb0e019d08 from=translated src=- shape=fad1407c vocab=1b63dd5d
-/
theorem orderOf_gammaT : orderOf (gammaT e) = 8 := by
  have h := orderOf_injective e.toMonoidHom e.injective (gammaT e)
  rw [MulEquiv.coe_toMonoidHom, e_gammaT, orderOf_tbarGL] at h
  exact h.symm

/--
@isnad1 id=ex.1h3v.s9.cb0df5f8b4be from=translated src=- shape=e8caa52b vocab=6197766d
-/
theorem exists_pow_gammaT_eq {γ : L ≃ₐ[ℚ] L} (hγ : γ ∈ c8H e) : ∃ k : ℕ, gammaT e ^ k = γ := by
  obtain ⟨M, hM, hMγ⟩ := hγ
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hM
  refine ⟨k, e.injective (Units.ext ?_)⟩
  rw [map_pow, e_gammaT, val_tbarGL_pow, ← pw_eq_pow, RingHom.mapMatrix_apply, hMγ]

def gammaTMem : ↥(c8H e) := ⟨gammaT e, gammaT_mem e⟩

/--
@isnad1 id=eq.0h2v.s10.cc3b7d6ec67e from=translated src=- shape=539406f1 vocab=0c40cf04
-/
theorem orderOf_gammaTMem : orderOf (gammaTMem e) = 8 := by
  rw [← orderOf_injective (c8H e).subtype Subtype.coe_injective (gammaTMem e)]
  exact orderOf_gammaT e

/--
@isnad1 id=mem.0h3v.s11.ff443272efc2 from=translated src=- shape=29454c7b vocab=64a1e765
-/
theorem mem_zpowers_gammaTMem (x : ↥(c8H e)) : x ∈ Subgroup.zpowers (gammaTMem e) := by
  obtain ⟨k, hk⟩ := exists_pow_gammaT_eq e x.2
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨(k : ℤ), Subtype.ext (by rw [zpow_natCast, Subgroup.coe_pow]; exact hk)⟩

/--
@isnad1 id=eq.0h2v.s8.5f233e01f3f7 from=translated src=- shape=0b5f00b8 vocab=de8df29f
-/
theorem c8H_eq_zpowers : c8H e = Subgroup.zpowers (gammaT e) := by
  refine le_antisymm (fun γ hγ => ?_) ((Subgroup.zpowers_le (G := L ≃ₐ[ℚ] L)).2 (gammaT_mem e))
  obtain ⟨k, rfl⟩ := exists_pow_gammaT_eq e hγ
  exact Subgroup.npow_mem_zpowers _ _

/--
@isnad1 id=eq.0h2v.s9.fd0cc211c075 from=translated src=- shape=68f38523 vocab=92a618f6
-/
theorem card_c8H : Nat.card ↥(c8H e) = 8 := by
  rw [c8H_eq_zpowers, Nat.card_zpowers, orderOf_gammaT]

end C8Sub

section ChiGal

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
  {ζ : ℂ} (hζ : ζ ^ 4 = -1)

include hζ in
/--
@isnad1 id=ne.1h1v.s5.d77c5db57786 from=translated src=- shape=9dce7ee5 vocab=a4738c31
-/
theorem zeta_ne_zero : ζ ≠ 0 := by
  rintro rfl
  norm_num at hζ

include hζ in
/--
@isnad1 id=eq.1h1v.s5.7fdbd45da220 from=translated src=- shape=c05ab1e2 vocab=a4738c31
-/
theorem zeta_pow_eight : ζ ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hζ]
  norm_num

def zetaUnit : ℂˣ := Units.mk0 ζ (zeta_ne_zero hζ)

/--
@isnad1 id=eq.1h1v.s5.186132fa06c0 from=translated src=- shape=15c25d24 vocab=f312f94b
-/
theorem val_zetaUnit : ((zetaUnit hζ : ℂˣ) : ℂ) = ζ := rfl

/--
@isnad1 id=eq.1h1v.s6.e55c456416f1 from=translated src=- shape=511127a5 vocab=514b6129
-/
theorem zetaUnit_pow_eight : zetaUnit hζ ^ 8 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, val_zetaUnit, zeta_pow_eight hζ, Units.val_one])

/--
@isnad1 id=dvd.1h3v.s10.5911c69cf446 from=translated src=- shape=c2d05889 vocab=4351ae57
-/
theorem orderOf_zetaUnit_dvd : orderOf (zetaUnit hζ) ∣ orderOf (gammaTMem e) := by
  rw [orderOf_gammaTMem]
  exact orderOf_dvd_of_pow_eq_one (zetaUnit_pow_eight hζ)

def chiGal : ↥(c8H e) →* ℂˣ :=
  monoidHomOfForallMemZpowers (mem_zpowers_gammaTMem e) (orderOf_zetaUnit_dvd e hζ)

/--
@isnad1 id=eq.1h3v.s11.110b740f1041 from=translated src=- shape=653c8c39 vocab=481b02c0
-/
theorem chiGal_gammaTMem : chiGal e hζ (gammaTMem e) = zetaUnit hζ :=
  monoidHomOfForallMemZpowers_apply_gen (mem_zpowers_gammaTMem e) (orderOf_zetaUnit_dvd e hζ)

/--
@isnad1 id=eq.1h4v.s12.a6425daadfdf from=translated src=- shape=6baffcfd vocab=481b02c0
-/
theorem chiGal_gammaT_pow (k : ℕ) : chiGal e hζ (gammaTMem e ^ k) = zetaUnit hζ ^ k := by
  rw [map_pow, chiGal_gammaTMem]

/--
@isnad1 id=ne.1h1v.s6.55167d8c3a68 from=translated src=- shape=90558064 vocab=514b6129
-/
theorem zetaUnit_pow_four_ne_one : zetaUnit hζ ^ 4 ≠ 1 := by
  intro h
  have h' := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, val_zetaUnit, hζ, Units.val_one] at h'
  norm_num at h'

/--
@isnad1 id=eq.1h1v.s5.dc122707c269 from=translated src=- shape=556961df vocab=12ffd690
-/
theorem orderOf_zetaUnit : orderOf (zetaUnit hζ) = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := zetaUnit hζ) (zetaUnit_pow_four_ne_one hζ)
    (zetaUnit_pow_eight hζ)
  norm_num at h
  exact h

/--
@isnad1 id=injectiv.1h3v.s12.bc833ed57abf from=translated src=- shape=e2008f60 vocab=172bd3e5
-/
theorem chiGal_injective : Function.Injective (chiGal e hζ) := by
  refine (injective_iff_map_eq_one (chiGal e hζ)).2 fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_gammaTMem e x)
  rw [map_zpow, chiGal_gammaTMem] at hx
  have hdvd : (8 : ℤ) ∣ k := by
    rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_zetaUnit] at hx
    exact_mod_cast hx
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_gammaTMem]
  exact_mod_cast hdvd

end ChiGal

section Artin

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)

open Classical in

/--
@isnad1 id=mem.0h3v.s12.32e94efd3172 from=translated src=- shape=5069617a vocab=ba3634b3
-/
theorem seedFrob_mem (H : Subgroup (L ≃ₐ[ℚ] L))
    (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))) : seedFrob H w ∈ H := by
  unfold seedFrob relDeg
  exact (Nat.find_spec (exists_pos_pow_mem H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w)))).2

def artinValue (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) : ℂˣ :=
  chiGal e hζ ⟨seedFrob (c8H e) v, seedFrob_mem (c8H e) v⟩

/--
@isnad1 id=eq.1h4v.s13.c0be0f67a829 from=translated src=- shape=975d9cb1 vocab=54cf2a27
-/
theorem artinValue_def (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) :
    artinValue e hζ v = chiGal e hζ ⟨seedFrob (c8H e) v, seedFrob_mem (c8H e) v⟩ := rfl

end Artin

end LanglandsTunnell.P2

end
