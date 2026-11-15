import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_C8Character
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_QuatH

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace LanglandsTunnell

/--
@isnad1 id=mem.1h1v.s4.01a4c9f03c83 from=translated src=- shape=92d89710 vocab=eec3d298
-/
theorem C8_sub_P16 : ∀ M ∈ P2.C8, M ∈ Lift48.P16 := by decide

section Containment

variable {L : Type} [Field L] [NumberField L]

/--
@isnad1 id=le.0h2v.s9.27049f17801e from=translated src=- shape=6a67c2b3 vocab=9282bf80
-/
theorem c8H_le_sylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    P2.c8H e ≤ sylowH e :=
  fun _ ⟨M, hM, h⟩ => ⟨M, C8_sub_P16 M hM, h⟩

/--
@isnad1 id=le.0h2v.s8.c8bc8823574c from=translated src=- shape=c54a6921 vocab=6ea07fe2
-/
theorem fixFld_sylowH_le_fixFld_c8H (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    fixFld (sylowH e) ≤ fixFld (P2.c8H e) :=
  fixFld_le_fixFld_of_le (c8H_le_sylowH e)

end Containment

section TowerInstances

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

noncomputable instance algebra_fixFldSylowH_fixFldC8H :
    Algebra ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) :=
  (IntermediateField.inclusion (fixFld_sylowH_le_fixFld_c8H e)).toRingHom.toAlgebra

/--
@isnad1 id=isscalar.0h2v.s9.902b969c8f1c from=translated src=- shape=5af864b4 vocab=fdea864a
-/
instance isScalarTower_fixFldSylowH_fixFldC8H_L :
    IsScalarTower ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_sylowH_le_fixFld_c8H e) x).symm)

end TowerInstances

section SynthProbe

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
end SynthProbe

private def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

private theorem red_eq_redc (z : ℤ√(-2)) : FLT.ExplicitLift.red z = redc z := by
  rw [show z = ⟨z.re, z.im⟩ from rfl]
  simp [FLT.ExplicitLift.red, redc, Zsqrtd.lift, sub_eq_add_neg]

private theorem map_red_eq_map_redc (M : Lift48.Mat) : M.map FLT.ExplicitLift.red = M.map redc := by
  ext i j
  simp [Matrix.map_apply, red_eq_redc]

private theorem nodup_P16 : Lift48.P16.Nodup := by decide

private theorem map_redc_injOn_P16 :
    ∀ M ∈ Lift48.P16, ∀ N ∈ Lift48.P16, M.map redc = N.map redc → M = N := by
  decide

private theorem det_map_redc_ne_zero : ∀ M ∈ Lift48.P16, (M.map redc).det ≠ 0 := by decide

private theorem det_map_red_ne_zero (M : Lift48.Mat) (hM : M ∈ Lift48.P16) :
    (M.map FLT.ExplicitLift.red).det ≠ 0 := by
  rw [map_red_eq_map_redc]
  exact det_map_redc_ne_zero M hM

private theorem natCard_P16 : Nat.card {M : Lift48.Mat // M ∈ Lift48.P16} = 16 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun M => (List.mem_toFinset (l := Lift48.P16) (a := M)).symm)),
    Nat.card_eq_finsetCard, List.toFinset_card_of_nodup nodup_P16, Lift48.length_P16]

private noncomputable def redUnit (M : {M : Lift48.Mat // M ∈ Lift48.P16}) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (M.1.map FLT.ExplicitLift.red) (det_map_red_ne_zero M.1 M.2)

private theorem coe_redUnit (M : {M : Lift48.Mat // M ∈ Lift48.P16}) :
    ((redUnit M : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
      = M.1.map FLT.ExplicitLift.red :=
  rfl

section Card

variable {L : Type} [Field L] [NumberField L]

private noncomputable def toSylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : {M : Lift48.Mat // M ∈ Lift48.P16}) : ↥(sylowH e) :=
  ⟨e.symm (redUnit M), M.1, M.2, by rw [MulEquiv.apply_symm_apply, coe_redUnit]⟩

private theorem toSylowH_bijective (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Function.Bijective (toSylowH e) := by
  constructor
  · rintro ⟨M, hM⟩ ⟨N, hN⟩ h
    have h1 : redUnit ⟨M, hM⟩ = redUnit ⟨N, hN⟩ := e.symm.injective (congrArg Subtype.val h)
    have h2 : M.map FLT.ExplicitLift.red = N.map FLT.ExplicitLift.red := by
      rw [← coe_redUnit ⟨M, hM⟩, ← coe_redUnit ⟨N, hN⟩, h1]
    rw [map_red_eq_map_redc M, map_red_eq_map_redc N] at h2
    exact Subtype.ext (map_redc_injOn_P16 M hM N hN h2)
  · rintro ⟨γ, M, hM, hMγ⟩
    refine ⟨⟨M, hM⟩, Subtype.ext ?_⟩
    show e.symm (redUnit ⟨M, hM⟩) = γ
    rw [MulEquiv.symm_apply_eq]
    exact Units.ext (by rw [coe_redUnit]; exact hMγ)

/--
@isnad1 id=eq.0h2v.s9.6f11d75159c9 from=translated src=- shape=7dc28876 vocab=91bcece7
-/
theorem card_sylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Nat.card ↥(sylowH e) = 16 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (toSylowH_bijective e)), natCard_P16]

end Card

section Degree

variable {L : Type} [Field L] [NumberField L]

private theorem finrank_fixFld_sylowH_L (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ↥(fixFld (sylowH e)) L = 16 := by
  have h : Module.finrank ↥(fixFld (sylowH e)) L = Nat.card ↥(sylowH e) :=
    IntermediateField.finrank_fixedField_eq_card (sylowH e)
  rw [h, card_sylowH]

private theorem finrank_fixFld_c8H_L (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ↥(fixFld (P2.c8H e)) L = 8 := by
  have h : Module.finrank ↥(fixFld (P2.c8H e)) L = Nat.card ↥(P2.c8H e) :=
    IntermediateField.finrank_fixedField_eq_card (P2.c8H e)
  rw [h, P2.card_c8H]

/--
@isnad1 id=eq.0h2v.s10.6a93c71afa3d from=translated src=- shape=581ab6fb vocab=0dcc7756
-/
theorem finrank_fixFldSylowH_fixFldC8H (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) = 2 := by
  haveI : Module.Free ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) :=
    Module.Free.of_divisionRing ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e))
  haveI : Module.Free ↥(fixFld (P2.c8H e)) L := Module.Free.of_divisionRing ↥(fixFld (P2.c8H e)) L
  have htower : Module.finrank ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) *
      Module.finrank ↥(fixFld (P2.c8H e)) L = Module.finrank ↥(fixFld (sylowH e)) L :=
    Module.finrank_mul_finrank ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) L
  rw [finrank_fixFld_c8H_L e, finrank_fixFld_sylowH_L e] at htower
  omega

end Degree

end LanglandsTunnell
