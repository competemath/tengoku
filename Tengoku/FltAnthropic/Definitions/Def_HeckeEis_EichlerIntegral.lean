import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace HeckeEis

open UpperHalfPlane MvPolynomial CongruenceSubgroup
open scoped MatrixGroups

section LinePow

variable (n : ℕ)

/--
@isnad1 id=ishomoge.0h1v.s8.2c7224c62cb9 from=translated src=- shape=ce68c88b vocab=c8e2afc1
-/
theorem isHomogeneous_line (τ : ℂ) : (C τ * X 0 + X 1 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
  ((isHomogeneous_X ℂ 0).C_mul τ).add (isHomogeneous_X ℂ 1)

/--
@isnad1 id=ishomoge.0h2v.s8.413272f7eaa8 from=translated src=- shape=bcbe962c vocab=0f0e32db
-/
theorem isHomogeneous_linePow (τ : ℂ) : ((C τ * X 0 + X 1 : MvPolynomial (Fin 2) ℂ) ^ n).IsHomogeneous n := by
  simpa using (isHomogeneous_line τ).pow n

def linePow (τ : ℂ) : ↥(BinaryForm ℂ n) :=
  ⟨(C τ * X 0 + X 1) ^ n, (mem_homogeneousSubmodule n _).mpr (isHomogeneous_linePow n τ)⟩

/--
@isnad1 id=eq.0h2v.s9.0fef391fe81c from=translated src=- shape=c67fefa7 vocab=4170c792
-/
@[simp] theorem coe_linePow (τ : ℂ) :
    ((linePow n τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = (C τ * X 0 + X 1) ^ n := rfl

def jFactor (g : SL(2, ℤ)) (τ : ℍ) : ℂ := ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) + ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)

/--
@isnad1 id=eq.0h2v.s9.388cd28c7c56 from=translated src=- shape=a835504c vocab=12b1a564
-/
theorem jFactor_eq_denom (g : SL(2, ℤ)) (τ : ℍ) :
    jFactor g τ = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) (τ : ℂ) := by
  rw [jFactor, Matrix.SpecialLinearGroup.mapGL, MonoidHom.comp_apply,
    show (algebraMap ℤ ℝ) = Int.castRingHom ℝ from rfl, ModularGroup.denom_apply]

/--
@isnad1 id=ne.0h2v.s5.19f982755507 from=translated src=- shape=48e25eb1 vocab=63f96f47
-/
theorem jFactor_ne_zero (g : SL(2, ℤ)) (τ : ℍ) : jFactor g τ ≠ 0 := by
  rw [jFactor_eq_denom]
  exact denom_ne_zero _ τ

/--
@isnad1 id=eq.0h2v.s8.3ba26d423661 from=translated src=- shape=3df1b259 vocab=f6c19ed1
-/
theorem coe_smul_mul_jFactor (g : SL(2, ℤ)) (τ : ℍ) :
    ((g • τ : ℍ) : ℂ) * jFactor g τ
      = ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (τ : ℂ) + ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) := by
  rw [coe_specialLinearGroup_apply]
  have hj := jFactor_ne_zero g τ
  simp only [jFactor, eq_intCast, Complex.ofReal_intCast] at hj ⊢
  rw [div_mul_cancel₀ _ hj]

/--
@isnad1 id=eq.0h2v.s10.15b6ecab399d from=translated src=- shape=626b0d3e vocab=31dba8bf
-/
theorem binarySubst_line (M : Matrix (Fin 2) (Fin 2) ℤ) (τ : ℂ) :
    binarySubst ℂ M (C τ * X 0 + X 1)
      = C ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) * X 0 + C ((M 1 0 : ℂ) * τ + (M 1 1 : ℂ)) * X 1 := by
  simp only [map_add, map_mul, binarySubst_C, binarySubst_X, Fin.sum_univ_two, Fin.isValue]
  ring

/--
@isnad1 id=eq.0h3v.s12.348ee527fb73 from=translated src=- shape=717a456a vocab=5d53eea3
-/
theorem binaryFormRepSL_linePow (g : SL(2, ℤ)) (τ : ℍ) :
    binaryFormRepSL ℂ n g (linePow n (τ : ℂ)) = (jFactor g τ) ^ n • linePow n ((g • τ : ℍ) : ℂ) := by
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe, Submodule.coe_smul, coe_linePow, coe_linePow, map_pow, binarySubst_line,
    smul_eq_C_mul, map_pow, ← mul_pow]
  congr 1
  rw [mul_add, ← mul_assoc, ← map_mul, mul_comm (jFactor g τ), coe_smul_mul_jFactor]
  rfl

end LinePow

section Equivariant

variable {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]

def IsEquivariantPrimitiveWith (ρ : Representation K Γ V) (F : ℍ → V) : Prop :=
  ∀ γ : Γ, ∃ c : V, ∀ τ : ℍ, F ((γ : SL(2, ℤ)) • τ) - ρ γ (F τ) = c

namespace IsEquivariantPrimitiveWith

variable {ρ : Representation K Γ V} {F : ℍ → V}

def cocycle (_hF : IsEquivariantPrimitiveWith ρ F) (γ : Γ) : V :=
  F ((γ : SL(2, ℤ)) • I) - ρ γ (F I)

/--
@isnad1 id=eq.1h7v.s11.bfdf009b4b8c from=translated src=- shape=7f50b9c9 vocab=c64e4665
-/
theorem sub_eq_cocycle (hF : IsEquivariantPrimitiveWith ρ F) (γ : Γ) (τ : ℍ) :
    F ((γ : SL(2, ℤ)) • τ) - ρ γ (F τ) = hF.cocycle γ := by
  obtain ⟨c, hc⟩ := hF γ
  rw [cocycle, hc τ, hc I]

/--
@isnad1 id=eq.1h7v.s11.ba86895805a7 from=translated src=- shape=07dcad15 vocab=91103974
-/
theorem apply_smul (hF : IsEquivariantPrimitiveWith ρ F) (γ : Γ) (τ : ℍ) :
    F ((γ : SL(2, ℤ)) • τ) = hF.cocycle γ + ρ γ (F τ) := by
  rw [← hF.sub_eq_cocycle γ τ, sub_add_cancel]

/--
@isnad1 id=mem.1h5v.s12.729b3449605f from=translated src=- shape=523ec71e vocab=95875983
-/
theorem cocycle_mem_coeffCocycles (hF : IsEquivariantPrimitiveWith ρ F) : hF.cocycle ∈ coeffCocycles ρ := by
  intro γ δ
  have h := hF.apply_smul (γ * δ) I
  rw [Subgroup.coe_mul, mul_smul, hF.apply_smul γ, hF.apply_smul δ, map_add, map_mul, Module.End.mul_apply] at h

  have := congrArg (fun v => v - ρ γ (ρ δ (F I))) h
  simp only [add_sub_cancel_right] at this
  rw [← this]
  abel

end IsEquivariantPrimitiveWith

end Equivariant

section EichlerIntegral

variable (n : ℕ)

def IsEichlerIntegral (f : ℍ → ℂ) (F : ℍ → ↥(BinaryForm ℂ n)) : Prop :=
  ∀ (d : Fin 2 →₀ ℕ) (τ : ℍ),
    HasDerivAt (fun z : ℂ => MvPolynomial.coeff d ((F (ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      (f τ * MvPolynomial.coeff d ((linePow n (τ : ℂ) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) (τ : ℂ)

variable (N : ℕ)

open Classical in

def eichlerShimuraMap (f : ℍ → ℂ) :
    coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) :=
  if h : ∃ F : ℍ → ↥(BinaryForm ℂ n), IsEichlerIntegral n f F ∧
      ∃ hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F,
        IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle
  then coeffH1parMk _ ⟨h.choose_spec.2.choose.cocycle,
    ⟨h.choose_spec.2.choose.cocycle_mem_coeffCocycles, h.choose_spec.2.choose_spec⟩⟩
  else 0

/--
@isnad1 id=ex.3h4v.s17.0a906539d6a1 from=translated src=- shape=a27c1de8 vocab=11e6bdc4
-/
theorem eichlerShimuraMap_def (f : ℍ → ℂ) {F : ℍ → ↥(BinaryForm ℂ n)}
    (hEI : IsEichlerIntegral n f F)
    (hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F)
    (hpar : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle) :
    ∃ (F₀ : ℍ → ↥(BinaryForm ℂ n)) (_ : IsEichlerIntegral n f F₀)
      (h₀ : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F₀)
      (hpar₀ : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) h₀.cocycle),
      eichlerShimuraMap n N f = coeffH1parMk _ ⟨h₀.cocycle, ⟨h₀.cocycle_mem_coeffCocycles, hpar₀⟩⟩ := by
  classical
  have h : ∃ F : ℍ → ↥(BinaryForm ℂ n), IsEichlerIntegral n f F ∧
      ∃ hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F,
        IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle := ⟨F, hEI, hF, hpar⟩
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.choose, h.choose_spec.2.choose_spec, dite_eq_left h⟩

/--
@isnad1 id=eq.1h3v.s15.2a71907a1717 from=translated src=- shape=d2898e50 vocab=721846a3
-/
theorem eichlerShimuraMap_of_not_exists (f : ℍ → ℂ)
    (h : ¬ ∃ F : ℍ → ↥(BinaryForm ℂ n), IsEichlerIntegral n f F ∧
      ∃ hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F,
        IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle) :
    eichlerShimuraMap n N f = 0 := by
  classical
  exact dite_eq_right h

end EichlerIntegral

end HeckeEis

end
