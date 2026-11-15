import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PeriodMap
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Tengoku.Seed.Tactic.Group
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Matrix UpperHalfPlane CongruenceSubgroup Function

open scoped MatrixGroups

noncomputable section

namespace ModularCurve.Period

variable {Γ Δ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}

def conjRel (g : GL (Fin 2) ℝ) (γ' γ : SL(2, ℤ)) : Prop :=
  g * Matrix.SpecialLinearGroup.mapGL ℝ γ' = Matrix.SpecialLinearGroup.mapGL ℝ γ * g

namespace conjRel

variable {g : GL (Fin 2) ℝ}

/--
@isnad1 id=conjrel.0h1v.s7.9004534f1c34 from=translated src=- shape=eb21f339 vocab=f739c489
-/
theorem one : conjRel g 1 1 := by
  simp [conjRel]

/--
@isnad1 id=conjrel.2h5v.s8.e7ae84485317 from=translated src=- shape=67194de2 vocab=644db959
-/
theorem mul {γ₁' γ₂' γ₁ γ₂ : SL(2, ℤ)} (h₁ : conjRel g γ₁' γ₁) (h₂ : conjRel g γ₂' γ₂) :
    conjRel g (γ₁' * γ₂') (γ₁ * γ₂) := by
  unfold conjRel at *
  rw [map_mul, map_mul, ← mul_assoc, h₁, mul_assoc, h₂, mul_assoc]

/--
@isnad1 id=conjrel.1h3v.s7.94ebe8a0c6ba from=translated src=- shape=13c60f53 vocab=7ca18a64
-/
theorem inv {γ' γ : SL(2, ℤ)} (h : conjRel g γ' γ) : conjRel g γ'⁻¹ γ⁻¹ := by
  unfold conjRel at *
  rw [map_inv, map_inv]
  calc g * (Matrix.SpecialLinearGroup.mapGL ℝ γ')⁻¹
      = (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹
          * ((Matrix.SpecialLinearGroup.mapGL ℝ γ * g)
            * (Matrix.SpecialLinearGroup.mapGL ℝ γ')⁻¹) := by group
    _ = (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹
          * ((g * Matrix.SpecialLinearGroup.mapGL ℝ γ')
            * (Matrix.SpecialLinearGroup.mapGL ℝ γ')⁻¹) := by rw [h]
    _ = (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ * g := by group

/--
@isnad1 id=eq.2h4v.s6.28f4b16fe855 from=translated src=- shape=f92be848 vocab=f739c489
-/
theorem unique {γ' γ₁ γ₂ : SL(2, ℤ)} (h₁ : conjRel g γ' γ₁) (h₂ : conjRel g γ' γ₂) :
    γ₁ = γ₂ := by
  have hGL : Matrix.SpecialLinearGroup.mapGL ℝ γ₁ = Matrix.SpecialLinearGroup.mapGL ℝ γ₂ :=
    mul_right_cancel (h₁.symm.trans h₂)
  have hmat : ∀ a b : Fin 2, (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) a b
      = (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) a b := by
    intro a b
    have := congrArg (fun M : GL (Fin 2) ℝ => (M : Matrix (Fin 2) (Fin 2) ℝ) a b) hGL
    simpa [Matrix.SpecialLinearGroup.mapGL, Int.cast_injective.eq_iff] using this
  ext a b
  exact hmat a b

/--
@isnad1 id=eq.1h4v.s9.2e13b844ec72 from=translated src=- shape=817711c6 vocab=c7ffd3cd
-/
theorem smul_comm {γ' γ : SL(2, ℤ)} (h : conjRel g γ' γ) (z : ℍ) :
    g • (γ' • z) = γ • (g • z) := by
  rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def, ← mul_smul, h, mul_smul]

end conjRel

def conjSubgroup (g : GL (Fin 2) ℝ) (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {γ' | ∃ γ ∈ Γ, conjRel g γ' γ}
  one_mem' := ⟨1, Γ.one_mem, conjRel.one⟩
  mul_mem' := by
    rintro γ₁' γ₂' ⟨γ₁, hγ₁, h₁⟩ ⟨γ₂, hγ₂, h₂⟩
    exact ⟨γ₁ * γ₂, Γ.mul_mem hγ₁ hγ₂, h₁.mul h₂⟩
  inv_mem' := by
    rintro γ' ⟨γ, hγ, h⟩
    exact ⟨γ⁻¹, Γ.inv_mem hγ, h.inv⟩

def conjPrimitive (g : GL (Fin 2) ℝ) (F : ℍ → ℂ) : ℍ → ℂ :=
  fun z => F (g • z)

/--
@isnad1 id=isequiva.1h3v.s6.2d0d515a573f from=translated src=- shape=45428304 vocab=8e645c78
-/
theorem IsEquivariantPrimitive.conj (g : GL (Fin 2) ℝ)
    (hF : IsEquivariantPrimitive Γ F) :
    IsEquivariantPrimitive (conjSubgroup g Γ) (conjPrimitive g F) := by
  rintro ⟨γ', γ, hγ, hrel⟩
  refine ⟨hF.period ⟨γ, hγ⟩, fun z => ?_⟩
  show F (g • (γ' • z)) - F (g • z) = _
  rw [hrel.smul_comm z]
  exact hF.sub_eq_period ⟨γ, hγ⟩ (g • z)

def traceRep (q : ↥Γ ⧸ Δ.subgroupOf Γ) : ↥Γ :=
  (Quotient.out q)⁻¹

def transferElt (γ : ↥Γ) (q : ↥Γ ⧸ Δ.subgroupOf Γ) : ↥Δ :=
  ⟨((HeckeEis.transferAux (Δ.subgroupOf Γ) γ (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)),
    Subgroup.mem_subgroupOf.mp (HeckeEis.transferAux (Δ.subgroupOf Γ) γ (γ⁻¹ • q)).2⟩

/--
@isnad1 id=eq.0h4v.s13.11c6aa9689d2 from=translated src=- shape=4b1098e8 vocab=bdf85bf1
-/
theorem transferElt_spec (γ : ↥Γ) (q : ↥Γ ⧸ Δ.subgroupOf Γ) :
    ((traceRep q : ↥Γ) : SL(2, ℤ)) * (γ : SL(2, ℤ))
      = (transferElt (Δ := Δ) γ q : SL(2, ℤ))
        * ((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) := by
  have h : traceRep q * γ
      = (HeckeEis.transferAux (Δ.subgroupOf Γ) γ (γ⁻¹ • q) : ↥Γ) * traceRep (γ⁻¹ • q) := by
    rw [HeckeEis.coe_transferAux, smul_inv_smul]
    unfold traceRep
    group
  exact congrArg (fun x : ↥Γ => (x : SL(2, ℤ))) h

variable [Fintype (↥Γ ⧸ Δ.subgroupOf Γ)]

def traceSum (Γ Δ : Subgroup SL(2, ℤ)) [Fintype (↥Γ ⧸ Δ.subgroupOf Γ)] (F : ℍ → ℂ) :
    ℍ → ℂ :=
  fun z => ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep q : ↥Γ) : SL(2, ℤ)) • z)

/--
@isnad1 id=eq.1h5v.s11.295f0ad3b3fc from=translated src=- shape=bc894507 vocab=6cfe305a
-/
theorem sum_traceRep_smul_sub (hF : IsEquivariantPrimitive Δ F) (γ : ↥Γ) (z : ℍ) :
    traceSum Γ Δ F ((γ : SL(2, ℤ)) • z) - traceSum Γ Δ F z
      = ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, hF.period (transferElt γ q) := by
  have hterm : ∀ q : ↥Γ ⧸ Δ.subgroupOf Γ,
      F (((traceRep q : ↥Γ) : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • z))
        = F (((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) • z)
          + hF.period (transferElt γ q) := by
    intro q
    have h1 : ((traceRep q : ↥Γ) : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • z)
        = ((transferElt (Δ := Δ) γ q : SL(2, ℤ)))
            • (((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) • z) := by
      rw [← mul_smul, transferElt_spec γ q, mul_smul]
    rw [h1]
    have h2 := hF.sub_eq_period (transferElt γ q)
      (((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) • z)
    linear_combination h2
  unfold traceSum
  calc
    (∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep q : ↥Γ) : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • z)))
        - ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep q : ↥Γ) : SL(2, ℤ)) • z)
      = (∑ q : ↥Γ ⧸ Δ.subgroupOf Γ,
          (F (((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) • z) + hF.period (transferElt γ q)))
          - ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep q : ↥Γ) : SL(2, ℤ)) • z) := by
        rw [Finset.sum_congr rfl fun q _ => hterm q]
    _ = (∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) • z))
          + (∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, hF.period (transferElt γ q))
          - ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, F (((traceRep q : ↥Γ) : SL(2, ℤ)) • z) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, hF.period (transferElt γ q) := by
        rw [(MulAction.bijective (γ⁻¹ : ↥Γ)).sum_comp
          (fun q : ↥Γ ⧸ Δ.subgroupOf Γ => F (((traceRep q : ↥Γ) : SL(2, ℤ)) • z))]
        ring

/--
@isnad1 id=isequiva.1h3v.s9.ec6c51c1755c from=translated src=- shape=17f6d71e vocab=8b17745b
-/
theorem IsEquivariantPrimitive.traceSum (hF : IsEquivariantPrimitive Δ F) :
    IsEquivariantPrimitive Γ (ModularCurve.Period.traceSum Γ Δ F) := fun γ =>
  ⟨∑ q : ↥Γ ⧸ Δ.subgroupOf Γ, hF.period (transferElt γ q),
    fun z => sum_traceRep_smul_sub hF γ z⟩

end ModularCurve.Period

end
