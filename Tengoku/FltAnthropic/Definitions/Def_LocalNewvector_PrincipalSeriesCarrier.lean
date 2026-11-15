import Tengoku.FltAnthropic.Definitions.Def_LocalNewvector_ConductorDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable (p : ℕ) [Fact p.Prime]

section BorelElements

def borelElem (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  ⟨!![(a₁ : ℚ_[p]), x; 0, (a₂ : ℚ_[p])],
   !![((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), -(((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p]));
      0, ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p])],
   by
    have h1 : (a₁ : ℚ_[p]) ≠ 0 := a₁.ne_zero
    have h2 : (a₂ : ℚ_[p]) ≠ 0 := a₂.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val, mul_assoc, h1, h2],
   by
    have h1 : (a₁ : ℚ_[p]) ≠ 0 := a₁.ne_zero
    have h2 : (a₂ : ℚ_[p]) ≠ 0 := a₂.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val, mul_assoc, h1, h2]⟩

/--
@isnad1 id=eq.0h4v.s8.571ac0dcd9ca from=translated src=- shape=1bbb3dfc vocab=b84c8cc6
-/
@[simp] lemma coe_borelElem (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    (borelElem p a₁ a₂ x : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![(a₁ : ℚ_[p]), x; 0, (a₂ : ℚ_[p])] :=
  rfl

/--
@isnad1 id=eq.0h4v.s9.338ccc87ec48 from=translated src=- shape=2e392326 vocab=8516c1ef
-/
@[simp] lemma coe_borelElem_inv (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    (((borelElem p a₁ a₂ x)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]),
            -(((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p]));
          0, ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p])] :=
  rfl

/--
@isnad1 id=eq.0h7v.s9.6a1d612992b0 from=translated src=- shape=21adac97 vocab=a98123e9
-/
theorem borelElem_mul (a₁ a₂ b₁ b₂ : ℚ_[p]ˣ) (x y : ℚ_[p]) :
    borelElem p a₁ a₂ x * borelElem p b₁ b₂ y
      = borelElem p (a₁ * b₁) (a₂ * b₂) ((a₁ : ℚ_[p]) * y + x * (b₂ : ℚ_[p])) := by
  apply Units.ext
  show (borelElem p a₁ a₂ x : Matrix (Fin 2) (Fin 2) ℚ_[p])
      * (borelElem p b₁ b₂ y : Matrix (Fin 2) (Fin 2) ℚ_[p]) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h4v.s8.7dc4566dfa0f from=translated src=- shape=fd1a8b8f vocab=42a96298
-/
theorem borelElem_inv (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    (borelElem p a₁ a₂ x)⁻¹
      = borelElem p a₁⁻¹ a₂⁻¹
          (-(((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p]))) :=
  Units.ext rfl

/--
@isnad1 id=eq.0h1v.s8.10a35a174c0e from=translated src=- shape=a2bb7c00 vocab=d67cc9f0
-/
@[simp] theorem borelElem_one : borelElem p 1 1 0 = 1 := by
  apply Units.ext
  show (borelElem p 1 1 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end BorelElements

section HalfModulus

def halfModulus (a₁ a₂ : ℚ_[p]ˣ) : ℂ :=
  (Real.sqrt (‖(a₁ : ℚ_[p])‖ / ‖(a₂ : ℚ_[p])‖) : ℝ)

/--
@isnad1 id=eq.2h3v.s7.1cee3ae679c2 from=translated src=- shape=e1463aef vocab=bb263980
-/
theorem halfModulus_eq_one_of_norm_eq_one {a₁ a₂ : ℚ_[p]ˣ}
    (h₁ : ‖(a₁ : ℚ_[p])‖ = 1) (h₂ : ‖(a₂ : ℚ_[p])‖ = 1) : halfModulus p a₁ a₂ = 1 := by
  simp only [halfModulus, h₁, h₂, div_one, Real.sqrt_one, Complex.ofReal_one]

/--
@isnad1 id=eq.0h1v.s7.a2c29c508225 from=translated src=- shape=d620df4f vocab=d8b39cb6
-/
@[simp] theorem halfModulus_one : halfModulus p 1 1 = 1 :=
  halfModulus_eq_one_of_norm_eq_one p (by simp) (by simp)

/--
@isnad1 id=eq.2h5v.s7.b02d8c779657 from=translated src=- shape=d4166a67 vocab=bb263980
-/
theorem halfModulus_congr {a₁ a₂ b₁ b₂ : ℚ_[p]ˣ}
    (h₁ : ‖(a₁ : ℚ_[p])‖ = ‖(b₁ : ℚ_[p])‖) (h₂ : ‖(a₂ : ℚ_[p])‖ = ‖(b₂ : ℚ_[p])‖) :
    halfModulus p a₁ a₂ = halfModulus p b₁ b₂ := by
  simp only [halfModulus, h₁, h₂]

/--
@isnad1 id=eq.0h5v.s8.8b00e1a88844 from=translated src=- shape=acbffbdc vocab=8a540ecb
-/
theorem halfModulus_mul (a₁ a₂ b₁ b₂ : ℚ_[p]ˣ) :
    halfModulus p (a₁ * b₁) (a₂ * b₂) = halfModulus p a₁ a₂ * halfModulus p b₁ b₂ := by
  have hquot : ‖((a₁ * b₁ : ℚ_[p]ˣ) : ℚ_[p])‖ / ‖((a₂ * b₂ : ℚ_[p]ˣ) : ℚ_[p])‖
      = (‖(a₁ : ℚ_[p])‖ / ‖(a₂ : ℚ_[p])‖) * (‖(b₁ : ℚ_[p])‖ / ‖(b₂ : ℚ_[p])‖) := by
    rw [Units.val_mul, Units.val_mul, norm_mul, norm_mul, div_mul_div_comm]
  simp only [halfModulus, hquot]
  rw [Real.sqrt_mul (by positivity), Complex.ofReal_mul]

end HalfModulus

section PrincipalSeries

def principalSeries (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) : Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ) where
  carrier := {f | IsLocallyConstant f ∧
    ∀ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]),
      f (borelElem p a₁ a₂ x * g)
        = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * f g}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun a₁ a₂ x g => by simp⟩
  add_mem' := by
    intro f g hf hg
    obtain ⟨hf_lc, hf_tr⟩ := hf
    obtain ⟨hg_lc, hg_tr⟩ := hg
    refine ⟨hf_lc.comp₂ hg_lc (· + ·), fun a₁ a₂ x g₀ => ?_⟩
    show f _ + g _ = _ * (f g₀ + g g₀)
    rw [hf_tr, hg_tr]
    ring
  smul_mem' := by
    intro c f hf
    obtain ⟨hf_lc, hf_tr⟩ := hf
    refine ⟨hf_lc.comp (c * ·), fun a₁ a₂ x g₀ => ?_⟩
    show c * f _ = _ * (c * f g₀)
    rw [hf_tr]
    ring

/--
@isnad1 id=iff.0h4v.s10.6eb00e35afbc from=translated src=- shape=5d5c10be vocab=62a89734
-/
theorem mem_principalSeries_iff {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {f : GL (Fin 2) ℚ_[p] → ℂ} :
    f ∈ principalSeries p μ₁ μ₂
      ↔ IsLocallyConstant f ∧
          ∀ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]),
            f (borelElem p a₁ a₂ x * g)
              = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * f g :=
  Iff.rfl

/--
@isnad1 id=islocall.1h4v.s10.f6ff4b81cb3c from=translated src=- shape=2163da5a vocab=27dc9a86
-/
theorem isLocallyConstant_of_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂) : IsLocallyConstant f :=
  ((mem_principalSeries_iff p).mp hf).1

/--
@isnad1 id=eq.1h8v.s10.b91942ada10d from=translated src=- shape=224e740c vocab=7388bb7a
-/
theorem apply_borelElem_mul_of_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂)
    (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]) :
    f (borelElem p a₁ a₂ x * g)
      = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * f g :=
  ((mem_principalSeries_iff p).mp hf).2 a₁ a₂ x g

/--
@isnad1 id=mem.1h5v.s10.30fec8e1af8f from=translated src=- shape=5c48e683 vocab=71475440
-/
theorem rightTranslate_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂) (g : GL (Fin 2) ℚ_[p]) :
    (fun y => f (y * g)) ∈ principalSeries p μ₁ μ₂ := by
  obtain ⟨hlc, htr⟩ := (mem_principalSeries_iff p).mp hf
  refine (mem_principalSeries_iff p).mpr
    ⟨hlc.comp_continuous (continuous_id.mul continuous_const), fun a₁ a₂ x g₀ => ?_⟩
  show f (borelElem p a₁ a₂ x * g₀ * g) = _ * f (g₀ * g)
  rw [mul_assoc, htr]

end PrincipalSeries

section RightInvariant

def rightInvariantFunctions (U : Subgroup (GL (Fin 2) ℚ_[p])) :
    Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ) where
  carrier := {f | ∀ u ∈ U, ∀ x, f (x * u) = f x}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro f g hf hg u hu x
    show f (x * u) + g (x * u) = f x + g x
    rw [hf u hu x, hg u hu x]
  smul_mem' := by
    intro c f hf u hu x
    show c * f (x * u) = c * f x
    rw [hf u hu x]

/--
@isnad1 id=iff.0h3v.s10.3c6c31bba968 from=translated src=- shape=6f73af49 vocab=e3439bb2
-/
theorem mem_rightInvariantFunctions_iff {U : Subgroup (GL (Fin 2) ℚ_[p])}
    {f : GL (Fin 2) ℚ_[p] → ℂ} :
    f ∈ rightInvariantFunctions p U ↔ ∀ u ∈ U, ∀ x, f (x * u) = f x :=
  Iff.rfl

end RightInvariant

section PrincipalSeriesCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

def PSCarrier : Type := ↥(principalSeries p μ₁ μ₂)

namespace PSCarrier

def mk (f : ↥(principalSeries p μ₁ μ₂)) : PSCarrier p μ₁ μ₂ := f

def toSub (f : PSCarrier p μ₁ μ₂) : ↥(principalSeries p μ₁ μ₂) := f

def toFn (f : PSCarrier p μ₁ μ₂) : GL (Fin 2) ℚ_[p] → ℂ :=
  (toSub p μ₁ μ₂ f : GL (Fin 2) ℚ_[p] → ℂ)

/--
@isnad1 id=mem.0h4v.s9.c3ebe537979b from=translated src=- shape=92b2c2c3 vocab=6f0d09af
-/
theorem toFn_mem (f : PSCarrier p μ₁ μ₂) : toFn p μ₁ μ₂ f ∈ principalSeries p μ₁ μ₂ :=
  (toSub p μ₁ μ₂ f).property

/--
@isnad1 id=eq.1h5v.s8.0f447a99bc4c from=translated src=- shape=ac306821 vocab=c160fa8e
-/
theorem ext {f g : PSCarrier p μ₁ μ₂}
    (h : ∀ y, toFn p μ₁ μ₂ f y = toFn p μ₁ μ₂ g y) : f = g :=
  Subtype.ext (funext h)

instance : AddCommGroup (PSCarrier p μ₁ μ₂) :=
  inferInstanceAs (AddCommGroup ↥(principalSeries p μ₁ μ₂))

instance : Module ℂ (PSCarrier p μ₁ μ₂) :=
  inferInstanceAs (Module ℂ ↥(principalSeries p μ₁ μ₂))

def toSubEquiv : PSCarrier p μ₁ μ₂ ≃ₗ[ℂ] ↥(principalSeries p μ₁ μ₂) where
  toFun := toSub p μ₁ μ₂
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := mk p μ₁ μ₂
  left_inv _ := rfl
  right_inv _ := rfl

instance : DistribMulAction (GL (Fin 2) ℚ_[p]) (PSCarrier p μ₁ μ₂) where
  smul g f := mk p μ₁ μ₂
    ⟨fun y => toFn p μ₁ μ₂ f (y * g),
     rightTranslate_mem_principalSeries p (toFn_mem p μ₁ μ₂ f) g⟩
  one_smul f := ext p μ₁ μ₂ fun y => congrArg (toFn p μ₁ μ₂ f) (mul_one y)
  mul_smul g h f := ext p μ₁ μ₂ fun y => congrArg (toFn p μ₁ μ₂ f) (mul_assoc y g h).symm
  smul_zero _ := ext p μ₁ μ₂ fun _ => rfl
  smul_add _ _ _ := ext p μ₁ μ₂ fun _ => rfl

/--
@isnad1 id=eq.0h6v.s9.ab9ced797b6b from=translated src=- shape=b0136993 vocab=10d2763f
-/
@[simp] theorem toFn_smul (g : GL (Fin 2) ℚ_[p]) (f : PSCarrier p μ₁ μ₂)
    (y : GL (Fin 2) ℚ_[p]) :
    toFn p μ₁ μ₂ (g • f) y = toFn p μ₁ μ₂ f (y * g) := rfl

/--
@isnad1 id=eq.0h6v.s8.993eb9028765 from=translated src=- shape=2f0082cd vocab=4b4f0572
-/
@[simp] theorem toFn_csmul (c : ℂ) (f : PSCarrier p μ₁ μ₂) (y : GL (Fin 2) ℚ_[p]) :
    toFn p μ₁ μ₂ (c • f) y = c * toFn p μ₁ μ₂ f y := rfl

instance : SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ (PSCarrier p μ₁ μ₂) where
  smul_comm _ _ _ := ext p μ₁ μ₂ fun _ => rfl

def fixedEquiv (U : Subgroup (GL (Fin 2) ℚ_[p])) :
    ↥(LocalNewvector.fixedSubmodule U (PSCarrier p μ₁ μ₂)) ≃ₗ[ℂ]
      ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p U) where
  toFun v := ⟨toFn p μ₁ μ₂ v.val, Submodule.mem_inf.mpr
    ⟨toFn_mem p μ₁ μ₂ v.val, by
      rw [mem_rightInvariantFunctions_iff]
      intro u hu y
      exact congrArg (fun z => toFn p μ₁ μ₂ z y)
        ((LocalNewvector.mem_fixedSubmodule_iff.mp v.property) u hu)⟩⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  invFun w := ⟨mk p μ₁ μ₂ ⟨w.val, (Submodule.mem_inf.mp w.property).1⟩, by
    rw [LocalNewvector.mem_fixedSubmodule_iff]
    intro u hu
    refine ext p μ₁ μ₂ fun y => ?_
    exact (mem_rightInvariantFunctions_iff p).mp
      (Submodule.mem_inf.mp w.property).2 u hu y⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/--
@isnad1 id=eq.0h4v.s11.e8549fc5d40e from=translated src=- shape=7ba0fded vocab=fc5c17fa
-/
theorem finrank_fixed_eq (U : Subgroup (GL (Fin 2) ℚ_[p])) :
    Module.finrank ℂ ↥(LocalNewvector.fixedSubmodule U (PSCarrier p μ₁ μ₂))
      = Module.finrank ℂ ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p U) :=
  (fixedEquiv p μ₁ μ₂ U).finrank_eq

end PSCarrier

end PrincipalSeriesCarrier

end LocalNewvector

end
