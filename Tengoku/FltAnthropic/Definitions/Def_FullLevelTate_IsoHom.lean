import Tengoku.FltAnthropic.Definitions.Def_FullLevelTate_Datum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

local notation α "^+" M:51 => FixedPoints.addSubgroup M α

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FullLevelTate

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} {O' : Type} [CommRing O'] [IsLocalRing O']

namespace Datum

variable (D : Datum q M' O') (K : Type) [Field K] [Algebra O' K]
  {H : Subgroup (CuspidalType.GL2 q)} {W : Type} [AddCommGroup W] [Module K W]
  (χ : Representation K H W)

def isoHom : Submodule K (W →ₗ[K] K ⊗[O'] D.V) where
  carrier := {f | ∀ h : H, f ∘ₗ χ h = ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) ∘ₗ f}
  add_mem' {f g} hf hg h := by rw [LinearMap.add_comp, LinearMap.comp_add, hf h, hg h]
  zero_mem' h := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  smul_mem' c f hf h := by rw [LinearMap.smul_comp, LinearMap.comp_smul, hf h]

/--
@isnad1 id=iff.0h9v.s13.7535eb26b1b9 from=translated src=- shape=7ad122ed vocab=a4e828e2
-/
theorem mem_isoHom_iff (f : W →ₗ[K] K ⊗[O'] D.V) :
    f ∈ D.isoHom K χ ↔ ∀ h : H, f ∘ₗ χ h = ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) ∘ₗ f :=
  Iff.rfl

def isoHomGal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End K (D.isoHom K χ) where
  toFun σ :=
    { toFun := fun f => ⟨((D.gal σ).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V), fun h => by
        have hc : ((D.gal σ).baseChange K) ∘ₗ ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) =
            ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) ∘ₗ ((D.gal σ).baseChange K) := by
          rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp,
            ← Module.End.mul_eq_comp, D.gal_comm_gl2]
        rw [LinearMap.comp_assoc, f.2 h, ← LinearMap.comp_assoc, hc, LinearMap.comp_assoc]⟩
      map_add' := fun f g => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c f => Subtype.ext (LinearMap.comp_smul _ _ _) }
  map_one' := LinearMap.ext fun f => Subtype.ext (by
    change ((D.gal 1).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) = f
    rw [map_one, LinearMap.baseChange_one, Module.End.one_eq_id, LinearMap.id_comp])
  map_mul' σ τ := LinearMap.ext fun f => Subtype.ext (by
    change ((D.gal (σ * τ)).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) =
      ((D.gal σ).baseChange K) ∘ₗ (((D.gal τ).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V))
    rw [map_mul, LinearMap.baseChange_mul, Module.End.mul_eq_comp, LinearMap.comp_assoc])

/--
@isnad1 id=eq.0h10v.s16.5ae486490142 from=translated src=- shape=4bd6d01c vocab=318e4d5e
-/
theorem coe_isoHomGal_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : D.isoHom K χ) :
    ((D.isoHomGal K χ σ f : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V) =
      ((D.gal σ).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) :=
  rfl

def isoHomHecke : ModularCurve.HeckeAlg →+* Module.End K (D.isoHom K χ) where
  toFun t :=
    { toFun := fun f => ⟨((D.hecke t).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V), fun h => by
        have hc : ((D.hecke t).baseChange K) ∘ₗ ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) =
            ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) ∘ₗ ((D.hecke t).baseChange K) := by
          rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp,
            ← Module.End.mul_eq_comp, D.hecke_comm_gl2]
        rw [LinearMap.comp_assoc, f.2 h, ← LinearMap.comp_assoc, hc, LinearMap.comp_assoc]⟩
      map_add' := fun f g => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c f => Subtype.ext (LinearMap.comp_smul _ _ _) }
  map_one' := LinearMap.ext fun f => Subtype.ext (by
    change ((D.hecke 1).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) = f
    rw [map_one, LinearMap.baseChange_one, Module.End.one_eq_id, LinearMap.id_comp])
  map_mul' s t := LinearMap.ext fun f => Subtype.ext (by
    change ((D.hecke (s * t)).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) =
      ((D.hecke s).baseChange K) ∘ₗ (((D.hecke t).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V))
    rw [map_mul, LinearMap.baseChange_mul, Module.End.mul_eq_comp, LinearMap.comp_assoc])
  map_zero' := LinearMap.ext fun f => Subtype.ext (by
    change ((D.hecke 0).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) = 0
    rw [map_zero, LinearMap.baseChange_zero, LinearMap.zero_comp])
  map_add' s t := LinearMap.ext fun f => Subtype.ext (by
    change ((D.hecke (s + t)).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) =
      ((D.hecke s).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) +
        ((D.hecke t).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V)
    rw [map_add, LinearMap.baseChange_add, LinearMap.add_comp])

/--
@isnad1 id=eq.0h10v.s16.308dda8217a9 from=translated src=- shape=5facf8e0 vocab=14ee5264
-/
theorem coe_isoHomHecke_apply (t : ModularCurve.HeckeAlg) (f : D.isoHom K χ) :
    ((D.isoHomHecke K χ t f : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V) =
      ((D.hecke t).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) :=
  rfl

/--
@isnad1 id=eq.0h10v.s17.6708dc4ac55f from=translated src=- shape=4185d1c2 vocab=fa33245f
-/
theorem isoHomGal_comm_isoHomHecke (t : ModularCurve.HeckeAlg)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    D.isoHomHecke K χ t * D.isoHomGal K χ σ = D.isoHomGal K χ σ * D.isoHomHecke K χ t :=
  LinearMap.ext fun f => Subtype.ext (by
    change ((D.hecke t).baseChange K) ∘ₗ (((D.gal σ).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V)) =
      ((D.gal σ).baseChange K) ∘ₗ (((D.hecke t).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V))
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, D.hecke_comm_gal])

def eigenIsoHom (φ : ModularCurve.HeckeAlg →+* K) : Submodule K (D.isoHom K χ) where
  carrier := {f | ∀ t : ModularCurve.HeckeAlg, D.isoHomHecke K χ t f = φ t • f}
  add_mem' {f g} hf hg t := by rw [map_add, hf t, hg t, smul_add]
  zero_mem' t := by rw [map_zero, smul_zero]
  smul_mem' c f hf t := by rw [map_smul, hf t, smul_comm]

/--
@isnad1 id=iff.0h10v.s16.47747dec8d07 from=translated src=- shape=e332e88f vocab=88d78678
-/
theorem mem_eigenIsoHom_iff (φ : ModularCurve.HeckeAlg →+* K) (f : D.isoHom K χ) :
    f ∈ D.eigenIsoHom K χ φ ↔ ∀ t : ModularCurve.HeckeAlg, D.isoHomHecke K χ t f = φ t • f :=
  Iff.rfl

def eigenIsoHomGal (φ : ModularCurve.HeckeAlg →+* K) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End K (D.eigenIsoHom K χ φ) where
  toFun σ :=
    { toFun := fun f => ⟨D.isoHomGal K χ σ (f : D.isoHom K χ), fun t => by
        have hc := congrArg (fun T => T (f : D.isoHom K χ)) (D.isoHomGal_comm_isoHomHecke K χ t σ)
        simp only [Module.End.mul_apply] at hc
        rw [hc, f.2 t, map_smul]⟩
      map_add' := fun f g => Subtype.ext (map_add _ _ _)
      map_smul' := fun c f => Subtype.ext (map_smul _ _ _) }
  map_one' := LinearMap.ext fun f => Subtype.ext (by
    change D.isoHomGal K χ 1 (f : D.isoHom K χ) = f
    rw [map_one, Module.End.one_apply])
  map_mul' σ τ := LinearMap.ext fun f => Subtype.ext (by
    change D.isoHomGal K χ (σ * τ) (f : D.isoHom K χ) = D.isoHomGal K χ σ (D.isoHomGal K χ τ (f : D.isoHom K χ))
    rw [map_mul, Module.End.mul_apply])

/--
@isnad1 id=eq.0h11v.s19.6b0c412344b7 from=translated src=- shape=8f1f9630 vocab=f35c3336
-/
theorem coe_eigenIsoHomGal_apply (φ : ModularCurve.HeckeAlg →+* K)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : D.eigenIsoHom K χ φ) :
    ((D.eigenIsoHomGal K χ φ σ f : D.eigenIsoHom K χ φ) : D.isoHom K χ) = D.isoHomGal K χ σ f :=
  rfl

end Datum

def borel (q : ℕ) [Fact q.Prime] : Subgroup (CuspidalType.GL2 q) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0}
  mul_mem' {x y} hx hy := by
    have hx' : (x : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := hx
    have hy' : (y : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := hy
    show ((x * y : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx', hy']
    ring
  one_mem' := by
    show ((1 : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_one]
    exact Matrix.one_apply_ne (by decide)
  inv_mem' {x} hx := by
    have hx' : (x : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := hx
    show ((x⁻¹ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
    simp [Matrix.adjugate_fin_two, hx']

/--
@isnad1 id=iff.0h2v.s8.3fc8ac1c690d from=translated src=- shape=d4e10ead vocab=9089b8cb
-/
theorem mem_borel_iff {q : ℕ} [Fact q.Prime] (g : CuspidalType.GL2 q) :
    g ∈ borel q ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 :=
  Iff.rfl

def borelChar {q : ℕ} [Fact q.Prime] {K : Type} [CommRing K] (μ₁ μ₂ : (ZMod q)ˣ →* Kˣ) :
    borel q →* Kˣ where
  toFun g :=
    have hg : ((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 *
        ((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 ≠ 0 := by
      have hdet : ((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
      rwa [Matrix.det_fin_two, (mem_borel_iff _).1 g.2, mul_zero, sub_zero] at hdet
    μ₁ (Units.mk0 _ (mul_ne_zero_iff.mp hg).1) * μ₂ (Units.mk0 _ (mul_ne_zero_iff.mp hg).2)
  map_one' := by
    have h1 : ∀ h, Units.mk0 ((((1 : borel q) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h = 1 :=
      fun h => Units.ext (by simp)
    have h2 : ∀ h, Units.mk0 ((((1 : borel q) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) h = 1 :=
      fun h => Units.ext (by simp)
    show μ₁ (Units.mk0 _ _) * μ₂ (Units.mk0 _ _) = 1
    rw [h1, h2, map_one, map_one, one_mul]
  map_mul' x y := by
    have hx : ((x : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := (mem_borel_iff _).1 x.2
    have hy : ((y : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := (mem_borel_iff _).1 y.2
    have hdx : ((x : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    have hdy : ((y : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    rw [Matrix.det_fin_two, hx, mul_zero, sub_zero] at hdx
    rw [Matrix.det_fin_two, hy, mul_zero, sub_zero] at hdy
    have e0 : ∀ h, Units.mk0 ((((x * y : borel q) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h =
        Units.mk0 _ (mul_ne_zero_iff.mp hdx).1 * Units.mk0 _ (mul_ne_zero_iff.mp hdy).1 :=
      fun h => Units.ext (by
        rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, Subgroup.coe_mul,
          Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hy, mul_zero, add_zero])
    have e1 : ∀ h, Units.mk0 ((((x * y : borel q) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) h =
        Units.mk0 _ (mul_ne_zero_iff.mp hdx).2 * Units.mk0 _ (mul_ne_zero_iff.mp hdy).2 :=
      fun h => Units.ext (by
        rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, Subgroup.coe_mul,
          Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx, zero_mul, zero_add])
    show μ₁ (Units.mk0 _ _) * μ₂ (Units.mk0 _ _) =
      (μ₁ (Units.mk0 _ _) * μ₂ (Units.mk0 _ _)) * (μ₁ (Units.mk0 _ _) * μ₂ (Units.mk0 _ _))
    rw [e0, e1, map_mul, map_mul, mul_mul_mul_comm]

/--
@isnad1 id=eq.2h7v.s12.6af77d9632f8 from=translated src=- shape=f285e3e6 vocab=280b1d3d
-/
theorem borelChar_apply {q : ℕ} [Fact q.Prime] {K : Type} [CommRing K] (μ₁ μ₂ : (ZMod q)ˣ →* Kˣ)
    (g : borel q) (a d : (ZMod q)ˣ)
    (ha : (a : ZMod q) = ((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0)
    (hd : (d : ZMod q) = ((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) :
    borelChar μ₁ μ₂ g = μ₁ a * μ₂ d := by
  have ea : ∀ h, Units.mk0 (((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h = a :=
    fun h => Units.ext (by rw [Units.val_mk0, ha])
  have ed : ∀ h, Units.mk0 (((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) h = d :=
    fun h => Units.ext (by rw [Units.val_mk0, hd])
  show μ₁ (Units.mk0 _ _) * μ₂ (Units.mk0 _ _) = _
  rw [ea, ed]

def borelRep {q : ℕ} [Fact q.Prime] {K : Type} [Field K] (μ₁ μ₂ : (ZMod q)ˣ →* Kˣ) :
    Representation K (borel q) K :=
  (Algebra.lmul K K).toRingHom.toMonoidHom.comp ((Units.coeHom K).comp (borelChar μ₁ μ₂))

end FullLevelTate

end
