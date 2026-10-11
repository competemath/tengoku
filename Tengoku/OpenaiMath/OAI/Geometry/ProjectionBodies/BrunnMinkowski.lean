import Tengoku.OpenaiMath.OAI.Geometry.ProjectionBodies.SliceTransport

namespace OAI

universe uE uF

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The dimension-induction predicate, used only with a proved lower-dimensional
case. It is not an extra hypothesis on the projection-volume main theorem. -/
def BrunnMinkowskiRoot (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] (m : ℕ) : Prop :=
  ∀ K M : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
    IsCompact M → Convex ℝ M → (interior M).Nonempty →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      a*(volume.real K)^((m:ℝ)⁻¹)+b*(volume.real M)^((m:ℝ)⁻¹) ≤
        (volume.real (a • K+b • M))^((m:ℝ)⁻¹)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma sliceDensity_root_concave {m : ℕ} (hm : BrunnMinkowskiRoot E m)
    {K : Set (E × ℝ)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) :
    ConcaveOn ℝ (Ioo l r) (fun s => (sliceDensity K s)^((m:ℝ)⁻¹)) := by
  refine ⟨convex_Ioo l r,?_⟩
  intro s hs t ht a b ha hb hab
  have hlower := hm (horizontalSlice K s) (horizontalSlice K t)
    (horizontalSlice_compact hK s) (horizontalSlice_convex hc s)
    (horizontalSlice_interior_nonempty hc hi hl hr hs)
    (horizontalSlice_compact hK t) (horizontalSlice_convex hc t)
    (horizontalSlice_interior_nonempty hc hi hl hr ht) a b ha hb hab
  exact hlower.trans (Real.rpow_le_rpow measureReal_nonneg
    (measureReal_mono (horizontalSlice_combo_subset hc ha hb hab s t)
      (horizontalSlice_compact hK (a*s+b*t)).measure_ne_top) (by positivity))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma sliceDensity_continuous {m : ℕ} (hm0 : 0 < m) (hm : BrunnMinkowskiRoot E m)
    {K : Set (E × ℝ)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) :
    ContinuousOn (sliceDensity K) (Ioo l r) := by
  have h := (ConcaveOn.continuousOn isOpen_Ioo
    (sliceDensity_root_concave hm hK hc hi hl hr)).pow m
  convert h using 1
  funext s
  exact (Real.rpow_inv_natCast_pow (sliceDensity_nonneg K s) hm0.ne').symm

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma volumeReal_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (K : Set E) :
    volume.real (r • K)=r^(Module.finrank ℝ E)*volume.real K := by
  rw [Measure.real,Measure.addHaar_smul_of_nonneg volume hr,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr _)]
  rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma volumeReal_pos_of_body {K : Set E} (hK : IsCompact K) (hi : (interior K).Nonempty) :
    0 < volume.real K :=
  ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (isOpen_interior.measure_pos volume hi)
    (measure_mono interior_subset))) hK.measure_ne_top

/-- Usual normalization from the unit-volume form. The exponent is the actual
finite dimension of the Haar space, and the bodies remain arbitrary. -/
theorem brunnMinkowski_of_unit {d : ℕ} (hd : 0 < d) (hDim : Module.finrank ℝ E=d)
    (hunit : ∀ K M : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      IsCompact M → Convex ℝ M → (interior M).Nonempty →
      volume.real K=1 → volume.real M=1 → ∀ a b : ℝ, 0 < a → 0 < b → a+b=1 →
      1 ≤ volume.real (a • K+b • M)) : BrunnMinkowskiRoot E d := by
  intro K M hK hcK hiK hM hcM hiM a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · have hb1 : b=1 := by linarith
    simp [hb1,zero_smul_set (hiK.mono interior_subset)]
  obtain rfl | hb := hb.eq_or_lt
  · have ha1 : a=1 := by linarith
    simp [ha1,zero_smul_set (hiM.mono interior_subset)]
  let p := (volume.real K)^((d:ℝ)⁻¹)
  let q := (volume.real M)^((d:ℝ)⁻¹)
  let D := a*p+b*q
  have hp : 0 < p := Real.rpow_pos_of_pos (volumeReal_pos_of_body hK hiK) _
  have hq : 0 < q := Real.rpow_pos_of_pos (volumeReal_pos_of_body hM hiM) _
  have hD : 0 < D := by dsimp [D]; positivity
  have hpm : p^d=volume.real K := Real.rpow_inv_natCast_pow measureReal_nonneg hd.ne'
  have hqm : q^d=volume.real M := Real.rpow_inv_natCast_pow measureReal_nonneg hd.ne'
  have hUK : volume.real (p⁻¹ • K)=1 := by
    rw [volumeReal_smul_nonneg (inv_nonneg.mpr hp.le),hDim,inv_pow,hpm]
    exact inv_mul_cancel₀ (volumeReal_pos_of_body hK hiK).ne'
  have hUM : volume.real (q⁻¹ • M)=1 := by
    rw [volumeReal_smul_nonneg (inv_nonneg.mpr hq.le),hDim,inv_pow,hqm]
    exact inv_mul_cancel₀ (volumeReal_pos_of_body hM hiM).ne'
  have hiUK : (interior (p⁻¹ • K)).Nonempty := by
    rw [interior_smul₀ (inv_ne_zero hp.ne')]
    exact hiK.image _
  have hiUM : (interior (q⁻¹ • M)).Nonempty := by
    rw [interior_smul₀ (inv_ne_zero hq.ne')]
    exact hiM.image _
  have he := hunit (p⁻¹ • K) (q⁻¹ • M) (hK.smul _) (hcK.smul _) hiUK
    (hM.smul _) (hcM.smul _) hiUM hUK hUM (a*p/D) (b*q/D)
    (by positivity) (by positivity) (by rw [← add_div]; exact div_self hD.ne')
  have hsets : (a*p/D) • (p⁻¹ • K)+(b*q/D) • (q⁻¹ • M)=D⁻¹ • (a • K+b • M) := by
    rw [smul_add,smul_smul,smul_smul,smul_smul,smul_smul]
    congr 2 <;> field_simp
  rw [hsets,volumeReal_smul_nonneg (inv_nonneg.mpr hD.le),hDim,inv_pow] at he
  have hpow : D^d ≤ volume.real (a • K+b • M) := by
    have hx := mul_le_mul_of_nonneg_left he (pow_nonneg hD.le d)
    simpa only [mul_one,← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hD.ne'),one_mul] using hx
  have hr := Real.rpow_le_rpow (pow_nonneg hD.le d) hpow (by positivity : 0 ≤ (d:ℝ)⁻¹)
  rw [← Real.rpow_natCast,← Real.rpow_mul hD.le,mul_inv_cancel₀ (by exact_mod_cast hd.ne'),Real.rpow_one] at hr
  exact hr

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F]

omit [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F] in
lemma linearEquiv_preimage_combo (e : E ≃L[ℝ] F) (K M : Set F) (a b : ℝ) :
    e ⁻¹' (a • K+b • M)=a • (e ⁻¹' K)+b • (e ⁻¹' M) := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,he⟩
    refine ⟨a • e.symm x,⟨e.symm x,by simpa using hx,rfl⟩,
      b • e.symm y,⟨e.symm y,by simpa using hy,rfl⟩,?_⟩
    apply e.injective
    simpa using he
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨a • e x,⟨e x,hx,rfl⟩,b • e y,⟨e y,hy,rfl⟩,by simp⟩

omit [BorelSpace E] in
lemma BrunnMinkowskiRoot.equiv {m : ℕ} (hm : BrunnMinkowskiRoot E m)
    (e : E ≃L[ℝ] F) (he : MeasurePreserving e) : BrunnMinkowskiRoot F m := by
  intro K M hK hcK hiK hM hcM hiM a b ha hb hab
  have hPK : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hPM : IsCompact (e ⁻¹' M) := e.toHomeomorph.isCompact_preimage.mpr hM
  have hiPK : (interior (e ⁻¹' K)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' K)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x,hx⟩ := hiK
    exact ⟨e.symm x,by simpa using hx⟩
  have hiPM : (interior (e ⁻¹' M)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' M)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x,hx⟩ := hiM
    exact ⟨e.symm x,by simpa using hx⟩
  have h := hm (e ⁻¹' K) (e ⁻¹' M) hPK (hcK.linear_preimage e.toLinearMap) hiPK
    hPM (hcM.linear_preimage e.toLinearMap) hiPM a b ha hb hab
  have hm' (S : Set F) (hS : IsCompact S) : volume.real (e ⁻¹' S)=volume.real S :=
    congrArg ENNReal.toReal (he.measure_preimage hS.measurableSet.nullMeasurableSet)
  rw [hm' K hK,hm' M hM,← linearEquiv_preimage_combo,hm' _ ((hK.smul _).add (hM.smul _))] at h
  exact h
end

/-- The one-dimensional base case, with no symmetry or origin condition. -/
lemma brunnMinkowski_real : BrunnMinkowskiRoot ℝ 1 := by
  intro K M hK hcK hiK hM hcM hiM a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · have hb1 : b=1 := by linarith
    simp [hb1,zero_smul_set (hiK.mono interior_subset)]
  obtain rfl | hb := hb.eq_or_lt
  · have ha1 : a=1 := by linarith
    simp [ha1,zero_smul_set (hiM.mono interior_subset)]
  rw [compact_convex_real_interval hK hcK (hiK.mono interior_subset),
    compact_convex_real_interval hM hcM (hiM.mono interior_subset)]
  have hKlr : sInf K ≤ sSup K := (hK.isGLB_sInf (hiK.mono interior_subset)).1
    (hK.sSup_mem (hiK.mono interior_subset))
  have hMlr : sInf M ≤ sSup M := (hM.isGLB_sInf (hiM.mono interior_subset)).1
    (hM.sSup_mem (hiM.mono interior_subset))
  have hKa : a*sInf K ≤ a*sSup K := mul_le_mul_of_nonneg_left hKlr ha.le
  have hMb : b*sInf M ≤ b*sSup M := mul_le_mul_of_nonneg_left hMlr hb.le
  rw [LinearOrderedField.smul_Icc ha,LinearOrderedField.smul_Icc hb,Icc_add_Icc hKa hMb]
  simp only [Nat.cast_one,inv_one,Real.rpow_one,Real.volume_real_Icc]
  rw [max_eq_left (sub_nonneg.mpr hKlr),max_eq_left (sub_nonneg.mpr hMlr),
    max_eq_left (sub_nonneg.mpr (add_le_add hKa hMb))]
  nlinarith

/-- Standard coordinate splitting, with explicit measure evidence. -/
def finSplitLinear (n : ℕ) : (Fin (n+1) → ℝ) ≃ₗ[ℝ] ((Fin n → ℝ) × ℝ) where
  toEquiv := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).toEquiv.trans
    (Equiv.prodComm _ _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finSplit (n : ℕ) : (Fin (n+1) → ℝ) ≃L[ℝ] ((Fin n → ℝ) × ℝ) :=
  (finSplitLinear n).toContinuousLinearEquiv

lemma finSplit_measurePreserving (n : ℕ) : MeasurePreserving (finSplit n) := by
  have hs : MeasurePreserving (Prod.swap : ℝ × (Fin n → ℝ) → (Fin n → ℝ) × ℝ) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))))
  exact hs.comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0)

def finOneLinear : (Fin 1 → ℝ) ≃ₗ[ℝ] ℝ := LinearEquiv.funUnique (Fin 1) ℝ ℝ

def finOne : (Fin 1 → ℝ) ≃L[ℝ] ℝ := finOneLinear.toContinuousLinearEquiv

lemma finOne_measurePreserving : MeasurePreserving finOne :=
  volume_preserving_piUnique (fun _ : Fin 1 => ℝ)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

end PettyProjection
end

end OAI
