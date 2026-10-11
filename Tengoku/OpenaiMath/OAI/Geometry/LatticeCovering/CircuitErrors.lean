import Tengoku.OpenaiMath.OAI.Geometry.LatticeCovering.PrimeGrids

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped BigOperators

lemma affineCircuitVolumeSum_le_rational {r d : ℕ} (J : Set (Fin d → ℝ)) :
    affineCircuitVolumeSum (r:=r) J ≤ rationalCircuitVolumeSum (r:=r) J := by
  apply ENNReal.tsum_le_tsum
  intro a
  split_ifs <;> simp

lemma finite_circuitTerm_series_le {d k : ℕ} {V : ℝ}
    (hV : 0 ≤ V) (hVd : V ≤ (d:ℝ)/6) :
    ∑ r ∈ Finset.Icc 3 k, circuitTerm d V r ≤ 4*circuitTerm d V 3 := by
  have hh : (∑ r ∈ Finset.Icc 3 k, ENNReal.ofReal (circuitTerm d V r)) ≤
      ∑' s : ℕ, ENNReal.ofReal (circuitTerm d V (s+3)) := by
    rw [←Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm] using
      (ENNReal.sum_le_tsum (Finset.range (k+1-3))
        (f:=fun s : ℕ => ENNReal.ofReal (circuitTerm d V (s+3))))
  have hb := hh.trans (tsum_circuitTerm_le hV hVd)
  rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => circuitTerm_nonneg _ _ hV)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) (circuitTerm_nonneg _ _ hV))).mp hb

end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.ConvexGrid
open MeasureTheory SimplexYoung RogersPreparation

end SingleLatticeCovering.ConvexGrid

section

section

noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Horizontal Completion MeasureTheory Set Topology
open scoped ENNReal Pointwise BigOperators

instance lattice_vadd_invariant {m : ℕ} (L : FullLattice m) :
    VAddInvariantMeasure L.module (Fin m → ℝ) volume :=
  inferInstanceAs (VAddInvariantMeasure L.module.toAddSubgroup (Fin m → ℝ) volume)

def periodize {m : ℕ} (L : FullLattice m) (f : (Fin m → ℝ) → ℝ≥0∞)
    (x : Fin m → ℝ) : ℝ≥0∞ := ∑' z : L.module, f (x+z)

def pointCount {m : ℕ} (L : FullLattice m) (J : Set (Fin m → ℝ)) :
    (Fin m → ℝ) → ℝ≥0∞ := periodize L (J.indicator 1)

def cell {m : ℕ} (L : FullLattice m) : Set (Fin m → ℝ) :=
  ZSpan.fundamentalDomain (latticeBasis L.module)

lemma cell_fundamental {m : ℕ} (L : FullLattice m) :
    IsAddFundamentalDomain L.module (cell L) volume :=
  ZLattice.isAddFundamentalDomain (IsZLattice.basis L.module) volume

lemma cell_measurable {m : ℕ} (L : FullLattice m) : MeasurableSet (cell L) :=
  ZSpan.fundamentalDomain_measurableSet _

lemma cell_volume_ne_zero {m : ℕ} (L : FullLattice m) : volume (cell L)≠0 :=
  ZSpan.measure_fundamentalDomain_ne_zero _

lemma cell_volume_ne_top {m : ℕ} (L : FullLattice m) : volume (cell L)≠⊤ :=
  (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne

lemma measurable_periodize {m : ℕ} (L : FullLattice m)
    {f : (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) : Measurable (periodize L f) := by
  exact Measurable.tsum (fun z => hf.comp (measurable_id.add measurable_const))

lemma integral_periodize {m : ℕ} (L : FullLattice m)
    {f : (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in cell L, periodize L f x = ∫⁻ x, f x := by
  unfold periodize
  have hm (z : L.module) : Measurable (fun x : Fin m → ℝ => f (x+(z : Fin m → ℝ))) :=
    hf.comp (measurable_id.add measurable_const)
  rw [lintegral_tsum (fun z => (hm z).aemeasurable)]
  convert (cell_fundamental L).lintegral_eq_tsum'' f |>.symm using 1
  congr 1
  funext z
  congr 1
  funext x
  congr 1
  change x+(z : Fin m → ℝ)=(z : Fin m → ℝ)+x
  exact add_comm _ _

def translateLaw {m : ℕ} (L : FullLattice m) : Measure (Fin m → ℝ) :=
  (volume (cell L))⁻¹ • volume.restrict (cell L)

lemma integral_pointCount {m : ℕ} (L : FullLattice m)
    {J : Set (Fin m → ℝ)} (hJ : MeasurableSet J) :
    ∫⁻ x, pointCount L J x ∂translateLaw L =
      volume J / ENNReal.ofReal (ZLattice.covolume L.module) := by
  rw [translateLaw,lintegral_smul_measure,pointCount,
    integral_periodize L (measurable_one.indicator hJ),lintegral_indicator_one hJ]
  have hc := ZLattice.covolume_eq_measure_fundamentalDomain L.module volume (cell_fundamental L)
  rw [hc,measureReal_def,ENNReal.ofReal_toReal (cell_volume_ne_top L)]
  exact mul_comm _ _

lemma pointCount_eq_zero {m : ℕ} (L : FullLattice m) (J : Set (Fin m → ℝ))
    (x : Fin m → ℝ) : pointCount L J x=0 ↔ latticeProjection L.module x ∉
      latticeProjection L.module '' J := by
  classical
  rw [pointCount,periodize,ENNReal.tsum_eq_zero]
  constructor
  · intro h ⟨y,hy,hxy⟩
    have hz : y-x ∈ L.module := (latticeProjection_eq_zero_iff L.module _).mp (by
      rw [map_sub,hxy,sub_self])
    have hh := h ⟨y-x,hz⟩
    have he : x+(y-x)=y := by abel
    simp only [he,Set.indicator_of_mem hy,Pi.one_apply,one_ne_zero] at hh
  · intro hx z
    apply Set.indicator_of_notMem
    intro hz
    apply hx
    refine ⟨x+z,hz,?_⟩
    rw [map_add,(latticeProjection_eq_zero_iff L.module _).mpr z.property,add_zero]

end SingleLatticeCovering.RogersPreparation

end
end

section

noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Horizontal Completion MeasureTheory Set Topology
open scoped ENNReal Pointwise BigOperators

lemma periodize_periodic {m : ℕ} (L : FullLattice m)
    (f : (Fin m → ℝ) → ℝ≥0∞) (z : L.module) (x : Fin m → ℝ) :
    periodize L f (z+x)=periodize L f x := by
  unfold periodize
  calc
    _ = ∑' w : L.module, f (x+((z+w : L.module) : Fin m → ℝ)) := by
      apply tsum_congr
      intro w
      congr 1
      change (z : Fin m → ℝ)+x+(w : Fin m → ℝ)=x+((z : Fin m → ℝ)+w)
      abel
    _ = _ := (Equiv.addLeft z).tsum_eq (fun w : L.module => f (x+w))

lemma periodize_mul {m : ℕ} (L : FullLattice m)
    (f g : (Fin m → ℝ) → ℝ≥0∞) (x : Fin m → ℝ) :
    periodize L f x*periodize L g x =
      periodize L (fun y => f y*periodize L g y) x := by
  change (∑' z : L.module, f (x+z))*periodize L g x =
    ∑' z : L.module, f (x+z)*periodize L g (x+z)
  rw [←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro z
  rw [add_comm x (z : Fin m → ℝ),periodize_periodic]

lemma integral_periodize_mul {m : ℕ} (L : FullLattice m)
    {f g : (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x in cell L, periodize L f x*periodize L g x =
      ∑' z : L.module, ∫⁻ x, f x*g (x+z) := by
  simp_rw [periodize_mul]
  have hi := integral_periodize L (f := fun y => f y*periodize L g y)
    (hf.mul (measurable_periodize L hg))
  rw [hi]
  simp_rw [periodize,←ENNReal.tsum_mul_left]
  apply lintegral_tsum
  intro z
  exact (hf.mul (hg.comp (measurable_id.add measurable_const))).aemeasurable

lemma pointCount_second_moment {m : ℕ} (L : FullLattice m)
    {J : Set (Fin m → ℝ)} (hJ : MeasurableSet J) :
    ∫⁻ x, pointCount L J x*pointCount L J x ∂translateLaw L =
      (volume (cell L))⁻¹ * ∑' z : L.module,
        volume (J ∩ (fun x : Fin m → ℝ => x+z) ⁻¹' J) := by
  rw [translateLaw,lintegral_smul_measure]
  change (volume (cell L))⁻¹ *
    (∫⁻ x in cell L, periodize L (J.indicator 1) x*periodize L (J.indicator 1) x)=_
  rw [integral_periodize_mul L (measurable_one.indicator hJ) (measurable_one.indicator hJ)]
  congr 1
  apply tsum_congr
  intro z
  have he (x : Fin m → ℝ) :
      J.indicator (1 : (Fin m → ℝ) → ℝ≥0∞) x*J.indicator 1 (x+z)=
      (J ∩ (fun y : Fin m → ℝ => y+z) ⁻¹' J).indicator 1 x := by
    classical
    by_cases hx : x ∈ J <;> by_cases hy : x+(z : Fin m → ℝ)∈J <;> simp [hx,hy]
  simp_rw [he]
  exact lintegral_indicator_one (hJ.inter (hJ.preimage (measurable_id.add measurable_const)))

end SingleLatticeCovering.RogersPreparation

end
end

section

noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Horizontal Completion MeasureTheory Set Topology
open scoped ENNReal Pointwise BigOperators

lemma integral_periodic_shift {m : ℕ} (L : FullLattice m)
    (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : ∀ (z : L.module) x, f (z+x)=f x) (a : Fin m → ℝ) :
    ∫⁻ x in cell L, f (a+x) = ∫⁻ x in cell L, f x := by
  rw [(measurePreserving_add_left volume a).setLIntegral_comp_emb
    (measurableEmbedding_addLeft a) f (cell L)]
  apply IsAddFundamentalDomain.setLIntegral_eq _ (cell_fundamental L) f hf
  exact (cell_fundamental L).vadd_of_comm a

lemma integral_torus_shift {m : ℕ} (L : FullLattice m)
    (f : Torus m → ℝ≥0∞) (t : Torus m) :
    ∫⁻ x, f (t+latticeProjection L.module x) ∂translateLaw L =
      ∫⁻ x, f (latticeProjection L.module x) ∂translateLaw L := by
  obtain ⟨a,rfl⟩ := latticeProjection_surjective L.module t
  simp only [translateLaw,lintegral_smul_measure]
  congr 1
  simp only [←map_add]
  exact integral_periodic_shift L (fun y => f (latticeProjection L.module y)) (by
    intro z x
    rw [map_add,(latticeProjection_eq_zero_iff L.module _).mpr z.property,zero_add]) a

end SingleLatticeCovering.RogersPreparation

end
end

noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.PrimeKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tailForm (i : ι) (a : ι → ℤ) (x : ι → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, (a j : ℝ)*x j

lemma tailForm_update (i : ι) (a : ι → ℤ) (x : ι → ℝ) (r : ℝ) :
    tailForm i a (Function.update x i r) = tailForm i a x := by
  unfold tailForm
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

lemma tailForm_add (i : ι) (a : ι → ℤ) (x y : ι → ℝ) :
    tailForm i a (x+y) = tailForm i a x+tailForm i a y := by
  simp [tailForm, mul_add, Finset.sum_add_distrib]
lemma tailForm_smul (i : ι) (a : ι → ℤ) (r : ℝ) (x : ι → ℝ) :
    tailForm i a (r • x) = r*tailForm i a x := by
  simp only [tailForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

def coordinates (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun x := Function.update x i ((x i+tailForm i a x)/p)
  invFun x := Function.update x i ((p : ℝ)*x i-tailForm i a x)
  left_inv x := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,tailForm_update]
      field_simp [hpR]
      ring
    · simp [Function.update_of_ne hji]
  right_inv x := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,tailForm_update]
      field_simp [hpR]
      ring
    · simp [Function.update_of_ne hji]
  map_add' x y := by
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,Pi.add_apply,tailForm_add]
      ring
    · simp [Function.update_of_ne hji]
  map_smul' r x := by
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,Pi.smul_apply,smul_eq_mul,tailForm_smul,RingHom.id_apply]
      ring
    · simp [Function.update_of_ne hji]

def basis (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) : Basis ι ℝ (ι → ℝ) :=
  Basis.ofEquivFun (coordinates p hp i a)

lemma basis_repr (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (x : ι → ℝ) (j : ι) :
    (basis p hp i a).repr x j =
      Function.update x i ((x i+tailForm i a x)/p) j := by
  simp [basis, Basis.ofEquivFun_repr_apply,coordinates]

lemma basis_apply (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (j k : ι) :
    basis p hp i a j k =
      if k=i then (if j=i then (p : ℝ) else -(a j : ℝ))
      else if j=k then 1 else 0 := by
  simp only [basis, Basis.coe_ofEquivFun,coordinates,LinearEquiv.coe_symm_mk]
  by_cases hki : k=i
  · subst k
    by_cases hji : j=i
    · subst j
      simp [tailForm,Function.update_self,Pi.single_apply,Finset.mem_erase]
    · simp [tailForm,Function.update_self,Pi.single_apply,hji,Finset.mem_erase,eq_comm]
  · simp [Pi.single_apply,hki,eq_comm]

def lattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (basis p hp i a))

instance lattice_discrete (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    DiscreteTopology (lattice p hp i a) := inferInstanceAs
      (DiscreteTopology (Submodule.span ℤ (Set.range (basis p hp i a))))
instance lattice_full (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    IsZLattice ℝ (lattice p hp i a) := inferInstanceAs
      (IsZLattice ℝ (Submodule.span ℤ (Set.range (basis p hp i a))))

lemma covolume_lattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    ZLattice.covolume (lattice p hp i a) = p := by
  change ZLattice.covolume (span ℤ (Set.range (basis p hp i a))) = _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (basis p hp i a) volume),
    ZSpan.volume_real_fundamentalDomain]
  let v : ι → ℝ := fun k => if k=i then p else -(a k : ℝ)
  have he : Matrix.of (basis p hp i a) = ((1 : Matrix ι ι ℝ).updateRow i v).transpose := by
    ext j k
    rw [Matrix.of_apply,basis_apply]
    by_cases hki : k=i
    · subst k; simp [v]
    · simp [Matrix.transpose_apply,Matrix.one_apply,hki,eq_comm]
  have hs : (∑ j, v j • (1 : Matrix ι ι ℝ) j) = v := by
    ext k
    simp [Matrix.one_apply,Pi.smul_apply,smul_eq_mul]
  rw [he,Matrix.det_transpose,←hs,Matrix.det_updateRow_sum]
  simp [v,abs_of_pos (show (0 : ℝ)<p by exact_mod_cast hp)]

lemma integer_mem_iff_dvd (p : ℕ) (hp : 0 < p) (i : ι) (a z : ι → ℤ) :
    (fun j => (z j : ℝ)) ∈ lattice p hp i a ↔
      (p : ℤ) ∣ z i+∑ j ∈ Finset.univ.erase i, a j*z j := by
  rw [lattice,(basis p hp i a).mem_span_iff_repr_mem ℤ]
  simp only [basis_repr]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · intro h
    obtain ⟨q,hq⟩ := h i
    have hqi : (q : ℝ) = ((z i : ℝ)+tailForm i a (fun j => (z j : ℝ)))/p := by
      simpa only [Function.update_self, algebraMap_int_eq,Int.coe_castRingHom] using hq
    refine ⟨q,?_⟩
    have he := (eq_div_iff hpR).mp hqi
    exact_mod_cast (show (z i : ℝ)+∑ j ∈ Finset.univ.erase i,
      (a j : ℝ)*(z j : ℝ)=(p : ℝ)*q by simpa [tailForm,mul_comm] using he.symm)
  · rintro ⟨q,hq⟩ j
    by_cases hji : j=i
    · subst j
      refine ⟨q,?_⟩
      simp only [Function.update_self]
      apply (eq_div_iff hpR).mpr
      have hr : (z i : ℝ)+∑ j ∈ Finset.univ.erase i,
          (a j : ℝ)*(z j : ℝ)=(p : ℝ)*q := by exact_mod_cast hq
      simpa [tailForm,mul_comm] using hr.symm
    · exact ⟨z j,by simp [Function.update_of_ne hji]⟩

lemma exists_integer_of_mem (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ)
    {x : ι → ℝ} (hx : x ∈ lattice p hp i a) :
    ∃ z : ι → ℤ, (fun j => (z j : ℝ)) = x := by
  have h := ((basis p hp i a).mem_span_iff_repr_mem ℤ x).mp hx
  choose q hq using h
  have hc : coordinates p hp i a x = (fun j => (q j : ℝ)) := by
    ext j
    simpa only [basis,Basis.ofEquivFun_repr_apply,algebraMap_int_eq,Int.coe_castRingHom] using (hq j).symm
  let z : ι → ℤ := Function.update q i ((p : ℤ)*q i-∑ j ∈ Finset.univ.erase i, a j*q j)
  refine ⟨z,?_⟩
  have he : (fun j => (z j : ℝ)) = (coordinates p hp i a).symm (fun j => (q j : ℝ)) := by
    ext j
    by_cases hji : j=i
    · subst j
      simp [z,coordinates,tailForm]
    · simp [z,coordinates,Function.update_of_ne hji]
  rw [he,←hc,LinearEquiv.symm_apply_apply]

lemma mem_lattice_iff (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (x : ι → ℝ) :
    x ∈ lattice p hp i a ↔ ∃ z : ι → ℤ, (fun j => (z j : ℝ)) = x ∧
      (p : ℤ) ∣ z i+∑ j ∈ Finset.univ.erase i, a j*z j := by
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := exists_integer_of_mem p hp i a hx
    exact ⟨z,hz,(integer_mem_iff_dvd p hp i a z).mp (hz.symm ▸ hx)⟩
  · rintro ⟨z,rfl,hz⟩
    exact (integer_mem_iff_dvd p hp i a z).mpr hz

lemma integer_mem_iff_congruence (p : ℕ) (hp : 0 < p) (i : ι) (a z : ι → ℤ) :
    (fun j => (z j : ℝ)) ∈ lattice p hp i a ↔
      (z i : ZMod p)+∑ j ∈ Finset.univ.erase i, (a j : ZMod p)*(z j : ZMod p)=0 := by
  rw [integer_mem_iff_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add,Int.cast_sum,Int.cast_mul]

end SingleLatticeCovering.PrimeKernel

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
