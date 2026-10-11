import Tengoku.OpenaiMath.OAI.Geometry.HarmonicGrowth.Attainment
import Tengoku.OpenaiMath.OAI.Geometry.HarmonicGrowth.EndpointBounds

namespace OAI

noncomputable section
open scoped Topology
open NormedSpace Module Filter

namespace HarmonicCounterexample.FiniteControl
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance 100] LieRing.ofAssociativeRing
local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

def expUnit (x : A) : Aˣ := (NormedSpace.isUnit_exp x).unit

@[simp] lemma expUnit_val (x : A) : (expUnit x : A)=NormedSpace.exp x :=
  (NormedSpace.isUnit_exp x).unit_spec

lemma expUnit_inv_val (x : A) : ((expUnit x)⁻¹ : Aˣ).val = NormedSpace.exp (-x) := by
  rw [← Ring.inverse_exp,← expUnit_val,Ring.inverse_unit]

def adjoint (h : Aˣ) : A →ₗ[ℝ] A where
  toFun X := (h:A)*X*(h⁻¹:Aˣ).val
  map_add' X Y := by simp only [mul_add,add_mul]
  map_smul' c X := by simp only [mul_smul_comm,smul_mul_assoc,RingHom.id_apply]

omit [CompleteSpace A] in
@[simp] lemma adjoint_apply (h : Aˣ) (X : A) :
    adjoint h X=(h:A)*X*(h⁻¹:Aˣ).val := rfl

omit [CompleteSpace A] in
@[simp] lemma adjoint_one (X : A) : adjoint 1 X=X := by simp [adjoint]

omit [CompleteSpace A] in
lemma adjoint_mul (h k : Aˣ) (X : A) : adjoint (h*k) X=adjoint h (adjoint k X) := by
  simp only [adjoint_apply,mul_inv_rev,Units.val_mul]
  noncomm_ring

omit [CompleteSpace A] in
lemma adjoint_lie (h : Aˣ) (X Y : A) :
    adjoint h ⁅X,Y⁆=⁅adjoint h X,adjoint h Y⁆ := by
  simp only [adjoint_apply,Ring.lie_def,mul_sub,sub_mul,mul_assoc]
  simp only [← mul_assoc (h⁻¹:Aˣ).val (h:A),Units.inv_mul,one_mul]

lemma adjoint_exp_deriv (X Y : A) :
    HasDerivAt (fun t : ℝ => adjoint (expUnit (t • X)) Y) ⁅X,Y⁆ 0 := by
  have hp : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
    simpa only [zero_smul,NormedSpace.exp_zero,one_mul] using hasDerivAt_exp_smul_const X (0:ℝ)
  have hm : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (-X))) (-X) 0 := by
    simpa only [zero_smul,NormedSpace.exp_zero,one_mul] using hasDerivAt_exp_smul_const (-X) (0:ℝ)
  convert (hp.mul_const Y).mul hm using 1 <;> first | rfl |
    simp only [adjoint_apply,expUnit_val,expUnit_inv_val,smul_neg,zero_smul,
      NormedSpace.exp_zero,mul_one,one_mul,mul_neg,neg_zero,Ring.lie_def,sub_eq_add_neg] <;> rfl

omit [CompleteSpace A] in
lemma deriv_mem_submodule [FiniteDimensional ℝ A] (S : Submodule ℝ A)
    {f : ℝ → A} {f' : A} {t : ℝ} (hf : HasDerivAt f f' t) (hS : ∀ t,f t ∈ S) : f' ∈ S := by
  apply S.closed_of_finiteDimensional.mem_of_tendsto hf.tendsto_slope
  exact Filter.Eventually.of_forall (fun u => S.smul_mem _ (S.sub_mem (hS u) (hS t)))

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter

namespace HarmonicCounterexample.FiniteControl
open NormedSpace Module
variable {A κ : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance 100] LieRing.ofAssociativeRing

def reachable (g : κ → A) : Subgroup Aˣ :=
  Subgroup.closure (Set.range (fun p : κ × ℝ => expUnit (p.2 • g p.1)))

def adjointSpan (g : κ → A) : Submodule ℝ A :=
  Submodule.span ℝ {x | ∃ h ∈ reachable g,∃ k,x=adjoint h (g k)}

lemma generator_mem_adjointSpan (g : κ → A) (k : κ) : g k ∈ adjointSpan g :=
  Submodule.subset_span ⟨1,(reachable g).one_mem,k,(adjoint_one _).symm⟩

lemma adjoint_mem_adjointSpan (g : κ → A) {h : Aˣ} (hh : h ∈ reachable g)
    {X : A} (hX : X ∈ adjointSpan g) : adjoint h X ∈ adjointSpan g := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k,hk,i,rfl⟩ := hx
    exact Submodule.subset_span ⟨h*k,(reachable g).mul_mem hh hk,i,(adjoint_mul h k (g i)).symm⟩
  | zero => rw [map_zero]; exact (adjointSpan g).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (adjointSpan g).add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact (adjointSpan g).smul_mem c hx

lemma generator_lie_adjointSpan [FiniteDimensional ℝ A] (g : κ → A) (k : κ)
    {X : A} (hX : X ∈ adjointSpan g) : ⁅g k,X⁆ ∈ adjointSpan g := by
  apply deriv_mem_submodule (adjointSpan g) (adjoint_exp_deriv (g k) X)
  intro t
  exact adjoint_mem_adjointSpan g
    (Subgroup.subset_closure (Set.mem_range_self (k,t))) hX

omit [CompleteSpace A] in
lemma adjoint_inv_cancel (h : Aˣ) (X : A) : adjoint h (adjoint h⁻¹ X)=X := by
  rw [← adjoint_mul,mul_inv_cancel,adjoint_one]

lemma adjointSpan_lie_mem [FiniteDimensional ℝ A] (g : κ → A)
    {X Y : A} (hX : X ∈ adjointSpan g) (hY : Y ∈ adjointSpan g) :
    ⁅X,Y⁆ ∈ adjointSpan g := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h,hh,k,rfl⟩ := hx
    have hz := adjoint_mem_adjointSpan g ((reachable g).inv_mem hh) hY
    have hb := generator_lie_adjointSpan g k hz
    have hc := adjoint_mem_adjointSpan g hh hb
    rw [adjoint_lie,adjoint_inv_cancel] at hc
    exact hc
  | zero => simpa only [zero_lie] using (adjointSpan g).zero_mem
  | add x y _ _ hx hy => rw [add_lie]; exact (adjointSpan g).add_mem hx hy
  | smul c x _ hx => rw [smul_lie]; exact (adjointSpan g).smul_mem c hx

/-- Differentiating ACTUAL reachable conjugations, in a closed finite
-dimensional span, proves the spanning assertion used for finite words. -/
theorem lieSpan_le_adjointSpan [FiniteDimensional ℝ A] (g : κ → A) :
    (LieSubalgebra.lieSpan ℝ A (Set.range g)).toSubmodule ≤ adjointSpan g := by
  let E : LieSubalgebra ℝ A :=
    { adjointSpan g with lie_mem' := adjointSpan_lie_mem g }
  have h : LieSubalgebra.lieSpan ℝ A (Set.range g) ≤ E := by
    apply LieSubalgebra.lieSpan_le.2
    rintro _ ⟨k,rfl⟩
    exact generator_mem_adjointSpan g k
  exact h

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter

namespace HarmonicCounterexample.FiniteControl
variable {A κ : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- A finite basis of actual reachable conjugates, as opposed to abstract
iterated brackets or a closure of the reachable subgroup. -/
theorem exists_adjoint_basis [FiniteDimensional ℝ A] (g : κ → A) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (adjointSpan g)),
      ∀ i,∃ (h : Aˣ),h ∈ reachable g ∧ ∃ k,(b i : A)=adjoint h (g k) := by
  classical
  let S : Set A := {x | ∃ h ∈ reachable g,∃ k,x=adjoint h (g k)}
  let inc : S → adjointSpan g := fun x => ⟨x.val,Submodule.subset_span x.property⟩
  have hs : (⊤ : Submodule ℝ (adjointSpan g)) ≤
      Submodule.span ℝ (Set.range inc) := by
    apply le_of_eq
    symm
    apply (Submodule.span_range_subtype_eq_top_iff (adjointSpan g)
      (fun x : S => Submodule.subset_span x.property)).2
    simp only [Subtype.range_coe_subtype,Set.ofPred_mem_eq]
    rfl
  let B := Set.range inc
  let ι : Type _ := ↥((linearIndepOn_empty ℝ (id : adjointSpan g → adjointSpan g)).extend
    (Set.empty_subset B))
  let b : Module.Basis ι ℝ (adjointSpan g) := Module.Basis.ofSpan hs
  let := FiniteDimensional.fintypeBasisIndex b
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι,b.reindex e,?_⟩
  intro i
  have hi := Module.Basis.ofSpan_subset hs (Set.mem_range_self (e.symm i))
  obtain ⟨x,hx⟩ := hi
  have heq : ((b.reindex e) i : A)=x.val := by
    simpa only [Module.Basis.reindex_apply,inc,b] using congrArg Subtype.val hx.symm
  rw [heq]
  exact x.property

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter

namespace HarmonicCounterexample.FiniteControl
open ContinuousLinearMap NormedSpace
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

lemma strict_deriv_conjugate [FiniteDimensional ℝ A] {d : ℕ}
    (h : Aˣ) (X : A) (i : Fin d) :
    HasStrictFDerivAt (fun t : Fin d → ℝ => adjoint h (NormedSpace.exp (t i • X)))
      ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (adjoint h X)) 0 := by
  have he : HasStrictFDerivAt (fun s : ℝ => NormedSpace.exp (s • X))
      ((1 : ℝ →L[ℝ] ℝ).smulRight X) 0 := by
    simpa only [zero_smul,NormedSpace.exp_zero,one_smul] using
      hasStrictFDerivAt_exp_smul_const (𝕂:=ℝ) X (0:ℝ)
  have hp := he.comp (0 : Fin d → ℝ) (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).hasStrictFDerivAt
  convert (adjoint h).toContinuousLinearMap.hasStrictFDerivAt.comp (0 : Fin d → ℝ) hp using 1 <;>
    ext t <;> simp

omit [CompleteSpace A] in
@[simp] lemma adjoint_unit (h : Aˣ) : adjoint h (1:A)=1 := by
  simp [adjoint]

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
lemma prod_at_zero {E ι : Type*} [Zero E] (l : List ι) (f : ι → E → A)
    (h0 : ∀ i,f i 0=1) : (l.map (fun i => f i 0)).prod=1 := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.map_cons,List.prod_cons,h0,ih,mul_one]

omit [CompleteSpace A] in
lemma strict_deriv_identity_product {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (l : List ι)
    (f : ι → E → A) (f' : ι → E →L[ℝ] A)
    (h0 : ∀ i,f i 0=1) (hf : ∀ i,HasStrictFDerivAt (f i) (f' i) 0) :
    HasStrictFDerivAt (fun t => (l.map (fun i => f i t)).prod)
      (l.map f').sum 0 := by
  induction l with
  | nil => simpa only [List.map_nil,List.prod_nil,List.sum_nil] using hasStrictFDerivAt_const (𝕜:=ℝ) (1:A) (0:E)
  | cons i l ih =>
    convert (hf i).fun_mul' ih using 1
    · ext t
      simp only [List.map_cons,List.prod_cons]
    · rw [h0,prod_at_zero l f h0]
      ext t
      simp [add_comm]

/-- The finite conjugation word has the required exact differential, calculated
in the actual Banach algebra, not postulated as a control hypothesis. -/
theorem conjugate_word_differential [FiniteDimensional ℝ A] {d : ℕ}
    (h : Fin d → Aˣ) (X : Fin d → A) :
    HasStrictFDerivAt
      (fun t : Fin d → ℝ => ((List.finRange d).map
        (fun i => adjoint (h i) (NormedSpace.exp (t i • X i)))).prod)
      (∑ i : Fin d,(ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (adjoint (h i) (X i))) 0 := by
  have he := strict_deriv_identity_product (List.finRange d)
    (fun i (t : Fin d → ℝ) => adjoint (h i) (NormedSpace.exp (t i • X i)))
    (fun i => (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (adjoint (h i) (X i)))
    (by intro i; simp)
    (fun i => strict_deriv_conjugate (h i) (X i) i)
  simpa only [← List.ofFn_eq_map,List.sum_ofFn] using he

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter

namespace HarmonicCounterexample.FiniteControl
open ContinuousLinearMap NormedSpace
open scoped ContDiff
variable {A κ : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def conjugateWord {d : ℕ} (h : Fin d → Aˣ) (X : Fin d → A) (t : Fin d → ℝ) : A :=
  ((List.finRange d).map (fun i => adjoint (h i) (NormedSpace.exp (t i • X i)))).prod

omit [CompleteSpace A] in
@[simp] lemma conjugateWord_zero {d : ℕ} (h : Fin d → Aˣ) (X : Fin d → A) :
    conjugateWord h X 0 = 1 := by
  unfold conjugateWord
  exact prod_at_zero (List.finRange d)
    (fun i (t : Fin d → ℝ) => adjoint (h i) (NormedSpace.exp (t i • X i)))
    (by intro i; simp)

lemma conjugateWord_smooth [FiniteDimensional ℝ A] {d : ℕ}
    (h : Fin d → Aˣ) (X : Fin d → A) : ContDiff ℝ ∞ (conjugateWord h X) := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : A → A) :=
    contDiff_iff_contDiffAt.2 (fun x => (NormedSpace.exp_analytic (𝕂:=ℝ) x).contDiffAt)
  have hi (i : Fin d) : ContDiff ℝ ∞ (fun t : Fin d → ℝ =>
      adjoint (h i) (NormedSpace.exp (t i • X i))) :=
    (adjoint (h i)).toContinuousLinearMap.contDiff.comp (he.comp ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).contDiff.smul contDiff_const))
  unfold conjugateWord
  induction List.finRange d with
  | nil => simpa only [List.map_nil,List.prod_nil] using (contDiff_const (c:=(1:A)))
  | cons i l ih => simpa only [List.map_cons,List.prod_cons] using (hi i).mul ih

/-- The ACTUAL finite word assembled from reachable conjugates has an
invertible differential onto its adjoint span. If Lie generation is full this
is exactly the finite-word submersion at the group identity. -/
theorem exists_word_submersion [FiniteDimensional ℝ A] (g : κ → A) :
    ∃ (d : ℕ) (h : Fin d → Aˣ) (k : Fin d → κ)
      (e : (Fin d → ℝ) ≃L[ℝ] (adjointSpan g)),
      (∀ i,h i ∈ reachable g) ∧
      d=Module.finrank ℝ (adjointSpan g) ∧
      ContDiff ℝ ∞ (conjugateWord h (g ∘ k)) ∧
      HasStrictFDerivAt (conjugateWord h (g ∘ k))
        ((adjointSpan g).subtypeL.comp (e : (Fin d → ℝ) →L[ℝ] (adjointSpan g))) 0 := by
  classical
  obtain ⟨d,b,hb⟩ := exists_adjoint_basis g
  choose h hh k hk using hb
  let e : (Fin d → ℝ) ≃L[ℝ] adjointSpan g := b.equivFun.symm.toContinuousLinearEquiv
  refine ⟨d,h,k,e,hh,?_,conjugateWord_smooth h (g ∘ k),?_⟩
  · simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis b).symm
  · have hd : (adjointSpan g).subtypeL.comp (e : (Fin d → ℝ) →L[ℝ] adjointSpan g) =
        ∑ i : Fin d,(ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight
          (adjoint (h i) (g (k i))) := by
      ext t
      simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,
        ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]
      change ↑(b.equivFun.symm t) = ∑ i,t i • adjoint (h i) (g (k i))
      rw [Module.Basis.equivFun_symm_apply]
      simp only [Submodule.coe_sum,Submodule.coe_smul,hk]
    rw [hd]
    exact conjugate_word_differential h (g ∘ k)

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter

namespace HarmonicCounterexample.FiniteControl
open ContinuousLinearMap Filter Set
variable {A κ : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def conjugateWordUnit {d : ℕ} (h : Fin d → Aˣ) (X : Fin d → A) (t : Fin d → ℝ) : Aˣ :=
  ((List.finRange d).map (fun i => h i * expUnit (t i • X i) * (h i)⁻¹)).prod

lemma conjugateWordUnit_val {d : ℕ} (h : Fin d → Aˣ) (X : Fin d → A) (t : Fin d → ℝ) :
    (conjugateWordUnit h X t : A) = conjugateWord h X t := by
  unfold conjugateWordUnit conjugateWord
  rw [← Units.coeHom_apply,map_list_prod,List.map_map]
  congr 1

lemma conjugateWordUnit_mem (g : κ → A) {d : ℕ} (h : Fin d → Aˣ)
    (hh : ∀ i,h i ∈ reachable g) (k : Fin d → κ) (t : Fin d → ℝ) :
    conjugateWordUnit h (g ∘ k) t ∈ reachable g := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.1 hx
  exact (reachable g).mul_mem ((reachable g).mul_mem (hh i)
    (Subgroup.subset_closure (Set.mem_range_self (k i,t i)))) ((reachable g).inv_mem (hh i))

/-- Full linear span is promoted to an ACTUAL open reachable subgroup by the
strict inverse/submersion theorem. No topological closure of reachability is used. -/
theorem reachable_open_of_adjointSpan_top [FiniteDimensional ℝ A] (g : κ → A)
    (hfull : adjointSpan g=⊤) : IsOpen (reachable g : Set Aˣ) := by
  obtain ⟨d,h,k,e,hh,_,_,hd⟩ := exists_word_submersion g
  have hsurj : Function.Surjective
      ((adjointSpan g).subtypeL.comp (e : (Fin d → ℝ) →L[ℝ] adjointSpan g)) := by
    intro x
    have hx : x ∈ adjointSpan g := by rw [hfull]; trivial
    exact ⟨e.symm ⟨x,hx⟩,by simp⟩
  have himage : conjugateWord h (g ∘ k) '' Set.univ ∈ (𝓝 (1:A)) := by
    rw [← conjugateWord_zero h (g ∘ k),← hd.map_nhds_eq_of_surj
      (LinearMap.range_eq_top.2 hsurj)]
    exact Filter.image_mem_map Filter.univ_mem
  apply (reachable g).isOpen_of_mem_nhds (g:=1)
  have hpre : Units.val ⁻¹' (conjugateWord h (g ∘ k) '' Set.univ) ∈ 𝓝 (1:Aˣ) :=
    (Units.continuous_val.continuousAt (x := (1:Aˣ))).preimage_mem_nhds himage
  apply Filter.mem_of_superset hpre
  intro u hu
  obtain ⟨t,_,ht⟩ := hu
  have he : conjugateWordUnit h (g ∘ k) t = u := by
    apply Units.ext
    rw [conjugateWordUnit_val,ht]
  rw [← he]
  exact conjugateWordUnit_mem g h hh k t

attribute [local instance 100] LieRing.ofAssociativeRing

theorem reachable_open_of_lieSpan_top [FiniteDimensional ℝ A] (g : κ → A)
    (hfull : LieSubalgebra.lieSpan ℝ A (Set.range g)=⊤) : IsOpen (reachable g : Set Aˣ) := by
  apply reachable_open_of_adjointSpan_top g
  apply top_le_iff.1
  simpa only [hfull,LieSubalgebra.top_toSubmodule] using lieSpan_le_adjointSpan g

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter

namespace HarmonicCounterexample.FiniteControl
variable {A κ : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

lemma expUnit_neg (x : A) : expUnit (-x)=(expUnit x)⁻¹ := by
  apply Units.ext
  simp only [expUnit_val,expUnit_inv_val]

lemma reachable_has_word (g : κ → A) {h : Aˣ} (hh : h ∈ reachable g) :
    ∃ l : List (κ × ℝ), (l.map (fun p => expUnit (p.2 • g p.1))).prod=h := by
  induction hh using Subgroup.closure_induction with
  | mem h hh =>
    obtain ⟨p,rfl⟩ := hh
    exact ⟨[p],by simp⟩
  | one => exact ⟨[],rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l,rfl⟩ := hx
    obtain ⟨m,rfl⟩ := hy
    exact ⟨l++m,by simp⟩
  | inv x _ hx =>
    obtain ⟨l,rfl⟩ := hx
    refine ⟨(l.map (fun p => (p.1,-p.2))).reverse,?_⟩
    rw [List.prod_inv_reverse,List.map_reverse,List.map_map]
    simp only [List.map_map]
    congr 2
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply,neg_smul,expUnit_neg]

lemma word_reachable (g : κ → A) (l : List (κ × ℝ)) :
    (l.map (fun p => expUnit (p.2 • g p.1))).prod ∈ reachable g := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure (Set.mem_range_self p)

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter

namespace HarmonicCounterexample.FiniteControl
open Matrix Matrix.SpecialLinearGroup
variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

lemma single_product (i j k l : ι) (a b : F) :
    single i j a * single k l b = if j=k then single i l (a*b) else 0 := by
  split_ifs with h
  · subst k; exact single_mul_single_same a i j l b
  · exact single_mul_single_of_ne a i j k h b

lemma diag2n_decompose {i j : ι} (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    diag2n hij a ha = transvection hij a * transvection hij.symm (-a⁻¹) *
      transvection hij a * transvection hij (-1) * transvection hij.symm 1 *
      transvection hij (-1) := by
  apply Subtype.ext
  simp only [coe_mul,transvection_coe,diag2n_coe]
  simp only [mul_add,add_mul,one_mul,mul_one,single_product,hij,hij.symm,ite_false,ite_true,add_zero]
  ext k l
  by_cases hki : k=i <;> by_cases hkj : k=j <;> by_cases hli : l=i <;> by_cases hlj : l=j
  all_goals subst_vars
  all_goals simp_all [diagonal_apply,single,one_apply,eq_comm]

/-- Every real or arbitrary-field special-linear matrix has a finite elementary
transvection word. This avoids assuming polar decomposition or connectedness. -/
lemma transvection_induction [Nontrivial ι] (P : Matrix.SpecialLinearGroup ι F → Prop)
    (htransvec : ∀ (i j : ι) (hij : i ≠ j) (a : F),P (transvection hij a))
    (hmul : ∀ A B,P A → P B → P (A*B)) (M : Matrix.SpecialLinearGroup ι F) : P M := by
  apply diagonal_transvection_induction' P M _ htransvec hmul
  intro i j hij a ha
  rw [diag2n_decompose hij a ha]
  exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _
    (htransvec i j hij a) (htransvec j i hij.symm (-a⁻¹)))
    (htransvec i j hij a)) (htransvec i j hij (-1)))
    (htransvec j i hij.symm 1)) (htransvec i j hij (-1))

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter

namespace HarmonicCounterexample.FiniteControl
open Matrix Matrix.SpecialLinearGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuous_transvection {i j : ι} (hij : i ≠ j) :
    Continuous (fun a : ℝ => transvection hij a) := by
  apply continuous_induced_rng.2
  change Continuous (fun a : ℝ => (1 : Matrix ι ι ℝ)+single i j a)
  apply continuous_const.add
  apply continuous_pi
  intro k
  apply continuous_pi
  intro l
  simp only [single,Matrix.of_apply]
  split_ifs <;> fun_prop

lemma joined_transvection {i j : ι} (hij : i ≠ j) (a : ℝ) :
    Joined (1 : Matrix.SpecialLinearGroup ι ℝ) (transvection hij a) := by
  simpa using (PathConnectedSpace.joined (0:ℝ) a).map (continuous_transvection hij)

lemma sl_joined_one [Nontrivial ι] (M : Matrix.SpecialLinearGroup ι ℝ) :
    Joined 1 M := by
  apply transvection_induction (fun M => Joined 1 M) _ _ M
  · intro i j hij a
    exact joined_transvection hij a
  · intro A B hA hB
    simpa using hA.mul hB

/-- Actual path connectedness of every nontrivial real special linear group,
proved by finite elementary operations, without any polar decomposition axiom. -/
theorem sl_pathConnected [Nontrivial ι] : PathConnectedSpace (Matrix.SpecialLinearGroup ι ℝ) := by
  constructor
  · exact ⟨1⟩
  · intro A B
    exact (sl_joined_one A).symm.trans (sl_joined_one B)

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter

namespace HarmonicCounterexample.FiniteControl
open Matrix
open scoped Matrix.Norms.Frobenius
variable {β κ : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)]

abbrev MatrixProduct (ι : β → Type*) [∀ b,Fintype (ι b)] := ∀ b,Matrix (ι b) (ι b) ℝ

def centralMatrix (c : β → ℝ) : MatrixProduct ι := fun b => c b • 1

omit [Fintype β] in
@[simp] lemma centralMatrix_zero : centralMatrix (ι:=ι) 0=0 := by
  funext b; exact zero_smul ℝ _

omit [Fintype β] in
lemma centralMatrix_add (c d : β → ℝ) : centralMatrix (ι:=ι) (c+d)=centralMatrix c+centralMatrix d := by
  funext b; exact add_smul _ _ _

omit [Fintype β] in
lemma centralMatrix_neg (c : β → ℝ) : centralMatrix (ι:=ι) (-c) = -centralMatrix c := by
  funext b; exact neg_smul _ _

omit [Fintype β] in
lemma centralMatrix_commute (c : β → ℝ) (X : MatrixProduct ι) : Commute (centralMatrix c) X := by
  show centralMatrix c*X=X*centralMatrix c
  funext b
  simp only [Pi.mul_apply,centralMatrix,smul_mul_assoc,one_mul,mul_smul_comm,mul_one]

lemma expUnit_add_commute {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X Y : A) (h : Commute X Y) : expUnit (X+Y)=expUnit X*expUnit Y := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Units.ext
  simp only [expUnit_val,Units.val_mul,NormedSpace.exp_add_of_commute h]

lemma central_expUnit_commute (c : β → ℝ) (u : (MatrixProduct ι)ˣ) :
    Commute (expUnit (centralMatrix c)) u := by
  apply Units.val_injective
  exact (centralMatrix_commute c (u : MatrixProduct ι)).exp_left.eq

def augmented (g : κ → MatrixProduct ι) : (κ ⊕ (β → ℝ)) → MatrixProduct ι :=
  Sum.elim g centralMatrix

attribute [local instance 100] LieRing.ofAssociativeRing

omit [Fintype β] in
lemma augmented_lieSpan_top [∀ b,Nonempty (ι b)] (g : κ → MatrixProduct ι)
    (hfull : ∀ X : MatrixProduct ι,(∀ b,(X b).trace=0) →
      X ∈ LieSubalgebra.lieSpan ℝ _ (Set.range g)) :
    LieSubalgebra.lieSpan ℝ _ (Set.range (augmented g))=⊤ := by
  apply top_le_iff.1
  intro X _
  let c : β → ℝ := fun b => (X b).trace/(Fintype.card (ι b):ℝ)
  have htrace : ∀ b,(X b-centralMatrix (ι:=ι) c b).trace=0 := by
    intro b
    simp only [centralMatrix,Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_one,smul_eq_mul,c]
    rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (Fintype.card_ne_zero)) ,sub_self]
  have hinc : LieSubalgebra.lieSpan ℝ _ (Set.range g) ≤
      LieSubalgebra.lieSpan ℝ _ (Set.range (augmented g)) := by
    apply LieSubalgebra.lieSpan_mono
    rintro _ ⟨k,rfl⟩
    exact ⟨Sum.inl k,rfl⟩
  have hc : centralMatrix (ι:=ι) c ∈ LieSubalgebra.lieSpan ℝ _ (Set.range (augmented g)) :=
    LieSubalgebra.subset_lieSpan (Set.mem_range_self (Sum.inr c))
  convert
    (LieSubalgebra.lieSpan ℝ _ (Set.range (augmented g))).add_mem
      (hinc (hfull (X-centralMatrix c) htrace)) hc using 1
  ext b i j; simp

lemma augmented_reachable_split (g : κ → MatrixProduct ι)
    {u : (MatrixProduct ι)ˣ} (hu : u ∈ reachable (augmented g)) :
    ∃ c : β → ℝ,∃ v ∈ reachable g,u=expUnit (centralMatrix c)*v := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨⟨k,t⟩,rfl⟩ := hu
    cases k with
    | inl k =>
      refine ⟨0,expUnit (t • g k),Subgroup.subset_closure (Set.mem_range_self (k,t)),?_⟩
      apply Units.ext
      simp [augmented,expUnit_val]
    | inr c =>
      refine ⟨t • c,1,(reachable g).one_mem,?_⟩
      rw [mul_one]
      change expUnit (t • centralMatrix c)=expUnit (centralMatrix (t • c))
      congr 1
      funext b
      simp [centralMatrix,smul_smul]
  | one =>
    refine ⟨0,1,(reachable g).one_mem,?_⟩
    apply Units.ext
    simp [expUnit_val]
  | mul u v _ _ hu hv =>
    obtain ⟨c,u,hu,rfl⟩ := hu
    obtain ⟨d,v,hv,rfl⟩ := hv
    refine ⟨c+d,u*v,(reachable g).mul_mem hu hv,?_⟩
    rw [centralMatrix_add,expUnit_add_commute _ _ (centralMatrix_commute _ _)]
    have hc := (central_expUnit_commute d u).eq
    calc
      (expUnit (centralMatrix c)*u)*(expUnit (centralMatrix d)*v) =
          expUnit (centralMatrix c)*(u*expUnit (centralMatrix d))*v := by group
      _ = (expUnit (centralMatrix c)*expUnit (centralMatrix d))*(u*v) := by rw [← hc]; group
  | inv u _ hu =>
    obtain ⟨c,v,hv,rfl⟩ := hu
    refine ⟨-c,v⁻¹,(reachable g).inv_mem hv,?_⟩
    rw [centralMatrix_neg,expUnit_neg,_root_.mul_inv_rev]
    exact ((central_expUnit_commute c v).inv_inv).eq.symm

/-- The ordinary product of REAL SL groups has a continuous genuine embedding
into units of the product matrix algebra. -/
def slProductToUnits : (∀ b,Matrix.SpecialLinearGroup (ι b) ℝ) →* (MatrixProduct ι)ˣ where
  toFun M :=
    { val := fun b => (M b : Matrix (ι b) (ι b) ℝ)
      inv := fun b => ((M b)⁻¹ : Matrix.SpecialLinearGroup (ι b) ℝ)
      val_inv := by funext b; exact (Matrix.SpecialLinearGroup.toGL (M b)).val_inv
      inv_val := by funext b; exact (Matrix.SpecialLinearGroup.toGL (M b)).inv_val }
  map_one' := by apply Units.ext; rfl
  map_mul' _ _ := by apply Units.ext; rfl

omit [Fintype β] in
lemma slProductToUnits_continuous : Continuous (slProductToUnits (ι:=ι)) := by
  rw [Units.continuous_iff]
  constructor
  · exact continuous_pi (fun b => continuous_subtype_val.comp (continuous_apply b))
  · change Continuous (fun M : ∀ b,Matrix.SpecialLinearGroup (ι b) ℝ =>
      fun b => ((M b)⁻¹ : Matrix.SpecialLinearGroup (ι b) ℝ).val)
    exact continuous_pi (fun b => continuous_subtype_val.comp ((continuous_apply b).inv))

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter
open scoped Topology

namespace HarmonicCounterexample.FiniteControl
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def detMultilinear : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  ⟨Matrix.detRowAlternating.toMultilinearMap,continuous_id.matrix_det⟩

lemma hasDerivAt_det {f : ℝ → Matrix ι ι ℝ} {f' : Matrix ι ι ℝ} {t : ℝ}
    (hf : ∀ i,HasDerivAt (fun s => f s i) (f' i) t) :
    HasDerivAt (fun s => (f s).det) (∑ i,(Matrix.updateRow (f t) i (f' i)).det) t := by
  have h := (detMultilinear (ι:=ι)).hasFDerivAt (f t) |>.comp_hasDerivAt t
    (hasDerivAt_pi.2 hf)
  erw [ContinuousMultilinearMap.linearDeriv_apply] at h
  exact h

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter
open scoped Topology

namespace HarmonicCounterexample.FiniteControl
open Matrix
open scoped Matrix.Norms.Frobenius
attribute [local instance 100] LieRing.ofAssociativeRing
variable {β κ : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)]

lemma slProduct_augmented_reachable [∀ b,Nontrivial (ι b)]
    (g : κ → MatrixProduct ι)
    (hfull : ∀ X : MatrixProduct ι,(∀ b,(X b).trace=0) →
      X ∈ LieSubalgebra.lieSpan ℝ _ (Set.range g))
    (M : ∀ b,Matrix.SpecialLinearGroup (ι b) ℝ) :
    slProductToUnits M ∈ reachable (augmented g) := by
  let : ∀ b,PathConnectedSpace (Matrix.SpecialLinearGroup (ι b) ℝ) :=
    fun b => sl_pathConnected
  let S : OpenSubgroup (MatrixProduct ι)ˣ :=
    ⟨reachable (augmented g),reachable_open_of_lieSpan_top _ (augmented_lieSpan_top g hfull)⟩
  let T := S.comap slProductToUnits slProductToUnits_continuous
  have he : (T : Set (∀ b,Matrix.SpecialLinearGroup (ι b) ℝ))=Set.univ :=
    T.isClopen.eq_univ ⟨1,T.one_mem⟩
  have hm : M ∈ (T : Set (∀ b,Matrix.SpecialLinearGroup (ι b) ℝ)) := by rw [he]; trivial
  exact hm

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open scoped Topology
open NormedSpace Module Filter
open scoped Topology

namespace HarmonicCounterexample.FiniteControl
open Matrix
open scoped Matrix.Norms.Frobenius ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing
variable {β κ : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)]

def tracefreeProduct : Submodule ℝ (MatrixProduct ι) where
  carrier := {X | ∀ b,(X b).trace=0}
  zero_mem' := by simp
  add_mem' hx hy := by intro b; rw [Pi.add_apply,Matrix.trace_add,hx,hy,add_zero]
  smul_mem' c X hx := by intro b; rw [Pi.smul_apply,Matrix.trace_smul,hx,smul_zero]

lemma adjoint_trace (h : (MatrixProduct ι)ˣ) (X : MatrixProduct ι) (b : β) :
    (adjoint h X b).trace=(X b).trace := by
  change (((h : MatrixProduct ι) b * X b) * ((h⁻¹ : (MatrixProduct ι)ˣ) : MatrixProduct ι) b).trace= _
  rw [Matrix.trace_mul_cycle]
  have hi := congrFun h.inv_val b
  change ((h⁻¹ : (MatrixProduct ι)ˣ) : MatrixProduct ι) b * (h : MatrixProduct ι) b=1 at hi
  rw [hi,Matrix.one_mul]

lemma adjointSpan_eq_tracefree (g : κ → MatrixProduct ι)
    (hg : ∀ k b,(g k b).trace=0)
    (hfull : ∀ X : MatrixProduct ι,(∀ b,(X b).trace=0) →
      X ∈ LieSubalgebra.lieSpan ℝ _ (Set.range g)) :
    adjointSpan g=tracefreeProduct := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro X ⟨h,_,k,rfl⟩
    intro b
    rw [adjoint_trace,hg]
  · intro X hX
    exact lieSpan_le_adjointSpan g (hfull X hX)

end HarmonicCounterexample.FiniteControl

end

noncomputable section

namespace HarmonicCounterexample.FiniteControl
open scoped ContDiff
variable {A κ H : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A finite control word with genuine smooth scalar amplitudes. -/
def parameterWord (g : κ → A) (w : List (κ × (H → ℝ))) (x : H) : A :=
  (w.map (fun p => NormedSpace.exp (p.2 x • g p.1))).prod

def constantWord (w : List (κ × ℝ)) : List (κ × (H → ℝ)) :=
  w.map (fun p => (p.1,fun _ => p.2))

def inverseWord (w : List (κ × ℝ)) : List (κ × ℝ) :=
  w.reverse.map (fun p => (p.1,-p.2))

omit [CompleteSpace A] [NormedAddCommGroup H] [NormedSpace ℝ H] in
lemma parameterWord_append (g : κ → A) (w v : List (κ × (H → ℝ))) (x : H) :
    parameterWord g (w++v) x=parameterWord g w x*parameterWord g v x := by
  simp [parameterWord]

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
lemma constantWord_value (g : κ → A) (w : List (κ × ℝ)) (x : H) :
    parameterWord g (constantWord w) x=
      ((w.map (fun p => expUnit (p.2 • g p.1))).prod : Aˣ) := by
  induction w with
  | nil => simp [parameterWord,constantWord]
  | cons p w ih => simpa only [constantWord,List.map_cons,parameterWord,List.prod_cons,
      Units.val_mul,expUnit_val] using congrArg (fun y : A => NormedSpace.exp (p.2 • g p.1)*y) ih

lemma inverseWord_value (g : κ → A) (w : List (κ × ℝ)) :
    ((inverseWord w).map (fun p => expUnit (p.2 • g p.1))).prod=
      ((w.map (fun p => expUnit (p.2 • g p.1))).prod)⁻¹ := by
  simp only [inverseWord,List.map_map,Function.comp_def,neg_smul,expUnit_neg]
  simp only [List.prod_inv_reverse,List.map_reverse,List.map_map,Function.comp_def]

lemma constantWord_smooth (w : List (κ × ℝ)) :
    ∀ p ∈ constantWord (H:=H) w,ContDiff ℝ ∞ p.2 := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := List.mem_map.1 hp
  exact contDiff_const

/-- Flatten reachable conjugations and the target into one fixed finite list.
No abstract exponential controls remain beyond the permitted generators. -/
theorem conjugate_word_flatten {d : ℕ} (g : κ → A)
    (h : Fin d → Aˣ) (k : Fin d → κ) (w : Fin d → List (κ × ℝ))
    (hw : ∀ i,(w i |>.map (fun p => expUnit (p.2 • g p.1))).prod=h i)
    (target : List (κ × ℝ)) (coord : H →L[ℝ] (Fin d → ℝ)) :
    ∃ z : List (κ × (H → ℝ)),
      (∀ p ∈ z,ContDiff ℝ ∞ p.2) ∧
      ∀ x,parameterWord g z x=conjugateWord h (g ∘ k) (coord x)*
        ((target.map (fun p => expUnit (p.2 • g p.1))).prod : Aˣ) := by
  let packet := fun i : Fin d => constantWord (H:=H) (w i) ++
    [(k i,fun x => coord x i)] ++ constantWord (H:=H) (inverseWord (w i))
  have hpacket (i : Fin d) (x : H) : parameterWord g (packet i) x=
      adjoint (h i) (NormedSpace.exp (coord x i • g (k i))) := by
    dsimp only [packet]
    rw [parameterWord_append,parameterWord_append,constantWord_value,constantWord_value,
      inverseWord_value,hw]
    simp only [parameterWord,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,adjoint_apply]
  have hpacketsmooth (i : Fin d) : ∀ p ∈ packet i,ContDiff ℝ ∞ p.2 := by
    intro p hp
    simp only [packet,List.mem_append,List.mem_singleton] at hp
    rcases hp with (hp|rfl)|hp
    · exact constantWord_smooth _ _ hp
    · exact ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).comp coord).contDiff
    · exact constantWord_smooth _ _ hp
  let z := (List.finRange d).flatMap packet ++ constantWord (H:=H) target
  refine ⟨z,?_,?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp|hp
    · obtain ⟨i,_,hp⟩ := List.mem_flatMap.1 hp
      exact hpacketsmooth i p hp
    · exact constantWord_smooth _ _ hp
  · intro x
    rw [show z=(List.finRange d).flatMap packet ++ constantWord target from rfl,
      parameterWord_append,constantWord_value]
    congr 1
    unfold conjugateWord
    induction List.finRange d with
    | nil => simp [parameterWord]
    | cons i l ih => simp only [List.flatMap_cons,parameterWord_append,List.map_cons,
        List.prod_cons,hpacket,ih,Function.comp_apply]

end HarmonicCounterexample.FiniteControl

end

noncomputable section

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff
variable {A κ H : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
lemma leftWord_reverse_product (X : ℕ → A) (n : ℕ) :
    leftWord X n=((List.ofFn (fun i : Fin n => NormedSpace.exp (X i.val))).reverse).prod := by
  induction n with
  | zero => simp [leftWord]
  | succ n ih =>
    simp only [leftWord,List.ofFn_succ',List.concat_eq_append,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.prod_append,List.prod_cons,List.prod_nil,mul_one,Fin.val_last,Fin.val_castSucc]
    rw [ih]

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
lemma packet_reverse_list (g : κ → A) (w : List (κ × (H → ℝ))) (x : H) :
    LinearODE.flow (fun t => ContinuousLinearMap.mul ℝ A
      (unitPacketCoefficient (fun i : Fin w.reverse.length => (w.reverse.get i).2 x)
        (fun i => g (w.reverse.get i).1) t)) 1 1=parameterWord g w x := by
  rw [actual_packet_endpoint,leftWord_reverse_product]
  have he : (List.ofFn (fun i : Fin w.reverse.length =>
      NormedSpace.exp (extendWord (fun i => (w.reverse.get i).2 x)
        (fun i => g (w.reverse.get i).1) i.val)))=
      w.reverse.map (fun p => NormedSpace.exp (p.2 x • g p.1)) := by
    simp only [extendWord,Fin.isLt,dite_eq_left]
    simpa only [Function.comp_def,List.ofFn_get] using
      (List.map_ofFn (f:=w.reverse.get)
        (g:=fun p : κ × (H → ℝ) => NormedSpace.exp (p.2 x • g p.1))).symm
  rw [he,← List.map_reverse,List.reverse_reverse]
  rfl

/-- The finite SL word is realized by the actual smooth chronological packet,
with a positive number of slots and smooth genuine amplitudes. -/
theorem smooth_packet_of_parameter_word [Nonempty κ] (g : κ → A)
    (w : List (κ × (H → ℝ))) (hw : ∀ p ∈ w,ContDiff ℝ ∞ p.2) :
    ∃ (n : ℕ) (_ : NeZero n) (slot : Fin n → κ) (amps : Fin n → H → ℝ),
      (∀ i,ContDiff ℝ ∞ (amps i)) ∧ ∀ x,
      LinearODE.flow (fun t => ContinuousLinearMap.mul ℝ A
        (unitPacketCoefficient (fun i => amps i x) (fun i => g (slot i)) t)) 1 1=
          parameterWord g w x := by
  classical
  let k₀ : κ := Classical.choice inferInstance
  let z : List (κ × (H → ℝ)) := (k₀,fun _ => (0:ℝ))::w
  refine ⟨z.reverse.length,⟨by simp [z]⟩,fun i => (z.reverse.get i).1,
    fun i => (z.reverse.get i).2,?_,?_⟩
  · intro i
    have hi : z.reverse.get i ∈ z := List.mem_reverse.1 (List.get_mem _ _)
    rcases List.mem_cons.1 hi with hi|hi
    · change ContDiff ℝ ∞ (z.reverse.get i).2
      rw [hi]
      exact contDiff_const
    · exact hw _ hi
  · intro x
    rw [packet_reverse_list]
    simp only [parameterWord,z,List.map_cons,List.prod_cons,zero_smul,NormedSpace.exp_zero,one_mul]

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section

namespace HarmonicCounterexample.FiniteControl.Frobenius
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {β : Type*} {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nonempty (ι b)]

abbrev MatrixProduct' := ∀ b,Matrix (ι b) (ι b) ℝ

def tracefreeProduct' : Submodule ℝ (MatrixProduct' (ι:=ι)) where
  carrier := {X | ∀ b,(X b).trace=0}
  zero_mem' := by simp
  add_mem' hx hy := by intro b; rw [Pi.add_apply,Matrix.trace_add,hx,hy,add_zero]
  smul_mem' c X hx := by intro b; rw [Pi.smul_apply,Matrix.trace_smul,hx,smul_zero]

def meanTrace (X : MatrixProduct' (ι:=ι)) (b : β) : ℝ :=
  (X b).trace/(Fintype.card (ι b):ℝ)

/-- Linear local SL chart: project away scalar matrices after translating the
exact target to the identity. No abstract manifold chart is assumed. -/
def tracefreeProjection : MatrixProduct' (ι:=ι) →ₗ[ℝ] tracefreeProduct' (ι:=ι) where
  toFun X := ⟨fun b => X b-meanTrace X b • 1,by
    intro b
    have hn : (Fintype.card (ι b):ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_one,smul_eq_mul,meanTrace]
    rw [div_mul_cancel₀ _ hn,sub_self]⟩
  map_add' X Y := by
    apply Subtype.ext
    funext b
    change (X b+Y b)-meanTrace (X+Y) b • 1=
      (X b-meanTrace X b • 1)+(Y b-meanTrace Y b • 1)
    simp only [Pi.add_apply,Matrix.trace_add,meanTrace,add_div,add_smul]
    abel
  map_smul' c X := by
    apply Subtype.ext
    funext b
    change c • X b-meanTrace (c • X) b • 1=c • (X b-meanTrace X b • 1)
    simp only [Pi.smul_apply,Matrix.trace_smul,meanTrace,smul_eq_mul,
      mul_div_assoc,smul_sub,smul_smul]

/-- Projection zero is exactly scalarity, with the scalar given explicitly. -/
lemma tracefreeProjection_zero_iff (X : MatrixProduct' (ι:=ι)) :
    tracefreeProjection X=0 ↔ ∀ b,X b=meanTrace X b • 1 := by
  constructor
  · intro h b
    have he := congrFun (congrArg Subtype.val h) b
    exact sub_eq_zero.1 he
  · intro h
    apply Subtype.ext
    funext b
    change X b-meanTrace X b • 1=0
    rw [h b,sub_self]

lemma tracefreeProjection_id : tracefreeProjection (1 : MatrixProduct' (ι:=ι))=0 := by
  apply (tracefreeProjection_zero_iff _).2
  intro b
  have hn : (Fintype.card (ι b):ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp [meanTrace,hn]

lemma tracefreeProjection_subtype (X : tracefreeProduct' (ι:=ι)) :
    tracefreeProjection X=X := by
  apply Subtype.ext
  funext b
  change (X : MatrixProduct' (ι:=ι)) b-meanTrace (X : MatrixProduct' (ι:=ι)) b • 1=(X : MatrixProduct' (ι:=ι)) b
  simp only [meanTrace,X.property b,zero_div,zero_smul,sub_zero]

/-- Positivity of trace resolves the spurious negative scalar branch. This is
an OPEN condition near the prescribed positive scalar times the target. -/
lemma positive_scalar_of_projection_zero {X : MatrixProduct' (ι:=ι)}
    (hX : tracefreeProjection X=0) (htr : ∀ b,0 < (X b).trace) :
    ∀ b,∃ c : ℝ,0 < c ∧ X b=c • 1 := by
  intro b
  exact ⟨meanTrace X b,div_pos (htr b) (Nat.cast_pos.2 Fintype.card_pos),
    (tracefreeProjection_zero_iff X).1 hX b⟩

/-- Vanishing projected transmission gives the EXACT target, up to the
positive scalar permitted by source equation (exact-transmission). -/
lemma exact_scalar_target {X : MatrixProduct' (ι:=ι)} (M : (MatrixProduct' (ι:=ι))ˣ)
    (hX : tracefreeProjection (X*(↑M⁻¹ : MatrixProduct' (ι:=ι)))=0)
    (htr : ∀ b,0 < ((X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b).trace) :
    ∀ b,∃ c : ℝ,0 < c ∧ X b=c • ((M : MatrixProduct' (ι:=ι)) b) := by
  intro b
  obtain ⟨c,hc,he⟩ := positive_scalar_of_projection_zero hX htr b
  refine ⟨c,hc,?_⟩
  have h := congrArg (fun A : Matrix (ι b) (ι b) ℝ => A*((M : MatrixProduct' (ι:=ι)) b)) he
  have hi := congrFun M.inv_val b
  change ((M⁻¹ : (MatrixProduct' (ι:=ι))ˣ) : MatrixProduct' (ι:=ι)) b*
    (M : MatrixProduct' (ι:=ι)) b=1 at hi
  simpa only [Pi.mul_apply,Matrix.mul_assoc,hi,Matrix.mul_one,Matrix.smul_mul,
    Matrix.one_mul] using h

end HarmonicCounterexample.FiniteControl.Frobenius

end

noncomputable section

namespace HarmonicCounterexample.FiniteControl.Frobenius
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius Topology
variable {β : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nonempty (ι b)]

def translatedProjection (M : (MatrixProduct' (ι:=ι))ˣ) :
    MatrixProduct' (ι:=ι) →L[ℝ] tracefreeProduct' (ι:=ι) :=
  (tracefreeProjection (ι:=ι)).toContinuousLinearMap.comp
    ((ContinuousLinearMap.mul ℝ (MatrixProduct' (ι:=ι))).flip (↑M⁻¹))

lemma translatedProjection_apply (M : (MatrixProduct' (ι:=ι))ˣ)
    (X : MatrixProduct' (ι:=ι)) :
    translatedProjection M X=tracefreeProjection (X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) := rfl

lemma positive_trace_neighborhood (M : (MatrixProduct' (ι:=ι))ˣ) :
    IsOpen {X : MatrixProduct' (ι:=ι) | ∀ b,0 < ((X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b).trace} ∧
    (M : MatrixProduct' (ι:=ι)) ∈
      {X : MatrixProduct' (ι:=ι) | ∀ b,0 < ((X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b).trace} := by
  constructor
  · rw [show {X : MatrixProduct' (ι:=ι) | ∀ b,0 < ((X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b).trace}=
        (⋂ b,{X : MatrixProduct' (ι:=ι) | 0 < ((X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b).trace}) by ext X; simp]
    apply isOpen_iInter_of_finite
    intro b
    apply isOpen_lt continuous_const
    simp only [Matrix.trace]
    apply continuous_finsetSum
    intro i _
    apply Continuous.matrix_elem
    exact (continuous_apply b).comp (continuous_id.mul continuous_const)
  · intro b
    rw [Units.mul_inv]
    change 0 < (1 : Matrix (ι b) (ι b) ℝ).trace
    rw [Matrix.trace_one]
    exact Nat.cast_pos.2 Fintype.card_pos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance : NormedAddCommGroup (E →L[ℝ] MatrixProduct' (ι:=ι)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] MatrixProduct' (ι:=ι)) :=
  ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.FiniteControl.Frobenius

end

noncomputable section

namespace HarmonicCounterexample.FiniteControl.Frobenius
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius Topology
variable {β : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nonempty (ι b)]

def boundedScalarNeighborhood (M : (MatrixProduct' (ι:=ι))ˣ) : Set (MatrixProduct' (ι:=ι)) :=
  {X | ∀ b,meanTrace (X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b ∈ Set.Ioo (1/2:ℝ) (3/2)}

lemma boundedScalarNeighborhood_open (M : (MatrixProduct' (ι:=ι))ˣ) :
    IsOpen (boundedScalarNeighborhood M) ∧ (M : MatrixProduct' (ι:=ι)) ∈ boundedScalarNeighborhood M := by
  have hc (b : β) : Continuous (fun X : MatrixProduct' (ι:=ι) =>
      meanTrace (X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b) := by
    apply Continuous.div_const
    simp only [Matrix.trace]
    apply continuous_finsetSum
    intro i _
    apply Continuous.matrix_elem
    exact (continuous_apply b).comp (continuous_id.mul continuous_const)
  constructor
  · rw [show boundedScalarNeighborhood M=⋂ b,{X | meanTrace (X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b ∈ Set.Ioo (1/2:ℝ) (3/2)} by ext X;simp [boundedScalarNeighborhood]]
    exact isOpen_iInter_of_finite fun b => isOpen_Ioo.preimage (hc b)
  · intro b
    rw [Units.mul_inv]
    have hn : (Fintype.card (ι b):ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    norm_num [meanTrace,hn]

lemma bounded_scalar_target {X : MatrixProduct' (ι:=ι)} (M : (MatrixProduct' (ι:=ι))ˣ)
    (hX : translatedProjection M X=0) (hU : X ∈ boundedScalarNeighborhood M) :
    ∀ b,∃ c : ℝ,c ∈ Set.Ioo (1/2:ℝ) (3/2) ∧ X b=c • ((M : MatrixProduct' (ι:=ι)) b) := by
  intro b
  refine ⟨meanTrace (X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b,hU b,?_⟩
  change tracefreeProjection (X*(↑M⁻¹ : MatrixProduct' (ι:=ι)))=0 at hX
  have he := (tracefreeProjection_zero_iff _).1 hX b
  have h := congrArg (fun A : Matrix (ι b) (ι b) ℝ => A*((M : MatrixProduct' (ι:=ι)) b)) he
  have hi := congrFun M.inv_val b
  change (↑M⁻¹ : MatrixProduct' (ι:=ι)) b*(M : MatrixProduct' (ι:=ι)) b=1 at hi
  simpa only [Pi.mul_apply,Matrix.mul_assoc,hi,Matrix.mul_one,Matrix.smul_mul,Matrix.one_mul] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance : NormedAddCommGroup (E →L[ℝ] MatrixProduct' (ι:=ι)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] MatrixProduct' (ι:=ι)) :=
  ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.FiniteControl.Frobenius

end

noncomputable section

namespace HarmonicCounterexample.FiniteControl.Frobenius
open Matrix HarmonicCounterexample.Transmission
open scoped BigOperators Matrix.Norms.Frobenius Topology
variable {β : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nonempty (ι b)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] MatrixProduct' (ι:=ι)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] MatrixProduct' (ι:=ι)) := ContinuousLinearMap.toNormedSpace

omit [∀ (b : β), Nonempty (ι b)] in
/-- Cancellation of the factor of the ENTIRE diagonal leg gives the exact
chronological target c D M. No exponentially anisotropic conjugation occurs. -/
lemma whole_period_exact_leg {U V P B : MatrixProduct' (ι:=ι)} {θ : ℝ}
    (D M : (MatrixProduct' (ι:=ι))ˣ) (hD : (D:MatrixProduct' (ι:=ι))=U+θ • V)
    (hatt : ∀ b,∃ c : ℝ,c ∈ Set.Ioo (1/2:ℝ) (3/2) ∧
      wholePeriod ((↑D⁻¹:MatrixProduct' (ι:=ι))*V) (P-θ • 1) B b=
        c • ((M:MatrixProduct' (ι:=ι)) b)) :
    ∀ b,∃ c : ℝ,c ∈ Set.Ioo (1/2:ℝ) (3/2) ∧
      ((U+V*P)*B) b=c • (((D:MatrixProduct' (ι:=ι))*(M:MatrixProduct' (ι:=ι))) b) := by
  intro b
  obtain ⟨c,hc,he⟩ := hatt b
  refine ⟨c,hc,?_⟩
  have hf := full_leg_factor U V P B θ D hD
  change (↑D⁻¹:MatrixProduct' (ι:=ι))*((U+V*P)*B)=wholePeriod ((↑D⁻¹:MatrixProduct' (ι:=ι))*V) (P-θ • 1) B at hf
  have hh := congrArg (fun X : MatrixProduct' (ι:=ι) => ((D:MatrixProduct' (ι:=ι))*X) b) hf
  rw [← mul_assoc,Units.mul_inv,one_mul] at hh
  rw [hh]
  change (D:MatrixProduct' (ι:=ι)) b*wholePeriod ((↑D⁻¹:MatrixProduct' (ι:=ι))*V) (P-θ • 1) B b=_
  rw [he,Matrix.mul_smul]
  rfl

end HarmonicCounterexample.FiniteControl.Frobenius

end

noncomputable section

namespace HarmonicCounterexample.FiniteControl
open SmoothWord Frobenius
open scoped ContDiff Matrix.Norms.Frobenius
attribute [local instance 100] LieRing.ofAssociativeRing
variable {β κ : Type*} [Fintype β] [Nonempty κ] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]

end HarmonicCounterexample.FiniteControl

end

end OAI
