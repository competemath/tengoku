import Tengoku.OpenaiMath.OAI.Geometry.LatticeCovering.PrimeKernels

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
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology AffineVoid ConvexGrid BrokenCircuit PrimeCircuit
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

def liftCoeff {p : ℕ} (a : Fin n → ZMod p) : Fin (n+1) → ℤ :=
  Fin.cons 0 (fun j => (a j).val)

lemma modForm_liftCoeff (p : ℕ) (hp : 0<p) (a : Fin n → ZMod p) (z : Fin (n+1) → ℤ) :
    modForm p 0 (liftCoeff a) z = (z 0 : ZMod p)+
      ∑ j, (z j.succ : ZMod p)*a j := by
  let : NeZero p := ⟨hp.ne'⟩
  change (z 0 : ZMod p) +
    (∑ j ∈ Finset.univ.erase 0, (liftCoeff a j : ZMod p)*(z j : ZMod p)) = _
  congr 1
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp [liftCoeff,Fin.sum_univ_succ,mul_comm]

def finResidue (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun b := (b.val:ZMod p)
  invFun b := ⟨b.val,ZMod.val_lt b⟩
  left_inv b := by apply Fin.ext; simp [ZMod.val_natCast,Nat.mod_eq_of_lt b.isLt]
  right_inv b := ZMod.natCast_zmod_val b

lemma card_badOffsets (p : ℕ) [Fact p.Prime] (a : Fin n → ZMod p)
    (S : Finset (Fin (n+1) → ℤ)) :
    ((badOffsets p 0 (liftCoeff a) S).card:ℝ) =
      ∑ b : ZMod p, normalizedMiss (fun z : S => fun j => (z.val j:ZMod p)) a b := by
  classical
  unfold badOffsets
  rw [←Finset.sum_boole]
  apply Fintype.sum_equiv (finResidue p)
  intro b
  unfold normalizedMiss
  congr 1
  apply propext
  simp only [finResidue,Equiv.coe_fn_mk,Subtype.forall,modForm_liftCoeff p (Nat.Prime.pos Fact.out),mul_comm]

abbrev ensembleFull (p : ℕ) (hp : 0<p) (a : Fin n → ZMod p) : Horizontal.FullLattice (n+1) :=
  normalizedFull p hp 0 (liftCoeff a)

def meanPrimeHole (J : Set (Fin (n+1) → ℝ)) (p : ℕ) [Fact p.Prime] : ℝ :=
  (∑ a : Fin n → ZMod p, ((ensembleFull p (Nat.Prime.pos Fact.out) a).hole J).toReal)/(p:ℝ)^n

lemma fintype_sum_irrel {A M : Type*} [AddCommMonoid M] (I₁ I₂ : Fintype A)
    (f g : A → M) (h : ∀ a, f a=g a) :
    @Finset.sum A M _ (@Finset.univ A I₁) f =
    @Finset.sum A M _ (@Finset.univ A I₂) g := by
  have he : I₁=I₂ := Subsingleton.elim _ _
  subst I₂
  exact @Fintype.sum_congr A M I₁ _ f g h

lemma fullMiss_eq_avoidance {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {σ : Type*} [Fintype σ] (v : σ → Fin (n+1) → K) (w : Fin (n+2) → K) :
    fullMiss v w=avoidanceIndicator (fun z => Fin.cons 1 (v z)) (dotProductBilin K K w) := by
  classical
  have he (i : σ) : (∑ j, w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j) =
      (dotProductBilin K K w) (Fin.cons 1 (v i)) := by
    change (∑ j : Fin (n+2), w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j) =
      ∑ j : Fin (n+2), w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j
    exact fintype_sum_irrel _ _ _ _ (fun j => rfl)
  unfold fullMiss avoidanceIndicator
  split_ifs with h₁ h₂ h₂
  · rfl
  · exfalso
    apply h₂
    intro i
    exact (he i).symm ▸ h₁ i
  · exfalso
    apply h₁
    intro i
    exact (he i) ▸ h₂ i
  · rfl

lemma meanFull_generic {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {σ : Type*} [Fintype σ] (v : σ → Fin (n+1) → K) :
    meanFull v=vectorAverage (fun w : Fin (n+2) → K =>
      avoidanceIndicator (fun z => Fin.cons 1 (v z)) (dotProductBilin K K w)) := by
  classical
  unfold meanFull vectorAverage
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  apply congrArg (fun t : ℝ => t/(Fintype.card K:ℝ)^(n+2))
  exact fintype_sum_irrel _ _ _ _ (fullMiss_eq_avoidance v)

lemma scaleFactor_eq_primeScale_inv (d p : ℕ) :
    scaleFactor (ι:=Fin d) p=(primeScale d p)⁻¹ := by
  simp only [scaleFactor,Fintype.card_fin,primeScale]
  exact Real.rpow_neg (Nat.cast_nonneg _) _

lemma gridMap_eq_scaledIntegerPoint (d p : ℕ) (hp : 0<p) (z : Fin d → ℤ) :
    gridMap p hp z=scaledIntegerPoint (primeScale d p) z := by
  ext j
  change scaleFactor (ι:=Fin d) p*(z j:ℝ)=_
  rw [scaleFactor_eq_primeScale_inv]
  rfl

lemma gridUnitCell_norm_le {d : ℕ} {u : Fin d → ℝ} (hu : u ∈ gridUnitCell) : ‖u‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro j
  have hh := (Set.mem_pi.mp hu) j (Set.mem_univ _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2.le

end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.AffineVoid
open Filter Topology
lemma conditioning_factor_tendsto :
    Tendsto (fun p : ℕ => (p:ℝ)/((p:ℝ)-1)) atTop (𝓝 (1:ℝ)) := by
  have hden : Tendsto (fun p : ℕ => (p:ℝ)-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ => (p:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (b+1))] with p hp
    linarith
  have ht : Tendsto (fun p : ℕ => 1+((p:ℝ)-1)⁻¹) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,add_zero] using
      (tendsto_inv_atTop_zero.comp hden).const_add 1
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hn : (p:ℝ)-1 ≠ 0 := by linarith
  field_simp [hn]
  ring

lemma eventually_factor_mul_lt {A B : ℝ} (hAB : A<B) :
    ∀ᶠ p : ℕ in atTop, ((p:ℝ)/((p:ℝ)-1))*A < B := by
  have ht := conditioning_factor_tendsto.mul_const A
  rw [one_mul] at ht
  exact ht.eventually (gt_mem_nhds hAB)
end SingleLatticeCovering.AffineVoid

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology AffineVoid ConvexGrid RogersPreparation ConvexCore SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.Horizontal
open Set MeasureTheory Completion
open scoped Pointwise
lemma FullLattice.hole_vadd {d : ℕ} (L : FullLattice d)
    (v : Fin d → ℝ) (J : Set (Fin d → ℝ)) : L.hole (v+ᵥJ)=L.hole J := by
  have he : latticeProjection L.module '' (v+ᵥJ)=
      latticeProjection L.module v +ᵥ (latticeProjection L.module '' J) := by
    ext y
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨latticeProjection L.module x,⟨x,hx,rfl⟩,(map_add _ _ _).symm⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨v+x,⟨x,hx,rfl⟩,map_add _ _ _⟩
  unfold FullLattice.hole
  rw [he,←vadd_set_compl,measure_vadd]
end SingleLatticeCovering.Horizontal

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology AffineVoid ConvexGrid RogersPreparation ConvexCore SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma meanPrimeHole_vadd (v : Fin (n+1) → ℝ) (J : Set (Fin (n+1) → ℝ))
    (p : ℕ) [Fact p.Prime] : meanPrimeHole (v+ᵥJ) p=meanPrimeHole J p := by
  classical
  unfold meanPrimeHole
  simp only [Horizontal.FullLattice.hole_vadd]

end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology Horizontal ConvexGrid SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma ensembleFull_covolume (p : ℕ) (hp : 0 < p) (a : Fin n → ZMod p) :
    ZLattice.covolume (ensembleFull p hp a).module=1 :=
  covolume_normalized p hp 0 (liftCoeff a)

lemma meanPrimeHole_le_one (J : Set (Fin (n+1) → ℝ)) (p : ℕ) [Fact p.Prime] :
    meanPrimeHole J p ≤ 1 := by
  classical
  have hp : 0 < p := Nat.Prime.pos Fact.out
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  unfold meanPrimeHole
  apply (div_le_one (pow_pos hpR n)).mpr
  calc
    _ ≤ ∑ _a : Fin n → ZMod p, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hh : (ensembleFull p hp a).hole J ≤ 1 := by
        unfold FullLattice.hole
        exact prob_le_one
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hh
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,
      Fintype.card_fin,ZMod.card,nsmul_eq_mul,Nat.cast_pow,mul_one]

end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology Horizontal ConvexGrid SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

lemma exists_le_finite_average {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    ∃ a, f a ≤ (Fintype.card A : ℝ)⁻¹*∑ b, f b := by
  have hc : (Fintype.card A : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (∑ a : A, f a)=∑ _a : A, (Fintype.card A : ℝ)⁻¹*∑ b, f b := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]
  obtain ⟨a,_,ha⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := A)) he.le
  exact ⟨a,ha⟩

lemma weighted_meanPrimeHole_sample {I : Type*} [Fintype I]
    (p : ℕ) [Fact p.Prime] (J : I → Set (Fin (n+1) → ℝ)) (w : I → ℝ) :
    ∃ a : Fin n → ZMod p,
      (∑ i, w i*((ensembleFull p (Nat.Prime.pos Fact.out) a).hole (J i)).toReal) ≤
        ∑ i, w i*meanPrimeHole (J i) p := by
  classical
  obtain ⟨a,ha⟩ := exists_le_finite_average
    (fun a : Fin n → ZMod p => ∑ i, w i*((ensembleFull p (Nat.Prime.pos Fact.out) a).hole (J i)).toReal)
  refine ⟨a,ha.trans_eq ?_⟩
  rw [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold meanPrimeHole
  rw [←Finset.mul_sum]
  ring

end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open SimplexYoung Inputs Horizontal MeasureTheory Set
open scoped ENNReal BigOperators
variable {n : ℕ}

end SingleLatticeCovering.PrimeKernel

noncomputable section
namespace SingleLatticeCovering.Assembly
open PrimeKernel SimplexYoung MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal
open scoped BigOperators Pointwise ENNReal

end SingleLatticeCovering.Assembly

noncomputable section
namespace SingleLatticeCovering.Assembly
open PrimeKernel SimplexYoung MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal Inputs
open Filter Topology
open scoped BigOperators Pointwise ENNReal

end SingleLatticeCovering.Assembly

noncomputable section

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
end
end
end
end
end

end OAI
