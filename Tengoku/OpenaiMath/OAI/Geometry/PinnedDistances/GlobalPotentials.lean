import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.MinPotentials

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

def placeUnion : Finset (NumberField.FinitePlace K)  := by
  classical
  exact badPlaces Z₁ h₁ ∪ badPlaces Z₂ h₂

def average (f : Depth P → Depth P → ℝ) : ℝ :=
  (∑ v : NumberField.InfinitePlace K, Arithmetic.archWeight v *
    ∫ ω, f (arch Z₁ v ω) (arch Z₂ v ω) ∂Grid.fullLaw) +
  (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ placeUnion Z₁ Z₂ h₁ h₂,
    f (finite Z₁ h₁ v) (finite Z₂ h₂ v)

def AverageIntegrable (f : Depth P → Depth P → ℝ) : Prop :=
  ∀ v : NumberField.InfinitePlace K,
    Integrable (fun ω => f (arch Z₁ v ω) (arch Z₂ v ω)) Grid.fullLaw

lemma average_mono {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g)
    (hfg : ∀ d d', f d d'≤g d d') :
    average Z₁ Z₂ h₁ h₂ f≤average Z₁ Z₂ h₁ h₂ g  := by
  classical
  apply add_le_add
  · apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (integral_mono (hi v) (hj v) (fun ω => hfg _ _))
      (Arithmetic.archWeight_nonneg v)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun v _ => hfg _ _)

lemma average_add {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => f d d'+g d d')=
      average Z₁ Z₂ h₁ h₂ f+average Z₁ Z₂ h₁ h₂ g  := by
  classical
  unfold average
  simp only [integral_add (hi _) (hj _),mul_add,Finset.sum_add_distrib]
  ring

lemma average_mul (f : Depth P → Depth P → ℝ) (c : ℝ) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => c*f d d')=c*average Z₁ Z₂ h₁ h₂ f  := by
  classical
  unfold average
  simp only [integral_const_mul,Finset.mul_sum,mul_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro v _ <;> ring

lemma average_sum {J : Type u3} [Fintype J] (f : J → Depth P → Depth P → ℝ)
    (hi : ∀ j, AverageIntegrable Z₁ Z₂ (f j)) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => ∑ j, f j d d')=
      ∑ j, average Z₁ Z₂ h₁ h₂ (f j)  := by
  classical
  unfold average
  simp_rw [integral_finsetSum _ (fun j _ => hi j _),Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_comm (s:=placeUnion Z₁ Z₂ h₁ h₂)]
  simp only [Finset.sum_add_distrib]

lemma average_potential_left (hn : 2≤Fintype.card P) (x : P) :
    average Z₁ Z₂ h₁ h₂ (fun d _ => d.potential x)=S Z₁ h₁ x  := by
  classical
  unfold average S
  congr 2
  exact sum_finite_potential h₁ hn _ Finset.subset_union_left x

lemma average_potential_right (hn : 2≤Fintype.card P) (x : P) :
    average Z₁ Z₂ h₁ h₂ (fun _ d' => d'.potential x)=S Z₂ h₂ x  := by
  classical
  unfold average S
  congr 2
  exact sum_finite_potential h₂ hn _ Finset.subset_union_right x

lemma average_mass_left (hn : 2≤Fintype.card P) (C : Finset P) :
    average Z₁ Z₂ h₁ h₂ (fun d _ => d.mass C)=cellMass Z₁ h₁ C  := by
  classical
  unfold average cellMass
  congr 2
  exact sum_finite_mass h₁ hn _ Finset.subset_union_left C

lemma average_mass_right (hn : 2≤Fintype.card P) (C : Finset P) :
    average Z₁ Z₂ h₁ h₂ (fun _ d' => d'.mass C)=cellMass Z₂ h₂ C  := by
  classical
  unfold average cellMass
  congr 2
  exact sum_finite_mass h₂ hn _ Finset.subset_union_right C

end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable {K : Type u5} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit Z₁ Z₂ h₁ h₂ in
def potentialEval (p : P → ℝ) (d d' : Depth P) : ℝ := ∑ y, p y*(d.potential y+d'.potential y)
omit Z₁ Z₂ h₁ h₂ in
def massEval (q : Finset P → ℝ) (d d' : Depth P) : ℝ :=
  weightedIntegral d.mass q+weightedIntegral d'.mass q

omit Z₁ Z₂ h₁ h₂ in
lemma massEval_edge {I : Type u6} [Fintype I] (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (d d' : Depth P) :
    massEval (SmallFiber.edgeCell w p x) d d'=
      ∑ i, w i*∑ y, p i y*(weightedOverlap d.mass (x i) y+weightedOverlap d'.mass (x i) y) := by
  have he (m : Finset P → ℝ) : weightedIntegral m (SmallFiber.edgeCell w p x)=
      ∑ i, w i*∑ y, p i y*weightedOverlap m (x i) y := by
    unfold SmallFiber.edgeCell
    rw [weighted_pair]
    unfold SmallFiber.edgeLaw
    simp only [Finset.sum_mul]
    calc
      _ = ∑ a, ∑ i, ∑ y, (if x i=a then w i*p i y else 0)*weightedOverlap m a y := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ y, (if x i=a then w i*p i y else 0)*weightedOverlap m a y := Finset.sum_comm
      _ = _ := by
        simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
        simp [Finset.mul_sum,mul_assoc]
  -- commute the source sum after inserting the indicator
  simp only [massEval,he,mul_add,Finset.sum_add_distrib]
end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u7} {I : Type u8} [Fintype P] [DecidableEq P] [Fintype I]
variable {K : Type u9} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit Z₁ Z₂ h₁ h₂ in
lemma potentialEval_mixture (w : I → ℝ) (p : I → P → ℝ) (d d' : Depth P) :
    potentialEval (fun y => ∑ i, w i*p i y) d d'=∑ i, w i*∑ y, p i y*(d.potential y+d'.potential y) := by
  simp only [potentialEval,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

lemma average_sub {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => f d d'-g d d')=
      average Z₁ Z₂ h₁ h₂ f-average Z₁ Z₂ h₁ h₂ g := by
  classical
  unfold average
  simp only [integral_sub (hi _) (hj _),mul_sub,Finset.sum_sub_distrib]
  ring

end WeakPinned.Global

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u10} [Fintype P] [DecidableEq P]

/-- Nonnegative additive off-diagonal overlap controls the potential at every
vertex, not merely at vertices typical for the edge marginal. -/
lemma point_potential_lower (m : Finset P → ℝ) (b : ℝ) (S : P → ℝ)
    (hm : ∀ C : Finset P, (0 : ℝ) ≤ m C) (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y)
    (hn : 3≤Fintype.card P) (x : P) :
    (∑ y, prob Finset.univ y*S y)-2*weightedIntegral m (pairCell Finset.univ)≤S x := by
  let n : ℝ := Fintype.card P
  have hn3 : 3≤n := by dsimp [n]; exact_mod_cast hn
  have hn0 : n≠0 := by linarith
  let A : ℝ := (∑ y, prob Finset.univ y*S y)
  let W : ℝ := weightedIntegral m (pairCell Finset.univ)
  have hW : 0≤W := Finset.sum_nonneg (fun C _ => mul_nonneg (hm C) (pairCell_nonneg _ _))
  have hu : W=b+2*A := uniform_additive m b S hL (by omega)
  have hs : (∑ y, S y)=n*A := by
    dsimp [A,prob,n]
    simp only [Finset.mem_univ,ite_true]
    rw [← Finset.mul_sum]
    have hn0' : (Fintype.card P : ℝ) ≠ 0 := hn0
    field_simp
  have hnn : 0 ≤ ∑ y ∈ Finset.univ.erase x, (b+S x+S y) := by
    apply Finset.sum_nonneg
    intro y hy
    rw [← hL x y (Finset.ne_of_mem_erase hy).symm]
    exact Finset.sum_nonneg (fun C _ => mul_nonneg (hm C) (by dsimp; split_ifs <;> norm_num))
  have hsx : (∑ y ∈ Finset.univ.erase x, S y)=(∑ y, S y)-S x := by
    exact eq_sub_of_add_eq (Finset.sum_erase_add Finset.univ S (Finset.mem_univ x))
  have hcount : ((Finset.univ.erase x).card:ℝ)=n-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,Nat.cast_sub (by omega),Nat.cast_one]
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hcount,hsx,hs] at hnn
  change A-2*W≤S x
  nlinarith [mul_nonneg (by linarith : 0≤n-3) hW]

end WeakPinned.Variance

namespace WeakPinned
open Global Variance
open scoped BigOperators
variable {P : Type u11} {I : Type u12} [Fintype P] [Fintype I] [DecidableEq P]
variable {K : Type u13} [Field K] [NumberField K]

end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology

/-- Elementary absorption of the two asymptotically small errors. -/
lemma scale_balance_rate (W A V δ : ℕ → ℝ) (B : ℝ) (hB : 0≤B)
    (hW : ∀ j, 0≤W j) (hA : ∀ j, 0≤A j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hV : Tendsto (fun j => V j/(W j+A j+1)) atTop (𝓝 0))
    (hbal : ∀ᶠ j in atTop, (1-δ j)*A j≤4*V j+(10+B)*W j+16) :
    ∀ᶠ j in atTop, A j≤(64+4*B)*(W j+1) := by
  filter_upwards [hbal,hδ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4)),
    hV.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/16))] with j hb hd hv
  have hden : 0<W j+A j+1 := by linarith [hW j,hA j]
  have hv' := (div_lt_iff₀ hden).mp hv
  nlinarith [hW j,hA j,mul_nonneg (hW j) hB]
end WeakPinned

namespace WeakPinned
open Global Variance Filter
open scoped Topology BigOperators
variable {V : ℕ → Type u14} {I : ℕ → Type u15} {K : ℕ → Type u16} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

end WeakPinned

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
