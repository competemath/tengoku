import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.FiberOverlap

namespace OAI

universe u1 u2 u3

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

namespace WeakPinned.Grid
open MeasureTheory

lemma truncated_sum_bound (a b H : ℝ) :
    max (|a+b|-H) 0 ≤ 2*max (|a|-H/2) 0 + 2*max (|b|-H/2) 0 := by
  apply max_le
  · have ht := abs_add_le a b
    have h₁ := le_max_left (|a|-H/2) 0
    have h₂ := le_max_left (|b|-H/2) 0
    have h₃ := le_max_right (|a|-H/2) 0
    have h₄ := le_max_right (|b|-H/2) 0
    linarith
  · positivity

end WeakPinned.Grid

namespace WeakPinned.Global
open Hierarchy Variance SmallFiber
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]
variable {K : Type u3} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
include h₁ h₂

lemma finite_small_fiber (hn : 2 ≤ Fintype.card P) (v : FinitePlace K)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (t : I → K)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ))
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, (finite Z₁ h₁ v).mass C*slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, (finite Z₁ h₁ v).mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, (finite Z₁ h₁ v).potential y)+(∑ y, (finite Z₂ h₂ v).potential y)) +
      2*lam*B*(∑ C, (finite Z₂ h₂ v).mass C*pairCell Finset.univ C) := by
  have hb := local_small_fiber_reduced (finite Z₁ h₁ v) (finite Z₂ h₂ v) w p x hw hW hp hp1 hx hn
    (fun i => -Real.log (v (t i))) B τ lam 0 hB hlam hlam2 hτ hτ1 hτn (le_refl _) hdom
  have he (i : I) (y : P) : p i y * max (|(finite Z₁ h₁ v).value (x i) y+
      (finite Z₂ h₂ v).value (x i) y- -Real.log (v (t i))|-0) 0=0 := by
    by_cases hy : p i y=0
    · simp [hy]
    · have hxy : x i ≠ y := by intro he; rw [← he,hx i] at hy; exact hy rfl
      have hh := Arithmetic.raw_fiber_identity v.val (Z₁ (x i)-Z₁ y) (Z₂ (x i)-Z₂ y)
        (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
      change -Real.log (v (Z₁ (x i)-Z₁ y)) + -Real.log (v (Z₂ (x i)-Z₂ y)) =
        -Real.log (v ((Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y))) at hh
      rw [ht i y hy] at hh
      simp only [finite,hxy,reduceIte,hh,sub_self,abs_zero,max_self,mul_zero]
  simpa only [he,Finset.sum_const_zero,mul_zero,add_zero] using hb

omit h₁ h₂ in
lemma finite_zero_outside {Z : P → K} (hZ : Function.Injective Z) (v : FinitePlace K)
    (hv : v ∉ badPlaces Z hZ) : ∀ a b, (finite Z hZ v).value a b=0 := by
  intro a b
  by_cases hab : a=b
  · simp [finite,hab]
  · have hunit : v (Z a-Z b)=1 := by
      by_contra h
      exact hv ((badPlaces_mem Z hZ v).mpr ⟨a,b,hab,h⟩)
    simp [finite,hab,hunit]

omit h₁ h₂ in
lemma finite_mass_zero {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (v : FinitePlace K) (hv : v ∉ badPlaces Z hZ) (C : Finset P) : (finite Z hZ v).mass C=0 := by
  have hz := (finite Z hZ v).zero_values hn (finite_zero_outside hZ v hv)
  by_cases hC : C.card ≤ 1
  · exact (finite Z hZ v).mass_singleton C hC
  · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1<C.card)
    have hl := (finite Z hZ v).mass_le_overlap hn C a b hab ha hb
    rw [hz.2.2 a b hab] at hl
    exact le_antisymm hl ((finite Z hZ v).mass_nonneg C)

omit h₁ h₂ in
lemma sum_finite_mass {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (C : Finset P) :
    (∑ v ∈ V, (finite Z hZ v).mass C) = ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).mass C := by
  symm
  exact Finset.sum_subset hV (fun v _ hv => finite_mass_zero hZ hn v hv C)

omit h₁ h₂ in
lemma sum_finite_potential {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (a : P) :
    (∑ v ∈ V, (finite Z hZ v).potential a) = ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential a := by
  symm
  exact Finset.sum_subset hV (fun v _ hv =>
    ((finite Z hZ v).zero_values hn (finite_zero_outside hZ v hv)).2.1 a)

omit h₁ h₂ in
def placeAverage (V : Finset (FinitePlace K)) (A : InfinitePlace K → ℝ) (F : FinitePlace K → ℝ) : ℝ :=
  (∑ v, Arithmetic.archWeight v * A v) + (Module.finrank ℚ K:ℝ)⁻¹ * ∑ v ∈ V, F v

omit h₁ h₂ in
lemma placeAverage_mono (V : Finset (FinitePlace K)) {A A' : InfinitePlace K → ℝ} {F F' : FinitePlace K → ℝ}
    (hA : ∀ v, A v ≤ A' v) (hF : ∀ v ∈ V, F v ≤ F' v) : placeAverage V A F ≤ placeAverage V A' F' := by
  apply add_le_add
  · exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hA v) (Arithmetic.archWeight_nonneg v))
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (by positivity)

omit h₁ h₂ in
lemma placeAverage_add (V : Finset (FinitePlace K)) (A A' : InfinitePlace K → ℝ) (F F' : FinitePlace K → ℝ) :
    placeAverage V (fun v => A v+A' v) (fun v => F v+F' v) = placeAverage V A F + placeAverage V A' F' := by
  simp only [placeAverage,mul_add,Finset.sum_add_distrib]
  ring

omit h₁ h₂ in
lemma placeAverage_mul (V : Finset (FinitePlace K)) (a : ℝ) (A : InfinitePlace K → ℝ) (F : FinitePlace K → ℝ) :
    placeAverage V (fun v => a*A v) (fun v => a*F v) = a*placeAverage V A F := by
  simp only [placeAverage,Finset.mul_sum,mul_add]
  congr 1
  · exact Finset.sum_congr rfl (fun v _ => by ring)
  · exact Finset.sum_congr rfl (fun v _ => by ring)

omit h₁ h₂ in
lemma placeAverage_arch_const (V : Finset (FinitePlace K)) (a : ℝ) :
    placeAverage V (fun _ => a) (fun _ => 0) = a := by
  simp only [placeAverage,Finset.sum_const_zero,mul_zero,add_zero,← Finset.sum_mul,Arithmetic.sum_archWeight,one_mul]

omit h₁ h₂ in
lemma cellIntegral_placeAverage {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (f : Finset P → ℝ) :
    weightedIntegral (cellMass Z hZ) f = placeAverage V
      (fun v => ∑ C, (∫ ω, (arch Z v ω).mass C ∂Grid.fullLaw)*f C)
      (fun v => ∑ C, (finite Z hZ v).mass C*f C) := by
  simp only [weightedIntegral,cellMass,placeAverage,add_mul,Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    exact Finset.sum_congr rfl (fun C _ => by ring)
  · rw [Finset.sum_comm (s:=V)]
    simp_rw [← Finset.sum_mul, sum_finite_mass hZ hn V hV,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun C _ => by rw [← Finset.mul_sum]; ring)

omit h₁ h₂ in
lemma potentialIntegral_placeAverage {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) :
    (∑ y, S Z hZ y) = placeAverage V
      (fun v => ∑ y, ∫ ω, (arch Z v ω).potential y ∂Grid.fullLaw)
      (fun v => ∑ y, (finite Z hZ v).potential y) := by
  simp only [S,placeAverage,Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm (s:=V)]
    simp_rw [sum_finite_potential hZ hn V hV,Finset.mul_sum]

end WeakPinned.Global

noncomputable section
open Filter
open scoped Topology

end
end
end
end
end
end
end

end OAI
