import Tengoku.OpenaiMath.OAI.Analysis.BackwardIntertwiners.PolarDiagonals

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def polarAlgebra : StarSubalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) := strongGenerated (Set.range polarDiagonal)

lemma halfExponent_eq_ten_iff (t : ℕ → ℕ) (k : ℕ) : halfExponent t k=10 ↔ k=0 := by
  constructor
  · intro h
    have hl := halfExponent_lower t k
    rw [h] at hl
    have hk : (k:ℝ)=0 := by have := Nat.cast_nonneg (α:=ℝ) k; nlinarith
    exact_mod_cast hk
  · rintro rfl
    simp [halfExponent,residueCorrection]
lemma explicitBeta_central (x : Base) (j : ℤ) : explicitBeta x j=Real.exp (-10) ↔ j=-1 ∨ j=0 := by
  have hh (t : ℕ → ℕ) (k : ℕ) : Real.exp (-halfExponent t k)=Real.exp (-10) ↔ k=0 := by
    rw [Real.exp_eq_exp,neg_inj,halfExponent_eq_ten_iff]
  cases j with
  | ofNat k =>
    change Real.exp (-halfExponent (plusResidue x) k)=Real.exp (-10) ↔ _
    rw [hh]
    change k=0 ↔ (k:ℤ) = -1 ∨ (k:ℤ) = 0
    omega
  | negSucc k =>
    change Real.exp (-halfExponent (minusResidue x) k)=Real.exp (-10) ↔ _
    rw [hh]
    omega

def rectangleProjection (r : ℤ) (E : Set Base) (hE : MeasurableSet E) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  diagonalProjection (fun j => if j=r then E else ∅) (fun j => by split_ifs; exact hE; exact MeasurableSet.empty)

def blockAnchor (m : ℕ) : ℕ := 8^(m-1)
lemma blockAnchor_ne_zero (m : ℕ) : blockAnchor m ≠ 0 := pow_ne_zero _ (by norm_num)
lemma blockAnchor_block {m : ℕ} (hm : 1 ≤ m) : weightBlock (blockAnchor m)=m := by
  rw [weightBlock,blockAnchor,Nat.log_pow (by norm_num : 1<8)]
  omega
def residueEigenvalue (m t : ℕ) : ℝ :=
  Real.exp (-(10*((blockAnchor m:ℝ)+1)+100*((2^m:ℝ)-2+(t:ℝ))))
lemma beta_anchor_residue {m : ℕ} (hm : 1 ≤ m) (t : ℕ) (x : Base) :
    explicitBeta x (blockAnchor m) = residueEigenvalue m t ↔ residue m x=t := by
  change Real.exp (-halfExponent (plusResidue x) (blockAnchor m))=residueEigenvalue m t ↔ _
  rw [residueEigenvalue,Real.exp_eq_exp,neg_inj]
  simp only [halfExponent,residueCorrection,blockAnchor_ne_zero,↓reduceIte,
    residueScale,blockAnchor_block hm,plusResidue]
  push_cast
  constructor
  · intro h
    have he : (residue m x:ℝ)=(t:ℝ) := by linarith
    exact_mod_cast he
  · intro h
    rw [h]

lemma DiagonalSymbol.sum_apply {ι : Type*} (s : Finset ι) (a : ι → DiagonalSymbol) (x : Base) (j : ℤ) :
    (∑ i ∈ s, a i) x j = ∑ i ∈ s, a i x j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [Finset.sum_insert,hi,hs]

def simpleSliceSymbol (r : ℤ) (f : SimpleFunc Base ℂ) : DiagonalSymbol :=
  ∑ t ∈ f.range, t • projectionSymbol
    (fun j => if j=r then f ⁻¹' {t} else ∅)
    (fun j=>by split_ifs; exact f.measurableSet_fiber t; exact MeasurableSet.empty)
lemma simpleSliceSymbol_apply (r : ℤ) (f : SimpleFunc Base ℂ) (x : Base) (j : ℤ) :
    simpleSliceSymbol r f x j=if j=r then f x else 0 := by
  simp only [simpleSliceSymbol,DiagonalSymbol.sum_apply,DiagonalSymbol.smul_apply,projectionSymbol_apply]
  by_cases hj : j=r
  · simp only [hj,↓reduceIte,Set.mem_preimage,Set.mem_singleton_iff,mul_ite,mul_one,mul_zero]
    rw [Finset.sum_eq_single (f x)]
    · simp
    · intro b hb hbx
      simp [Ne.symm hbx]
    · exact fun hn => (hn (f.mem_range_self x)).elim
  · simp [hj]

def sliceSymbol (r : ℤ) (a : DiagonalSymbol) : DiagonalSymbol :=
  a * projectionSymbol (fun j=>if j=r then Set.univ else ∅) (fun j=>by split_ifs <;> measurability)
lemma sliceSymbol_apply (r : ℤ) (a : DiagonalSymbol) (x : Base) (j : ℤ) :
    sliceSymbol r a x j=if j=r then a x r else 0 := by
  by_cases hj : j=r <;> simp [sliceSymbol,hj]
lemma sliceSymbol_norm_le (r : ℤ) (a : DiagonalSymbol) (x : Base) (j : ℤ) :
    ‖sliceSymbol r a x j‖ ≤ a.bound := by
  rw [sliceSymbol_apply]
  split_ifs
  · exact a.norm_le_bound x r
  · simpa using a.bound_nonneg

lemma finiteSliceSymbol_apply (s : Finset ℤ) (a : DiagonalSymbol) (x : Base) (j : ℤ) :
    (∑ r ∈ s,sliceSymbol r a) x j=if j∈s then a x j else 0 := by
  rw [DiagonalSymbol.sum_apply]
  simp_rw [sliceSymbol_apply]
  simp

end
end BackwardIntertwiners

end OAI
