import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.CoordinateSplit

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.EuclideanCells
open MeasureTheory Set ProductSlice CellInterface CoordinateSplit
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m : ℕ} {I : Type u1} {A : Type u2} [Fintype I] [Fintype A] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin m)

def B (u : I → E) : I → Z →L[ℝ] ℝ := fun i => slope (u i)
def pivot (u : I → E) (i : I) : ℝ := u i 0

def values (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) : Finset (I × s) → A → ℝ :=
  extension (ell (B u) (pivot u)) (pivot u) τ s U F

def chartFunction (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) (a : A) : E → ℝ :=
  (cell (B u) (fun i (k : s) => -((k:ℤ)*τ/pivot u i)) (fun P => values u τ s U F P a)) ∘ split

lemma form_comp (u : E) (hu : u 0≠0) :
    (form (slope u)).comp split.toContinuousLinearMap=(u 0)⁻¹ • InnerProductSpace.toDual ℝ E u := by
  ext x
  have hh := normalized_form u hu x
  change (split x).1-slope u (split x).2=(u 0)⁻¹*inner ℝ u x
  rw [← hh,div_eq_mul_inv,mul_comm]

lemma kernel_split (φ : ℝ → ℝ) :
    (ProductMollifier.kernel (m := m+1) φ) ∘ split.symm =
      (fun p : ℝ × Z => φ p.1*ProductMollifier.kernel φ p.2) := by
  funext p
  simp [ProductMollifier.kernel,Fin.prod_univ_succ]

omit [Fintype A] [DecidableEq I] in
lemma chartFunction_eq (u : I → E) (hu : ∀ i, u i 0≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (hb : ∀ x∈U, regular (ell (B u) (pivot u)) τ x → ∀ i, label (ell (B u) (pivot u)) τ x i∈s)
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ)
    (x : E) (hx : split x∈U) (hr : regular (ell (B u) (pivot u)) τ (split x)) (a : A) :
    chartFunction u τ s U F a x=F (vertex (ell (B u) (pivot u)) τ (split x) hx hr) a := by
  change cell (B u) (fun i (k : s) => -((k:ℤ)*τ/pivot u i)) (fun P => extension (ell (B u) (pivot u)) (pivot u) τ s U F P a) (split x)=_
  rw [cell_eq_extension (B u) (pivot u) hu (F := F)]
  exact congrFun (extension_eq (ell (B u) (pivot u)) (pivot u) hu hτ s U hb F _ hx hr) a

omit [Fintype A] in
lemma chartFunction_measurable (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) (a : A) :
    Measurable (chartFunction u τ s U F a) :=
  (cell_measurable _ _ _).comp split.continuous.measurable

omit [Fintype A] in
lemma chartFunction_integrable (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) {M : ℝ} (hM : 0≤M)
    (hF : ∀ v a, |F v a|≤M) (a : A) : LocallyIntegrable (chartFunction u τ s U F a) := by
  apply (locallyIntegrable_const M).mono (chartFunction_measurable _ _ _ _ _ _).aestronglyMeasurable
  filter_upwards with x
  simpa only [chartFunction,Function.comp_apply,cell,values,Real.norm_eq_abs,abs_of_nonneg hM] using extension_bounded _ _ _ _ _ F hM hF _ a

end
end UniformSparsestCut.EuclideanCells

end

end OAI
