import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Graded.FiniteVectorGrading

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The grading of a finite family of labelled coordinate spaces -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded.VectorGrading
variable {k ι : Type*} [Field k] [Fintype ι]
variable (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable (degree : ι → ℤ)

/-- Vectors supported on the coordinates carrying one prescribed degree.-/
def coordinateComponent (d : ℤ) : Submodule k (∀ i, V i) where
  carrier := {x | ∀ i, degree i ≠ d → x i = 0}
  zero_mem' := fun _ _ ↦ rfl
  add_mem' := by intro x y hx hy i hi; change x i + y i = 0; rw [hx i hi, hy i hi, add_zero]
  smul_mem' := by intro c x hx i hi; change c • x i = 0; rw [hx i hi, smul_zero]

/-- Keep only coordinates of one degree.-/
def coordinateProjection (d : ℤ) : (∀ i, V i) →ₗ[k] (∀ i, V i) := by
  classical
  exact
    { toFun := fun x i ↦ if degree i = d then x i else 0
      map_add' := by intro x y; funext i; by_cases h : degree i = d <;> simp [h]
      map_smul' := by intro c x; funext i; by_cases h : degree i = d <;> simp [h] }

/--
@isnad1 id=mem.0h6v.s8.cc5e5c46497e from=translated src=- shape=b0982bba vocab=87f68645
-/
theorem coordinateProjection_mem (d : ℤ) (x : ∀ i, V i) :
    coordinateProjection (k := k) V degree d x ∈ coordinateComponent (k := k) V degree d := by
  intro i hi
  simp only [coordinateProjection, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hi]

/--
@isnad1 id=eq.1h6v.s8.1a4a32c782bc from=translated src=- shape=5ef09ad6 vocab=87f68645
-/
theorem coordinateProjection_of_mem {d : ℤ} {x : ∀ i, V i}
    (hx : x ∈ coordinateComponent (k := k) V degree d) : coordinateProjection (k := k) V degree d x = x := by
  classical
  funext i
  by_cases hi : degree i = d
  · simp [coordinateProjection, hi]
  · simp [coordinateProjection, hi, hx i hi]

/--
@isnad1 id=eq.2h7v.s8.35899feaa17a from=translated src=- shape=af950aa8 vocab=87f68645
-/
theorem coordinateProjection_of_mem_ne {d n : ℤ} {x : ∀ i, V i}
    (hx : x ∈ coordinateComponent (k := k) V degree d) (hdn : d ≠ n) :
    coordinateProjection (k := k) V degree n x = 0 := by
  classical
  funext i
  by_cases hi : degree i = n
  · have hid : degree i ≠ d := by intro h; exact hdn (h.symm.trans hi)
    simp [coordinateProjection, hi, hx i hid]
  · simp [coordinateProjection, hi]

/--
@isnad1 id=eq.0h5v.s8.12e2b32aa865 from=translated src=- shape=987ba570 vocab=df7ec5f4
-/
theorem sum_coordinateProjection (x : ∀ i, V i) :
    ∑ d ∈ Finset.univ.image degree, coordinateProjection (k := k) V degree d x = x := by
  classical
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single (degree i)]
  · simp [coordinateProjection]
  · intro d hd hdi
    simp [coordinateProjection, Ne.symm hdi]
  · intro hn
    exact (hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).elim

/-- Grouping a finite product's coordinate spaces by their labels is an internal grading.-/
def coordinateGrading : VectorGrading k (∀ i, V i) where
  component := coordinateComponent (k := k) V degree
  internal := by
    classical
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_def]
      intro d
      have hk : (⨆ n, ⨆ (_ : n ≠ d), coordinateComponent (k := k) V degree n) ≤
          LinearMap.ker (coordinateProjection (k := k) V degree d) := by
        apply iSup_le
        intro n
        apply iSup_le
        intro hnd x hx
        exact coordinateProjection_of_mem_ne (k := k) V degree hx hnd
      apply Submodule.disjoint_def.mpr
      intro x hx hy
      have hz := hk hy
      change coordinateProjection (k := k) V degree d x = 0 at hz
      rw [coordinateProjection_of_mem (k := k) V degree hx] at hz
      exact hz
    · apply top_unique
      intro x hx
      rw [← sum_coordinateProjection (k := k) V degree x]
      apply Submodule.sum_mem
      intro d hd
      exact (le_iSup (coordinateComponent (k := k) V degree) d) (coordinateProjection_mem (k := k) V degree d x)

end MagnitudeConjecture.Graded.VectorGrading
