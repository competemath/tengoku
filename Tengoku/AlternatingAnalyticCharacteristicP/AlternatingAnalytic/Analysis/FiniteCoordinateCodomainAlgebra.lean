import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.LiftCriterion
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.FiniteCoordinateDeterminant
import Tengoku.Seed.LinearAlgebra.ExteriorPower.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The determinant lift for a finite basis of the codomain

The algebraic form of the determinant lift of Proposition 4.1(2), before norm estimates:
a multilinear map in the operators whose diagonal value is precomposition. It needs no
assumption on the characteristic.
-/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators
open Module

variable {K E E' F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  {d k : ℕ}

private theorem alternating_sum_apply {α : Type*} (s : Finset α)
    (g : α → E [⋀^Fin k]→ₗ[K] F) (x : Fin k → E) :
    (∑ a ∈ s, g a) x = ∑ a ∈ s, g a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AlternatingMap.add_apply, ih]

private theorem alternating_smulRight_apply (g : E [⋀^Fin k]→ₗ[K] K)
    (z : F) (x : Fin k → E) : g.smulRight z x = g x • z := rfl

/-- The determinant coefficient, as an alternating map in the vectors.-/
def finiteCoordinateCodomainScalar (b : Basis (Fin d) K E')
    (t : Fin k → Fin d) (f : Fin k → E →L[K] E') : E [⋀^Fin k]→ₗ[K] K :=
  Matrix.detRowAlternating.compLinearMap
    { toFun := fun x a => b.coord (t a) (f a x)
      map_add' := by intros; ext a; simp
      map_smul' := by intros; ext a; simp }

/--
@isnad1 id=eq.0h9v.s9.497e9837bb15 from=translated src=- shape=c329c0c3 vocab=011a738f
-/
theorem finiteCoordinateCodomainScalar_apply (b : Basis (Fin d) K E')
    (t : Fin k → Fin d) (f : Fin k → E →L[K] E') (x : Fin k → E) :
    finiteCoordinateCodomainScalar b t f x =
      Matrix.det (fun a j => b.coord (t a) (f a (x j))) := by
  change Matrix.det (Matrix.transpose (fun a j => b.coord (t a) (f a (x j)))) = _
  exact Matrix.det_transpose _

/-- The same coefficient, as a multilinear map in the operators.-/
def finiteCoordinateCodomainRows (b : Basis (Fin d) K E')
    (t : Fin k → Fin d) (x : Fin k → E) :
    MultilinearMap K (fun _ : Fin k => E →L[K] E') K :=
  Matrix.detRowAlternating.toMultilinearMap.compLinearMap fun a =>
    { toFun := fun f j => b.coord (t a) (f (x j))
      map_add' := by intros; ext j; simp
      map_smul' := by intros; ext j; simp }

/--
@isnad1 id=eq.0h9v.s10.885e888c7920 from=translated src=- shape=fb18bd20 vocab=8b8026de
-/
theorem finiteCoordinateCodomainRows_apply (b : Basis (Fin d) K E')
    (t : Fin k → Fin d) (x : Fin k → E) (f : Fin k → E →L[K] E') :
    finiteCoordinateCodomainRows b t x f =
      Matrix.det (fun a j => b.coord (t a) (f a (x j))) := rfl

/-- For fixed operators, the determinant formula is linear in the input form.-/
def finiteCoordinateCodomainFamily (b : Basis (Fin d) K E') (k : ℕ)
    (f : Fin k → E →L[K] E') :
    (E' [⋀^Fin k]→L[K] F) →ₗ[K] (E [⋀^Fin k]→ₗ[K] F) where
  toFun m := ∑ s : Set.powersetCard (Fin d) k,
    (finiteCoordinateCodomainScalar b (Set.powersetCard.ofFinEmbEquiv.symm s) f).smulRight
      (m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a)))
  map_add' := by
    intros m n
    ext x
    simp [alternating_sum_apply, Finset.sum_add_distrib, smul_add]
  map_smul' := by
    intros c m
    ext x
    simp only [alternating_sum_apply, alternating_smulRight_apply,
      ContinuousAlternatingMap.smul_apply, AlternatingMap.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro s _
    exact smul_comm _ _ _

/--
@isnad1 id=eq.0h10v.s11.202df2ee1324 from=translated src=- shape=9ca3dd9e vocab=61514101
-/
theorem finiteCoordinateCodomainFamily_apply (b : Basis (Fin d) K E') (k : ℕ)
    (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    finiteCoordinateCodomainFamily b k f m x =
      ∑ s : Set.powersetCard (Fin d) k,
        Matrix.det (fun a j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s a)
          (f a (x j))) • m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a)) := by
  simp [finiteCoordinateCodomainFamily, alternating_sum_apply,
    finiteCoordinateCodomainScalar_apply]

/-- The algebraic lift, multilinear in the operators.-/
def finiteCoordinateCodomainAlgebra (b : Basis (Fin d) K E') (k : ℕ) :
    MultilinearMap K (fun _ : Fin k => E →L[K] E')
      ((E' [⋀^Fin k]→L[K] F) →ₗ[K] (E [⋀^Fin k]→ₗ[K] F)) where
  toFun := finiteCoordinateCodomainFamily b k
  map_update_add' := by
    intros _ f i g h
    ext m x
    simp only [finiteCoordinateCodomainFamily_apply, LinearMap.add_apply,
      AlternatingMap.add_apply]
    simp_rw [← finiteCoordinateCodomainRows_apply,
      MultilinearMap.map_update_add, add_smul, Finset.sum_add_distrib]
  map_update_smul' := by
    intros _ f i c g
    ext m x
    simp only [finiteCoordinateCodomainFamily_apply, LinearMap.smul_apply,
      AlternatingMap.smul_apply]
    simp only [← finiteCoordinateCodomainRows_apply,
      MultilinearMap.map_update_smul, smul_smul, Finset.smul_sum, smul_eq_mul]

/--
@isnad1 id=eq.0h10v.s12.901cd3ca40bf from=translated src=- shape=ab2c0e63 vocab=3f004012
-/
theorem finiteCoordinateCodomainAlgebra_apply (b : Basis (Fin d) K E') (k : ℕ)
    (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    finiteCoordinateCodomainAlgebra b k f m x =
      ∑ s : Set.powersetCard (Fin d) k,
        Matrix.det (fun a j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s a)
          (f a (x j))) • m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a)) :=
  finiteCoordinateCodomainFamily_apply b k f m x

/-- The lifted map vanishes when two inputs are equal.
@isnad1 id=eq.2h12v.s12.10bc14070b51 from=translated src=- shape=384bc5f5 vocab=597396e9
-/
theorem finiteCoordinateCodomainAlgebra_map_eq_zero_of_eq
    (b : Basis (Fin d) K E') (k : ℕ) (f : Fin k → E →L[K] E')
    (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) {i j : Fin k}
    (h : x i = x j) (hij : i ≠ j) : finiteCoordinateCodomainAlgebra b k f m x = 0 :=
  (finiteCoordinateCodomainAlgebra b k f m).map_eq_zero_of_eq x h hij

end AlternatingAnalytic
