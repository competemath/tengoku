import Tengoku.NavierStokesEuler.Euler.ContinuousBoundedTensor
import Tengoku.NavierStokesEuler.Euler.SmoothTimeField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Continuous bounded coordinate fields reconstruct the actual tensor
field. This is a qualitative finite-dimensional construction; subsequent
norm estimates can use the actual tensor equality without a coordinate
reassembly constant. -/

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerBoundedTensorCoordinates

variable {K X E V ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace X] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (X →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (X →ᵇ (E [×n]→L[ℝ] V)) := inferInstance

def coordinates (b : Module.Basis ι ℝ E) (n : ℕ) :
    (E [×n]→L[ℝ] V) →L[ℝ] ((Fin n → ι) → V) :=
  ContinuousLinearMap.pi (fun w =>
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] V)).flipMultilinear (fun i => b (w i)))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [Fintype ι] in
/--
@isnad1 id=injectiv.0h5v.s9.6fd537e41275 from=translated src=- shape=a21913bb vocab=404cee27
-/
theorem coordinates_injective (b : Module.Basis ι ℝ E) (n : ℕ) :
    Function.Injective (coordinates (V := V) b n) := by
  intro A B h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin n => b)
  intro w
  exact congrFun h w

def reassembly (b : Module.Basis ι ℝ E) (n : ℕ) :
    ((Fin n → ι) → V) →L[ℝ] (E [×n]→L[ℝ] V) :=
  ((coordinates (V := V) b n).toLinearMap.leftInverse).toContinuousLinearMap

omit [FiniteDimensional ℝ E] in
/--
@isnad1 id=eq.0h6v.s10.5c9f8aa227f9 from=translated src=- shape=96550066 vocab=ac2c0622
-/
theorem reassembly_coordinates (b : Module.Basis ι ℝ E) (n : ℕ) (A : E [×n]→L[ℝ] V) :
    reassembly b n (coordinates b n A) = A :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (coordinates_injective b n)) A

def tupleBounded {j : Type*} [Fintype j] :
    (j → (X →ᵇ V)) →L[ℝ] (X →ᵇ (j → V)) := by
  classical
  exact ∑ i : j,
    ((ContinuousLinearMap.single ℝ (fun _ : j => V) i).compLeftContinuousBounded X).comp
      (ContinuousLinearMap.proj i)

omit [FiniteDimensional ℝ V] in
/--
@isnad1 id=eq.0h6v.s9.ad9a45df7e28 from=translated src=- shape=882b5a0b vocab=a0cb8b1c
-/
theorem tupleBounded_apply {j : Type*} [Fintype j]
    (u : j → (X →ᵇ V)) (x : X) (i : j) :
    tupleBounded u x i = u i x := by
  classical
  simp [tupleBounded]

def coordinatePath (b : Module.Basis ι ℝ E) (n : ℕ)
    (u : (Fin n → ι) → C(K, X →ᵇ V)) : C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toFun t := (reassembly (V := V) b n).compLeftContinuousBounded X
    (tupleBounded (fun w => u w t))
  continuous_toFun :=
    ((reassembly (V := V) b n).compLeftContinuousBounded X).continuous.comp
      ((tupleBounded (X := X) (V := V)).continuous.comp
        (continuous_pi (fun w => (u w).continuous)))

omit [CompactSpace K] [FiniteDimensional ℝ E] in
/--
@isnad1 id=eq.1h11v.s10.61fe04b6c982 from=translated src=- shape=3e5d92be vocab=23016182
-/
theorem coordinatePath_eq (b : Module.Basis ι ℝ E) (n : ℕ)
    (u : (Fin n → ι) → C(K, X →ᵇ V)) (t : K) (x : X)
    (A : E [×n]→L[ℝ] V) (hu : ∀ w, u w t x = A (fun i => b (w i))) :
    coordinatePath b n u t x = A := by
  change reassembly b n (tupleBounded _ x) = A
  have he : tupleBounded (fun w => u w t) x = coordinates b n A := by
    funext w
    rw [tupleBounded_apply]
    exact hu w
  rw [he, reassembly_coordinates]

end EulerBoundedTensorCoordinates

universe u

namespace SmoothTimeField

open EulerBoundedTensorCoordinates

variable {K E V ι : Type u} [TopologicalSpace K] [CompactSpace K] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def ofCoordinateJets (b : Module.Basis ι ℝ E) (f : C(K, E →ᵇ V))
    (hf : ∀ t, ContDiff ℝ ∞ (f t : E → V))
    (u : (n : ℕ) → (Fin n → ι) → C(K, E →ᵇ V))
    (hu : ∀ n w t x, u n w t x = iteratedFDeriv ℝ n (f t : E → V) x (fun i => b (w i))) :
    SmoothTimeField K E V where
  field := f
  smooth := hf
  jet n := coordinatePath b n (u n)
  jet_eq n t x := coordinatePath_eq b n (u n) t x _ (fun w => hu n w t x)

end SmoothTimeField
