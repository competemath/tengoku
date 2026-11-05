module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Points
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.SplitFiniteAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Coordinates of split finite affine quotients

A surjection from the two-variable polynomial algebra onto `K^p` is evaluation
at `p` distinct affine points. This identifies the quotient kernel with their
actual evaluation equations, rather than an abstract finite-dimensional model.
-/

noncomputable section
namespace ChoppedPlane
open MvPolynomial

variable {K : Type*} [Field K] {p : ℕ}

/-- The coordinates recovered from a split affine algebra presentation.-/
def affinePresentationCoordinates
    (φ : MvPolynomial (Fin 2) K →ₐ[K] (Fin p → K)) : PointCoordinates K p :=
  fun ij => φ (X ij.2) ij.1

/-- Every coordinate of an affine presentation is point evaluation.
@isnad1 id=eq.0h5v.s9.529f742d5654 from=translated src=- shape=7cd2388e vocab=805e5a86
-/
theorem affinePresentation_apply
    (φ : MvPolynomial (Fin 2) K →ₐ[K] (Fin p → K))
    (f : MvPolynomial (Fin 2) K) (i : Fin p) :
    φ f i = eval (fun j => affinePresentationCoordinates φ (i, j)) f := by
  have h : (Pi.evalAlgHom K (fun _ : Fin p => K) i).comp φ =
      aeval (fun j => affinePresentationCoordinates φ (i, j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [affinePresentationCoordinates]
  exact congrArg (fun g : MvPolynomial (Fin 2) K →ₐ[K] K => g f) h

/-- Surjectivity rules out repeated affine coordinates.
@isnad1 id=distinct.1h3v.s8.d22736587281 from=translated src=- shape=34970b46 vocab=c7082bee
-/
theorem affinePresentation_distinct
    (φ : MvPolynomial (Fin 2) K →ₐ[K] (Fin p → K))
    (hφ : Function.Surjective φ) : DistinctPoints K (affinePresentationCoordinates φ) := by
  classical
  intro i j hij
  have hc : (fun k => affinePresentationCoordinates φ (i, k)) =
      (fun k => affinePresentationCoordinates φ (j, k)) := by
    funext k
    fin_cases k
    · exact congrArg Prod.fst hij
    · exact congrArg Prod.snd hij
  by_contra hne
  obtain ⟨f, hf⟩ := hφ (Pi.single i 1)
  have he : φ f i = φ f j := by
    rw [affinePresentation_apply, affinePresentation_apply, hc]
  rw [hf] at he
  simp [Ne.symm hne] at he

/-- The presentation kernel is exactly simultaneous vanishing at its points.
@isnad1 id=iff.0h4v.s9.7c6188e391a1 from=translated src=- shape=8b377cb2 vocab=805e5a86
-/
theorem affinePresentation_ker
    (φ : MvPolynomial (Fin 2) K →ₐ[K] (Fin p → K))
    (f : MvPolynomial (Fin 2) K) :
    φ f = 0 ↔ ∀ i, eval (fun j => affinePresentationCoordinates φ (i, j)) f = 0 := by
  simp only [funext_iff, Pi.zero_apply, affinePresentation_apply]

/-- A reduced finite quotient over an algebraically closed field supplies
an actual distinct-point presentation with the original ideal as its kernel.
@isnad1 id=ex.1h3v.s11.98f18064d215 from=translated src=- shape=00b557f8 vocab=bca06565
-/
theorem exists_affine_point_presentation [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin 2) K))
    [Module.Finite K (MvPolynomial (Fin 2) K ⧸ I)]
    [IsReduced (MvPolynomial (Fin 2) K ⧸ I)]
    (h : Module.finrank K (MvPolynomial (Fin 2) K ⧸ I) = p) :
    ∃ φ : MvPolynomial (Fin 2) K →ₐ[K] (Fin p → K),
      Function.Surjective φ ∧ DistinctPoints K (affinePresentationCoordinates φ) ∧
      ∀ f, φ f = 0 ↔ f ∈ I := by
  let e := finiteReducedAlgebraFinEquiv (K := K) p h
  let φ := e.toAlgHom.comp (Ideal.Quotient.mkₐ K I)
  have hφ : Function.Surjective φ := e.surjective.comp Ideal.Quotient.mk_surjective
  refine ⟨φ, hφ, affinePresentation_distinct φ hφ, ?_⟩
  intro f
  change e (Ideal.Quotient.mk I f) = 0 ↔ f ∈ I
  rw [← map_zero e, e.injective.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

end ChoppedPlane
