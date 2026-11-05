module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylLaurentOperators
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylActualChartMaps
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.GradedLocalExactness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Local exactness and operator identities on the actual flattened Laurent modules. -/

noncomputable section
namespace ChoppedPlane.QWeyl

open LaurentPairing LaurentChartComplex FiniteCech SymmetricDerivative BinaryChartRings
variable {K : Type*} [Field K]

/--
@isnad1 id=eq.0h3v.s11.3d605fcc7b02 from=translated src=- shape=942cdcf1 vocab=4206f3e6
-/
@[simp] theorem auxiliaryLaurentVectorEquiv_uFreeEmbedding (n : ℕ)
    (c : Fin 3 × Sym (Fin 3) n → URing K) :
    auxiliaryLaurentVectorEquiv (uFreeEmbedding c) =
      uFiniteEmbedding n (fun j i => c (i,j)) := by
  funext j i
  change freeLaurentEquiv (uFreeEmbedding c) (i,j) = _
  rw [freeLaurentEquiv_uFreeEmbedding]
  rfl

/--
@isnad1 id=eq.0h3v.s11.25bf3ea702e1 from=translated src=- shape=942cdcf1 vocab=f1dcf119
-/
@[simp] theorem auxiliaryLaurentVectorEquiv_vFreeEmbedding (n : ℕ)
    (c : Fin 3 × Sym (Fin 3) n → VRing K) :
    auxiliaryLaurentVectorEquiv (vFreeEmbedding c) =
      vFiniteEmbedding n (fun j i => c (i,j)) := by
  funext j i
  change freeLaurentEquiv (vFreeEmbedding c) (i,j) = _
  rw [freeLaurentEquiv_vFreeEmbedding]
  rfl

end ChoppedPlane.QWeyl
