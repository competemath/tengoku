import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Coeff
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Matrix Polynomial

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K]

def IsCentralType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ c : K, M = c • (1 : Matrix (Fin 2) (Fin 2) K)

def IsUnipotentType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ¬IsCentralType M ∧ ∃ a : K, M.charpoly = (X - C a) ^ 2

def IsHyperbolicType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ a b : K, a ≠ b ∧ M.charpoly = (X - C a) * (X - C b)

def IsEllipticType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ a : K, ¬M.charpoly.IsRoot a

def centralCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsCentralType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

def unipotentCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsUnipotentType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

def hyperbolicCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsHyperbolicType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

def ellipticCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsEllipticType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

/--
@isnad1 id=iff.0h2v.s7.6a51181fd60f from=translated src=- shape=ad2f5934 vocab=2a1d2c04
-/
theorem mem_centralCell_iff {γ : GL (Fin 2) K} :
    γ ∈ centralCell K ↔ IsCentralType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s7.6bd4e7b2318c from=translated src=- shape=ad2f5934 vocab=cf0e464c
-/
theorem mem_unipotentCell_iff {γ : GL (Fin 2) K} :
    γ ∈ unipotentCell K ↔ IsUnipotentType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s7.bcdf7a39476b from=translated src=- shape=ad2f5934 vocab=956747fb
-/
theorem mem_hyperbolicCell_iff {γ : GL (Fin 2) K} :
    γ ∈ hyperbolicCell K ↔ IsHyperbolicType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s7.21a11d11a4a2 from=translated src=- shape=ad2f5934 vocab=b9c6d9ce
-/
theorem mem_ellipticCell_iff {γ : GL (Fin 2) K} :
    γ ∈ ellipticCell K ↔ IsEllipticType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

end AutomorphicForm
