import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace Submodule

variable {D : Type*} [Ring D] [Algebra ℚ D]

def finiteAdeleBox (Λ : Submodule ℤ D) : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  AddSubgroup.closure
    {x | ∃ z ∈ Λ, ∃ a : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] a}

def ofFiniteIdele (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Submodule ℤ D :=
  (AddSubgroup.toIntSubmodule
      ((finiteAdeleBox Λ).map
        (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)))).comap
    ((Algebra.TensorProduct.includeLeft :
        D →ₐ[ℚ] D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toLinearMap.restrictScalars ℤ)

def finiteIdeleStabilizer (Λ : Submodule ℤ D) : Subgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  MulAction.stabilizer (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ
    ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))

def conjByFiniteIdele (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule ℤ D :=
  (AddSubgroup.toIntSubmodule
      ((finiteAdeleBox Λ).map
        ((AddMonoidHom.mulRight ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
          (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))))).comap
    ((Algebra.TensorProduct.includeLeft :
        D →ₐ[ℚ] D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toLinearMap.restrictScalars ℤ)

variable (D) in

def finiteIdeleDiagonal : Dˣ →* (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom :
    D →+* D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ).toMonoidHom

/--
@isnad1 id=eq.0h2v.s11.464ac4499c5b from=translated src=- shape=407328be vocab=e38033da
-/
@[simp] theorem val_finiteIdeleDiagonal_apply (d : Dˣ) :
    ((finiteIdeleDiagonal D d : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (d : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

/--
@isnad1 id=iff.0h4v.s12.84227d65841f from=translated src=- shape=4fef6c79 vocab=d8944687
-/
theorem mem_ofFiniteIdele_iff (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (z : D) :
    z ∈ ofFiniteIdele Λ g ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        (finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s13.35a79a8dbdab from=translated src=- shape=fe414a67 vocab=ab7bd825
-/
theorem mem_conjByFiniteIdele_iff (Λ : Submodule ℤ D) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (z : D) :
    z ∈ conjByFiniteIdele Λ g ↔
      z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        (finiteAdeleBox Λ).map
          ((AddMonoidHom.mulRight ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
              D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
            (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) :=
  Iff.rfl

/--
@isnad1 id=iff.0h3v.s13.9e1321699584 from=translated src=- shape=34c78c61 vocab=b5d82a50
-/
theorem mem_finiteIdeleStabilizer_iff (Λ : Submodule ℤ D) (u : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ finiteIdeleStabilizer Λ ↔
      u • ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))
        = ((finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Set (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Iff.rfl

end Submodule

end
