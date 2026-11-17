import Tengoku.StringDiagramsLean.StringDiagrams.Super.MonoidalUniversal
import Tengoku.StringDiagramsLean.StringDiagrams.Super.Superalgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Π-envelope of the unit supercategory `I`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 4.8.

The monoidal supercategory `I` (one object, endomorphisms `k` in even parity;
`UnitSupercat k`) has Π-envelope `I_π` with two objects `Π⁰` and `Π¹`
(`UnitEnvelope.objEquiv`); each `Hom_{I_π}(Πᵃ, Πᵇ)` is free of rank one with basis
`1_a^b` (`UnitEnvelope.one`, `UnitEnvelope.homEquiv`), of parity `a + b`
(`UnitEnvelope.one_mem`). The tensor product satisfies `Πᵇ ⊗ Πᵃ = Π^{a+b}`
(`UnitEnvelope.tensorObj_eq`) and `1_b^d ⊗ 1_a^c = (-1)^{(a+c)b} 1_{a+b}^{c+d}`
(`UnitEnvelope.toHom_one_tensor_one`, for the paper's tensor product `superTensorHom`).

By the universal property (Lemma 4.7(i), monoidal case: `Envelope.extendMonoidal`), the
monoidal superfunctor `I → SVec` sending the object to `k` (`UnitSupercat.toSVecMonoidal`)
extends to a monoidal superfunctor `F̃ : I_π → SVec` (`UnitEnvelope.extendSVec`), for the
Π-supercategory structure `Π V` = `V` with the opposite grading, `ζ_V` the identity function,
of `SVec` (Example 1.8). It sends `Πᵃ ↦ Πᵃ k` (`extendSVec_obj_zero`, `extendSVec_obj_one`) and
`1_a^b` to the identity function `id_a^b : Πᵃ k → Πᵇ k` (`extendSVec_map_one`); its coherence
maps `Πᵇ k ⊗ Πᵃ k → Π^{a+b} k` send `1 ⊗ 1 ↦ 1` (`extendSVec_μ_one_tmul_one`). The signs are
consistent because `id_b^d ⊗ id_a^c` sends `1 ⊗ 1 ↦ (-1)^{(a+c)b} 1 ⊗ 1`
(`superTensorHom_extendSVec_one`).

The paper assumes that `k` is a field; the statements here hold over any commutative ring.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory TensorProduct

universe u

namespace UnitEnvelope

variable (k : Type u) [CommRing k]

/-- The Π-envelope `I_π` of the unit supercategory.-/
abbrev Iπ : Type := Envelope k (UnitSupercat k)

/-- The object `Πᵃ` of `I_π`.-/
def P (a : ZMod 2) : Iπ k := ⟨a, ()⟩

/-- **Example 4.8.** `I_π` has exactly two objects, `Π⁰` and `Π¹`.-/
def objEquiv : Iπ k ≃ ZMod 2 where
  toFun X := X.par
  invFun a := P k a
  left_inv _ := rfl
  right_inv _ := rfl

variable {k}

/-- The basis morphism `1_a^b : Πᵃ ⟶ Πᵇ`.-/
def one (a b : ZMod 2) : P k a ⟶ P k b := Envelope.ofHom (SuperalgebraCat.ofElem (1 : k))

/-- **Example 4.8.** `Hom_{I_π}(Πᵃ, Πᵇ)` is free of rank one with basis `1_a^b`.-/
def homEquiv (a b : ZMod 2) : (P k a ⟶ P k b) ≃ₗ[k] k where
  toFun f := SuperalgebraCat.toElem (Envelope.toHom f)
  invFun r := r • one a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    show SuperalgebraCat.toElem (Envelope.toHom f) • (Envelope.ofHom (SuperalgebraCat.ofElem 1) :
      P k a ⟶ P k b) = f
    exact Envelope.hom_ext (SuperalgebraCat.hom_ext (by
      show SuperalgebraCat.toElem (Envelope.toHom f) * 1 = _; rw [mul_one]))
  right_inv r := by
    show r * 1 = r
    rw [mul_one]

/--
@isnad1 id=eq.0h4v.s10.3f7fceac89a7 from=translated src=- shape=242e92ac vocab=fcaa33c0
-/
@[simp] theorem homEquiv_symm_apply (a b : ZMod 2) (r : k) :
    (homEquiv (k := k) a b).symm r = r • one a b := rfl

/-! ## The extension `F̃ : I_π → SVec` -/

local notation "F̃" => Envelope.extend k (UnitSupercat.toSVec k)

variable (k) in
/-- The element `1 ∈ Πᵃ k`.-/
def oneElt : ∀ a : ZMod 2, ((F̃).obj (P k a)).carrier
  | ⟨0, _⟩ => (1 : k)
  | ⟨1, _⟩ => (1 : k)
  | ⟨_ + 2, h⟩ => absurd h (by simp)

end UnitEnvelope

end StringDiagrams

end
