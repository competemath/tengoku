import Tengoku.Seed.LinearAlgebra.Alternating.DomCoprod
import Tengoku.Seed.LinearAlgebra.Alternating.Uncurry.Fin
import Tengoku.Seed.GroupTheory.Perm.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The shuffle product of scalar alternating maps

For a commutative ring `R` and an `R`-module `M`, `shuffle μ ν` is the product of
`μ ∈ Alt^k(M; R)` and `ν ∈ Alt^l(M; R)` given by Mathlib's `AlternatingMap.domCoprod` (a signed sum
over shuffles), followed by multiplication `R ⊗ R → R` and reindexing along `finSumFinEquiv`.
On multilinear maps, `mulProd a b` is the unsymmetrized product `v ↦ a(v_{<k}) b(v_{≥k})`.
The key lemma `shuffle_alternatization` says that the shuffle product of two alternatizations is
the alternatization of the product (Mathlib's `MultilinearMap.domCoprod_alternization`). The
file also gives the laws of `mulProd`, bilinearity of `shuffle`, and its naturality under linear
maps and reindexing by `finCongr`.
-/

open Equiv

namespace AlternatingAnalytic.Forms

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {k l m : ℕ}

/-- Alternatization commutes with reindexing.-/
theorem alternatization_domDomCongr {N : Type*} [AddCommGroup N] [Module R N]
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (a : MultilinearMap R (fun _ : ι => M) N) :
    MultilinearMap.alternatization (a.domDomCongr e) =
      (MultilinearMap.alternatization a).domDomCongr e := by
  ext v
  simp only [MultilinearMap.alternatization_apply, AlternatingMap.domDomCongr_apply,
    MultilinearMap.domDomCongr_apply, Function.comp_apply]
  refine Fintype.sum_equiv (e.symm.permCongr) _ _ fun σ => ?_
  simp [Perm.sign_permCongr]

/-- The alternatization of the constant `0`-ary map `1` is `1`.-/
theorem alternatization_constOfIsEmpty :
    MultilinearMap.alternatization (MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => M) (1 : R)) =
      AlternatingMap.constOfIsEmpty R M (Fin 0) (1 : R) := by
  ext v
  simp [MultilinearMap.alternatization_apply]

section Bilinear

end Bilinear

section Naturality

variable {M' : Type*} [AddCommGroup M'] [Module R M']

/-- `AlternatingMap.domCoprod` commutes with pullback along linear maps.-/
theorem domCoprod_compLinearMap {ιa ιb : Type*} [Fintype ιa] [Fintype ιb] [DecidableEq ιa]
    [DecidableEq ιb] (μ : M [⋀^ιa]→ₗ[R] R) (ν : M [⋀^ιb]→ₗ[R] R) (g : M' →ₗ[R] M) :
    (μ.compLinearMap g).domCoprod (ν.compLinearMap g) = (μ.domCoprod ν).compLinearMap g := by
  ext v
  simp only [AlternatingMap.domCoprod_apply, AlternatingMap.compLinearMap_apply, sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  induction σ using Quotient.inductionOn' with
  | h σ => simp [AlternatingMap.domCoprod.summand_mk'', MultilinearMap.domCoprod_apply]

end Naturality

end AlternatingAnalytic.Forms
