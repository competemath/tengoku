module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic
import Tengoku.Seed.Algebra.Order.Group.Nat
import Tengoku.Seed.Data.Finsupp.Order
import Tengoku.Seed.RingTheory.MvPolynomial.EulerIdentity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fischer adjointness: coefficient-level tools

For the Fischer inner product on the degree-`k` homogeneous piece `Pk k`, multiplication by `X i`
is adjoint to the partial derivative `∂ᵢ`. This file provides coefficient-level tools and defines
the degree-shifting maps `mulXPk` and `pderivPk`. The actual adjointness identity is proved in
`PSD/AdjointOpsFixed.lean`.

## Main definitions
* `mulXPk`, `pderivPk`

## Main statements
* `coeff_pderiv`
-/
namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
noncomputable section

open scoped BigOperators RealInnerProductSpace

open Finset Finsupp MvPolynomial

local notation "Pk" => Pk

/-!
### Coefficient formula for `pderiv`

`coeff d (∂ᵢ p) = (d i + 1) * coeff (d + eᵢ) p`.
-/

/-!
### Degree-shifting maps: multiply by `X i` and `pderiv i`
-/

/-- Multiply by `X i`, shifting degree `k ↦ k+1`.-/
@[expose] public noncomputable def mulXPk (k : ℕ) (i : Var) : Pk k →ₗ[ℝ] Pk (k + 1) :=
  LinearMap.codRestrict (Pk (k + 1))
    ((LinearMap.mul ℝ Poly (X i)).comp (Submodule.subtype (Pk k))) (by
      intro p
      have hp : (p.1 : Poly).IsHomogeneous k :=
        (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) k (p := (p.1 : Poly))).1 p.2
      have hx : (X i : Poly).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X (R := ℝ) i
      have hmul : ((X i : Poly) * (p.1 : Poly)).IsHomogeneous (k + 1) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (hx.mul hp)
      assumption)

/-- Partial derivative `∂ᵢ`, shifting degree `k+1 ↦ k`.-/
@[expose] public noncomputable def pderivPk (k : ℕ) (i : Var) : Pk (k + 1) →ₗ[ℝ] Pk k :=
  LinearMap.codRestrict (Pk k)
    ((MvPolynomial.pderiv i).toLinearMap.comp (Submodule.subtype (Pk (k + 1)))) (by
      intro p
      have hp : (p.1 : Poly).IsHomogeneous (k + 1) :=
        (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) (k + 1) (p := p.1)).1 p.2
      refine
        (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) k
          (p := MvPolynomial.pderiv i p.1)).2 ?_
      simpa using (hp.pderiv (i := i)))

end
end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
