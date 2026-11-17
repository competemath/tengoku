import Tengoku.Seed.RingTheory.HopfAlgebra.TensorProduct
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.RingTheory.FiniteStability
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_isReduced_of_finiteType_of_charZero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_charZero

set_option maxHeartbeats 3200000
open scoped TensorProduct

theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by
  let Ω := AlgebraicClosure K

  haveI : IsReduced (Ω ⊗[K] A) :=
    HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero Ω (Ω ⊗[K] A)

  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[K] Ω ⊗[K] A) :=
    Algebra.TensorProduct.includeRight_injective (R := K) (A := Ω) (B := A)
      (algebraMap K Ω).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[K] Ω ⊗[K] A).toRingHom hinj
