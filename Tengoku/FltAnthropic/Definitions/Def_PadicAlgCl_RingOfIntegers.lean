import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace PadicAlgCl

variable (p : ℕ) [Fact p.Prime]

def ringOfIntegers (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Subalgebra ℤ_[p] (PadicAlgCl p) :=
  integralClosure ℤ_[p] (PadicAlgCl p) ⊓ K.toSubalgebra.restrictScalars ℤ_[p]

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

namespace ringOfIntegers

variable {p K}

variable (p K)

theorem algebraMap_mem (a : ℤ_[p]) : algebraMap ℤ_[p] (PadicAlgCl p) a ∈ ringOfIntegers p K :=
  Subalgebra.algebraMap_mem _ a

end ringOfIntegers

end PadicAlgCl

end
