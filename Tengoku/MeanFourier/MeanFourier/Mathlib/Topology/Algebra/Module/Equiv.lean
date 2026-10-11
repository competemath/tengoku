module

public import Tengoku

public section

namespace ContinuousLinearEquiv
variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

@[simp] lemma toLinearEquiv_one : toLinearEquiv (1 : M ≃L[R] M) = 1 := rfl

end ContinuousLinearEquiv
