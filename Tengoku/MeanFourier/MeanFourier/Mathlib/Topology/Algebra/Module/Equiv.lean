module

public import Tengoku

public section

namespace ContinuousLinearEquiv
variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/--
@isnad1 id=eq.0h2v.s8.f10094377db2 from=translated src=- shape=b27dc431 vocab=e6522e60
-/
@[simp] lemma toLinearEquiv_one : toLinearEquiv (1 : M ≃L[R] M) = 1 := rfl

end ContinuousLinearEquiv
