module

public import Tengoku

public section

namespace LinearEquiv
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

-- TODO: Replace `coe_toLinearMap_one`
/--
@isnad1 id=eq.0h2v.s7.fb18b7963814 from=translated src=- shape=165ca941 vocab=a2386ae9
-/
@[simp high] lemma toLinearMap_one : toLinearMap (1 : M ≃ₗ[R] M) = 1 := rfl

end LinearEquiv
