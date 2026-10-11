module

public import Tengoku

public section

namespace RCLike
variable {K : Type*} [RCLike K]

/--
@isnad1 id=eq.0h2v.s6.408045ceacd5 from=translated src=- shape=4859b07c vocab=d9dc82d8
-/
@[simp] lemma enorm_ofReal (r : ℝ) : ‖(r : K)‖ₑ = ‖r‖ₑ := by simp [enorm]

end RCLike
