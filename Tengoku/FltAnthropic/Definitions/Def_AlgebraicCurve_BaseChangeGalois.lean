import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.Seed.Algebra.Ring.Action.End
import Tengoku.Seed.LinearAlgebra.Dimension.Finrank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def SemilinearAut : Subgroup (RingAut F × RingAut K) where
  carrier := {p | ∀ a : K, p.1 (algebraMap K F a) = algebraMap K F (p.2 a)}
  one_mem' _ := rfl
  mul_mem' := fun {p q} hp hq a => by
    show p.1 (q.1 (algebraMap K F a)) = algebraMap K F (p.2 (q.2 a))
    rw [hq a, hp (q.2 a)]
  inv_mem' := fun {p} hp a => by
    show p.1.symm (algebraMap K F a) = algebraMap K F (p.2.symm a)
    apply p.1.injective
    rw [RingEquiv.apply_symm_apply, hp (p.2.symm a), RingEquiv.apply_symm_apply]

namespace SemilinearAut

variable {K F}

def toRingAut (g : SemilinearAut K F) : F ≃+* F := g.val.1

instance : MulSemiringAction (SemilinearAut K F) F where
  smul g x := toRingAut g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero g := map_zero (toRingAut g)
  smul_add g := map_add (toRingAut g)
  smul_one g := map_one (toRingAut g)
  smul_mul g := map_mul (toRingAut g)

def ofAlgAut : (F ≃ₐ[K] F) →* SemilinearAut K F where
  toFun σ := ⟨((σ : F ≃+* F), 1), fun a => by simp⟩
  map_one' := Subtype.ext (by ext <;> rfl)
  map_mul' σ τ := Subtype.ext (by ext <;> rfl)

end SemilinearAut

namespace SemilinearAut

open scoped Pointwise

variable {K F}
variable (g : SemilinearAut K F)

/--
@isnad1 id=eq.0h3v.s11.19ab746c1536 from=translated src=- shape=d730b26f vocab=a74b3867
-/
theorem pointwise_smul_top : g • (⊤ : ValuationSubring F) = ⊤ := by
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => ValuationSubring.mem_top _⟩

variable (v : Place K F)

end SemilinearAut

namespace SemilinearAut

open scoped Pointwise

variable {K F}

end SemilinearAut

end AlgebraicCurve

namespace AlgebraicCurve

namespace SemilinearAut

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end SemilinearAut

namespace Pic0

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Pic0

namespace SemilinearAut

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end SemilinearAut

end AlgebraicCurve
