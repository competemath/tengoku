import Tengoku.Seed.LinearAlgebra.Prod
import Tengoku.Seed.LinearAlgebra.Quotient.Basic
import Tengoku.Seed.RingTheory.Finiteness.Cardinality
import Tengoku.Seed.Algebra.Module.Projective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u v w w'

namespace TwoChartCech

namespace KerCoprod

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable {P : Type w'} [AddCommGroup P] [Module R P]
variable (d : C0 →ₗ[R] C1) (g : P →ₗ[R] C1)

abbrev K0 : Submodule R (C0 × P) := LinearMap.ker (d.coprod g)

/--
@isnad1 id=iff.0h7v.s8.9e60271200fd from=translated src=- shape=a0b65d97 vocab=1b25826c
-/
theorem mem_K0_iff (z : C0 × P) : z ∈ K0 d g ↔ d z.1 + g z.2 = 0 := by
  rw [LinearMap.mem_ker, LinearMap.coprod_apply]

def dK : K0 d g →ₗ[R] P := (LinearMap.snd R C0 P) ∘ₗ (K0 d g).subtype

def ι0 : K0 d g →ₗ[R] C0 := (LinearMap.fst R C0 P) ∘ₗ (K0 d g).subtype

def ι1 : P →ₗ[R] C1 := -g

/--
@isnad1 id=eq.0h7v.s10.721f9fc09f7b from=translated src=- shape=1bf544c4 vocab=0910e7b2
-/
@[simp] theorem dK_apply (z : K0 d g) : dK d g z = (z : C0 × P).2 := rfl
/--
@isnad1 id=eq.0h7v.s10.8ecbadf24b7a from=translated src=- shape=0a0553e8 vocab=ca5f91e2
-/
@[simp] theorem ι0_apply (z : K0 d g) : ι0 d g z = (z : C0 × P).1 := rfl
/--
@isnad1 id=eq.0h5v.s7.59ba644dc743 from=translated src=- shape=149e5813 vocab=f89ecc9e
-/
@[simp] theorem ι1_apply (p : P) : ι1 g p = -g p := rfl

/--
@isnad1 id=eq.0h6v.s9.29816ac5bd7c from=translated src=- shape=232fc581 vocab=83ab004c
-/
theorem comm : d ∘ₗ ι0 d g = ι1 g ∘ₗ dK d g := by
  ext z
  have hz : d (z : C0 × P).1 + g (z : C0 × P).2 = 0 := (mem_K0_iff d g _).mp z.2
  simp only [LinearMap.comp_apply, ι0_apply, dK_apply, ι1_apply, eq_neg_iff_add_eq_zero]
  exact hz

end KerCoprod

namespace Mumford

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

def rank : ℕ := (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose

def quot : (Fin (rank d) → R) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose

/--
@isnad1 id=surjecti.0h4v.s9.c8d6e3744ce0 from=translated src=- shape=b69d70d8 vocab=1dc22b33
-/
theorem quot_surjective : Function.Surjective (quot d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose_spec

def lift : (Fin (rank d) → R) →ₗ[R] C1 :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose

/--
@isnad1 id=eq.0h4v.s9.4c2ea37707a6 from=translated src=- shape=7af9659a vocab=1985f50e
-/
theorem mkQ_comp_lift : (LinearMap.range d).mkQ ∘ₗ lift d = quot d :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose_spec

/--
@isnad1 id=eq.0h5v.s10.03206a00f7c0 from=translated src=- shape=8770175f vocab=b289500b
-/
theorem mkQ_lift_apply (v : Fin (rank d) → R) : (LinearMap.range d).mkQ (lift d v) = quot d v := by
  rw [← LinearMap.comp_apply, mkQ_comp_lift]

/--
@isnad1 id=surjecti.0h4v.s9.5d71adc10d94 from=translated src=- shape=1a4e9e36 vocab=012f3edf
-/
theorem surjective_coprod : Function.Surjective (d.coprod (lift d)) := by
  intro y
  obtain ⟨v, hv⟩ := quot_surjective d ((LinearMap.range d).mkQ y)
  have hy : y - lift d v ∈ LinearMap.range d := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← hv, mkQ_lift_apply, sub_self]
  obtain ⟨x, hx⟩ := hy
  exact ⟨(x, v), by simp only [LinearMap.coprod_apply, hx, sub_add_cancel]⟩

abbrev K0 : Submodule R (C0 × (Fin (rank d) → R)) := KerCoprod.K0 d (lift d)

/--
@isnad1 id=iff.0h5v.s10.db48c7dfd514 from=translated src=- shape=51686c1e vocab=c3853a34
-/
theorem mem_K0_iff (z : C0 × (Fin (rank d) → R)) : z ∈ K0 d ↔ d z.1 + lift d z.2 = 0 :=
  KerCoprod.mem_K0_iff d (lift d) z

abbrev dK : K0 d →ₗ[R] (Fin (rank d) → R) := KerCoprod.dK d (lift d)

abbrev ι0 : K0 d →ₗ[R] C0 := KerCoprod.ι0 d (lift d)

abbrev ι1 : (Fin (rank d) → R) →ₗ[R] C1 := KerCoprod.ι1 (lift d)

/--
@isnad1 id=eq.0h5v.s12.412d3a1ba1c1 from=translated src=- shape=de46e9fb vocab=20ca3fb4
-/
@[simp] theorem dK_apply (z : K0 d) : dK d z = (z : C0 × (Fin (rank d) → R)).2 := rfl
/--
@isnad1 id=eq.0h5v.s12.bd29a86fc318 from=translated src=- shape=9f858222 vocab=d1a86f22
-/
@[simp] theorem ι0_apply (z : K0 d) : ι0 d z = (z : C0 × (Fin (rank d) → R)).1 := rfl
/--
@isnad1 id=eq.0h5v.s9.758af63f7fc7 from=translated src=- shape=2a38cdd5 vocab=42da5e08
-/
@[simp] theorem ι1_apply (v : Fin (rank d) → R) : ι1 d v = -lift d v := rfl
/--
@isnad1 id=eq.0h4v.s9.07a105e11aa4 from=translated src=- shape=776b18ae vocab=0f5763ac
-/
theorem ι1_eq : ι1 d = -lift d := rfl

/--
@isnad1 id=eq.0h4v.s11.c3c3e6edac44 from=translated src=- shape=e257ceb0 vocab=41125302
-/
theorem comm : d ∘ₗ ι0 d = ι1 d ∘ₗ dK d := KerCoprod.comm d (lift d)

end Mumford

section Gates

end Gates

end TwoChartCech

end
