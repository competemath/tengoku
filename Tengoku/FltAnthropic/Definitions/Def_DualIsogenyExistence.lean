import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_DualIsogenyAPI

import Tengoku.Seed.Algebra.Group.Subgroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped Function

namespace AddMonoidHom

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

private def zsmulHom (n : ℤ) : A →+ A where
  toFun a := n • a
  map_zero' := zsmul_zero n
  map_add' a a' := zsmul_add a a' n

private theorem ker_le_zsmulHom_ker {φ : A →+ B} {n : ℤ}
    (hker : ∀ a, φ a = 0 → n • a = 0) :
    φ.ker ≤ (zsmulHom (A := A) n).ker := by
  intro a ha
  exact mem_ker.mpr (hker a (mem_ker.mp ha))

noncomputable def dualOfSurjective (φ : A →+ B) (hsurj : Function.Surjective φ)
    (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0) : B →+ A :=
  φ.liftOfSurjective hsurj ⟨zsmulHom n, ker_le_zsmulHom_ker hker⟩

/--
@isnad1 id=eq.2h5v.s8.3faba545e1f0 from=translated src=- shape=8740d012 vocab=5a703357
-/
theorem dualOfSurjective_comp_apply (φ : A →+ B) (hsurj : Function.Surjective φ)
    (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0) (a : A) :
    dualOfSurjective φ hsurj n hker (φ a) = n • a :=
  φ.liftOfRightInverse_comp_apply _ _ ⟨zsmulHom n, ker_le_zsmulHom_ker hker⟩ a

/--
@isnad1 id=isdualpa.2h4v.s7.46bc4061bf98 from=translated src=- shape=a097f615 vocab=6f877355
-/
theorem isDualPair_dualOfSurjective (φ : A →+ B) (hsurj : Function.Surjective φ)
    (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0) :
    IsDualPair φ (dualOfSurjective φ hsurj n hker) n := by
  refine ⟨dualOfSurjective_comp_apply φ hsurj n hker, fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj b
  rw [dualOfSurjective_comp_apply, ← map_zsmul]

/--
@isnad1 id=eq.3h5v.s8.fda6a3116c74 from=translated src=- shape=4d1c98c6 vocab=5a703357
-/
theorem dualOfSurjective_unique (φ : A →+ B) (hsurj : Function.Surjective φ)
    (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0)
    {ψ' : B →+ A} (hψ' : ∀ a, ψ' (φ a) = n • a) :
    ψ' = dualOfSurjective φ hsurj n hker :=
  (isDualPair_dualOfSurjective φ hsurj n hker).left_unique_of_surjective hsurj hψ'

end AddMonoidHom

namespace AddMonoidHom

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/--
@isnad1 id=ex.2h7v.s8.ee06d27d5ea4 from=translated src=- shape=d6b4409f vocab=49d1e904
-/
theorem exists_isDualPair_of_factor {φ' : A →+ B} {ψ' : B →+ C} {m n : ℤ}
    (hφ : ∃ φ : B →+ A, IsDualPair φ' φ m) (hψ : ∃ ψ : C →+ B, IsDualPair ψ' ψ n) :
    ∃ χ : C →+ A, IsDualPair (ψ'.comp φ') χ (m * n) := by
  obtain ⟨φ, hφ⟩ := hφ; obtain ⟨ψ, hψ⟩ := hψ
  exact ⟨φ.comp ψ, hφ.comp hψ⟩

end AddMonoidHom

section Discharge

variable {A : Type*} [AddCommGroup A]

open AddMonoid.End

private theorem norm_nonneg_of_disc_neg {t n : ℤ} (hdisc : t ^ 2 < 4 * n) : 0 ≤ n := by
  nlinarith [sq_nonneg t]

private theorem intCast_sub_mem {S : Subring (AddMonoid.End A)} {φ : AddMonoid.End A}
    (hφ : φ ∈ S) (t : ℤ) : (t : AddMonoid.End A) - φ ∈ S :=
  S.sub_mem (intCast_mem S t) hφ

/--
@isnad1 id=dualisog.1h2v.s9.e82cb3b7e93f from=translated src=- shape=43d98f71 vocab=e5fbf0d2
-/
theorem dualIsogenyExistence_of_charPoly {S : Subring (AddMonoid.End A)}
    (hcp : ∀ φ ∈ S, ∃ t n : ℤ,
      φ * φ = (t : AddMonoid.End A) * φ - (n : AddMonoid.End A) ∧
      (φ ∉ (⊥ : Subring (AddMonoid.End A)) → t ^ 2 < 4 * n)) :
    DualIsogenyExistence S := by
  intro φ hφS
  by_cases hint : φ ∈ (⊥ : Subring (AddMonoid.End A))
  ·
    obtain ⟨m, rfl⟩ := Subring.mem_bot.mp hint
    exact ⟨dualEndData_intCast m, intCast_mem S m, sq_nonneg m⟩
  ·
    obtain ⟨t, n, hquad, hdisc⟩ := hcp φ hφS
    have hchar : φ * φ - (t : AddMonoid.End A) * φ + (n : AddMonoid.End A) = 0 := by
      rw [hquad]; abel
    refine ⟨DualEndData.ofCharPoly φ t n hchar, ?_, norm_nonneg_of_disc_neg (hdisc hint)⟩
    rw [DualEndData.ofCharPoly_dual]
    exact intCast_sub_mem hφS t

/--
@isnad1 id=ex.2h3v.s8.1705772a13bc from=translated src=- shape=2f69b77c vocab=cf5c845e
-/
theorem charPoly_of_dualIsogenyExistence {S : Subring (AddMonoid.End A)}
    (hex : DualIsogenyExistence S) :
    ∀ φ ∈ S, ∃ t n : ℤ,
      φ * φ = (t : AddMonoid.End A) * φ - (n : AddMonoid.End A) ∧ 0 ≤ n := by
  intro φ hφS
  obtain ⟨D, _, hn⟩ := hex φ hφS
  refine ⟨D.trace, D.norm, ?_, hn⟩
  have h := D.charPoly
  have : (D.norm : AddMonoid.End A)
      = (D.trace : AddMonoid.End A) * φ - φ * φ := by
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← h]; abel
  rw [this]; abel

end Discharge

namespace AddMonoid.End

variable {A : Type*} [AddCommGroup A]

noncomputable def dualEndDataOfSurjective (φ : AddMonoid.End A)
    (hsurj : Function.Surjective φ) (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0)
    (t : ℤ) (htr : ∀ a, φ a + AddMonoidHom.dualOfSurjective φ hsurj n hker a = t • a) :
    DualEndData φ where
  dual := AddMonoidHom.dualOfSurjective φ hsurj n hker
  trace := t
  norm := n
  add_dual := by
    refine AddMonoidHom.ext fun a => ?_
    show φ a + AddMonoidHom.dualOfSurjective φ hsurj n hker a = (t : AddMonoid.End A) a
    rw [htr, AddMonoid.End.intCast_apply]
  mul_dual := by
    refine AddMonoidHom.ext fun a => ?_
    show φ (AddMonoidHom.dualOfSurjective φ hsurj n hker a) = (n : AddMonoid.End A) a
    rw [AddMonoid.End.intCast_apply]
    exact (AddMonoidHom.isDualPair_dualOfSurjective φ hsurj n hker).comp_right a
  dual_mul := by
    refine AddMonoidHom.ext fun a => ?_
    show AddMonoidHom.dualOfSurjective φ hsurj n hker (φ a) = (n : AddMonoid.End A) a
    rw [AddMonoid.End.intCast_apply]
    exact (AddMonoidHom.isDualPair_dualOfSurjective φ hsurj n hker).comp_left a

/--
@isnad1 id=eq.3h4v.s8.bda4eae4b014 from=translated src=- shape=a46c42b6 vocab=d6cbcb03
-/
@[simp] theorem dualEndDataOfSurjective_norm (φ : AddMonoid.End A)
    (hsurj : Function.Surjective φ) (n : ℤ) (hker) (t : ℤ) (htr) :
    (dualEndDataOfSurjective φ hsurj n hker t htr).norm = n := rfl

/--
@isnad1 id=eq.3h4v.s8.382d3af5010e from=translated src=- shape=494771cc vocab=503fd887
-/
@[simp] theorem dualEndDataOfSurjective_trace (φ : AddMonoid.End A)
    (hsurj : Function.Surjective φ) (n : ℤ) (hker) (t : ℤ) (htr) :
    (dualEndDataOfSurjective φ hsurj n hker t htr).trace = t := rfl

end AddMonoid.End

section SatGates

/--
@isnad1 id=eq.0h0v.s7.bde4102341e4 from=translated src=- shape=c34f1e54 vocab=9b0cc327
-/
theorem gate_dualOfSurjective_id :
    AddMonoidHom.dualOfSurjective (AddMonoidHom.id ℤ) Function.surjective_id 1
      (fun a ha => by rwa [one_zsmul]) = AddMonoidHom.id ℤ :=
  ((AddMonoidHom.dualOfSurjective_unique (AddMonoidHom.id ℤ) Function.surjective_id 1
    (fun a ha => by rwa [one_zsmul]) (fun a => (one_zsmul a).symm))).symm

/--
@isnad1 id=ex.0h0v.s7.c0715a117204 from=translated src=- shape=59d21603 vocab=8c84348f
-/
theorem gate_exists_of_factor_intCast :
    ∃ χ : ℤ →+ ℤ, AddMonoidHom.IsDualPair
      ((3 : AddMonoid.End ℤ).comp (2 : AddMonoid.End ℤ)) χ ((2 : ℤ)^2 * 3^2) :=
  AddMonoidHom.exists_isDualPair_of_factor
    ⟨_, AddMonoidHom.isDualPair_intCast (A := ℤ) 2⟩
    ⟨_, AddMonoidHom.isDualPair_intCast (A := ℤ) 3⟩

/--
@isnad1 id=dualisog.0h1v.s6.2d80c2b5b219 from=translated src=- shape=7d1e16a9 vocab=a5c5878a
-/
theorem gate_dualIsogenyExistence_of_charPoly_bot {A : Type*} [AddCommGroup A] :
    DualIsogenyExistence (⊥ : Subring (AddMonoid.End A)) := by
  apply dualIsogenyExistence_of_charPoly
  intro φ hφ
  obtain ⟨m, rfl⟩ := Subring.mem_bot.mp hφ
  refine ⟨2 * m, m ^ 2, ?_, fun hbot => absurd (Subring.mem_bot.mpr ⟨m, rfl⟩) hbot⟩
  rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub]
  exact congrArg Int.cast (by ring)

/--
@isnad1 id=ex.1h2v.s9.0c9cb5d0347a from=translated src=- shape=910738e3 vocab=cf3984fa
-/
theorem gate_charPoly_of_dualIsogenyExistence_bot {A : Type*} [AddCommGroup A] :
    ∀ φ ∈ (⊥ : Subring (AddMonoid.End A)), ∃ t n : ℤ,
      φ * φ = (t : AddMonoid.End A) * φ - (n : AddMonoid.End A) ∧ 0 ≤ n :=
  charPoly_of_dualIsogenyExistence dualIsogenyExistence_bot

end SatGates
