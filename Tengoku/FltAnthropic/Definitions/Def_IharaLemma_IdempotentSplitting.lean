import Tengoku.Seed.RingTheory.Idempotents
import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace IharaLemma

structure IdempotentSplitting (B : Type) [CommRing B] where
  n : ℕ
  e : Fin n → B
  𝔪 : Fin n → Ideal B
  coi : CompleteOrthogonalIdempotents e
  isMaximal : ∀ i, (𝔪 i).IsMaximal
  exists_eq : ∀ I : Ideal B, I.IsMaximal → ∃ i, 𝔪 i = I
  mem_iff : ∀ i j, e i ∈ 𝔪 j ↔ i ≠ j

namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B)

/--
@isnad1 id=injectiv.0h2v.s4.2f9c5c9c968f from=translated src=- shape=f4a2a615 vocab=27bf475b
-/
theorem 𝔪_injective : Function.Injective S.𝔪 := by
  intro i j h
  by_contra hij
  have h1 : S.e i ∈ S.𝔪 j := (S.mem_iff i j).mpr hij
  rw [← h] at h1
  exact ((S.mem_iff i i).mp h1) rfl

/--
@isnad1 id=not.0h3v.s6.6561e3ac038a from=translated src=- shape=842c4411 vocab=54094954
-/
theorem notMem (i : Fin S.n) : S.e i ∉ S.𝔪 i := fun h => ((S.mem_iff i i).mp h) rfl

/--
@isnad1 id=mem.1h4v.s6.4ccb7aaa4338 from=translated src=- shape=7b87b18f vocab=54094954
-/
theorem mem_of_ne {i j : Fin S.n} (h : i ≠ j) : S.e i ∈ S.𝔪 j := (S.mem_iff i j).mpr h

/--
@isnad1 id=mem.2h4v.s6.1522f2bbf440 from=translated src=- shape=c265f2dc vocab=32987d0b
-/
theorem mem_of_isMaximal_of_ne (i : Fin S.n) (J : Ideal B) (hJ : J.IsMaximal) (hne : J ≠ S.𝔪 i) :
    S.e i ∈ J := by
  obtain ⟨j, rfl⟩ := S.exists_eq J hJ
  exact S.mem_of_ne fun h => hne (congrArg S.𝔪 h.symm)

/--
@isnad1 id=isidempo.0h3v.s4.dbf22bf06160 from=translated src=- shape=f2c662a2 vocab=2e581358
-/
theorem idem (i : Fin S.n) : IsIdempotentElem (S.e i) := S.coi.idem i

/--
@isnad1 id=ismaxima.0h3v.s4.bf26c8237a38 from=translated src=- shape=f2c662a2 vocab=eb95e315
-/
instance isMaximal_𝔪 (i : Fin S.n) : (S.𝔪 i).IsMaximal := S.isMaximal i

end IdempotentSplitting

section CornerModule

variable {B : Type} [CommRing B] {M : Type} [AddCommGroup M] [Module B M]

def cornerSubmodule (e : B) : Submodule B M := LinearMap.range (e • (LinearMap.id : M →ₗ[B] M))

def toCorner (e : B) : M →ₗ[B] cornerSubmodule (M := M) e :=
  LinearMap.rangeRestrict (e • (LinearMap.id : M →ₗ[B] M))

/--
@isnad1 id=eq.0h4v.s8.dce9731efc9a from=translated src=- shape=13ba3312 vocab=b10e2fb4
-/
@[simp] theorem toCorner_apply (e : B) (v : M) :
    ((toCorner (M := M) e v : cornerSubmodule e) : M) = e • v := rfl

end CornerModule

/--
@isnad1 id=ex.3h4v.s7.3266623e7ded from=translated src=- shape=4ce3309e vocab=27ce7da8
-/
theorem exists_mul_mul_eq_of_notMem {B : Type} [CommRing B] {e : B} (he : IsIdempotentElem e)
    (𝔪 : Ideal B) (hother : ∀ J : Ideal B, J.IsMaximal → J ≠ 𝔪 → e ∈ J) {s : B} (hs : s ∉ 𝔪) :
    ∃ t : B, t * s * e = e := by
  have htop : Ideal.span {s} ⊔ Ideal.span {1 - e} = ⊤ := by
    by_contra hne
    obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1e : 1 - e ∈ J := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hsJ : s ∈ J := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
    have hJ𝔪 : J ≠ 𝔪 := fun h => hs (h ▸ hsJ)
    have heJ : e ∈ J := hother J hJ hJ𝔪
    apply hJ.ne_top
    rw [Ideal.eq_top_iff_one]
    have := J.add_mem heJ h1e
    rwa [add_sub_cancel] at this
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at htop
  obtain ⟨a, ha, b, hb, hab⟩ := htop
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨t, ?_⟩
  have h0 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have key : t * s * e + u * ((1 - e) * e) = 1 * e := by
    have := congrArg (· * e) hab
    simpa only [add_mul, mul_assoc] using this
  rwa [h0, mul_zero, add_zero, one_mul] at key

namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n)

abbrev CornerRing : Type := (S.idem i).Corner

instance coeOutCornerRing : CoeOut (S.CornerRing i) B := ⟨Subtype.val⟩

/--
@isnad1 id=eq.1h4v.s7.8edd88d7048e from=translated src=- shape=daeaf111 vocab=cc15ef5b
-/
theorem coe_mk_cornerRing (x : B) (hx) : ((⟨x, hx⟩ : S.CornerRing i) : B) = x := rfl

/--
@isnad1 id=eq.1h5v.s7.9926aef6c7c3 from=translated src=- shape=69222d99 vocab=4c905c2f
-/
@[ext] theorem ext_cornerRing {z w : S.CornerRing i} (h : (z : B) = w) : z = w := Subtype.ext h

/--
@isnad1 id=eq.0h3v.s7.9b71cb97a11f from=translated src=- shape=f4189ac9 vocab=f39dbb65
-/
theorem coe_one_cornerRing : ((1 : S.CornerRing i) : B) = S.e i := rfl

def toCornerRing : B →+* S.CornerRing i where
  toFun b := ⟨S.e i * b * S.e i, b, rfl⟩
  map_one' := Subtype.ext (by
    show S.e i * 1 * S.e i = S.e i
    rw [mul_one, (S.idem i).eq])
  map_mul' a b := Subtype.ext (by
    show S.e i * (a * b) * S.e i = S.e i * a * S.e i * (S.e i * b * S.e i)
    have h2 : S.e i * S.e i = S.e i := (S.idem i).eq
    linear_combination (-(a * b) * (S.e i * S.e i + S.e i)) * h2)
  map_zero' := Subtype.ext (by
    show S.e i * 0 * S.e i = 0
    rw [mul_zero, zero_mul])
  map_add' a b := Subtype.ext (by
    show S.e i * (a + b) * S.e i = S.e i * a * S.e i + S.e i * b * S.e i
    rw [mul_add, add_mul])

/--
@isnad1 id=eq.0h4v.s7.748cef24da60 from=translated src=- shape=8d1d1ca4 vocab=a784e7cb
-/
@[simp] theorem coe_toCornerRing (b : B) :
    ((S.toCornerRing i b : S.CornerRing i) : B) = S.e i * b * S.e i := rfl

/--
@isnad1 id=eq.0h4v.s7.aedcb8ea7ead from=translated src=- shape=ed493946 vocab=ad16357d
-/
theorem e_mul_coe (z : S.CornerRing i) : S.e i * (z : B) = z := by
  obtain ⟨_, a, rfl⟩ := z
  show S.e i * (S.e i * a * S.e i) = S.e i * a * S.e i
  rw [← mul_assoc, ← mul_assoc, (S.idem i).eq]

/--
@isnad1 id=eq.0h4v.s7.66b98617030c from=translated src=- shape=9de4f4e7 vocab=ad16357d
-/
theorem coe_mul_e (z : S.CornerRing i) : (z : B) * S.e i = z := by
  rw [mul_comm]; exact S.e_mul_coe i z

section Base

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]

instance algebraBaseCornerRing : Algebra 𝒪 (S.CornerRing i) :=
  ((S.toCornerRing i).comp (algebraMap 𝒪 B)).toAlgebra

/--
@isnad1 id=isscalar.0h4v.s6.32e7e3e5566f from=translated src=- shape=43c55b2d vocab=c6886e92
-/
instance isScalarTower_base_cornerRing : IsScalarTower 𝒪 B (S.CornerRing i) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/--
@isnad1 id=eq.0h5v.s8.409f37bb4d84 from=translated src=- shape=78f81428 vocab=27cdb985
-/
theorem algebraMap_base_cornerRing_coe (r : 𝒪) :
    ((algebraMap 𝒪 (S.CornerRing i) r : S.CornerRing i) : B) = S.e i * algebraMap 𝒪 B r * S.e i :=
  rfl

end Base

/--
@isnad1 id=eq.0h4v.s7.8b0631f192ec from=translated src=- shape=4141d5a7 vocab=7979d083
-/
theorem algebraMap_cornerRing_coe (b : B) :
    ((algebraMap B (S.CornerRing i) b : S.CornerRing i) : B) = S.e i * b * S.e i := rfl

/--
@isnad1 id=islocali.0h3v.s5.bad2f36f2336 from=translated src=- shape=cb24994f vocab=4ad7c554
-/
instance isLocalization_cornerRing : IsLocalization (S.𝔪 i).primeCompl (S.CornerRing i) where
  map_units y := by
    obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem (S.idem i) (S.𝔪 i) (S.mem_of_isMaximal_of_ne i) y.2
    refine IsUnit.of_mul_eq_one (algebraMap B (S.CornerRing i) t) (Subtype.ext ?_)
    show S.e i * (y : B) * S.e i * (S.e i * t * S.e i) = S.e i
    have h2 : S.e i * S.e i = S.e i := (S.idem i).eq
    linear_combination (t * (y : B) * (S.e i * S.e i + S.e i + 1)) * h2 + ht
  surj z := by
    obtain ⟨_, a, rfl⟩ := z
    refine ⟨(S.e i * a * S.e i, 1), Subtype.ext ?_⟩
    show S.e i * a * S.e i * (S.e i * ((1 : (S.𝔪 i).primeCompl) : B) * S.e i)
        = S.e i * (S.e i * a * S.e i) * S.e i
    rw [OneMemClass.coe_one]
    ring
  exists_of_eq {x y} h := by
    refine ⟨⟨S.e i, S.notMem i⟩, ?_⟩
    have h' : S.e i * x * S.e i = S.e i * y * S.e i := congrArg Subtype.val h
    show S.e i * x = S.e i * y
    have h2 : S.e i * S.e i = S.e i := (S.idem i).eq
    linear_combination h' + (y - x) * h2

/--
@isnad1 id=islocalr.0h3v.s5.3ab655f9cfde from=translated src=- shape=dd70ce58 vocab=9a75d9e5
-/
instance isLocalRing_cornerRing : IsLocalRing (S.CornerRing i) :=
  IsLocalization.AtPrime.isLocalRing (S.CornerRing i) (S.𝔪 i)

section CornerModule

variable {M : Type} [AddCommGroup M] [Module B M]

/--
@isnad1 id=eq.0h5v.s8.aba25dfafd42 from=translated src=- shape=25e17a31 vocab=817fcfcc
-/
theorem e_smul_coe (m : cornerSubmodule (M := M) (S.e i)) : S.e i • (m : M) = m := by
  obtain ⟨m0, hm0⟩ := m.2
  rw [← hm0]
  show S.e i • (S.e i • m0) = S.e i • m0
  rw [smul_smul, (S.idem i).eq]

/--
@isnad1 id=mem.0h6v.s8.08307a53ea23 from=translated src=- shape=9586bc25 vocab=235c8abd
-/
theorem coe_smul_mem (z : S.CornerRing i) (m : cornerSubmodule (M := M) (S.e i)) :
    (z : B) • (m : M) ∈ cornerSubmodule (M := M) (S.e i) :=
  ⟨(z : B) • (m : M), by
    show S.e i • ((z : B) • (m : M)) = (z : B) • (m : M)
    rw [smul_smul, S.e_mul_coe]⟩

instance smulCornerModule : SMul (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) :=
  ⟨fun z m => ⟨(z : B) • (m : M), S.coe_smul_mem i z m⟩⟩

/--
@isnad1 id=eq.0h3v.s7.3766345a3209 from=translated src=- shape=d7094669 vocab=f39dbb65
-/
theorem coe_zero_cornerRing : ((0 : S.CornerRing i) : B) = 0 := rfl

/--
@isnad1 id=eq.0h6v.s9.dee0bef44eab from=translated src=- shape=6782430a vocab=235c8abd
-/
@[simp] theorem coe_cornerSmul (z : S.CornerRing i) (m : cornerSubmodule (M := M) (S.e i)) :
    ((z • m : cornerSubmodule (M := M) (S.e i)) : M) = (z : B) • (m : M) := rfl

instance moduleCornerModule : Module (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) where
  one_smul m := Subtype.ext (by rw [coe_cornerSmul, coe_one_cornerRing, e_smul_coe])
  mul_smul x y m := Subtype.ext (by
    rw [coe_cornerSmul, coe_cornerSmul, coe_cornerSmul, ← mul_smul]; rfl)
  smul_zero x := Subtype.ext (by rw [coe_cornerSmul, ZeroMemClass.coe_zero, smul_zero])
  smul_add x m n := Subtype.ext (by
    rw [coe_cornerSmul, AddMemClass.coe_add, smul_add, AddMemClass.coe_add, coe_cornerSmul,
      coe_cornerSmul])
  add_smul x y m := Subtype.ext (by
    rw [coe_cornerSmul, AddMemClass.coe_add, coe_cornerSmul, coe_cornerSmul, ← add_smul]; rfl)
  zero_smul m := Subtype.ext (by
    rw [coe_cornerSmul, coe_zero_cornerRing, zero_smul, ZeroMemClass.coe_zero])

/--
@isnad1 id=isscalar.0h4v.s7.22495152e969 from=translated src=- shape=18f84536 vocab=6959afbc
-/
instance isScalarTower_cornerModule :
    IsScalarTower B (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) :=
  ⟨fun b z m => Subtype.ext (by
    show (S.e i * b * S.e i * (z : B)) • (m : M) = b • ((z : B) • (m : M))
    rw [mul_assoc, S.e_mul_coe, mul_comm (S.e i) b, mul_assoc, S.e_mul_coe, mul_smul])⟩

end CornerModule

section Base

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]

noncomputable def cornerRingLinearEquiv :
    S.CornerRing i ≃ₗ[𝒪] ↥(cornerSubmodule (M := B) (S.e i)) where
  toFun x := ⟨x.1, by
    obtain ⟨b, hb⟩ := x.2
    refine ⟨b * S.e i, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    linear_combination hb⟩
  invFun x := ⟨x.1, by
    obtain ⟨y, hy⟩ := x.2
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at hy
    exact ⟨y, by linear_combination y * (S.idem i).eq + hy⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_smul' r x := Subtype.ext (by
    obtain ⟨b, hb⟩ := x.2
    show (S.e i * algebraMap 𝒪 B r * S.e i) * (x : B) = r • (x : B)
    rw [Algebra.smul_def]
    linear_combination (algebraMap 𝒪 B r * b * (S.e i * S.e i + S.e i)) * (S.idem i).eq
      + (algebraMap 𝒪 B r - S.e i * algebraMap 𝒪 B r * S.e i) * hb)

/--
@isnad1 id=eq.0h5v.s10.02b2884c76f7 from=translated src=- shape=56ec849d vocab=83afd3a8
-/
@[simp] theorem cornerRingLinearEquiv_apply (x : S.CornerRing i) :
    ((cornerRingLinearEquiv S i 𝒪 x : cornerSubmodule (M := B) (S.e i)) : B) = (x : B) := rfl

/--
@isnad1 id=eq.0h5v.s10.5ea89a0d79fb from=translated src=- shape=5bf45a1a vocab=f65b86d6
-/
@[simp] theorem cornerRingLinearEquiv_symm_apply (x : cornerSubmodule (M := B) (S.e i)) :
    (((cornerRingLinearEquiv S i 𝒪).symm x : S.CornerRing i) : B) = (x : B) := rfl

end Base

section BaseModule

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]
variable {M : Type} [AddCommGroup M] [Module B M] [Module 𝒪 M] [IsScalarTower 𝒪 B M]

/--
@isnad1 id=isscalar.0h5v.s8.af6f46a47b80 from=translated src=- shape=1f7cdfec vocab=b6ce46aa
-/
instance isScalarTower_base_cornerModule :
    IsScalarTower 𝒪 (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) :=
  ⟨fun r z m => by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪 B (S.CornerRing i) r, ← Algebra.smul_def,
      smul_assoc, algebraMap_smul]⟩

end BaseModule

end IdempotentSplitting

end IharaLemma
