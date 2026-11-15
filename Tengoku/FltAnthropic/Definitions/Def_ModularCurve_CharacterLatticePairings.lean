import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace ModularCurve

open Finset

variable (S : Type*) [Fintype S]

/--
@isnad1 id=eq.0h3v.s6.21e35c2ea53b from=translated src=- shape=44e6e43d vocab=ba68ecc2
-/
theorem degreeOn_single [DecidableEq S] (s : S) (n : ℤ) : degreeOn S (Pi.single s n) = n := by
  simp [degreeOn_apply]

/--
@isnad1 id=eq.0h2v.s6.c1f5e6a9f16e from=translated src=- shape=e47bb354 vocab=e31fc2c3
-/
theorem degreeOn_const (n : ℤ) : degreeOn S (fun _ => n) = Fintype.card S • n := by
  simp [degreeOn_apply]

variable {S}

/--
@isnad1 id=mem.0h3v.s7.dec7753acaee from=translated src=- shape=45147215 vocab=9e24c6a1
-/
theorem single_sub_single_mem [DecidableEq S] (s t : S) :
    Pi.single s (1 : ℤ) - Pi.single t 1 ∈ characterLattice S := by
  rw [characterLattice, LinearMap.mem_ker, map_sub, degreeOn_single, degreeOn_single, sub_self]

namespace CharacterLattice

section MultiplicativePairing

variable {G : Type*} [CommGroup G]

/--
@isnad1 id=eq.0h5v.s6.ee042c0d6ea6 from=translated src=- shape=82cdc3aa vocab=46fa6e31
-/
theorem zpow_finset_sum {ι : Type*} (g : G) (e : ι → ℤ) (t : Finset ι) :
    g ^ (∑ i ∈ t, e i) = ∏ i ∈ t, g ^ e i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

def zpowProd (a : S → ℤ) (w : S → G) : G := ∏ s, w s ^ a s

/--
@isnad1 id=eq.0h4v.s5.401647fd59b6 from=translated src=- shape=96927b69 vocab=80a3a6a0
-/
@[simp]
theorem zpowProd_def (a : S → ℤ) (w : S → G) : zpowProd a w = ∏ s, w s ^ a s := rfl

/--
@isnad1 id=eq.0h5v.s6.fb56f051c12b from=translated src=- shape=cac1a371 vocab=ed7d726c
-/
theorem zpowProd_add (a b : S → ℤ) (w : S → G) :
    zpowProd (a + b) w = zpowProd a w * zpowProd b w := by
  simp [zpowProd, zpow_add, Finset.prod_mul_distrib]

/--
@isnad1 id=eq.0h3v.s5.7a05748c05b7 from=translated src=- shape=cbce573d vocab=ae91fe8c
-/
theorem zpowProd_zero_left (w : S → G) : zpowProd (0 : S → ℤ) w = 1 := by
  simp [zpowProd]

/--
@isnad1 id=eq.0h4v.s5.c709e7ab3de7 from=translated src=- shape=6b13b6d8 vocab=9ba7c74d
-/
theorem zpowProd_neg (a : S → ℤ) (w : S → G) : zpowProd (-a) w = (zpowProd a w)⁻¹ := by
  simp [zpowProd, Finset.prod_inv_distrib]

/--
@isnad1 id=eq.0h5v.s6.c7e33c82f155 from=translated src=- shape=d1fe388d vocab=34ad968f
-/
theorem zpowProd_mul (a : S → ℤ) (w w' : S → G) :
    zpowProd a (w * w') = zpowProd a w * zpowProd a w' := by
  simp [zpowProd, mul_zpow, Finset.prod_mul_distrib]

/--
@isnad1 id=eq.0h3v.s6.47371748a872 from=translated src=- shape=3a21bd0a vocab=ae91fe8c
-/
theorem zpowProd_one_right (a : S → ℤ) : zpowProd a (1 : S → G) = 1 := by
  simp [zpowProd]

/--
@isnad1 id=eq.0h4v.s7.147931e98acc from=translated src=- shape=0784a871 vocab=49c269d9
-/
theorem zpowProd_const (a : S → ℤ) (c : G) : zpowProd a (fun _ => c) = c ^ degreeOn S a := by
  rw [zpowProd_def, degreeOn_apply, zpow_finset_sum]

/--
@isnad1 id=eq.1h4v.s7.1cc0336a876b from=translated src=- shape=80cdf01e vocab=d5fe3547
-/
theorem zpowProd_const_of_mem {a : S → ℤ} (ha : a ∈ characterLattice S) (c : G) :
    zpowProd a (fun _ => c) = 1 := by
  rw [zpowProd_const, show degreeOn S a = 0 from ha, zpow_zero]

def zpowProdHom (a : S → ℤ) : (S → G) →* G where
  toFun := zpowProd a
  map_one' := zpowProd_one_right a
  map_mul' := zpowProd_mul a

/--
@isnad1 id=eq.0h4v.s6.5fc6f1564b9f from=translated src=- shape=ac47bc00 vocab=438b0984
-/
@[simp]
theorem zpowProdHom_apply (a : S → ℤ) (w : S → G) : zpowProdHom a w = zpowProd a w := rfl

def evalHom (a : characterLattice S) : (S → G) →* G := zpowProdHom (a : S → ℤ)

/--
@isnad1 id=eq.0h4v.s8.46e32b7bacbf from=translated src=- shape=710b1d31 vocab=49ec6c3b
-/
@[simp]
theorem evalHom_apply (a : characterLattice S) (w : S → G) : evalHom a w = ∏ s, w s ^ (a : S → ℤ) s := rfl

/--
@isnad1 id=eq.0h4v.s7.d1cc846aef8b from=translated src=- shape=8aea37a3 vocab=5b1e5acd
-/
theorem evalHom_const (a : characterLattice S) (c : G) : evalHom a (fun _ => c) = 1 :=
  zpowProd_const_of_mem a.2 c

/--
@isnad1 id=eq.0h5v.s9.107784b3724b from=translated src=- shape=2a17643b vocab=45e1deb4
-/
theorem evalHom_add (a b : characterLattice S) (w : S → G) :
    evalHom (a + b) w = evalHom a w * evalHom b w :=
  zpowProd_add _ _ w

end MultiplicativePairing

section AdditivePairing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def smulSum (a : S → ℤ) (v : S → M) : M := ∑ s, a s • v s

/--
@isnad1 id=eq.0h4v.s5.9fa3a976fc3a from=translated src=- shape=b9065ad9 vocab=324e962a
-/
@[simp]
theorem smulSum_def (a : S → ℤ) (v : S → M) : smulSum a v = ∑ s, a s • v s := rfl

/--
@isnad1 id=eq.0h5v.s6.b2c9c93c3f4d from=translated src=- shape=cac1a371 vocab=7133e8b9
-/
theorem smulSum_add_left (a b : S → ℤ) (v : S → M) :
    smulSum (a + b) v = smulSum a v + smulSum b v := by
  simp [smulSum, add_smul, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h5v.s6.0c4b51b764f6 from=translated src=- shape=d1fe388d vocab=7133e8b9
-/
theorem smulSum_add_right (a : S → ℤ) (v v' : S → M) :
    smulSum a (v + v') = smulSum a v + smulSum a v' := by
  simp [smulSum, smul_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h6v.s7.92b6583f8b76 from=translated src=- shape=718b5826 vocab=5c639c91
-/
theorem smulSum_smul_right (a : S → ℤ) (r : R) (v : S → M) :
    smulSum a (r • v) = r • smulSum a v := by
  simp only [smulSum_def, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _

/--
@isnad1 id=eq.0h4v.s7.3aefb683e222 from=translated src=- shape=9f08944b vocab=05af3b7a
-/
theorem smulSum_const (a : S → ℤ) (m : M) : smulSum a (fun _ => m) = degreeOn S a • m := by
  simp [smulSum, degreeOn_apply, Finset.sum_smul]

/--
@isnad1 id=eq.1h4v.s7.741a8bdc3f04 from=translated src=- shape=80cdf01e vocab=ad12fb5a
-/
theorem smulSum_const_of_mem {a : S → ℤ} (ha : a ∈ characterLattice S) (m : M) :
    smulSum a (fun _ => m) = 0 := by
  rw [smulSum_const, show degreeOn S a = 0 from ha, zero_smul]

end AdditivePairing

section Functoriality

variable {S' : Type*} [Fintype S']

def IsDegreeScaling (f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)) (d : ℤ) : Prop :=
  ∀ a, degreeOn S' (f a) = d * degreeOn S a

/--
@isnad1 id=mem.2h5v.s8.14e9ef9525bd from=translated src=- shape=c5de25ee vocab=8ab02b07
-/
theorem IsDegreeScaling.map_mem {f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)} {d : ℤ} (hf : IsDegreeScaling f d)
    {a : S → ℤ} (ha : a ∈ characterLattice S) : f a ∈ characterLattice S' := by
  rw [characterLattice, LinearMap.mem_ker, hf a, show degreeOn S a = 0 from ha, mul_zero]

def restrictDegZero (f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)) (d : ℤ) (hf : IsDegreeScaling f d) :
    characterLattice S →ₗ[ℤ] characterLattice S' :=
  f.restrict fun _ ha => hf.map_mem ha

/--
@isnad1 id=eq.1h5v.s10.10491081668e from=translated src=- shape=e7c1967e vocab=e81d1213
-/
@[simp]
theorem coe_restrictDegZero_apply (f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)) (d : ℤ) (hf : IsDegreeScaling f d)
    (a : characterLattice S) : (restrictDegZero f d hf a : S' → ℤ) = f a := rfl

omit [Fintype S] [Fintype S'] in

def permMapFun (σ : S ≃ S') : (S → ℤ) →ₗ[ℤ] (S' → ℤ) :=
  LinearMap.funLeft ℤ ℤ σ.symm

omit [Fintype S] [Fintype S'] in
/--
@isnad1 id=eq.0h5v.s7.d40af8eae05b from=translated src=- shape=563161a0 vocab=6de0a956
-/
@[simp]
theorem permMapFun_apply (σ : S ≃ S') (a : S → ℤ) (s' : S') : permMapFun σ a s' = a (σ.symm s') := rfl

/--
@isnad1 id=isdegree.0h3v.s4.464e5b324fb8 from=translated src=- shape=53d43319 vocab=af8b1251
-/
theorem isDegreeScaling_permMapFun (σ : S ≃ S') : IsDegreeScaling (permMapFun σ) 1 := by
  intro a
  simp only [degreeOn_apply, permMapFun_apply, one_mul]
  exact Fintype.sum_equiv σ.symm _ _ fun _ => rfl

def permMap (σ : S ≃ S') : characterLattice S →ₗ[ℤ] characterLattice S' :=
  restrictDegZero (permMapFun σ) 1 (isDegreeScaling_permMapFun σ)

/--
@isnad1 id=eq.0h5v.s10.97e61bea84e5 from=translated src=- shape=96935b84 vocab=f479ea79
-/
@[simp]
theorem coe_permMap_apply (σ : S ≃ S') (a : characterLattice S) (s' : S') :
    (permMap σ a : S' → ℤ) s' = (a : S → ℤ) (σ.symm s') := rfl

omit [Fintype S'] in

def corrMapFun (B : S → S' → ℤ) : (S → ℤ) →ₗ[ℤ] (S' → ℤ) where
  toFun a s' := ∑ s, a s * B s s'
  map_add' a b := by ext s'; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by ext s'; simp [Finset.mul_sum, mul_assoc]

omit [Fintype S'] in
/--
@isnad1 id=eq.0h5v.s7.a203929d3a3d from=translated src=- shape=35f14c6b vocab=36079ea0
-/
@[simp]
theorem corrMapFun_apply (B : S → S' → ℤ) (a : S → ℤ) (s' : S') :
    corrMapFun B a s' = ∑ s, a s * B s s' := rfl

/--
@isnad1 id=isdegree.1h4v.s5.eb0848dbfcd7 from=translated src=- shape=805d7359 vocab=744388ba
-/
theorem isDegreeScaling_corrMapFun (B : S → S' → ℤ) (d : ℤ) (hB : ∀ s, ∑ s', B s s' = d) :
    IsDegreeScaling (corrMapFun B) d := by
  intro a
  simp only [degreeOn_apply, corrMapFun_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, hB s, mul_comm]

def corrMap (B : S → S' → ℤ) (d : ℤ) (hB : ∀ s, ∑ s', B s s' = d) :
    characterLattice S →ₗ[ℤ] characterLattice S' :=
  restrictDegZero (corrMapFun B) d (isDegreeScaling_corrMapFun B d hB)

/--
@isnad1 id=eq.1h6v.s10.f97a958d27d5 from=translated src=- shape=3e699d0a vocab=96848ffe
-/
@[simp]
theorem coe_corrMap_apply (B : S → S' → ℤ) (d : ℤ) (hB : ∀ s, ∑ s', B s s' = d)
    (a : characterLattice S) (s' : S') :
    (corrMap B d hB a : S' → ℤ) s' = ∑ s, (a : S → ℤ) s * B s s' := rfl

/--
@isnad1 id=eq.0h6v.s7.19ddfbe8a0ef from=translated src=- shape=9d2f7563 vocab=573b6bd8
-/
theorem zpowProd_permMapFun {G : Type*} [CommGroup G] (σ : S ≃ S') (a : S → ℤ) (w : S' → G) :
    zpowProd (permMapFun σ a) w = zpowProd a (w ∘ σ) := by
  simp only [zpowProd, permMapFun_apply, Function.comp_apply]
  exact Fintype.prod_equiv σ.symm _ _ fun _ => by simp

/--
@isnad1 id=eq.0h6v.s7.0c0914be8bb7 from=translated src=- shape=d7b89eba vocab=8d73a484
-/
theorem zpowProd_corrMapFun {G : Type*} [CommGroup G] (B : S → S' → ℤ) (a : S → ℤ) (w : S' → G) :
    zpowProd (corrMapFun B a) w = zpowProd a (fun s => ∏ s', w s' ^ B s s') := by
  simp only [zpowProd_def, corrMapFun_apply]
  calc (∏ s', w s' ^ ∑ s, a s * B s s')
      = ∏ s', ∏ s, w s' ^ (a s * B s s') :=
          Finset.prod_congr rfl fun s' _ => zpow_finset_sum (w s') _ _
    _ = ∏ s, ∏ s', w s' ^ (a s * B s s') := Finset.prod_comm
    _ = ∏ s, (∏ s', w s' ^ B s s') ^ a s := by
          refine Finset.prod_congr rfl fun s _ => ?_
          rw [← Finset.prod_zpow]
          exact Finset.prod_congr rfl fun s' _ => by rw [zpow_mul']

end Functoriality

end CharacterLattice

end ModularCurve
