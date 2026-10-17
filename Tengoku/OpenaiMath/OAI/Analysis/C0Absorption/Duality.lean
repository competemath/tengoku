import Tengoku.OpenaiMath.OAI.Analysis.C0Absorption.Tests

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section ClassDuality
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def BoundedTest (f : S → ℝ) : Prop :=
  ∃ K : ℝ≥0, ∀ m : PreSpace L o, |pairing S f m| ≤ K*‖m‖

/--
@isnad1 id=ex.1h5v.s9.33fd3115ba4d from=translated src=- shape=395f4694 vocab=12420933
-/
theorem class_pairing_bound (j : ℕ) (K : ℝ≥0)
    (hK : ∀ f ∈ L j, LipschitzWith K f) :
    ∃ A : ℝ≥0, ∀ f ∈ L j, ∀ m : PreSpace L o, |pairing S f m| ≤ A*‖m‖ := by
  obtain ⟨C,hC⟩ := exists_nat_gt (K : ℝ)
  obtain ⟨n,hn⟩ := triple_surjective (j,C,0)
  refine ⟨(squareWeight n)⁻¹,?_⟩
  intro f hf m
  apply test_pairing_bound L o n f
  · simpa only [hn] using hf
  · apply (hK f hf).weaken
    change K ≤ ((triple n).2.1 : ℝ≥0)+1
    rw [hn]
    exact_mod_cast (show (K : ℝ) ≤ (C : ℝ)+1 by linarith)

/--
@isnad1 id=tendsto.2h6v.s8.c80063c54683 from=translated src=- shape=433bd9e3 vocab=3977b115
-/
theorem BoundedTest.weak_null {f : S → ℝ} (hf : BoundedTest L o f)
    (m : ℕ → TestSpace L o) (M : ℝ)
    (hm : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    Tendsto (fun i => completedPairing L o f (m i)) atTop (nhds 0) := by
  obtain ⟨K,hK⟩ := hf
  simpa only [completedTest_eq] using bounded_signs_weak_null m M hm (completedTest L o f K hK)

/--
@isnad1 id=eq.0h4v.s10.98b01e0fc510 from=translated src=- shape=f571593b vocab=7fbffff8
-/
theorem pairing_add {S : Type*} [MetricSpace S]
    (f g : S → ℝ) (m : Molecule S) :
    pairing S (fun s => f s+g s) m = pairing S f m+pairing S g m := by
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul, mul_add, Finsupp.sum, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h4v.s10.39a36be5d7c7 from=translated src=- shape=7b783f73 vocab=c284ff30
-/
theorem pairing_smul {S : Type*} [MetricSpace S]
    (a : ℝ) (f : S → ℝ) (m : Molecule S) :
    pairing S (fun s => a*f s) m = a*pairing S f m := by
  simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply, smul_eq_mul, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/--
@isnad1 id=boundedt.2h5v.s5.e94b9d5400e0 from=translated src=- shape=157e659c vocab=986d11bc
-/
theorem BoundedTest.add {f g : S → ℝ} (hf : BoundedTest L o f) (hg : BoundedTest L o g) :
    BoundedTest L o (fun s => f s+g s) := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨A,hA⟩ := hg
  refine ⟨K+A,fun m => ?_⟩
  erw [pairing_add]
  exact (abs_add_le _ _).trans ((add_le_add (hK m) (hA m)).trans_eq (by push_cast; ring))

/--
@isnad1 id=boundedt.1h5v.s5.90244b0a1409 from=translated src=- shape=73702f13 vocab=ca1d58d2
-/
theorem BoundedTest.smul {f : S → ℝ} (hf : BoundedTest L o f) (a : ℝ) :
    BoundedTest L o (fun s => a*f s) := by
  obtain ⟨K,hK⟩ := hf
  refine ⟨‖a‖₊*K,fun m => ?_⟩
  erw [pairing_smul, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hK m) (abs_nonneg a)).trans_eq (by
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]; ring)

/--
@isnad1 id=eq.2h6v.s6.ce9bb0a9e1e9 from=translated src=- shape=5f198f22 vocab=04ff4f7b
-/
theorem completedPairing_add (f g : S → ℝ) (hf : BoundedTest L o f) (hg : BoundedTest L o g)
    (z : TestSpace L o) : completedPairing L o (fun s => f s+g s) z =
      completedPairing L o f z+completedPairing L o g z := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨A,hA⟩ := hg
  obtain ⟨B,hB⟩ := (BoundedTest.add L o ⟨K,hK⟩ ⟨A,hA⟩)
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (completedPairing_lipschitz L o _ B hB).continuous
      ((completedPairing_lipschitz L o _ K hK).continuous.add (completedPairing_lipschitz L o _ A hA).continuous)
  | ih m =>
    change completedPairing L o _ (toTestSpace L o m) = _
    erw [completedPairing_coe L o _ B hB, completedPairing_coe L o _ K hK,
      completedPairing_coe L o _ A hA]
    exact pairing_add f g m

/--
@isnad1 id=eq.1h6v.s6.932c005178e5 from=translated src=- shape=3a9f00de vocab=df64dad0
-/
theorem completedPairing_smul (a : ℝ) (f : S → ℝ) (hf : BoundedTest L o f)
    (z : TestSpace L o) : completedPairing L o (fun s => a*f s) z = a*completedPairing L o f z := by
  obtain ⟨K,hK⟩ := hf
  obtain ⟨B,hB⟩ := BoundedTest.smul L o ⟨K,hK⟩ a
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (completedPairing_lipschitz L o _ B hB).continuous
      (continuous_const.mul (completedPairing_lipschitz L o _ K hK).continuous)
  | ih m =>
    change completedPairing L o _ (toTestSpace L o m) = _
    erw [completedPairing_coe L o _ B hB, completedPairing_coe L o _ K hK]
    exact pairing_smul a f m

end ClassDuality

variable {Γ : Type*} {B : CylinderBases Γ}

def c0Origin : C0Ball := ⟨0,by simp⟩
abbrev SourceSpace (B : CylinderBases Γ) := TestSpace (sourceClasses B) c0Origin

/--
@isnad1 id=le.1h4v.s5.397af83581d4 from=translated src=- shape=e9672661 vocab=79f633a6
-/
theorem TClass_mono {h k : ℕ} (hk : h ≤ k) : TClass B h ⊆ TClass B k := by
  rintro f ⟨γ,r,hr,rfl⟩
  exact ⟨γ,r,hr.trans hk,rfl⟩

/--
@isnad1 id=le.1h4v.s5.86872167e37e from=translated src=- shape=e9672661 vocab=2702e067
-/
theorem VClass_mono {h k : ℕ} (hk : h ≤ k) : VClass B h ⊆ VClass B k := by
  rintro f ⟨γ,r,ts,hr,hj,ht,hs,rfl⟩
  exact ⟨γ,r,ts,hr.trans hk,hj.trans hk,ht.trans hk,fun t hm => (hs t hm).trans hk,rfl⟩

/--
@isnad1 id=mem.2h5v.s6.6a7ae240334b from=translated src=- shape=19de2276 vocab=5c461cb0
-/
theorem representation_mem_VClass {γ : Γ} (r : GeneratedRepresentation B γ) {h : ℕ}
    (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h) : r.value ∈ VClass B h := by
  refine ⟨γ,r,[],hr,hj,by simp,by simp,?_⟩
  funext s
  simp

/--
@isnad1 id=ex.0h3v.s6.5041596d3759 from=translated src=- shape=69f0cc9b vocab=2c11eeff
-/
theorem sourceClasses_lipschitz (B : CylinderBases Γ) (n : ℕ) :
    ∃ K : ℝ≥0, ∀ f ∈ sourceClasses B n, LipschitzWith K f := by
  unfold sourceClasses
  split
  · exact ⟨_, fun _ hf => TClass_lipschitz B _ hf⟩
  · exact ⟨_, fun _ hf => VClass_lipschitz B _ hf⟩

/--
@isnad1 id=ex.0h3v.s9.ddb325a2ae21 from=translated src=- shape=9c81b5e5 vocab=48110f1e
-/
theorem TClass_pairing_bound (B : CylinderBases Γ) (h : ℕ) :
    ∃ A : ℝ≥0, ∀ f ∈ TClass B h, ∀ m : PreSpace (sourceClasses B) c0Origin,
      |pairing C0Ball f m| ≤ A*‖m‖ := by
  have hh := class_pairing_bound (sourceClasses B) c0Origin (2*h) (4^(h+1)*B.L0) (by
    simpa only [sourceClasses_even] using (fun f hf => TClass_lipschitz B (h+1) (f := f) hf))
  obtain ⟨A,hA⟩ := hh
  exact ⟨A,fun f hf => hA f (by simpa only [sourceClasses_even] using TClass_mono (Nat.le_succ h) hf)⟩

/--
@isnad1 id=ex.0h3v.s9.bd3d94a3b67a from=translated src=- shape=9c81b5e5 vocab=137e3c6d
-/
theorem VClass_pairing_bound (B : CylinderBases Γ) (h : ℕ) :
    ∃ A : ℝ≥0, ∀ f ∈ VClass B h, ∀ m : PreSpace (sourceClasses B) c0Origin,
      |pairing C0Ball f m| ≤ A*‖m‖ := by
  have hh := class_pairing_bound (sourceClasses B) c0Origin (2*h+1)
    (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A) (by
      simpa only [sourceClasses_odd, Nat.cast_add, Nat.cast_one] using (fun f hf => VClass_lipschitz B (h+1) (f := f) hf))
  obtain ⟨A,hA⟩ := hh
  exact ⟨A,fun f hf => hA f (by simpa only [sourceClasses_odd] using VClass_mono (Nat.le_succ h) hf)⟩

/--
@isnad1 id=boundedt.1h4v.s6.6871b136bbb9 from=translated src=- shape=3cd2bc58 vocab=3d09ef65
-/
theorem TClass_bounded {h : ℕ} {f : C0Ball → ℝ} (hf : f ∈ TClass B h) :
    BoundedTest (sourceClasses B) c0Origin f := by
  obtain ⟨A,hA⟩ := TClass_pairing_bound B h
  exact ⟨A,hA f hf⟩

/--
@isnad1 id=boundedt.1h4v.s6.4d6d43120408 from=translated src=- shape=3cd2bc58 vocab=cefbfd9d
-/
theorem VClass_bounded {h : ℕ} {f : C0Ball → ℝ} (hf : f ∈ VClass B h) :
    BoundedTest (sourceClasses B) c0Origin f := by
  obtain ⟨A,hA⟩ := VClass_pairing_bound B h
  exact ⟨A,hA f hf⟩

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def flattenOperation (I : Finset ℕ) (a : ℕ) (v : Cube I) : CylinderOperation I :=
  ⟨a,nearestOperationGrid I a v,true⟩

/--
@isnad1 id=eq.0h3v.s4.351dec2bd331 from=translated src=- shape=a6b159b6 vocab=f816edd1
-/
@[simp] theorem flattenOperation_scale (I : Finset ℕ) (a : ℕ) (v : Cube I) :
    (flattenOperation I a v).scale = dyadic a := rfl

/--
@isnad1 id=eq.0h4v.s8.4fb5c5e5fd38 from=translated src=- shape=a71c22bb vocab=9df1d415
-/
@[simp] theorem flattenOperation_act (I : Finset ℕ) (a : ℕ) (v : Cube I) (u : Cube I → ℝ) :
    (flattenOperation I a v).act u = localG (flattenOperation I a v).point (dyadic a) u := rfl

/--
@isnad1 id=le.0h3v.s7.b9218a747ddc from=translated src=- shape=857a8dfd vocab=359b34e7
-/
theorem flattenOperation_center (I : Finset ℕ) (a : ℕ) (v : Cube I) :
    dist v (flattenOperation I a v).point ≤ dyadic a/16 := nearestOperationGrid_dist I a v

/--
@isnad1 id=eq.1h5v.s8.059a52b8d186 from=translated src=- shape=26bb5cd7 vocab=58a7b00c
-/
theorem flattenOperation_plateau (I : Finset ℕ) (a : ℕ) (v : Cube I) (u : Cube I → ℝ)
    (x : Cube I) (hx : dist x v < 3*dyadic a/8) :
    (flattenOperation I a v).act u x = u (flattenOperation I a v).point := by
  apply localG_plateau _ (dyadic_pos a) u x
  have hh := dist_triangle x v (flattenOperation I a v).point
  have hc := flattenOperation_center I a v
  linarith [dyadic_pos a]

/--
@isnad1 id=le.1h6v.s8.766853a3b0c4 from=translated src=- shape=64d44cd4 vocab=27a844a2
-/
theorem flattenOperation_difference (I : Finset ℕ) (a : ℕ) (v : Cube I)
    {u : Cube I → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (x : Cube I) :
    |(flattenOperation I a v).act u x-u x| ≤ dyadic a*K := by
  rw [flattenOperation_act, localG_eq, add_sub_cancel_left]
  exact localR_sup_lip _ (dyadic_pos a) u hu x

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

/--
@isnad1 id=ex.6h10v.s9.a5f13369c1ef from=translated src=- shape=2e697c48 vocab=c64fe401
-/
theorem exists_flatten (r : GeneratedRepresentation B γ) (ts : List TailOperation)
    (h : ℕ) (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ts.length ≤ h) (hs : ∀ t ∈ ts, t.scaleIndex ≤ h)
    (v : Cube (B.coordinates γ)) (z : SourceSpace B) {δ cap : ℝ}
    (hδ : 0 < δ) (hcap : 0 < cap) :
    ∃ (a : ℕ) (r' : GeneratedRepresentation B γ),
      dyadic a < cap ∧ r'.operations = r.operations++[flattenOperation (B.coordinates γ) a v] ∧
      |completedPairing (sourceClasses B) c0Origin (fun s => r'.value s*tailProduct ts s) z-
        completedPairing (sourceClasses B) c0Origin (fun s => r.value s*tailProduct ts s) z| < δ ∧
      (∀ s, dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic a/8 →
        r'.value s = r.cubeValue (flattenOperation (B.coordinates γ) a v).point) ∧
      (∀ s, |r'.value s| ≤ (2 : ℝ)^r.operations.length*B.A) := by
  have he := r.eventually_append_allowed.and (dyadic_tendsto.eventually (eventually_lt_nhds hcap))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let op (n : ℕ) := flattenOperation (B.coordinates γ) (N+n) v
  have ho (n : ℕ) : ∀ p ∈ r.operations, (op n).scale ≤ p.scale := (hN (N+n) (by omega)).1.1
  have hb (n : ℕ) : (r.operations.map CylinderOperation.scale).sum+(op n).scale < B.ell (B.band γ)/2 :=
    (hN (N+n) (by omega)).1.2
  let rr (n : ℕ) := r.append (op n) (ho n) (hb n)
  let f (n : ℕ) (s : C0Ball) := (rr n).value s*tailProduct ts s
  let g (s : C0Ball) := r.value s*tailProduct ts s
  have hf (n : ℕ) : f n ∈ VClass B (h+1) := by
    refine ⟨γ,rr n,ts,?_,hj.trans (Nat.le_succ h),ht.trans (Nat.le_succ h),
      fun t hm => (hs t hm).trans (Nat.le_succ h),rfl⟩
    simpa only [rr, append, List.length_append, List.length_singleton] using Nat.add_le_add_right hr 1
  have hsc : Tendsto (fun n => dyadic (N+n)) atTop (nhds 0) :=
    dyadic_tendsto.comp (tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ N+n) tendsto_id)
  have hp (s : C0Ball) : Tendsto (fun n => f n s) atTop (nhds (g s)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound (n : ℕ) : dist (f n s) (g s) ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
      simp only [f,g,Real.dist_eq,← sub_mul,abs_mul]
      have hd : |(rr n).value s-r.value s| ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
        change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)-r.cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
        rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
        exact flattenOperation_difference _ (N+n) v r.cubeValue_lipschitz _
      exact (mul_le_mul hd (tailProduct_abs_le ts s) (abs_nonneg _) (mul_nonneg (dyadic_pos _).le (NNReal.coe_nonneg _))).trans_eq (mul_one _)
    exact squeeze_zero (fun n => dist_nonneg) hbound (by simpa using hsc.mul_const ((4^r.operations.length*B.L0 : ℝ≥0) : ℝ))
  obtain ⟨A,hA⟩ := VClass_pairing_bound B (h+1)
  have hconv := (completedPairing_tendsto (sourceClasses B) c0Origin f g A
    (fun n => hA (f n) (hf n)) hp).2 z
  have hev : ∀ᶠ n in atTop, |completedPairing (sourceClasses B) c0Origin (f n) z-
      completedPairing (sourceClasses B) c0Origin g z| < δ := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hconv) δ hδ
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨N+n,rr n,(hN (N+n) (by omega)).2,rfl,hn,?_,?_⟩
  · intro s hss
    change (rr n).cubeValue (cubeRestrict (B.coordinates γ) s) = _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact flattenOperation_plateau _ _ _ r.cubeValue _ hss
  · intro s
    change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact localG_sup _ _ _ _ r.cubeValue_sup _

/--
@isnad1 id=ex.3h9v.s8.c5223ec48dde from=translated src=- shape=b644c0bd vocab=8364c2c3
-/
theorem exists_flatten_T (r : GeneratedRepresentation B γ)
    (h : ℕ) (hr : r.operations.length ≤ h)
    (v : Cube (B.coordinates γ)) (z : SourceSpace B) {δ cap : ℝ}
    (hδ : 0 < δ) (hcap : 0 < cap) :
    ∃ (a : ℕ) (r' : GeneratedRepresentation B γ),
      dyadic a < cap ∧ r'.operations = r.operations++[flattenOperation (B.coordinates γ) a v] ∧
      |completedPairing (sourceClasses B) c0Origin r'.value z-
        completedPairing (sourceClasses B) c0Origin r.value z| < δ ∧
      (∀ s, dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic a/8 →
        r'.value s = r.cubeValue (flattenOperation (B.coordinates γ) a v).point) ∧
      (∀ s, |r'.value s| ≤ (2 : ℝ)^r.operations.length*B.A) := by
  have he := r.eventually_append_allowed.and (dyadic_tendsto.eventually (eventually_lt_nhds hcap))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let op (n : ℕ) := flattenOperation (B.coordinates γ) (N+n) v
  have ho (n : ℕ) : ∀ p ∈ r.operations, (op n).scale ≤ p.scale := (hN (N+n) (by omega)).1.1
  have hb (n : ℕ) : (r.operations.map CylinderOperation.scale).sum+(op n).scale < B.ell (B.band γ)/2 :=
    (hN (N+n) (by omega)).1.2
  let rr (n : ℕ) := r.append (op n) (ho n) (hb n)
  let f (n : ℕ) (s : C0Ball) := (rr n).value s
  let g (s : C0Ball) := r.value s
  have hf (n : ℕ) : f n ∈ TClass B (h+1) := by
    refine ⟨γ,rr n,?_,rfl⟩
    simpa only [rr, append, List.length_append, List.length_singleton] using Nat.add_le_add_right hr 1
  have hsc : Tendsto (fun n => dyadic (N+n)) atTop (nhds 0) :=
    dyadic_tendsto.comp (tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ N+n) tendsto_id)
  have hp (s : C0Ball) : Tendsto (fun n => f n s) atTop (nhds (g s)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound (n : ℕ) : dist (f n s) (g s) ≤ dyadic (N+n)*(4^r.operations.length*B.L0 : ℝ≥0) := by
      change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)-r.cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
      rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
      exact flattenOperation_difference _ (N+n) v r.cubeValue_lipschitz _
    exact squeeze_zero (fun n => dist_nonneg) hbound (by simpa using hsc.mul_const ((4^r.operations.length*B.L0 : ℝ≥0) : ℝ))
  obtain ⟨A,hA⟩ := TClass_pairing_bound B (h+1)
  have hconv := (completedPairing_tendsto (sourceClasses B) c0Origin f g A
    (fun n => hA (f n) (hf n)) hp).2 z
  have hev : ∀ᶠ n in atTop, |completedPairing (sourceClasses B) c0Origin (f n) z-
      completedPairing (sourceClasses B) c0Origin g z| < δ := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hconv) δ hδ
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨N+n,rr n,(hN (N+n) (by omega)).2,rfl,hn,?_,?_⟩
  · intro s hss
    change (rr n).cubeValue (cubeRestrict (B.coordinates γ) s) = _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact flattenOperation_plateau _ _ _ r.cubeValue _ hss
  · intro s
    change |(rr n).cubeValue (cubeRestrict (B.coordinates γ) s)| ≤ _
    rw [show (rr n).cubeValue = (op n).act r.cubeValue from r.append_cubeValue _ _ _]
    exact localG_sup _ _ _ _ r.cubeValue_sup _

end GeneratedRepresentation
end
end C0Absorption

end OAI
