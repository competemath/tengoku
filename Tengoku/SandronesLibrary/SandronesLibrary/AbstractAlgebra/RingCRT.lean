/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.RingIsomorphismTheorems

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 中国剩余定理

本模块从本库集合型双边理想和显式商环出发，构造二元及有限族中国剩余规范映射，证明其核、
满射性与最终环同构。有限族满射的证明局部借用 Mathlib 的理想 CRT；主同构以语义一致的
`RingEquiv` 为正式承载，历史 `RingIsomorphism` 结果只保留为无损兼容层。本库
`TwoSidedIdealSet`、`quotientRingSet` 与 `RingHomomorphism` 教材定义层保持不变。

> **Entry**: abstract-algebra.ring.crt
-/

namespace SandronesLibrary.AbstractAlgebra.Ring

attribute [local instance] quotientRingSetRing

/-- 两个理想互素：它们的和等于整个环。-/
def ComaximalIdealSets {R : Type*} [Ring R] (I J : Set R) : Prop :=
  idealSetSum I J = Set.univ

/-- 两个双边理想的交仍是双边理想。
@isnad1 id=twosided.2h3v.s7.07e3f69c8d36 from=translated src=- shape=0540dca0 vocab=da7dc750
-/
theorem idealSetIntersection_is_ideal {R : Type*} [Ring R] {I J : Set R}
    (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J) :
    TwoSidedIdealSet (I ∩ J) := by
  constructor
  · exact ⟨⟨hI.1.1, hJ.1.1⟩,
      (by intro x y hx hy; exact ⟨hI.1.2.1 hx.1 hy.1, hJ.1.2.1 hx.2 hy.2⟩),
      (by intro x hx; exact ⟨hI.1.2.2.1 hx.1, hJ.1.2.2.1 hx.2⟩),
      by intro r x hx; exact ⟨hI.1.2.2.2 r hx.1, hJ.1.2.2.2 r hx.2⟩⟩
  · exact ⟨⟨hI.2.1, hJ.2.1⟩,
      (by intro x y hx hy; exact ⟨hI.2.2.1 hx.1 hy.1, hJ.2.2.1 hx.2 hy.2⟩),
      (by intro x hx; exact ⟨hI.2.2.2.1 hx.1, hJ.2.2.2.1 hx.2⟩),
      by intro r x hx; exact ⟨hI.2.2.2.2 r hx.1, hJ.2.2.2.2 r hx.2⟩⟩

/-- 互素性等价地给出 `1 = i + j` 型见证。
@isnad1 id=iff.2h3v.s7.b685d01351ce from=translated src=- shape=46547770 vocab=e715e6a4
-/
theorem comaximalIdealSets_iff_exists_add_eq_one {R : Type*} [Ring R]
    {I J : Set R} (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J) :
    ComaximalIdealSets I J ↔ ∃ i ∈ I, ∃ j ∈ J, i + j = 1 := by
  constructor
  · intro h
    have hone : (1 : R) ∈ idealSetSum I J := by rw [h]; trivial
    exact hone
  · rintro ⟨i, hi, j, hj, hij⟩
    apply Set.eq_univ_of_forall
    intro x
    refine ⟨x * i, ?_, x * j, ?_, ?_⟩
    · exact hI.1.2.2.2 x hi
    · exact hJ.1.2.2.2 x hj
    · rw [← mul_add, hij, mul_one]

/-- 到两个商环乘积的规范映射。-/
def chineseRemainderMap {R : Type*} [Ring R] (I J : Set R)
    (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J) :
    R → quotientRingSet I hI × quotientRingSet J hJ :=
  fun x ↦ (quotientRingProjection I hI x, quotientRingProjection J hJ x)

/-- 中国剩余规范映射是本库意义下的环同态。
@isnad1 id=ringhomo.2h3v.s7.469a2c75d194 from=translated src=- shape=0aacde88 vocab=e7e4ca63
-/
theorem chineseRemainderMap_is_ringHomomorphism {R : Type*} [Ring R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J) :
    RingHomomorphism (chineseRemainderMap I J hI hJ) := by
  let hπI := quotientRingProjection_is_ringHomomorphism I hI
  let hπJ := quotientRingProjection_is_ringHomomorphism J hJ
  exact ⟨Prod.ext hπI.1 hπJ.1, Prod.ext hπI.2.1 hπJ.2.1,
    (fun x y ↦ Prod.ext (hπI.2.2.1 x y) (hπJ.2.2.1 x y)),
    (fun x y ↦ Prod.ext (hπI.2.2.2.1 x y) (hπJ.2.2.2.1 x y)),
    fun x ↦ Prod.ext (hπI.2.2.2.2 x) (hπJ.2.2.2.2 x)⟩

/-- 规范映射的核正是两个理想的交。
@isnad1 id=iff.2h4v.s7.6e7cae88f453 from=translated src=- shape=658045e7 vocab=9b439968
-/
theorem chineseRemainderMap_eq_zero_iff {R : Type*} [Ring R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J)
    (x : R) :
    chineseRemainderMap I J hI hJ x = 0 ↔ x ∈ I ∩ J := by
  constructor
  · intro hx
    constructor
    · rw [← quotientRingProjection_kernel I hI]
      exact congrArg Prod.fst hx
    · rw [← quotientRingProjection_kernel J hJ]
      exact congrArg Prod.snd hx
  · intro hx
    apply Prod.ext
    · change quotientRingProjection I hI x = 0
      rw [quotientZero_eq_projection]
      apply (quotientRingProjection_eq_iff hI _ _).2
      simpa [idealCongruent] using hx.1
    · change quotientRingProjection J hJ x = 0
      rw [quotientZero_eq_projection]
      apply (quotientRingProjection_eq_iff hJ _ _).2
      simpa [idealCongruent] using hx.2

/-- 交换环中，互素理想使中国剩余规范映射满射。
@isnad1 id=surjecti.3h3v.s7.7c1e1b7331e6 from=translated src=- shape=7eac2bae vocab=b5fcbab7
-/
theorem chineseRemainderMap_surjective {R : Type*} [CommRing R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J)
    (hcomax : ComaximalIdealSets I J) :
    Function.Surjective (chineseRemainderMap I J hI hJ) := by
  obtain ⟨i, hi, j, hj, hij⟩ :=
    (comaximalIdealSets_iff_exists_add_eq_one hI hJ).1 hcomax
  rintro ⟨a, b⟩
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  refine ⟨x * j + y * i, ?_⟩
  apply Prod.ext
  · apply (quotientRingProjection_eq_iff hI _ _).2
    change x * j + y * i - x ∈ I
    have hmem : (y - x) * i ∈ I := hI.1.2.2.2 (y - x) hi
    convert hmem using 1
    calc
      x * j + y * i - x = x * j + y * i - x * (i + j) := by rw [hij, mul_one]
      _ = (y - x) * i := by ring
  · apply (quotientRingProjection_eq_iff hJ _ _).2
    change x * j + y * i - y ∈ J
    have hmem : (x - y) * j ∈ J := hJ.1.2.2.2 (x - y) hj
    convert hmem using 1
    calc
      x * j + y * i - y = x * j + y * i - y * (i + j) := by rw [hij, mul_one]
      _ = (x - y) * j := by ring

/-- 规范映射由交理想商下降到两个商环的乘积。-/
def chineseRemainderQuotientMap {R : Type*} [Ring R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J) :
    quotientRingSet (I ∩ J) (idealSetIntersection_is_ideal hI hJ) →
      quotientRingSet I hI × quotientRingSet J hJ :=
  quotientRingSetLift (I ∩ J) (idealSetIntersection_is_ideal hI hJ)
    (chineseRemainderMap I J hI hJ)
    (chineseRemainderMap_is_ringHomomorphism I J hI hJ)
    (fun x hx ↦ (chineseRemainderMap_eq_zero_iff I J hI hJ x).2 hx)

/-- 下降后的映射在代表元上的计算公式。
@isnad1 id=eq.2h4v.s7.b2882dd4e726 from=translated src=- shape=78e8ffc2 vocab=4280da4a
-/
@[simp] theorem chineseRemainderQuotientMap_projection {R : Type*} [Ring R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J)
    (x : R) :
    chineseRemainderQuotientMap I J hI hJ
      (quotientRingProjection (I ∩ J) (idealSetIntersection_is_ideal hI hJ) x) =
      chineseRemainderMap I J hI hJ x := by
  apply quotientRingSetLift_projection

/-- 二元中国剩余定理（正式承载）：互素理想之交的商环同构于两个商环的乘积。-/
noncomputable def chineseRemainderEquiv {R : Type*} [CommRing R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J)
    (hcomax : ComaximalIdealSets I J) :
    RingEquiv
      (quotientRingSet (I ∩ J) (idealSetIntersection_is_ideal hI hJ))
      (quotientRingSet I hI × quotientRingSet J hJ) := by
  classical
  let K : Set R := I ∩ J
  let hK : TwoSidedIdealSet K := idealSetIntersection_is_ideal hI hJ
  let forward : quotientRingSet K hK →
      quotientRingSet I hI × quotientRingSet J hJ :=
    chineseRemainderQuotientMap I J hI hJ
  have hforward : RingHomomorphism forward :=
    quotientRingSetLift_is_ringHomomorphism K hK
      (chineseRemainderMap I J hI hJ)
      (chineseRemainderMap_is_ringHomomorphism I J hI hJ)
      (fun x hx ↦ (chineseRemainderMap_eq_zero_iff I J hI hJ x).2 hx)
  have hsurjective : Function.Surjective forward := by
    intro y
    obtain ⟨x, hx⟩ := chineseRemainderMap_surjective I J hI hJ hcomax y
    refine ⟨quotientRingProjection K hK x, ?_⟩
    exact (chineseRemainderQuotientMap_projection I J hI hJ x).trans hx
  have hkernel (q : quotientRingSet K hK) (hq : forward q = 0) : q = 0 := by
    refine Quotient.inductionOn q ?_ hq
    intro x hx
    have hxK : x ∈ K :=
      (chineseRemainderMap_eq_zero_iff I J hI hJ x).1
        ((chineseRemainderQuotientMap_projection I J hI hJ x).symm.trans hx)
    rw [quotientZero_eq_projection]
    apply (quotientRingProjection_eq_iff hK _ _).2
    simpa [idealCongruent] using hxK
  have hinjective : Function.Injective forward := by
    intro a b hab
    have hz : forward (a - b) = 0 := by
      calc
        forward (a - b) = forward a - forward b := by
          rw [sub_eq_add_neg, sub_eq_add_neg, hforward.2.2.1, hforward.2.2.2.2]
        _ = 0 := sub_eq_zero.mpr hab
    exact sub_eq_zero.mp (hkernel (a - b) hz)
  let inverse : (quotientRingSet I hI × quotientRingSet J hJ) →
      quotientRingSet K hK := fun y ↦ (hsurjective y).choose
  have hright : ∀ y, forward (inverse y) = y := fun y ↦ (hsurjective y).choose_spec
  have hleft : ∀ q, inverse (forward q) = q := by
    intro q
    apply hinjective
    exact hright (forward q)
  exact RingEquiv.mk
    { toFun := forward
      invFun := inverse
      left_inv := hleft
      right_inv := hright }
    hforward.2.2.2.1 hforward.2.2.1

/-- 二元中国剩余定理的旧载体兼容接口；证明由 `chineseRemainderEquiv` 拥有。-/
noncomputable def chineseRemainderIsomorphism {R : Type*} [CommRing R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J)
    (hcomax : ComaximalIdealSets I J) :
    RingIsomorphism
      (quotientRingSet (I ∩ J) (idealSetIntersection_is_ideal hI hJ))
      (quotientRingSet I hI × quotientRingSet J hJ) :=
  RingIsomorphism.ofRingEquiv (chineseRemainderEquiv I J hI hJ hcomax)

/-- 正式中国剩余同构在代表元上就是同时取两个剩余类。
@isnad1 id=eq.3h4v.s9.af96f473528b from=translated src=- shape=01a2f43f vocab=714c567a
-/
@[simp] theorem chineseRemainderEquiv_projection {R : Type*} [CommRing R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J)
    (hcomax : ComaximalIdealSets I J) (x : R) :
    chineseRemainderEquiv I J hI hJ hcomax
      (quotientRingProjection (I ∩ J) (idealSetIntersection_is_ideal hI hJ) x) =
      chineseRemainderMap I J hI hJ x := by
  unfold chineseRemainderEquiv
  dsimp only
  rfl

/-- 旧二元中国剩余同构兼容接口的代表元公式。
@isnad1 id=eq.3h4v.s7.ccbc513e1ac0 from=translated src=- shape=e6a40d41 vocab=3fe000cd
-/
@[simp] theorem chineseRemainderIsomorphism_projection {R : Type*} [CommRing R]
    (I J : Set R) (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J)
    (hcomax : ComaximalIdealSets I J) (x : R) :
    chineseRemainderIsomorphism I J hI hJ hcomax
      (quotientRingProjection (I ∩ J) (idealSetIntersection_is_ideal hI hJ) x) =
      chineseRemainderMap I J hI hJ x := by
  exact chineseRemainderEquiv_projection I J hI hJ hcomax x

/-! ### 有限族中国剩余定理 -/

/-- 有限理想族两两互素。-/
def PairwiseComaximalIdealSets {R ι : Type*} [Ring R] (I : ι → Set R) : Prop :=
  ∀ i j, i ≠ j → ComaximalIdealSets (I i) (I j)

/-- 有限理想族的集合型交：同时属于每个理想的元素。-/
def finiteIdealIntersection {R ι : Type*} (I : ι → Set R) : Set R :=
  {x | ∀ i, x ∈ I i}

/-- 有限个双边理想的集合型交仍是双边理想。
@isnad1 id=twosided.1h3v.s6.f025407efe03 from=translated src=- shape=3e204cd2 vocab=57449905
-/
theorem finiteIdealIntersection_is_ideal {R ι : Type*} [Ring R]
    (I : ι → Set R) (hI : ∀ i, TwoSidedIdealSet (I i)) :
    TwoSidedIdealSet (finiteIdealIntersection I) := by
  constructor
  · refine ⟨(fun i ↦ (hI i).1.1), ?_, ?_, ?_⟩
    · intro x y hx hy i
      exact (hI i).1.2.1 (hx i) (hy i)
    · intro x hx i
      exact (hI i).1.2.2.1 (hx i)
    · intro r x hx i
      exact (hI i).1.2.2.2 r (hx i)
  · refine ⟨(fun i ↦ (hI i).2.1), ?_, ?_, ?_⟩
    · intro x y hx hy i
      exact (hI i).2.2.1 (hx i) (hy i)
    · intro x hx i
      exact (hI i).2.2.2.1 (hx i)
    · intro r x hx i
      exact (hI i).2.2.2.2 r (hx i)

/-- 到有限个商环直积的规范映射。-/
def finiteChineseRemainderMap {R ι : Type*} [Ring R]
    (I : ι → Set R) (hI : ∀ i, TwoSidedIdealSet (I i)) :
    R → ∀ i, quotientRingSet (I i) (hI i) :=
  fun x i ↦ quotientRingProjection (I i) (hI i) x

/-- 有限族规范映射是本库意义下的环同态。
@isnad1 id=ringhomo.1h3v.s7.3f16599867af from=translated src=- shape=2afbe0e7 vocab=e431e96b
-/
theorem finiteChineseRemainderMap_is_ringHomomorphism {R ι : Type*} [Ring R]
    (I : ι → Set R) (hI : ∀ i, TwoSidedIdealSet (I i)) :
    RingHomomorphism (finiteChineseRemainderMap I hI) := by
  refine ⟨funext (fun i ↦ (quotientRingProjection_is_ringHomomorphism (I i) (hI i)).1),
    funext (fun i ↦ (quotientRingProjection_is_ringHomomorphism (I i) (hI i)).2.1),
    ?_, ?_, ?_⟩
  · intro x y
    funext i
    exact (quotientRingProjection_is_ringHomomorphism (I i) (hI i)).2.2.1 x y
  · intro x y
    funext i
    exact (quotientRingProjection_is_ringHomomorphism (I i) (hI i)).2.2.2.1 x y
  · intro x
    funext i
    exact (quotientRingProjection_is_ringHomomorphism (I i) (hI i)).2.2.2.2 x

/-- 有限族规范映射的核正是全部理想的交。
@isnad1 id=iff.1h4v.s7.08c30d26114c from=translated src=- shape=fcd632de vocab=43457c77
-/
theorem finiteChineseRemainderMap_eq_zero_iff {R ι : Type*} [Ring R]
    (I : ι → Set R) (hI : ∀ i, TwoSidedIdealSet (I i)) (x : R) :
    finiteChineseRemainderMap I hI x = 0 ↔ x ∈ finiteIdealIntersection I := by
  constructor
  · intro hx i
    rw [← quotientRingProjection_kernel (I i) (hI i)]
    exact congrFun hx i
  · intro hx
    funext i
    change quotientRingProjection (I i) (hI i) x = 0
    rw [quotientZero_eq_projection]
    apply (quotientRingProjection_eq_iff (hI i) _ _).2
    simpa [idealCongruent] using hx i

/-- 有限交换环情形中，两两互素保证规范映射满射。
@isnad1 id=surjecti.2h3v.s6.3e24c9fe1e15 from=translated src=- shape=b8a6336e vocab=dd07f0e2
-/
theorem finiteChineseRemainderMap_surjective {R ι : Type*} [CommRing R]
    [Finite ι]
    (I : ι → Set R) (hI : ∀ i, TwoSidedIdealSet (I i))
    (hpairwise : PairwiseComaximalIdealSets I) :
    Function.Surjective (finiteChineseRemainderMap I hI) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let A : ι → Ideal R := fun i ↦
    ((twoSidedIdealSet_iff_exists_ideal (I i)).1 (hI i)).choose
  have hA : ∀ i, ((A i : Ideal R) : Set R) = I i := fun i ↦
    ((twoSidedIdealSet_iff_exists_ideal (I i)).1 (hI i)).choose_spec
  have hAcoprime : Pairwise (Function.onFun IsCoprime A) := by
    intro i j hij
    apply Ideal.isCoprime_iff_exists.2
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (comaximalIdealSets_iff_exists_add_eq_one (hI i) (hI j)).1
        (hpairwise i j hij)
    exact ⟨a, by change a ∈ (A i : Set R); rw [hA i]; exact ha,
      b, by change b ∈ (A j : Set R); rw [hA j]; exact hb, hab⟩
  intro q
  let representative : ι → R := fun i ↦ Quotient.out (q i)
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hAcoprime representative
  refine ⟨r, funext ?_⟩
  intro i
  calc
    quotientRingProjection (I i) (hI i) r =
        quotientRingProjection (I i) (hI i) (representative i) :=
      (quotientRingProjection_eq_iff (hI i) _ _).2 (by
        change r - representative i ∈ I i
        rw [← hA i]
        exact hr i)
    _ = q i := Quotient.out_eq (q i)

/-- 有限族规范映射由全部理想之交的商环下降到商环直积。-/
def finiteChineseRemainderQuotientMap {R ι : Type*} [Ring R]
    (I : ι → Set R) (hI : ∀ i, TwoSidedIdealSet (I i)) :
    quotientRingSet (finiteIdealIntersection I) (finiteIdealIntersection_is_ideal I hI) →
      ∀ i, quotientRingSet (I i) (hI i) :=
  quotientRingSetLift (finiteIdealIntersection I) (finiteIdealIntersection_is_ideal I hI)
    (finiteChineseRemainderMap I hI)
    (finiteChineseRemainderMap_is_ringHomomorphism I hI)
    (fun x hx ↦ (finiteChineseRemainderMap_eq_zero_iff I hI x).2 hx)

/-- 有限族下降映射在代表元上的计算公式。
@isnad1 id=eq.1h4v.s6.3d3b5eb74163 from=translated src=- shape=12a889a1 vocab=d063a552
-/
@[simp] theorem finiteChineseRemainderQuotientMap_projection
    {R ι : Type*} [Ring R] (I : ι → Set R)
    (hI : ∀ i, TwoSidedIdealSet (I i)) (x : R) :
    finiteChineseRemainderQuotientMap I hI
      (quotientRingProjection (finiteIdealIntersection I)
        (finiteIdealIntersection_is_ideal I hI) x) =
      finiteChineseRemainderMap I hI x := by
  apply quotientRingSetLift_projection

/-- 有限中国剩余定理（正式承载）：理想交的商环同构于各商环的有限直积。-/
noncomputable def finiteChineseRemainderEquiv
    {R ι : Type*} [CommRing R] [Finite ι]
    (I : ι → Set R) (hI : ∀ i, TwoSidedIdealSet (I i))
    (hpairwise : PairwiseComaximalIdealSets I) :
    RingEquiv
      (quotientRingSet (finiteIdealIntersection I) (finiteIdealIntersection_is_ideal I hI))
      (∀ i, quotientRingSet (I i) (hI i)) := by
  classical
  let K : Set R := finiteIdealIntersection I
  let hK : TwoSidedIdealSet K := finiteIdealIntersection_is_ideal I hI
  let forward : quotientRingSet K hK → ∀ i, quotientRingSet (I i) (hI i) :=
    finiteChineseRemainderQuotientMap I hI
  have hforward : RingHomomorphism forward :=
    quotientRingSetLift_is_ringHomomorphism K hK
      (finiteChineseRemainderMap I hI)
      (finiteChineseRemainderMap_is_ringHomomorphism I hI)
      (fun x hx ↦ (finiteChineseRemainderMap_eq_zero_iff I hI x).2 hx)
  have hsurjective : Function.Surjective forward := by
    intro y
    obtain ⟨x, hx⟩ := finiteChineseRemainderMap_surjective I hI hpairwise y
    refine ⟨quotientRingProjection K hK x, ?_⟩
    exact (finiteChineseRemainderQuotientMap_projection I hI x).trans hx
  have hkernel (q : quotientRingSet K hK) (hq : forward q = 0) : q = 0 := by
    refine Quotient.inductionOn q ?_ hq
    intro x hx
    have hxK : x ∈ K :=
      (finiteChineseRemainderMap_eq_zero_iff I hI x).1
        ((finiteChineseRemainderQuotientMap_projection I hI x).symm.trans hx)
    rw [quotientZero_eq_projection]
    apply (quotientRingProjection_eq_iff hK _ _).2
    simpa [idealCongruent] using hxK
  have hinjective : Function.Injective forward := by
    intro a b hab
    have hz : forward (a - b) = 0 := by
      calc
        forward (a - b) = forward a - forward b := by
          rw [sub_eq_add_neg, sub_eq_add_neg, hforward.2.2.1, hforward.2.2.2.2]
        _ = 0 := sub_eq_zero.mpr hab
    exact sub_eq_zero.mp (hkernel (a - b) hz)
  let inverse : (∀ i, quotientRingSet (I i) (hI i)) → quotientRingSet K hK :=
    fun y ↦ (hsurjective y).choose
  have hright : ∀ y, forward (inverse y) = y := fun y ↦ (hsurjective y).choose_spec
  have hleft : ∀ q, inverse (forward q) = q := by
    intro q
    apply hinjective
    exact hright (forward q)
  exact RingEquiv.mk
    { toFun := forward
      invFun := inverse
      left_inv := hleft
      right_inv := hright }
    hforward.2.2.2.1 hforward.2.2.1

/-- 有限中国剩余定理的旧载体兼容接口；证明由 `finiteChineseRemainderEquiv` 拥有。-/
noncomputable def finiteChineseRemainderIsomorphism
    {R ι : Type*} [CommRing R] [Finite ι]
    (I : ι → Set R) (hI : ∀ i, TwoSidedIdealSet (I i))
    (hpairwise : PairwiseComaximalIdealSets I) :
    RingIsomorphism
      (quotientRingSet (finiteIdealIntersection I) (finiteIdealIntersection_is_ideal I hI))
      (∀ i, quotientRingSet (I i) (hI i)) :=
  RingIsomorphism.ofRingEquiv (finiteChineseRemainderEquiv I hI hpairwise)

/-- 正式有限中国剩余同构在代表元上同时取每个理想的剩余类。
@isnad1 id=eq.2h4v.s8.afdd1070ceec from=translated src=- shape=a2a12ea4 vocab=44861426
-/
@[simp] theorem finiteChineseRemainderEquiv_projection
    {R ι : Type*} [CommRing R] [Finite ι]
    (I : ι → Set R) (hI : ∀ i, TwoSidedIdealSet (I i))
    (hpairwise : PairwiseComaximalIdealSets I) (x : R) :
    finiteChineseRemainderEquiv I hI hpairwise
      (quotientRingProjection (finiteIdealIntersection I)
        (finiteIdealIntersection_is_ideal I hI) x) =
      finiteChineseRemainderMap I hI x := by
  unfold finiteChineseRemainderEquiv
  dsimp only
  rfl

/-- 旧有限中国剩余同构兼容接口的代表元公式。
@isnad1 id=eq.2h4v.s7.4c55966dc997 from=translated src=- shape=8245431d vocab=17c96ec8
-/
@[simp] theorem finiteChineseRemainderIsomorphism_projection
    {R ι : Type*} [CommRing R] [Finite ι]
    (I : ι → Set R) (hI : ∀ i, TwoSidedIdealSet (I i))
    (hpairwise : PairwiseComaximalIdealSets I) (x : R) :
    finiteChineseRemainderIsomorphism I hI hpairwise
      (quotientRingProjection (finiteIdealIntersection I)
        (finiteIdealIntersection_is_ideal I hI) x) =
      finiteChineseRemainderMap I hI x := by
  exact finiteChineseRemainderEquiv_projection I hI hpairwise x

end SandronesLibrary.AbstractAlgebra.Ring
