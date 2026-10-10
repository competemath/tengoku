module

public import Tengoku

@[expose] public section

open WithLp ENNReal

/--
@isnad1 id=eq.0h5v.s8.6f214a356996 from=translated src=- shape=1e1a5de6 vocab=381581a8
-/
lemma PiLp.coe_proj (p : ENNReal) {ι : Type*} (𝕜 : Type*) {E : ι → Type*} [Semiring 𝕜]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] {i : ι} :
    ⇑(proj p (𝕜 := 𝕜) E i) = fun x ↦ x i := rfl

/--
@isnad1 id=eq.0h4v.s9.5cd2ed134721 from=translated src=- shape=7d7cfd53 vocab=09680f79
-/
@[simp]
lemma EuclideanSpace.proj_apply {ι 𝕜 : Type*} [RCLike 𝕜] {i : ι} (x : EuclideanSpace 𝕜 ι) :
    proj i x = x i := rfl

/--
@isnad1 id=eq.0h4v.s7.83ac05c8e2fd from=translated src=- shape=cbc69136 vocab=513075d5
-/
lemma ContinuousLinearMap.coe_proj' (R : Type*) {ι : Type*} [Semiring R] {φ : ι → Type*}
    [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)] (i : ι) :
    ⇑(ContinuousLinearMap.proj (R := R) (φ := φ) i) = fun x ↦ x i := rfl

/--
@isnad1 id=eq.0h2v.s10.426aec21e856 from=translated src=- shape=e00beee6 vocab=cc0c991f
-/
lemma EuclideanSpace.coe_equiv_symm {ι 𝕜 : Type*} [RCLike 𝕜] :
    ⇑(EuclideanSpace.equiv ι 𝕜).symm = toLp 2 := rfl
