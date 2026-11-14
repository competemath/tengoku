/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.Jordan

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / JordanDecomposition —— 幂零算子的 Jordan 链分解

本文件以不变子空间上的像空间归纳，构造幂零线性算子的完整 Jordan 链基。
归纳步骤提升像空间中的链，并以核空间基补齐各条链的首向量和剩余长度为一的链。

> **Entry**: linear-algebra.eigen.jordan-decomposition
-/

namespace SandronesLibrary.LinearAlgebra.Jordan

open SandronesLibrary.LinearAlgebra.VectorSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]

variable {A B I J : Type*} [AddCommGroup A] [AddCommGroup B]
variable [Module K A] [Module K B] [Module.Finite K A]
variable [Fintype I] [Fintype J]

private theorem linearMap_range_lifts_kernel_isBasis
    (D : A →ₗ[K] B) (b : I → LinearMap.range D) (c : I → A)
    (k : J → LinearMap.ker D)
    (hb : LinearIndependent K b ∧ Submodule.span K (Set.range b) = ⊤)
    (hk : LinearIndependent K k ∧ Submodule.span K (Set.range k) = ⊤)
    (hc : ∀ i, D (c i) = b i) :
    LinearIndependent K (Sum.elim c (fun j => (k j : A))) ∧
      Submodule.span K (Set.range (Sum.elim c (fun j => (k j : A)))) = ⊤ := by
  let family : I ⊕ J → A := Sum.elim c (fun j => (k j : A))
  have hli : LinearIndependent K family := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hDa := congrArg D ha
    have hbrel : ∑ i : I, a (Sum.inl i) • b i = 0 := by
      apply Subtype.ext
      simpa [family, Fintype.sum_sum_type, map_sum, map_smul, hc] using hDa
    have hi : ∀ i : I, a (Sum.inl i) = 0 :=
      (Fintype.linearIndependent_iff.mp hb.1) _ hbrel
    have hkrel : ∑ j : J, a (Sum.inr j) • k j = 0 := by
      apply Subtype.ext
      simpa [family, Fintype.sum_sum_type, hi] using ha
    have hj : ∀ j : J, a (Sum.inr j) = 0 :=
      (Fintype.linearIndependent_iff.mp hk.1) _ hkrel
    intro p
    cases p with
    | inl i => exact hi i
    | inr j => exact hj j
  refine ⟨hli, ?_⟩
  let bBasis : Module.Basis I K (LinearMap.range D) :=
    Module.Basis.mk hb.1 hb.2.ge
  let kBasis : Module.Basis J K (LinearMap.ker D) :=
    Module.Basis.mk hk.1 hk.2.ge
  have hI : Fintype.card I = Module.finrank K (LinearMap.range D) := by
    simpa using (Module.finrank_eq_card_basis bBasis).symm
  have hJ : Fintype.card J = Module.finrank K (LinearMap.ker D) := by
    simpa using (Module.finrank_eq_card_basis kBasis).symm
  have hrank := D.finrank_range_add_finrank_ker
  have hcard : Fintype.card (I ⊕ J) = Module.finrank K A := by
    rw [Fintype.card_sum, hI, hJ, hrank]
  exact hli.span_eq_top_of_card_eq_finrank' hcard

private theorem basis_sumExtend_apply_inl {W ι : Type*} [AddCommGroup W] [Module K W]
    {v : ι → W} (hs : LinearIndependent K v) (i : ι) :
    Module.Basis.sumExtend hs (Sum.inl i) = v i := by
  classical
  unfold Module.Basis.sumExtend Module.Basis.sumExtendIndex
  rw [Module.Basis.reindex_apply]
  change Module.Basis.extend hs.linearIndepOn_id
    (((Equiv.sumCongr (Equiv.ofInjective v hs.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumDiffSubset (hs.linearIndepOn_id.subset_extend _))) (Sum.inl i)) = v i
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply]
  exact Module.Basis.extend_apply_self hs.linearIndepOn_id _

/-- `S` 在 `N` 下不变。-/
private def IsInvariantSubspace (N : V →ₗ[K] V) (S : Submodule K V) : Prop :=
  ∀ x ∈ S, N x ∈ S

/-- `N` 在不变子空间 `S` 上的限制。-/
private def invariantRestriction (N : V →ₗ[K] V) (S : Submodule K V)
    (hS : IsInvariantSubspace N S) : S →ₗ[K] S :=
  N.restrict hS

private theorem invariantRestriction_coe_pow (N : V →ₗ[K] V) (S : Submodule K V)
    (hS : IsInvariantSubspace N S) (n : ℕ) (x : S) :
    (↑(((invariantRestriction N S hS) ^ n) x) : V) = (N ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      change N (((invariantRestriction N S hS) ^ n) x) = N ((N ^ n) x)
      rw [ih]

/-- `N(S)` 仍是 `N`-不变子空间。-/
private theorem image_invariant (N : V →ₗ[K] V) (S : Submodule K V)
    (hS : IsInvariantSubspace N S) :
    IsInvariantSubspace N (LinearMap.range (N.domRestrict S)) := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨⟨N x, hS x x.property⟩, rfl⟩

private theorem image_restriction_nilpotent (N : V →ₗ[K] V) (S : Submodule K V)
    (hS : IsInvariantSubspace N S)
    (hNil : IsNilpotent (invariantRestriction N S hS)) :
    IsNilpotent
      (invariantRestriction N (LinearMap.range (N.domRestrict S)) (image_invariant N S hS)) := by
  obtain ⟨n, hn⟩ := hNil
  refine ⟨n, ?_⟩
  ext x
  have hxS : (x : V) ∈ S := by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy]
    exact hS y y.property
  have hz := congrArg
    (fun F : S →ₗ[K] S => F ⟨(x : V), hxS⟩) hn
  rw [invariantRestriction_coe_pow]
  simpa [invariantRestriction_coe_pow] using congrArg Subtype.val hz

private theorem image_finrank_lt_of_nilpotent [IsFiniteDimensional K V]
    (N : V →ₗ[K] V) (S : Submodule K V) (hS : IsInvariantSubspace N S)
    (hNontrivial : Nontrivial S)
    (hNil : IsNilpotent (invariantRestriction N S hS)) :
    Module.finrank K (LinearMap.range (N.domRestrict S)) < Module.finrank K S := by
  letI : Nontrivial S := hNontrivial
  letI : LinearSpace K S := ⟨inferInstance⟩
  obtain ⟨x, hx, hNx⟩ :=
    nilpotent_exists_nonzero_kernel_vector (invariantRestriction N S hS) hNil
  have hxker : x ∈ LinearMap.ker (N.domRestrict S) := by
    change N x = 0
    exact congrArg Subtype.val hNx
  haveI : Nontrivial (LinearMap.ker (N.domRestrict S)) := by
    refine ⟨⟨⟨x, hxker⟩, 0, ?_⟩⟩
    intro h
    apply hx
    exact congrArg (fun y : LinearMap.ker (N.domRestrict S) => (y : S)) h
  have hker : 0 < Module.finrank K (LinearMap.ker (N.domRestrict S)) :=
    Module.finrank_pos_iff.mpr inferInstance
  have hrank := (N.domRestrict S).finrank_range_add_finrank_ker
  omega

/-- 一族 Jordan 链线性无关并恰好张成指定子空间。-/
private def IsJordanBasisFamilyForSubspace (N : V →ₗ[K] V) (S : Submodule K V)
    (r : ℕ) (length : Fin r → ℕ)
    (b : (i : Fin r) → Fin (length i + 1) → V) : Prop :=
  LinearIndependent K (fun p : Σ i : Fin r, Fin (length i + 1) => b p.1 p.2) ∧
    Submodule.span K (Set.range fun p : Σ i : Fin r, Fin (length i + 1) => b p.1 p.2) = S ∧
    ∀ i : Fin r, IsJordanChain N 0 (b i)

private theorem jordanBasisFamilyForSubspace_mem
    (N : V →ₗ[K] V) (S : Submodule K V) {r : ℕ} {length : Fin r → ℕ}
    (b : (i : Fin r) → Fin (length i + 1) → V)
    (hb : IsJordanBasisFamilyForSubspace N S r length b)
    (i : Fin r) (j : Fin (length i + 1)) : b i j ∈ S := by
  have hmem : b i j ∈ Submodule.span K
      (Set.range fun p : Σ i : Fin r, Fin (length i + 1) => b p.1 p.2) := by
    apply Submodule.subset_span
    exact ⟨⟨i, j⟩, rfl⟩
  rw [hb.2.1] at hmem
  exact hmem

private theorem jordanBasisFamily_chainFirsts_kernel_linearIndependent
    (N : V →ₗ[K] V) (S : Submodule K V) {r : ℕ} {length : Fin r → ℕ}
    (hInv : IsInvariantSubspace N S)
    (b : (i : Fin r) → Fin (length i + 1) → V)
    (hb : IsJordanBasisFamilyForSubspace N (LinearMap.range (N.domRestrict S)) r length b) :
    ∃ f : Fin r → LinearMap.ker (N.domRestrict S),
      (∀ i, ((f i : S) : V) = b i 0) ∧ LinearIndependent K f := by
  let f : Fin r → LinearMap.ker (N.domRestrict S) := fun i =>
    ⟨⟨b i 0, by
        obtain ⟨x, hx⟩ := jordanBasisFamilyForSubspace_mem N _ b hb i 0
        rw [← hx]
        exact hInv x x.property⟩,
      by
        change N (b i 0) = 0
        simpa using (hb.2.2 i).2.1⟩
  have hinj : Function.Injective (fun i : Fin r =>
      (⟨i, (0 : Fin (length i + 1))⟩ : Σ i, Fin (length i + 1))) := by
    intro i j h
    exact congrArg Sigma.fst h
  have hliV : LinearIndependent K (fun i : Fin r => b i 0) :=
    hb.1.comp _ hinj
  have hliF : LinearIndependent K f := by
    apply LinearIndependent.of_comp
      (S.subtype.comp (LinearMap.ker (N.domRestrict S)).subtype)
    simpa [Function.comp_def, f] using hliV
  exact ⟨f, fun i => rfl, hliF⟩

/-- 归纳组装步骤：若 `N(S)` 已有链分解，则提升这些链并补核基，得到 `S` 的链分解。-/
private theorem invariantSubspace_decomposition_step_framework
    [IsFiniteDimensional K V]
    (N : V →ₗ[K] V) (S : Submodule K V)
    (hInv : IsInvariantSubspace N S) (hNontrivial : Nontrivial S)
    (ih : ∃ (r : ℕ) (length : Fin r → ℕ)
      (b : (i : Fin r) → Fin (length i + 1) → V),
      IsJordanBasisFamilyForSubspace N (LinearMap.range (N.domRestrict S)) r length b) :
    ∃ (r : ℕ) (length : Fin r → ℕ)
      (b : (i : Fin r) → Fin (length i + 1) → V),
      IsJordanBasisFamilyForSubspace N S r length b := by
  classical
  obtain ⟨r, length, b, hb⟩ := ih
  obtain ⟨first, hfirst, hfirstLI⟩ :=
    jordanBasisFamily_chainFirsts_kernel_linearIndependent N S hInv b hb
  let kernelBasis := Module.Basis.sumExtend hfirstLI
  let extra := Module.Basis.sumExtendIndex hfirstLI
  letI : Finite (Fin r ⊕ extra) := kernelBasis.linearIndependent.finite
  letI : Finite extra := Finite.of_injective
    (fun x : extra => (Sum.inr x : Fin r ⊕ extra)) Sum.inr_injective
  letI : Fintype extra := Fintype.ofFinite extra
  have hkernelFirst (i : Fin r) : kernelBasis (Sum.inl i) = first i := by
    exact basis_sumExtend_apply_inl hfirstLI i
  let P := Σ i : Fin r, Fin (length i + 1)
  let D : S →ₗ[K] V := N.domRestrict S
  let rangeVec : P → LinearMap.range D := fun p =>
    ⟨b p.1 p.2, jordanBasisFamilyForSubspace_mem N _ b hb p.1 p.2⟩
  have hRangeLI : LinearIndependent K rangeVec := by
    apply LinearIndependent.of_comp (LinearMap.range D).subtype
    simpa [Function.comp_def, rangeVec, P, D] using hb.1
  have hRangeCard : Fintype.card P = Module.finrank K (LinearMap.range D) := by
    have hspanCard := finrank_span_eq_card hb.1
    rw [hb.2.1] at hspanCard
    simpa [P, D] using hspanCard.symm
  have hRangeBasis :
      LinearIndependent K rangeVec ∧ Submodule.span K (Set.range rangeVec) = ⊤ := by
    exact ⟨hRangeLI, hRangeLI.span_eq_top_of_card_eq_finrank' hRangeCard⟩
  have hbS (i : Fin r) (j : Fin (length i + 1)) : b i j ∈ S := by
    obtain ⟨x, hx⟩ := jordanBasisFamilyForSubspace_mem N _ b hb i j
    rw [← hx]
    exact hInv x x.property
  let topLift (i : Fin r) : S :=
    Classical.choose (rangeVec ⟨i, Fin.last (length i)⟩).property
  have htopLift (i : Fin r) :
      D (topLift i) = rangeVec ⟨i, Fin.last (length i)⟩ :=
    Classical.choose_spec (rangeVec ⟨i, Fin.last (length i)⟩).property
  let liftVec : P → S := fun p =>
    Fin.lastCases (topLift p.1)
      (fun j : Fin (length p.1) => ⟨b p.1 j.succ, hbS p.1 j.succ⟩) p.2
  have hLift (p : P) : D (liftVec p) = rangeVec p := by
    rcases p with ⟨i, j⟩
    refine Fin.lastCases ?_ (fun q => ?_) j
    · simpa [liftVec] using htopLift i
    · have hchain := (hb.2.2 i).2.2 q
      simp only [liftVec, Fin.lastCases_castSucc]
      change N (b i q.succ) = b i q.castSucc
      simpa using hchain
  have hKernelBasis :
      LinearIndependent K kernelBasis ∧
        Submodule.span K (Set.range kernelBasis) = ⊤ := by
    exact ⟨kernelBasis.linearIndependent, kernelBasis.span_eq⟩
  have hDomainBasis := linearMap_range_lifts_kernel_isBasis
    D rangeVec liftVec kernelBasis hRangeBasis hKernelBasis hLift
  let extendedChain (i : Fin r) : Fin (length i + 2) → V :=
    Fin.cases ((first i : LinearMap.ker D) : S)
      (fun j : Fin (length i + 1) => (liftVec ⟨i, j⟩ : S))
  have hExtendedChain (i : Fin r) : IsJordanChain N 0 (extendedChain i) := by
    refine ⟨?_, ?_, ?_⟩
    · change (((first i : LinearMap.ker D) : S) : V) ≠ 0
      intro hz
      have hzS : ((first i : LinearMap.ker D) : S) = 0 := Subtype.ext hz
      have hzK : first i = 0 := Subtype.ext hzS
      exact (LinearIndependent.ne_zero i hfirstLI) hzK
    · simp only [extendedChain, Fin.cases_zero, zero_smul]
      change N ((((first i : LinearMap.ker D) : S) : V)) = 0
      exact (first i).property
    · intro j
      change N ((liftVec ⟨i, j⟩ : S) : V) =
        0 • ((liftVec ⟨i, j⟩ : S) : V) + extendedChain i j.castSucc
      rw [zero_smul, zero_add]
      have hmap : N ((liftVec ⟨i, j⟩ : S) : V) = b i j := by
        simpa [D, rangeVec] using hLift ⟨i, j⟩
      rw [hmap]
      refine Fin.cases ?_ (fun q => ?_) j
      · simpa [extendedChain] using (hfirst i).symm
      · have hidx : (Fin.succ q).castSucc = q.castSucc.succ := Fin.ext rfl
        rw [hidx]
        simp only [extendedChain, Fin.cases_succ]
        simp [liftVec]
  let extraChain (e : extra) : Fin 1 → V := fun _ =>
    ((((kernelBasis (Sum.inr e) : LinearMap.ker D) : S)) : V)
  have hExtraChain (e : extra) : IsJordanChain N 0 (extraChain e) := by
    refine ⟨?_, ?_, ?_⟩
    · change (((kernelBasis (Sum.inr e) : LinearMap.ker D) : S) : V) ≠ 0
      intro hz
      have hzS : ((kernelBasis (Sum.inr e) : LinearMap.ker D) : S) = 0 :=
        Subtype.ext hz
      have hzK : (kernelBasis (Sum.inr e) : LinearMap.ker D) = 0 :=
        Subtype.ext hzS
      exact (LinearIndependent.ne_zero (Sum.inr e) kernelBasis.linearIndependent) hzK
    · simp only [extraChain, zero_smul]
      change N (((kernelBasis (Sum.inr e) : LinearMap.ker D) : S) : V) = 0
      exact (kernelBasis (Sum.inr e)).property
    · intro j
      exact Fin.elim0 j
  let Q := Fin r ⊕ extra
  let rawLength : Q → ℕ := Sum.elim (fun i => length i + 1) (fun _ => 0)
  let rawChain : (q : Q) → Fin (rawLength q + 1) → V := fun q =>
    match q with
    | Sum.inl i => extendedChain i
    | Sum.inr e => extraChain e
  have hRawChain (q : Q) : IsJordanChain N 0 (rawChain q) := by
    cases q with
    | inl i => simpa [rawChain, rawLength, Q] using hExtendedChain i
    | inr e => simpa [rawChain, rawLength, Q] using hExtraChain e
  let chainEquiv : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let finalLength : Fin (Fintype.card Q) → ℕ := fun i => rawLength (chainEquiv.symm i)
  let finalChain : (i : Fin (Fintype.card Q)) → Fin (finalLength i + 1) → V :=
    fun i => rawChain (chainEquiv.symm i)
  have hFinalChain (i : Fin (Fintype.card Q)) :
      IsJordanChain N 0 (finalChain i) := hRawChain (chainEquiv.symm i)
  let rawIndex := Σ q : Q, Fin (rawLength q + 1)
  let domainIndex := P ⊕ (Fin r ⊕ extra)
  let rawToDomain : rawIndex → domainIndex := fun x =>
    match x with
    | ⟨Sum.inl i, j⟩ =>
        Fin.cases (Sum.inr (Sum.inl i))
          (fun k => Sum.inl ⟨i, k⟩) j
    | ⟨Sum.inr e, _⟩ => Sum.inr (Sum.inr e)
  let domainToRaw : domainIndex → rawIndex := fun x =>
    match x with
    | Sum.inl ⟨i, j⟩ => ⟨Sum.inl i, j.succ⟩
    | Sum.inr (Sum.inl i) => ⟨Sum.inl i, 0⟩
    | Sum.inr (Sum.inr e) => ⟨Sum.inr e, 0⟩
  have hRawLeft : Function.LeftInverse domainToRaw rawToDomain := by
    rintro ⟨q, j⟩
    cases q with
    | inl i =>
        refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · rfl
    | inr e =>
        change Fin 1 at j
        have hj : j = 0 := Fin.eq_zero j
        subst j
        rfl
  have hRawRight : Function.RightInverse domainToRaw rawToDomain := by
    intro x
    cases x with
    | inl p => rfl
    | inr q =>
        cases q <;> rfl
  let rawEquivDomain : rawIndex ≃ domainIndex :=
    ⟨rawToDomain, domainToRaw, hRawLeft, hRawRight⟩
  let finalIndex := Σ i : Fin (Fintype.card Q), Fin (finalLength i + 1)
  let finalEquivRaw : finalIndex ≃ rawIndex :=
    Equiv.sigmaCongr chainEquiv.symm (fun _ => Equiv.refl _)
  let finalEquivDomain : finalIndex ≃ domainIndex :=
    finalEquivRaw.trans rawEquivDomain
  let domainFamily : domainIndex → V := fun x =>
    ((Sum.elim liftVec (fun j => (kernelBasis j : S)) x : S) : V)
  have hRawReindex (x : rawIndex) :
      rawChain x.1 x.2 = domainFamily (rawEquivDomain x) := by
    rcases x with ⟨q, j⟩
    cases q with
    | inl i =>
        refine Fin.cases ?_ (fun k => ?_) j
        · change (((first i : LinearMap.ker D) : S) : V) =
            (((kernelBasis (Sum.inl i) : LinearMap.ker D) : S) : V)
          rw [hkernelFirst]
        · rfl
    | inr e =>
        change Fin 1 at j
        have hj : j = 0 := Fin.eq_zero j
        subst j
        rfl
  have hFinalReindex (x : finalIndex) :
      finalChain x.1 x.2 = domainFamily (finalEquivDomain x) := by
    rcases x with ⟨i, j⟩
    exact hRawReindex ⟨chainEquiv.symm i, j⟩
  have hDomainLI : LinearIndependent K domainFamily := by
    have hli := hDomainBasis.1.map' S.subtype S.ker_subtype
    simpa [domainFamily, Function.comp_def] using hli
  have hFinalLI : LinearIndependent K
      (fun x : finalIndex => finalChain x.1 x.2) := by
    have hli := hDomainLI.comp finalEquivDomain finalEquivDomain.injective
    simpa [Function.comp_def, hFinalReindex] using hli
  have hDomainSpanLe :
      Submodule.span K (Set.range domainFamily) ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨p, rfl⟩
    exact (Sum.elim liftVec (fun j => (kernelBasis j : S)) p).property
  have hDomainCard : Fintype.card domainIndex = Module.finrank K S := by
    have hcard := finrank_span_eq_card hDomainBasis.1
    rw [hDomainBasis.2] at hcard
    simpa [domainIndex] using hcard.symm
  have hDomainSpan : Submodule.span K (Set.range domainFamily) = S := by
    apply Submodule.eq_of_le_of_finrank_eq hDomainSpanLe
    rw [finrank_span_eq_card hDomainLI, hDomainCard]
  have hRangeEq :
      Set.range (fun x : finalIndex => finalChain x.1 x.2) =
        Set.range domainFamily := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨finalEquivDomain p, (hFinalReindex p).symm⟩
    · rintro ⟨p, rfl⟩
      refine ⟨finalEquivDomain.symm p, ?_⟩
      change finalChain _ _ = domainFamily p
      rw [hFinalReindex]
      simp
  refine ⟨Fintype.card Q, finalLength, finalChain, hFinalLI, ?_, hFinalChain⟩
  rw [hRangeEq, hDomainSpan]

/-- 不变子空间内的幂零 Jordan 链分解。固定环境空间，只对子空间递归。-/
private theorem nilpotent_invariantSubspace_decomposition_framework
    [IsFiniteDimensional K V]
    (N : V →ₗ[K] V) (S : Submodule K V)
    (hInv : IsInvariantSubspace N S)
    (hNil : IsNilpotent (invariantRestriction N S hInv)) :
    ∃ (r : ℕ) (length : Fin r → ℕ)
      (b : (i : Fin r) → Fin (length i + 1) → V),
      IsJordanBasisFamilyForSubspace N S r length b := by
  by_cases hSnon : Nontrivial S
  · let Snext : Submodule K V := LinearMap.range (N.domRestrict S)
    have hNextInv : IsInvariantSubspace N Snext := image_invariant N S hInv
    have hNextNil : IsNilpotent (invariantRestriction N Snext hNextInv) :=
      image_restriction_nilpotent N S hInv hNil
    have hNextDim : Module.finrank K Snext < Module.finrank K S :=
      image_finrank_lt_of_nilpotent N S hInv hSnon hNil
    have ihNext := nilpotent_invariantSubspace_decomposition_framework
      N Snext hNextInv hNextNil
    exact invariantSubspace_decomposition_step_framework N S hInv hSnon ihNext
  · have hSub : Subsingleton S := not_nontrivial_iff_subsingleton.mp hSnon
    have hSbot : S = ⊥ := by
      apply le_antisymm
      · intro x _hx
        have hx0 : (⟨x, _hx⟩ : S) = 0 := hSub.elim _ _
        exact congrArg Subtype.val hx0
      · exact bot_le
    refine ⟨0, Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simp
    · simp [hSbot]
    · intro i
      exact Fin.elim0 i
termination_by Module.finrank K S
decreasing_by exact hNextDim

/-- **幂零算子的 Jordan 链基分解**：有限维空间上的每个幂零算子都存在一族
Jordan 链，其全部链向量合在一起构成空间的一组基。

证明在固定环境空间内，对不变子空间的维数归纳。归纳步骤先分解像空间 `N(S)`，
再把每条链向上提升一个向量；这些提升向量与核空间的一组基共同构成 `S` 的基。
核基中尚未作为旧链首向量的部分各自形成长度为一的新链。取 `S = V` 即得结论。
@isnad1 id=ex.1h3v.s8.678fedcb8592 from=translated src=- shape=bbe975a7 vocab=296f7bbd
-/
theorem nilpotent_exists_jordanBasisFamily
    [IsFiniteDimensional K V] (N : V →ₗ[K] V) (hN : IsNilpotent N) :
    ∃ (r : ℕ) (length : Fin r → ℕ)
      (b : (i : Fin r) → Fin (length i + 1) → V),
      IsJordanBasisFamily N r (fun _ => 0) length b := by
  have hTopInv : IsInvariantSubspace N (⊤ : Submodule K V) := by
    intro x _hx
    exact Submodule.mem_top
  have hTopNil : IsNilpotent (invariantRestriction N ⊤ hTopInv) := by
    obtain ⟨n, hn⟩ := hN
    refine ⟨n, ?_⟩
    ext x
    rw [invariantRestriction_coe_pow, hn]
    simp
  obtain ⟨r, length, b, hb⟩ :=
    nilpotent_invariantSubspace_decomposition_framework N ⊤ hTopInv hTopNil
  refine ⟨r, length, b, ?_⟩
  refine ⟨⟨hb.1, ?_⟩, hb.2.2⟩
  simpa using hb.2.1

end SandronesLibrary.LinearAlgebra.Jordan
