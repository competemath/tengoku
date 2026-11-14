import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.RingQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# AbstractAlgebra / RingPrimeIdeal —— 素理想、极大理想与商环判据

本文件完全沿用 `RingQuotient` 建立的集合层理想与商环框架：素理想和极大理想均直接定义为
环底层集合上的性质，不把 Mathlib 的 `Ideal` 承载结构暴露在教材主接口中。对于交换环，
文件证明极大理想集合必为素理想集合，并用显式的集合商环刻画素理想与极大理想：前者恰好
对应满足整环公理的商环，后者恰好对应满足域公理的商环。

文件中只有两条明确标注的兼容桥把集合层定义与 Mathlib 的 `Ideal.IsPrime` 和
`Ideal.IsMaximal` 对接；其余公开主签名只使用本库的集合层概念、商环投影及显式代数公理。
证明沿用已验证框架，不引入额外公理或占位符。

## 本文件当前条目

- `abstract-algebra.ring.prime-ideal`：集合层素理想、极大理想及其商环判据。

> **Entry**: abstract-algebra.ring.prime-ideal
-/

namespace SandronesLibrary.AbstractAlgebra.Ring

/-- **素理想集合**：`I` 是双边理想集合、不是全集，并且乘积属于 `I` 时至少一个因子属于 `I`。
> **Entry**: abstract-algebra.ring.prime-ideal-/
def PrimeIdealSet {R : Type*} [Zero R] [One R] [Add R] [Mul R] [Neg R]
    (I : Set R) : Prop :=
  TwoSidedIdealSet I ∧ I ≠ Set.univ ∧
    ∀ a b : R, a * b ∈ I → a ∈ I ∨ b ∈ I

/-- **极大理想集合**：`I` 是真双边理想集合，且任何包含 `I` 的双边理想集合只能是 `I` 或全集。
> **Entry**: abstract-algebra.ring.prime-ideal-/
def MaximalIdealSet {R : Type*} [Zero R] [One R] [Add R] [Mul R] [Neg R]
    (I : Set R) : Prop :=
  TwoSidedIdealSet I ∧ I ≠ Set.univ ∧
    ∀ J : Set R, TwoSidedIdealSet J → I ⊆ J → J = I ∨ J = Set.univ

/-- **Mathlib 素理想兼容桥**：集合层素理想恰好是某个 Mathlib 素理想的底层集合。
这是允许在公开签名中出现 `Ideal` 与 `IsPrime` 的两条明确兼容桥之一。
> **Entry**: abstract-algebra.ring.prime-ideal
@isnad1 id=iff.0h2v.s6.f17bc32dde0f from=translated src=- shape=14b5be8e vocab=75873a59
-/
theorem primeIdealSet_iff_exists_ideal_isPrime {R : Type*} [CommRing R] (I : Set R) :
    PrimeIdealSet I ↔ ∃ J : Ideal R, (J : Set R) = I ∧ J.IsPrime := by
  constructor
  · intro h
    obtain ⟨J, hJI⟩ := (twoSidedIdealSet_iff_exists_ideal I).mp h.1
    refine ⟨J, hJI, (is_prime_iff J).mpr ⟨?_, ?_⟩⟩
    · intro htop
      apply h.2.1
      rw [← hJI, htop]
      rfl
    · intro x y hxy
      have hxyI : x * y ∈ I := by
        change x * y ∈ (J : Set R) at hxy
        rw [hJI] at hxy
        exact hxy
      rcases h.2.2 x y hxyI with hx | hy
      · left
        change x ∈ (J : Set R)
        rw [hJI]
        exact hx
      · right
        change y ∈ (J : Set R)
        rw [hJI]
        exact hy
  · rintro ⟨J, hJI, hJ⟩
    refine ⟨(twoSidedIdealSet_iff_exists_ideal I).mpr ⟨J, hJI⟩, ?_, ?_⟩
    · intro htop
      apply (is_prime_iff J).mp hJ |>.1
      ext x
      change x ∈ (J : Set R) ↔ x ∈ (⊤ : Ideal R)
      rw [hJI, htop]
      simp
    · intro x y hxy
      have hxy' : x * y ∈ J := by
        change x * y ∈ (J : Set R)
        rw [hJI]
        exact hxy
      rcases (is_prime_iff J).mp hJ |>.2 hxy' with hx | hy
      · left
        rw [← hJI]
        exact hx
      · right
        rw [← hJI]
        exact hy

/-- **Mathlib 极大理想兼容桥**：集合层极大理想恰好是某个 Mathlib 极大理想的底层集合。
这是允许在公开签名中出现 `Ideal` 与 `IsMaximal` 的两条明确兼容桥之一。
> **Entry**: abstract-algebra.ring.prime-ideal
@isnad1 id=iff.0h2v.s6.ad8ee0e13b67 from=translated src=- shape=14b5be8e vocab=8b0c2659
-/
theorem maximalIdealSet_iff_exists_ideal_isMaximal {R : Type*} [CommRing R] (I : Set R) :
    MaximalIdealSet I ↔ ∃ J : Ideal R, (J : Set R) = I ∧ J.IsMaximal := by
  constructor
  · intro h
    obtain ⟨J, hJI⟩ := (twoSidedIdealSet_iff_exists_ideal I).mp h.1
    refine ⟨J, hJI, Ideal.isMaximal_def.mpr ⟨?_, ?_⟩⟩
    · intro htop
      apply h.2.1
      rw [← hJI, htop]
      rfl
    · intro K hJK
      have hsubset : I ⊆ (K : Set R) := by
        intro x hx
        apply hJK.le
        change x ∈ (J : Set R)
        rw [hJI]
        exact hx
      rcases h.2.2 (K : Set R)
          ((twoSidedIdealSet_iff_exists_ideal (K : Set R)).mpr ⟨K, rfl⟩) hsubset with hKI | hKtop
      · exfalso
        apply hJK.ne
        ext x
        change x ∈ (J : Set R) ↔ x ∈ (K : Set R)
        rw [hJI, hKI]
      · ext x
        change x ∈ (K : Set R) ↔ x ∈ (⊤ : Ideal R)
        rw [hKtop]
        simp
  · rintro ⟨J, hJI, hJ⟩
    refine ⟨(twoSidedIdealSet_iff_exists_ideal I).mpr ⟨J, hJI⟩, ?_, ?_⟩
    · intro htop
      apply hJ.ne_top
      ext x
      change x ∈ (J : Set R) ↔ x ∈ (⊤ : Ideal R)
      rw [hJI, htop]
      simp
    · intro K hK hsubset
      obtain ⟨L, hLK⟩ := (twoSidedIdealSet_iff_exists_ideal K).mp hK
      have hJL : J ≤ L := by
        intro x hx
        change x ∈ (L : Set R)
        rw [hLK]
        apply hsubset
        change x ∈ (J : Set R) at hx
        rwa [hJI] at hx
      by_cases hLtop : L = ⊤
      · right
        rw [← hLK, hLtop]
        rfl
      · left
        have hJL_eq : J = L := hJ.eq_of_le hLtop hJL
        rw [← hJI, ← hLK, hJL_eq]

/-- **极大理想必为素理想**：交换环中的每个极大理想集合都是素理想集合。
> **Entry**: abstract-algebra.ring.prime-ideal
@isnad1 id=primeide.1h2v.s6.f45420c234f6 from=translated src=- shape=93e860ac vocab=442ecf15
-/
theorem maximalIdealSet_is_prime {R : Type*} [CommRing R] {I : Set R}
    (hI : MaximalIdealSet I) : PrimeIdealSet I := by
  obtain ⟨J, hJI, hJ⟩ := (maximalIdealSet_iff_exists_ideal_isMaximal I).mp hI
  exact (primeIdealSet_iff_exists_ideal_isPrime I).mpr
    ⟨J, hJI, is_maximal_implies_is_prime J hJ⟩

/-- **商类为零判据**：商环投影的像为零，当且仅当原元素属于给定理想集合。
> **Entry**: abstract-algebra.ring.prime-ideal
@isnad1 id=iff.1h3v.s6.368cd73f14b8 from=translated src=- shape=7af2515b vocab=3c29a1f7
-/
theorem quotientRingProjection_eq_zero_iff {R : Type*} [CommRing R] {I : Set R}
    (hI : TwoSidedIdealSet I) (x : R) :
    quotientRingProjection I hI x = 0 ↔ x ∈ I := by
  simpa [quotientZero_eq_projection, idealCongruent] using
    quotientRingProjection_eq_iff hI x 0

/-- **商环非平凡判据**：集合商环中零不等于一，当且仅当被商去的理想集合不是全集。
> **Entry**: abstract-algebra.ring.prime-ideal
@isnad1 id=iff.1h2v.s6.766931d7874e from=translated src=- shape=82b5705e vocab=7cd8bd4e
-/
theorem quotientRingSet_zero_ne_one_iff {R : Type*} [CommRing R] {I : Set R}
    (hI : TwoSidedIdealSet I) :
    (0 : quotientRingSet I hI) ≠ 1 ↔ I ≠ Set.univ := by
  constructor
  · intro h01 htop
    apply h01
    rw [quotientZero_eq_projection, quotientOne_eq_projection,
      quotientRingProjection_eq_iff]
    change (0 : R) - 1 ∈ I
    rw [htop]
    exact Set.mem_univ _
  · intro hproper h01
    apply hproper
    rw [Set.eq_univ_iff_forall]
    intro x
    let A := quotientRingSet_ringAxioms I hI
    have hx0 : quotientRingProjection I hI x = 0 := by
      calc
        quotientRingProjection I hI x = quotientRingProjection I hI x * 1 :=
          (A.mul_one (quotientRingProjection I hI x)).symm
        _ = quotientRingProjection I hI x * 0 := by rw [h01]
        _ = quotientRingProjection I hI (x * 0) := quotientMul_projection I hI x 0
        _ = quotientRingProjection I hI 0 := by rw [mul_zero]
        _ = 0 := (quotientZero_eq_projection I hI).symm
    exact quotientRingProjection_eq_zero_iff hI x |>.mp hx0

/-- **商环乘积为零判据**：两个代表元像的乘积为零，当且仅当代表元乘积属于理想集合。
> **Entry**: abstract-algebra.ring.prime-ideal
@isnad1 id=iff.1h4v.s7.3b74e3eb94a4 from=translated src=- shape=bd4108c4 vocab=cacb8b0a
-/
theorem quotientRingSet_mul_eq_zero_iff {R : Type*} [CommRing R] {I : Set R}
    (hI : TwoSidedIdealSet I) (a b : R) :
    quotientRingProjection I hI a * quotientRingProjection I hI b = 0 ↔ a * b ∈ I := by
  rw [quotientMul_projection, quotientRingProjection_eq_zero_iff]

/-- **商环投影可逆判据**：代表元的像是单位元，当且仅当存在 `b` 使 `a * b - 1` 属于理想集合。
> **Entry**: abstract-algebra.ring.prime-ideal
@isnad1 id=iff.1h3v.s7.93f15d719ca9 from=translated src=- shape=1e7c88e7 vocab=e322401d
-/
theorem quotientRingSet_projection_unit_iff {R : Type*} [CommRing R] {I : Set R}
    (hI : TwoSidedIdealSet I) (a : R) :
    UnitElement (quotientRingProjection I hI a) ↔
      ∃ b : R, a * b - 1 ∈ I := by
  constructor
  · rintro ⟨q, haq, _⟩
    revert haq
    refine Quotient.inductionOn q ?_
    intro b haq
    refine ⟨b, ?_⟩
    have heq : quotientRingProjection I hI (a * b) =
        quotientRingProjection I hI 1 := by
      change quotientRingProjection I hI a * quotientRingProjection I hI b = 1 at haq
      rw [quotientMul_projection, quotientOne_eq_projection] at haq
      exact haq
    simpa [idealCongruent] using (quotientRingProjection_eq_iff hI (a * b) 1).mp heq
  · rintro ⟨b, hab⟩
    refine ⟨quotientRingProjection I hI b, ?_, ?_⟩
    · rw [quotientMul_projection, quotientOne_eq_projection]
      apply (quotientRingProjection_eq_iff hI (a * b) 1).mpr
      simpa [idealCongruent] using hab
    · rw [quotientMul_projection, quotientOne_eq_projection]
      apply (quotientRingProjection_eq_iff hI (b * a) 1).mpr
      simpa [idealCongruent, mul_comm] using hab

/-- **商环交换环公理**：交换环按双边理想集合得到的集合商环满足本库显式交换环公理。
> **Entry**: abstract-algebra.ring.prime-ideal
@isnad1 id=commutat.1h2v.s6.7f6507243f75 from=translated src=- shape=d5b4db11 vocab=72adc493
-/
theorem quotientRingSet_commutativeRingAxioms {R : Type*} [CommRing R]
    (I : Set R) (hI : TwoSidedIdealSet I) :
    CommutativeRingAxioms (quotientRingSet I hI) := by
  refine ⟨quotientRingSet_ringAxioms I hI, ?_⟩
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  change quotientRingProjection I hI (a * b) = quotientRingProjection I hI (b * a)
  rw [mul_comm]

/-- **素理想商环刻画**：理想集合为素理想，当且仅当对应集合商环满足本库显式整环公理。
> **Entry**: abstract-algebra.ring.prime-ideal
@isnad1 id=iff.1h2v.s7.ddb5b3705633 from=translated src=- shape=0a5d8173 vocab=330f7c66
-/
theorem primeIdealSet_iff_quotient_integralDomainAxioms {R : Type*} [CommRing R]
    (I : Set R) (hI : TwoSidedIdealSet I) :
    PrimeIdealSet I ↔ IntegralDomainAxioms (quotientRingSet I hI) := by
  constructor
  · intro hprime
    refine ⟨quotientRingSet_commutativeRingAxioms I hI,
      (quotientRingSet_zero_ne_one_iff hI).mpr hprime.2.1, ?_⟩
    intro x y hxy
    refine Quotient.inductionOn₂ x y ?_ hxy
    intro a b hab
    have habI : a * b ∈ I :=
      (quotientRingSet_mul_eq_zero_iff hI a b).mp hab
    rcases hprime.2.2 a b habI with ha | hb
    · left
      exact (quotientRingProjection_eq_zero_iff hI a).mpr ha
    · right
      exact (quotientRingProjection_eq_zero_iff hI b).mpr hb
  · intro hdomain
    refine ⟨hI, (quotientRingSet_zero_ne_one_iff hI).mp hdomain.zero_ne_one, ?_⟩
    intro a b hab
    have hmul : quotientRingProjection I hI a * quotientRingProjection I hI b = 0 :=
      (quotientRingSet_mul_eq_zero_iff hI a b).mpr hab
    rcases hdomain.noZeroDivisors _ _ hmul with ha | hb
    · left
      exact (quotientRingProjection_eq_zero_iff hI a).mp ha
    · right
      exact (quotientRingProjection_eq_zero_iff hI b).mp hb

/-- **极大理想商环刻画**：理想集合为极大理想，当且仅当对应集合商环满足本库显式域公理。
> **Entry**: abstract-algebra.ring.prime-ideal
@isnad1 id=iff.1h2v.s7.fd7a619476a7 from=translated src=- shape=0a5d8173 vocab=26681a94
-/
theorem maximalIdealSet_iff_quotient_fieldAxioms {R : Type*} [CommRing R]
    (I : Set R) (hI : TwoSidedIdealSet I) :
    MaximalIdealSet I ↔ FieldAxioms (quotientRingSet I hI) := by
  constructor
  · intro hmax
    refine ⟨quotientRingSet_commutativeRingAxioms I hI,
      (quotientRingSet_zero_ne_one_iff hI).mpr hmax.2.1, ?_⟩
    intro q hq
    refine Quotient.inductionOn q ?_ hq
    intro a ha
    have haI : a ∉ I := by
      intro haI
      exact ha ((quotientRingProjection_eq_zero_iff hI a).mpr haI)
    let K : Set R := {x | ∃ i ∈ I, ∃ r : R, x = i + r * a}
    have hKleft : LeftIdealSet K := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact ⟨0, hI.1.1, 0, by simp⟩
      · rintro x y ⟨i, hi, r, rfl⟩ ⟨j, hj, s, rfl⟩
        refine ⟨i + j, hI.1.2.1 hi hj, r + s, ?_⟩
        ring
      · rintro x ⟨i, hi, r, rfl⟩
        refine ⟨-i, hI.1.2.2.1 hi, -r, ?_⟩
        ring
      · rintro c x ⟨i, hi, r, rfl⟩
        refine ⟨c * i, hI.1.2.2.2 c hi, c * r, ?_⟩
        ring
    have hK : TwoSidedIdealSet K := by
      refine ⟨hKleft, hKleft.1, hKleft.2.1, hKleft.2.2.1, ?_⟩
      intro c x hx
      rw [mul_comm]
      exact hKleft.2.2.2 c hx
    have hIK : I ⊆ K := by
      intro x hx
      exact ⟨x, hx, 0, by simp⟩
    have haK : a ∈ K := ⟨0, hI.1.1, 1, by simp⟩
    have hKne : K ≠ I := by
      intro hKI
      exact haI (hKI ▸ haK)
    have hKtop : K = Set.univ :=
      (hmax.2.2 K hK hIK).resolve_left hKne
    have hOneK : (1 : R) ∈ K := hKtop.symm ▸ Set.mem_univ 1
    obtain ⟨i, hi, r, hir⟩ := hOneK
    apply (quotientRingSet_projection_unit_iff hI a).mpr
    refine ⟨r, ?_⟩
    have hneg := hI.1.2.2.1 hi
    have heq : a * r - 1 = -i := by
      calc
        a * r - 1 = r * a - 1 := by rw [mul_comm a r]
        _ = r * a - (i + r * a) := by rw [← hir]
        _ = -i := by ring
    rw [heq]
    exact hneg
  · intro hfield
    refine ⟨hI, (quotientRingSet_zero_ne_one_iff hI).mp hfield.zero_ne_one, ?_⟩
    intro J hJ hIJ
    by_cases hJI : J = I
    · exact Or.inl hJI
    · right
      rw [Set.eq_univ_iff_forall]
      obtain ⟨a, haJ, haI⟩ : ∃ a, a ∈ J ∧ a ∉ I := by
        by_contra hnone
        apply hJI
        apply Set.Subset.antisymm _ hIJ
        intro x hxJ
        by_contra hxI
        exact hnone ⟨x, hxJ, hxI⟩
      have hpa : quotientRingProjection I hI a ≠ 0 := by
        intro hzero
        exact haI ((quotientRingProjection_eq_zero_iff hI a).mp hzero)
      obtain ⟨b, hab⟩ :=
        (quotientRingSet_projection_unit_iff hI a).mp
          (hfield.nonzero_unit (quotientRingProjection I hI a) hpa)
      have habJ : a * b - 1 ∈ J := hIJ hab
      have habmulJ : a * b ∈ J := hJ.2.2.2.2 b haJ
      have hnegJ : -(a * b - 1) ∈ J := hJ.1.2.2.1 habJ
      have honeJ : (1 : R) ∈ J := by
        have := hJ.1.2.1 habmulJ hnegJ
        convert this using 1
        ring
      intro x
      have hxmul : x * 1 ∈ J := hJ.1.2.2.2 x honeJ
      simpa using hxmul

end SandronesLibrary.AbstractAlgebra.Ring
