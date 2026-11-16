import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_AdmissibleAlgebra_fixedPoints_isAdicComplete_and_finite_and_finiteType.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_fixedPoints_isAdicComplete_and_finite_and_finiteType

set_option autoImplicit false

namespace ADMINV

/--
@isnad1 id=ex.1h7v.s12.6ca68cf1eda6 from=translated src=- shape=0cb36251 vocab=0264e5ab
-/
theorem exists_mvPolynomial_sub_mem_pow
    (𝒪 : Type) [CommRing 𝒪] (R : Type) [CommRing R] [Algebra 𝒪 R] (ϖ : 𝒪) {m : ℕ} (x : Fin m → R)
    (hgen : Algebra.adjoin 𝒪 (Set.range fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R ϖ}) (x i)) = ⊤)
    (k : ℕ) (r : R) :
    ∃ P : MvPolynomial (Fin m) 𝒪, r - MvPolynomial.aeval x P ∈ Ideal.span {algebraMap 𝒪 R ϖ} ^ k := by
  classical
  set ϖ' := algebraMap 𝒪 R ϖ with hϖ'
  let I : Ideal R := Ideal.span {ϖ'}

  have step : ∀ s : R, ∃ Q : MvPolynomial (Fin m) 𝒪, s - MvPolynomial.aeval x Q ∈ I := by
    intro s
    have hs : Ideal.Quotient.mk I s ∈ Algebra.adjoin 𝒪 (Set.range fun i => Ideal.Quotient.mk I (x i)) := by rw [hgen]; trivial
    rw [Algebra.adjoin_range_eq_range_aeval] at hs
    obtain ⟨Q, hQ⟩ := hs
    refine ⟨Q, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, ← hQ]
    have := congrArg (fun φ => φ Q) (MvPolynomial.comp_aeval x (Ideal.Quotient.mkₐ 𝒪 I))
    simpa [Ideal.Quotient.mkₐ_eq_mk] using this.symm
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨P, hP⟩ := ih
    rw [Ideal.span_singleton_pow] at hP
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hP
    obtain ⟨Q, hQ⟩ := step s
    refine ⟨P + MvPolynomial.C (ϖ ^ k) * Q, ?_⟩
    have : r - MvPolynomial.aeval x (P + MvPolynomial.C (ϖ ^ k) * Q) = (s - MvPolynomial.aeval x Q) * ϖ' ^ k := by
      rw [map_add, map_mul, MvPolynomial.aeval_C, map_pow, ← hϖ', ← sub_sub, ← hs]; ring
    rw [this, pow_succ, Ideal.span_singleton_pow, mul_comm (s - MvPolynomial.aeval x Q)]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hQ

/--
@isnad1 id=ex.4h6v.s9.7edec3afebdc from=translated src=- shape=73d8ed18 vocab=7957d403
-/
theorem exists_repr_of_forall_exists_repr_add_mul
    (R : Type) [CommRing R] (ϖ : R) (hc : IsAdicComplete (Ideal.span {ϖ}) R) (A : Subring R)
    (hAclosed : ∀ (f : ℕ → R) (L : R), (∀ n, f n ∈ A) →
      (∀ n, f n ≡ L [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule R R)]) → L ∈ A)
    (hϖA : ϖ ∈ A) {d : ℕ} (μ : Fin d → R)
    (hstep : ∀ r : R, ∃ (c : Fin d → R) (r' : R), (∀ j, c j ∈ A) ∧ r = (∑ j, c j * μ j) + ϖ * r') (r : R) :
    ∃ a : Fin d → R, (∀ j, a j ∈ A) ∧ r = ∑ j, a j * μ j := by
  classical
  obtain ⟨I, hI⟩ : ∃ I : Ideal R, Ideal.span {ϖ} = I := ⟨_, rfl⟩
  rw [hI] at hc hAclosed
  have hpow : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by rw [smul_eq_mul, Ideal.mul_top]
  have smodR : ∀ (n : ℕ) (x y : R), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := fun n x y => by
    rw [SModEq.sub_mem, hpow]
  have hϖn : ∀ n : ℕ, ϖ ^ n ∈ I ^ n := fun n => Ideal.pow_mem_pow (hI ▸ Ideal.subset_span rfl) n

  choose cf nx hcf hnx using hstep
  let sq : ℕ → R := fun k => nx^[k] r
  have sq_zero : sq 0 = r := rfl
  have sq_succ : ∀ k, sq (k + 1) = nx (sq k) := fun k => Function.iterate_succ_apply' nx k _
  let S : Fin d → ℕ → R := fun j k => ∑ i ∈ Finset.range k, ϖ ^ i * cf (sq i) j
  have hSA : ∀ j k, S j k ∈ A := fun j k =>
    A.sum_mem fun i _ => A.mul_mem (A.pow_mem hϖA i) (hcf (sq i) j)

  have hinv : ∀ k, r = (∑ j, S j k * μ j) + ϖ ^ k * sq k := by
    intro k
    induction k with
    | zero => simp [S, sq_zero]
    | succ k ih =>
      have h := hnx (sq k)
      have e1 : ∑ j, S j (k + 1) * μ j = ∑ j, S j k * μ j + ∑ j, ϖ ^ k * cf (sq k) j * μ j := by
        simp only [S, Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
      have e2 : ∑ j, ϖ ^ k * cf (sq k) j * μ j = ϖ ^ k * ∑ j, cf (sq k) j * μ j := by
        rw [Finset.mul_sum]; simp only [mul_assoc]
      rw [e1, e2, sq_succ, pow_succ]
      conv_lhs => rw [ih, h]
      ring

  have hS : ∀ (j : Fin d) {m n : ℕ}, m ≤ n → S j m ≡ S j n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro j m n hmn
    rw [smodR]
    have : S j m - S j n = -(∑ i ∈ Finset.Ico m n, ϖ ^ i * cf (sq i) j) := by
      simp only [S]; rw [← Finset.sum_range_add_sum_Ico _ hmn]; ring
    rw [this]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hϖn i))

  have hL : ∀ j : Fin d, ∃ L : R, ∀ n, S j n ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] :=
    fun j => hc.toIsPrecomplete.prec' (S j) (hS j)
  choose a ha using hL
  have haA : ∀ j, a j ∈ A := fun j => hAclosed (S j) (a j) (hSA j) (ha j)
  refine ⟨a, haA, ?_⟩

  have hzero : r - ∑ j, a j * μ j = 0 := by
    apply hc.toIsHausdorff.haus'
    intro n
    rw [smodR, sub_zero]
    have e : r - ∑ j, a j * μ j = ϖ ^ n * sq n + ∑ j, (S j n - a j) * μ j := by
      conv_lhs => rw [hinv n]
      simp only [sub_mul, Finset.sum_sub_distrib]; ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hϖn n)) (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_)
    exact (smodR n _ _).1 (ha j n)
  exact (sub_eq_zero.1 hzero)

end ADMINV

/--
@isnad1 id=and.6h4v.s12.0d5e6fc9ad1e from=translated src=- shape=a6870bb9 vocab=7b4e7146
-/
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (G : Type) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R] :
    IsAdicComplete (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π}) ↥(FixedPoints.subalgebra 𝒪 R G) ∧
    Module.Finite ↥(FixedPoints.subalgebra 𝒪 R G) R ∧
    Algebra.FiniteType 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⧸ Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π}) ∧
    (∀ k : ℕ, ∀ x : ↥(FixedPoints.subalgebra 𝒪 R G),
      (x : R) ∈ Ideal.span {(algebraMap 𝒪 R π) ^ k} → x ∈ Ideal.span {(algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π) ^ k}) := by
  classical
  set A := FixedPoints.subalgebra 𝒪 R G with hA
  set ϖ : R := algebraMap 𝒪 R π with hϖ

  have hreg : ∀ (k : ℕ) (y : R), ϖ ^ k * y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      apply ih
      apply hRtf
      rw [← mul_assoc, ← pow_succ']; exact hy

  have hgϖ : ∀ g : G, g • ϖ = ϖ := fun g => by rw [hϖ, Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

  have hAtors : ∀ k : ℕ, ∀ x : ↥A, (x : R) ∈ Ideal.span {ϖ ^ k} → x ∈ Ideal.span {(algebraMap 𝒪 (↥A) π) ^ k} := by
    intro k x hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx
    have hcA : c ∈ A := by
      rw [hA]; intro g
      show g • c = c
      have h1 : g • (x : R) = x := x.2 g
      rw [← hc, smul_mul', smul_pow', hgϖ] at h1
      have h2 : ϖ ^ k * (g • c - c) = 0 := by rw [mul_sub, mul_comm, mul_comm (ϖ ^ k), h1, sub_self]
      exact sub_eq_zero.1 (hreg k _ h2)
    refine Ideal.mem_span_singleton'.2 ⟨⟨c, hcA⟩, Subtype.ext ?_⟩
    show c * ((algebraMap 𝒪 (↥A) π : ↥A) : R) ^ k = x
    rw [← hc]; rfl

  haveI hRc' : IsAdicComplete (Ideal.span {ϖ}) R := hRc
  set ϖA : ↥A := algebraMap 𝒪 (↥A) π with hϖA
  have memA : ∀ (n : ℕ) (x : ↥A), x ∈ Ideal.span {ϖA} ^ n ↔ (x : R) ∈ Ideal.span {ϖ} ^ n := by
    intro n x
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx
      refine Ideal.mem_span_singleton'.2 ⟨(c : R), ?_⟩
      rw [← hc]; rfl
    · intro hx; exact hAtors n x hx
  have smodA : ∀ (n : ℕ) (x y : ↥A), x ≡ y [SMOD (Ideal.span {ϖA} ^ n • ⊤ : Submodule ↥A ↥A)] ↔ x - y ∈ Ideal.span {ϖA} ^ n := by
    intro n x y; rw [SModEq.sub_mem]; simp
  have smodR : ∀ (n : ℕ) (x y : R), x ≡ y [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ Ideal.span {ϖ} ^ n := by
    intro n x y; rw [SModEq.sub_mem]; simp
  have hH : IsHausdorff (Ideal.span {ϖA}) ↥A := ⟨fun x hx => by
    apply Subtype.ext
    apply IsHausdorff.haus' (I := Ideal.span {ϖ})
    intro n
    have := (smodA n x 0).1 (hx n)
    rw [sub_zero] at this
    rw [smodR, sub_zero]; exact (memA n x).1 this⟩
  have hgpow : ∀ (g : G) (n : ℕ) (y : R), y ∈ Ideal.span {ϖ} ^ n → g • y ∈ Ideal.span {ϖ} ^ n := by
    intro g n y hy
    rw [Ideal.span_singleton_pow] at hy ⊢
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    rw [smul_mul', smul_pow', hgϖ]
    exact Ideal.mem_span_singleton'.2 ⟨g • c, rfl⟩
  have hP : IsPrecomplete (Ideal.span {ϖA}) ↥A := ⟨fun {f} hf => by

    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (fun n => (f n : R)) (fun {m n} hmn => by
      rw [smodR]
      have := (memA m _).1 ((smodA m (f m) (f n)).1 (hf hmn))
      simpa using this)

    have hLA : L ∈ A := by
      rw [hA]; intro g
      show g • L = L
      apply eq_of_sub_eq_zero
      apply IsHausdorff.haus' (I := Ideal.span {ϖ})
      intro n
      rw [smodR, sub_zero]
      have h1 : (f n : R) - L ∈ Ideal.span {ϖ} ^ n := (smodR n _ _).1 (hL n)
      have h2 : g • ((f n : R) - L) - ((f n : R) - L) = -(g • L - L) := by
        rw [smul_sub, show g • ((f n : ↥A) : R) = (f n : R) from (f n).2 g]; ring
      have h3 := Ideal.sub_mem _ (hgpow g n _ h1) h1
      rw [h2] at h3
      exact (Ideal.neg_mem_iff _).1 h3
    refine ⟨⟨L, hLA⟩, fun n => ?_⟩
    rw [smodA, memA]
    have h1 : (f n : R) - L ∈ Ideal.span {ϖ} ^ n := (smodR n _ _).1 (hL n)
    simpa using h1⟩
  have hcompl : IsAdicComplete (Ideal.span {ϖA}) ↥A := { toIsHausdorff := hH, toIsPrecomplete := hP }

  have hAclosed : ∀ (f : ℕ → R) (L : R), (∀ n, f n ∈ A.toSubring) →
      (∀ n, f n ≡ L [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule R R)]) → L ∈ A.toSubring := by
    intro f L hf hfL
    rw [Subalgebra.mem_toSubring, hA]
    intro g
    show g • L = L
    apply eq_of_sub_eq_zero
    apply IsHausdorff.haus' (I := Ideal.span {ϖ})
    intro n
    rw [smodR, sub_zero]
    have h1 : f n - L ∈ Ideal.span {ϖ} ^ n := (smodR n _ _).1 (hfL n)
    have hfn : g • f n = f n := by
      have := hf n; rw [Subalgebra.mem_toSubring, hA] at this; exact this g
    have h2 : g • (f n - L) - (f n - L) = -(g • L - L) := by rw [smul_sub, hfn]; ring
    have h3 := Ideal.sub_mem _ (hgpow g n _ h1) h1
    rw [h2] at h3
    exact (Ideal.neg_mem_iff _).1 h3

  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨t, htfin, ht⟩ := Subalgebra.fg_def.1 hRft.out
  obtain ⟨m, emb, hemb⟩ := htfin.fin_embedding
  choose x hx using fun i : Fin m => Ideal.Quotient.mk_surjective (emb i)
  have hgen : Algebra.adjoin 𝒪 (Set.range fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π}) (x i)) = ⊤ := by
    have : (Set.range fun i => Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π}) (x i)) = t := by
      rw [← hemb]; ext y; constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, (hx i).symm⟩
      · rintro ⟨i, rfl⟩; exact ⟨i, hx i⟩
    rw [this]; exact ht

  let C : Set R := Set.range fun p : (Σ i : Fin m, Fin ((prodXSubSMul G R (x i)).natDegree + 1)) =>
    (prodXSubSMul G R (x p.1)).coeff p.2
  let S₀ : Subalgebra 𝒪 R := Algebra.adjoin 𝒪 C
  have hCA : C ⊆ (A : Set R) := by
    rintro _ ⟨⟨i, n⟩, rfl⟩
    show (prodXSubSMul G R (x i)).coeff n ∈ A
    rw [hA]; intro g; exact prodXSubSMul.coeff G R (x i) g n
  have hS₀A : S₀ ≤ A := Algebra.adjoin_le hCA

  have hint : ∀ i, IsIntegral (↥S₀) (x i) := by
    intro i
    have hl : prodXSubSMul G R (x i) ∈ Polynomial.lifts (algebraMap (↥S₀) R) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : n ≤ (prodXSubSMul G R (x i)).natDegree
      · have hc : (prodXSubSMul G R (x i)).coeff n ∈ S₀ :=
          Algebra.subset_adjoin ⟨⟨i, ⟨n, Nat.lt_succ_of_le hn⟩⟩, rfl⟩
        exact ⟨⟨_, hc⟩, rfl⟩
      · refine ⟨0, ?_⟩
        rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hn)]
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (prodXSubSMul.monic G R (x i))
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq]; exact prodXSubSMul.eval G R (x i)

  have hNfg : (Subalgebra.toSubmodule (Algebra.adjoin (↥S₀) (Set.range x))).FG :=
    fg_adjoin_of_finite (Set.finite_range x) (by rintro _ ⟨i, rfl⟩; exact hint i)
  obtain ⟨T, hT⟩ := hNfg
  obtain ⟨d, μe, hμ⟩ := T.finite_toSet.fin_embedding

  have hstep : ∀ r : R, ∃ (c : Fin d → R) (r' : R), (∀ j, c j ∈ A.toSubring) ∧ r = (∑ j, c j * μe j) + ϖ * r' := by
    intro r
    obtain ⟨P, hP⟩ := ADMINV.exists_mvPolynomial_sub_mem_pow 𝒪 R π x hgen 1 r
    rw [pow_one] at hP
    obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton'.1 hP
    have hmem : MvPolynomial.aeval x P ∈ Submodule.span (↥S₀) (Set.range μe) := by
      rw [hμ, hT, Subalgebra.mem_toSubmodule, ← MvPolynomial.aeval_map_algebraMap (↥S₀) x P,
        Algebra.adjoin_range_eq_range_aeval]
      exact ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥S₀)).1 hmem
    refine ⟨fun j => (c j : R), r', fun j => ?_, ?_⟩
    · rw [Subalgebra.mem_toSubring]; exact hS₀A (c j).2
    · have : (∑ j, (c j : R) * μe j) = MvPolynomial.aeval x P := by
        rw [← hc]; rfl
      rw [this, mul_comm, hr']; ring
  have hϖA : ϖ ∈ A.toSubring := by rw [Subalgebra.mem_toSubring, hϖ]; exact A.algebraMap_mem π
  have hrep := ADMINV.exists_repr_of_forall_exists_repr_add_mul R ϖ hRc' A.toSubring hAclosed hϖA μe hstep

  have hfinAR : Module.Finite (↥A) R := by
    rw [Module.finite_def]
    refine ⟨Finset.univ.image μe, ?_⟩
    rw [eq_top_iff]
    intro r _
    obtain ⟨a, ha, rfl⟩ := hrep r
    refine Submodule.sum_mem _ fun j _ => ?_
    have haj : a j ∈ A := by have := ha j; rwa [Subalgebra.mem_toSubring] at this
    have : (⟨a j, haj⟩ : ↥A) • μe j = a j * μe j := rfl
    rw [← this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  refine ⟨hcompl, hfinAR, ?_, hAtors⟩

  haveI : IsNoetherianRing 𝒪 := inferInstance
  let J : Ideal ↥A := Ideal.span {ϖA}
  have hJI : J ≤ Ideal.comap (A.val : ↥A →ₐ[𝒪] R).toRingHom (Ideal.span {ϖ}) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.subset_span rfl
  let φ : (↥A ⧸ J) →+* (R ⧸ Ideal.span {ϖ}) := Ideal.quotientMap (Ideal.span {ϖ}) (A.val : ↥A →ₐ[𝒪] R).toRingHom hJI
  have hφ : ∀ a : ↥A, φ (Ideal.Quotient.mk J a) = Ideal.Quotient.mk (Ideal.span {ϖ}) (a : R) := fun a => Ideal.quotientMap_mk
  letI : Algebra (↥A ⧸ J) (R ⧸ Ideal.span {ϖ}) := φ.toAlgebra
  haveI : IsScalarTower 𝒪 (↥A ⧸ J) (R ⧸ Ideal.span {ϖ}) := IsScalarTower.of_algebraMap_eq (fun c => by
    show Ideal.Quotient.mk (Ideal.span {ϖ}) (algebraMap 𝒪 R c) = φ (Ideal.Quotient.mk J (algebraMap 𝒪 (↥A) c))
    rw [hφ]; rfl)
  have hinj : Function.Injective φ := by
    intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [hφ, hφ, Ideal.Quotient.eq] at huv
    rw [Ideal.Quotient.eq]
    have := hAtors 1 (a - b) (by simpa [pow_one] using huv)
    simpa [pow_one, J] using this
  have hfin' : (⊤ : Submodule (↥A ⧸ J) (R ⧸ Ideal.span {ϖ})).FG := by
    rw [← Module.finite_def]
    haveI := hfinAR
    let f : R →ₛₗ[(Ideal.Quotient.mk J : ↥A →+* ↥A ⧸ J)] (R ⧸ Ideal.span {ϖ}) :=
      { toFun := Ideal.Quotient.mk (Ideal.span {ϖ})
        map_add' := fun u v => map_add _ u v
        map_smul' := fun a r => by
          show Ideal.Quotient.mk (Ideal.span {ϖ}) ((a : R) * r) = φ (Ideal.Quotient.mk J a) * Ideal.Quotient.mk (Ideal.span {ϖ}) r
          rw [hφ, map_mul] }
    exact Module.Finite.of_surjective f Ideal.Quotient.mk_surjective
  have hAT := fg_of_fg_of_fg 𝒪 (↥A ⧸ J) (R ⧸ Ideal.span {ϖ}) hRft.out hfin' hinj
  exact ⟨hAT⟩
