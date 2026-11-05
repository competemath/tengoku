import Tengoku.NsP23.P23.Presentation.QuotientLocalSocle
import Tengoku.NsP23.P23.Artin.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical dual and ordinary trace on the final polynomial quotient

Everything on the quotient side is defined intrinsically.  The frozen final
presentation equivalence is then used to prove exact dual, canonical-map,
trace, and nearly-Gorenstein transport.
-/

namespace P23.Presentation

noncomputable section

set_option maxHeartbeats 400000

open P23.OneTie P23.Artin

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

private abbrev Q (k : Type*) [Field k] (S : Finset (Normal a b c)) :=
  FinitePolynomialQuotient k S

private abbrev A (k : Type*) [Field k] (S : Finset (Normal a b c)) :=
  MonomialArtin k S

/-- The intrinsic canonical dual of the final polynomial quotient.-/
abbrev QuotientOmega (k : Type*) [Field k]
    (S : Finset (Normal a b c)) := Module.Dual k (Q k S)

namespace QuotientOmega

variable {S : Finset (Normal a b c)}

/-- Intrinsic contragredient quotient action.-/
def act (q : Q k S) (φ : QuotientOmega k S) : QuotientOmega k S where
  toFun r := φ (q * r)
  map_add' r r' := by simp [mul_add]
  map_smul' t r := by simp [mul_smul_comm]

instance : SMul (Q k S) (QuotientOmega k S) := ⟨act⟩

/--
@isnad1 id=eq.0h8v.s9.728e92561160 from=translated src=- shape=728ebf1f vocab=63eadade
-/
@[simp]
theorem smul_apply (q : Q k S) (φ : QuotientOmega k S) (r : Q k S) :
    (q • φ) r = φ (q * r) := rfl

instance : Module (Q k S) (QuotientOmega k S) where
  one_smul φ := by
    apply LinearMap.ext
    intro r
    change φ (1 * r) = φ r
    rw [one_mul]
  mul_smul q r φ := by
    apply LinearMap.ext
    intro t
    change φ ((q * r) * t) = φ (r * (q * t))
    congr 1
    ac_rfl
  smul_zero q := by
    apply LinearMap.ext
    intro r
    rfl
  smul_add q φ ψ := by
    apply LinearMap.ext
    intro r
    rfl
  zero_smul φ := by
    apply LinearMap.ext
    intro r
    change φ (0 * r) = 0
    rw [zero_mul, map_zero]
  add_smul q r φ := by
    apply LinearMap.ext
    intro t
    change φ ((q + r) * t) = φ (q * t) + φ (r * t)
    rw [add_mul, map_add]

end QuotientOmega

/-- Precomposition with the inverse final-presentation equivalence identifies
the quotient and direct canonical duals.-/
noncomputable def quotientOmegaEquivDirectOmega
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) :
    QuotientOmega k S ≃ₗ[k] Omega k S where
  toFun φ := φ.comp
    (finitePolynomialQuotientEquiv (k := k) S hS hdom).symm.toLinearMap
  invFun ψ := ψ.comp
    (finitePolynomialQuotientEquiv (k := k) S hS hdom).toLinearMap
  left_inv φ := by
    apply LinearMap.ext
    intro q
    exact congrArg φ
      ((finitePolynomialQuotientEquiv (k := k) S hS hdom).symm_apply_apply q)
  right_inv ψ := by
    apply LinearMap.ext
    intro r
    exact congrArg ψ
      ((finitePolynomialQuotientEquiv (k := k) S hS hdom).apply_symm_apply r)
  map_add' φ ψ := by apply LinearMap.ext; intro r; rfl
  map_smul' t φ := by apply LinearMap.ext; intro r; rfl

/--
@isnad1 id=eq.2h7v.s11.af242a438886 from=translated src=- shape=4b6a4105 vocab=a2adb76a
-/
@[simp]
theorem quotientOmegaEquivDirectOmega_apply_equiv
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (φ : QuotientOmega k S)
    (q : Q k S) :
    quotientOmegaEquivDirectOmega (k := k) S hS hdom φ
        (finitePolynomialQuotientEquiv (k := k) S hS hdom q) = φ q := by
  change φ ((finitePolynomialQuotientEquiv (k := k) S hS hdom).symm
    (finitePolynomialQuotientEquiv (k := k) S hS hdom q)) = φ q
  rw [(finitePolynomialQuotientEquiv (k := k) S hS hdom).symm_apply_apply]

/--
@isnad1 id=eq.2h7v.s12.dea5c49ff929 from=translated src=- shape=3076a447 vocab=9f98aa2f
-/
@[simp]
theorem quotientOmegaEquivDirectOmega_symm_apply
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (ψ : Omega k S) (q : Q k S) :
    (quotientOmegaEquivDirectOmega (k := k) S hS hdom).symm ψ q =
      ψ (finitePolynomialQuotientEquiv (k := k) S hS hdom q) := by
  rfl

/-- Exact compatibility of dual transport with the intrinsic quotient action.
@isnad1 id=eq.2h7v.s12.12ab44831fb1 from=translated src=- shape=68008794 vocab=512a3569
-/
theorem quotientOmegaEquivDirectOmega_smul
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (q : Q k S)
    (φ : QuotientOmega k S) :
    quotientOmegaEquivDirectOmega (k := k) S hS hdom (q • φ) =
      finitePolynomialQuotientEquiv (k := k) S hS hdom q •
        quotientOmegaEquivDirectOmega (k := k) S hS hdom φ := by
  apply LinearMap.ext
  intro r
  change φ (q * (finitePolynomialQuotientEquiv (k := k) S hS hdom).symm r) =
    φ ((finitePolynomialQuotientEquiv (k := k) S hS hdom).symm
      (finitePolynomialQuotientEquiv (k := k) S hS hdom q * r))
  congr 1
  simp

/--
@isnad1 id=eq.2h7v.s13.e868af03ef64 from=translated src=- shape=885422db vocab=e653b5b3
-/
theorem quotientOmegaEquivDirectOmega_symm_smul
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (r : A k S) (ψ : Omega k S) :
    (quotientOmegaEquivDirectOmega (k := k) S hS hdom).symm (r • ψ) =
      (finitePolynomialQuotientEquiv (k := k) S hS hdom).symm r •
        (quotientOmegaEquivDirectOmega (k := k) S hS hdom).symm ψ := by
  apply (quotientOmegaEquivDirectOmega (k := k) S hS hdom).injective
  rw [quotientOmegaEquivDirectOmega_smul]
  simp

/-- Conjugate a quotient-linear canonical homomorphism to the direct model.-/
def pushCanonicalHom
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c)
    (F : QuotientOmega k S →ₗ[Q k S] Q k S) :
    Omega k S →ₗ[A k S] A k S where
  toFun ψ := finitePolynomialQuotientEquiv (k := k) S hS hdom
    (F ((quotientOmegaEquivDirectOmega (k := k) S hS hdom).symm ψ))
  map_add' ψ ψ' := by simp
  map_smul' r ψ := by
    rw [quotientOmegaEquivDirectOmega_symm_smul, F.map_smul]
    simp [smul_eq_mul]

/-- Conjugate a direct canonical homomorphism to the quotient.-/
def pullCanonicalHom
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c)
    (F : Omega k S →ₗ[A k S] A k S) :
    QuotientOmega k S →ₗ[Q k S] Q k S where
  toFun φ := (finitePolynomialQuotientEquiv (k := k) S hS hdom).symm
    (F (quotientOmegaEquivDirectOmega (k := k) S hS hdom φ))
  map_add' φ φ' := by simp
  map_smul' q φ := by
    rw [quotientOmegaEquivDirectOmega_smul, F.map_smul]
    simp [smul_eq_mul]

/--
@isnad1 id=eq.2h6v.s10.10f04209aa54 from=translated src=- shape=adbcad06 vocab=01a23de3
-/
@[simp]
theorem pull_pushCanonicalHom
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c)
    (F : QuotientOmega k S →ₗ[Q k S] Q k S) :
    pullCanonicalHom (k := k) S hS hdom
      (pushCanonicalHom (k := k) S hS hdom F) = F := by
  apply LinearMap.ext
  intro φ
  simp [pullCanonicalHom, pushCanonicalHom]

/--
@isnad1 id=eq.2h6v.s9.cf3f1181377d from=translated src=- shape=adbcad06 vocab=e1dc400e
-/
@[simp]
theorem push_pullCanonicalHom
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c)
    (F : Omega k S →ₗ[A k S] A k S) :
    pushCanonicalHom (k := k) S hS hdom
      (pullCanonicalHom (k := k) S hS hdom F) = F := by
  apply LinearMap.ext
  intro ψ
  simp [pullCanonicalHom, pushCanonicalHom]

/-- Ordinary trace on the quotient: the supremum of the ranges of all
quotient-linear maps from its intrinsic canonical dual.-/
def QuotientTraceSubmodule (k : Type*) [Field k]
    (S : Finset (Normal a b c)) : Submodule (Q k S) (Q k S) :=
  ⨆ F : QuotientOmega k S →ₗ[Q k S] Q k S, F.range

/--
@isnad1 id=le.0h6v.s11.f4f6e0eeb5cf from=translated src=- shape=6c73146c vocab=df082923
-/
theorem quotientTrace_range_le (S : Finset (Normal a b c))
    (F : QuotientOmega k S →ₗ[Q k S] Q k S) :
    F.range ≤ QuotientTraceSubmodule k S :=
  le_iSup (fun G : QuotientOmega k S →ₗ[Q k S] Q k S => G.range) F

/-- Ordinary trace membership is transported exactly by the frozen algebra
equivalence.
@isnad1 id=iff.2h6v.s10.d26bde7e4dbc from=translated src=- shape=9928ed68 vocab=bacee951
-/
theorem mem_quotientTrace_iff_equiv_mem_directTrace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (q : Q k S) :
    q ∈ QuotientTraceSubmodule k S ↔
      finitePolynomialQuotientEquiv (k := k) S hS hdom q ∈
        TraceSubmodule k S := by
  let E := finitePolynomialQuotientEquiv (k := k) S hS hdom
  constructor
  · intro hq
    refine Submodule.iSup_induction
      (fun F : QuotientOmega k S →ₗ[Q k S] Q k S => F.range)
      (motive := fun x => E x ∈ TraceSubmodule k S) hq ?_ (by simp) ?_
    · intro F x hx
      rcases hx with ⟨φ, rfl⟩
      exact trace_range_le (k := k) S (pushCanonicalHom (k := k) S hS hdom F)
        ⟨quotientOmegaEquivDirectOmega (k := k) S hS hdom φ,
          by simp [pushCanonicalHom, E]⟩
    · intro x y hx hy
      simpa using (TraceSubmodule k S).add_mem hx hy
  · intro hq
    have hback : E.symm (E q) ∈ QuotientTraceSubmodule k S := by
      refine Submodule.iSup_induction
        (fun F : Omega k S →ₗ[A k S] A k S => F.range)
        (motive := fun x => E.symm x ∈ QuotientTraceSubmodule k S) hq ?_ (by simp) ?_
      · intro F x hx
        rcases hx with ⟨ψ, rfl⟩
        exact quotientTrace_range_le (k := k) S
          (pullCanonicalHom (k := k) S hS hdom F)
          ⟨(quotientOmegaEquivDirectOmega (k := k) S hS hdom).symm ψ,
            by simp [pullCanonicalHom, E]⟩
      · intro x y hx hy
        simpa using (QuotientTraceSubmodule k S).add_mem hx hy
    simpa [E] using hback

/-- Intrinsic quotient nearly-Gorenstein condition.-/
def QuotientNearlyGorenstein
    (k : Type*) [Field k] (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c)
    (hlive : IsLiveTie S) : Prop := by
  letI := quotientIsLocalRing (k := k) S hS hdom hlive
  exact IsLocalRing.maximalIdeal (Q k S) ≤ QuotientTraceSubmodule k S

/-- The intrinsic quotient NG condition is exactly the frozen direct-model
condition.
@isnad1 id=iff.3h5v.s6.337701f4cb8e from=translated src=- shape=ff1e07ab vocab=3fdd9bb4
-/
theorem quotientNearlyGorenstein_iff_directNearlyGorenstein
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    QuotientNearlyGorenstein k S hS hdom hlive ↔
      DirectNearlyGorenstein k S hS hdom := by
  let E := finitePolynomialQuotientEquiv (k := k) S hS hdom
  unfold QuotientNearlyGorenstein DirectNearlyGorenstein
  letI := quotientIsLocalRing (k := k) S hS hdom hlive
  rw [quotientMaximalIdeal_eq_augmentationIdeal (k := k) S hS hdom hlive]
  constructor
  · intro hng r hr
    let q : Q k S := E.symm r
    have hqaug : q ∈ quotientAugmentationIdeal (k := k) S hS hdom := by
      change E q ∈ augmentationIdeal (k := k) S hS hdom
      simpa [q, E] using hr
    have hqt := hng hqaug
    have ht := (mem_quotientTrace_iff_equiv_mem_directTrace
      (k := k) S hS hdom q).1 hqt
    simpa [q, E] using ht
  · intro hng q hq
    have hEq : E q ∈ augmentationIdeal (k := k) S hS hdom := hq
    have hEt := hng hEq
    exact (mem_quotientTrace_iff_equiv_mem_directTrace
      (k := k) S hS hdom q).2 hEt

/-- Scope-explicit Run18 transport package.-/
structure FiniteQuotientArtinTransport
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) : Prop where
  localRing : IsLocalRing (Q k S)
  socleFinrank : Module.finrank k
    (QuotientSocle (k := k) S hS hdom hlive) = S.card
  typeEq : quotientType k S hS hdom hlive = S.card
  traceTransport : ∀ q : Q k S,
    q ∈ QuotientTraceSubmodule k S ↔
      finitePolynomialQuotientEquiv (k := k) S hS hdom q ∈ TraceSubmodule k S
  ngTransport : QuotientNearlyGorenstein k S hS hdom hlive ↔
    DirectNearlyGorenstein k S hS hdom

/--
@isnad1 id=finitequ.4h5v.s5.a96b66663431 from=translated src=- shape=fc3c8271 vocab=d1be373c
-/
theorem finiteQuotientArtinTransport
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    FiniteQuotientArtinTransport (k := k) S hS hdom hlive hanti :=
  ⟨quotientIsLocalRing (k := k) S hS hdom hlive,
    quotientSocle_finrank_eq_card (k := k) S hS hdom hlive hanti,
    quotientType_eq_rootCard (k := k) S hS hdom hlive hanti,
    mem_quotientTrace_iff_equiv_mem_directTrace (k := k) S hS hdom,
    quotientNearlyGorenstein_iff_directNearlyGorenstein
      (k := k) S hS hdom hlive⟩

end

end P23.Presentation
