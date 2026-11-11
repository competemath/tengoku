module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Setup
public import Tengoku.Seed.RingTheory.Ideal.Quotient.Nilpotent
public import Tengoku.Seed.RingTheory.Localization.Basic
public import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concrete Stickelberger setup (Layer 3, REF-18c2c4)

This file packages the arithmetic data needed to turn the abstract
`StickelbergerSetup` API into the concrete cyclotomic situation used by the
digit-sum Stickelberger congruence.

The bundle intentionally keeps the difficult arithmetic assertions as fields:
the prime `Q` above `ℓ`, the integral element `π = ζ_ℓ - 1`, and the residue
map from `𝓞 R'` to the finite field. Later Layer 3 tickets can strengthen this
data by proving the canonical identification of `Q` and constructing
Teichmüller lifts.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- Concrete arithmetic data for the Stickelberger congruence over a
cyclotomic field.

The finite field `k` is the residue-field model used in the Gauss-sum layer.
The number field `K` is the `p`-th cyclotomic field, and `R'` is a larger
cyclotomic field containing the `p`- and `ℓ`-power roots needed for the
residue and additive characters.-/
structure ConcreteStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] where
  /-- The residue characteristic is different from the Kummer exponent.-/
  hℓ_ne_p : ℓ ≠ p
  /-- Residue degree, with `#k = ℓ ^ f`.-/
  f : ℕ
  /-- The chosen finite field has cardinality `ℓ ^ f`.-/
  card_k : Fintype.card k = ℓ ^ f
  /-- A primitive `p`-th root of unity in the residue field.-/
  zeta_k : kˣ
  /-- Primitivity of `zeta_k`.-/
  hzeta_k : IsPrimitiveRoot zeta_k p
  /-- The cardinality compatibility needed for the residue character.-/
  hdiv : p ∣ Fintype.card k - 1
  /-- A primitive `p`-th root of unity in `R'`.-/
  zeta_p : R'ˣ
  /-- Primitivity of `zeta_p`.-/
  hzeta_p : IsPrimitiveRoot zeta_p p
  /-- An integral lift of `zeta_p` to `𝓞 R'`, chosen compatibly with the
  residue-field root `zeta_k`.-/
  zeta_p_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`.-/
  zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ)
  /-- A primitive `ℓ`-th root of unity in `R'`, used for the additive character.-/
  zeta_ell : R'
  /-- Primitivity of `zeta_ell`.-/
  hzeta_ell : IsPrimitiveRoot zeta_ell ℓ
  /-- An integral lift of `zeta_ell` to `𝓞 R'`.-/
  zeta_ell_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`.-/
  zeta_ell_int_spec : algebraMap (𝓞 R') R' zeta_ell_int = zeta_ell
  /-- The uniformizer candidate `π = ζ_ℓ - 1`.-/
  π : 𝓞 R'
  /-- Defining equation for `π` in the ring of integers.-/
  hπ : π = zeta_ell_int - 1
  /-- A prime ideal of `𝓞 R'` above `ℓ`.-/
  Q : Ideal (𝓞 R')
  /-- Primality of `Q`.-/
  hQ_prime : Q.IsPrime
  /-- The rational prime `ℓ` lies in `Q`.-/
  hQ : (ℓ : 𝓞 R') ∈ Q
  /-- A concrete residue map onto the finite-field model `k`.-/
  residueMap : 𝓞 R' →+* k
  /-- The residue map is onto the chosen finite field model.-/
  residueMap_surjective : Function.Surjective residueMap
  /-- The kernel of the residue map is `Q`.-/
  residueMap_ker : RingHom.ker residueMap = Q
  /-- Compatibility between the target primitive `p`-th root and the
  residue-field primitive root. This pins down the Teichmüller convention used
  by `residueCharInt`.-/
  zeta_p_int_residue : residueMap zeta_p_int = (zeta_k : k)
  /-- The primitive additive character on `k`.-/
  psi : AddChar k R'
  /-- Primitivity of the additive character.-/
  hpsi : psi.IsPrimitive
  /-- Exponent function expressing `psi` in powers of `ζ_ℓ`.-/
  psiExponent : k → ℕ
  /-- The additive character has the expected `ζ_ℓ`-power form.-/
  psi_eq_zeta_ell_pow : ∀ x : k, psi x = zeta_ell ^ psiExponent x

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- Accessor for the primality of the residue characteristic.
@isnad1 id=prime.0h1v.s3.b2377fda8d17 from=translated src=- shape=77e6bbc5 vocab=c1c9ca6d
-/
theorem ell_prime : Nat.Prime ℓ :=
  Fact.out

/-- Accessor for the primality of the Kummer exponent.
@isnad1 id=prime.0h1v.s3.b2377fda8d17 from=translated src=- shape=77e6bbc5 vocab=c1c9ca6d
-/
theorem p_prime : Nat.Prime p :=
  Fact.out

/-- The residue characteristic and Kummer exponent are distinct.
@isnad1 id=ne.0h6v.s7.0c798cc22d0b from=translated src=- shape=e09a9f41 vocab=7a68a8c7
-/
theorem ell_ne_p (S : ConcreteStickelbergerSetup ℓ p k K R') : ℓ ≠ p :=
  S.hℓ_ne_p

/-- The residue-field root is primitive of order `p`.
@isnad1 id=isprimit.0h6v.s7.7759c9fe8ffa from=translated src=- shape=7f1572b1 vocab=18bbb757
-/
theorem zeta_k_isPrimitiveRoot : IsPrimitiveRoot S.zeta_k p :=
  S.hzeta_k

/-- The target-field `p`-th root is primitive.
@isnad1 id=isprimit.0h6v.s7.6cf1fdef42b5 from=translated src=- shape=fb1907d5 vocab=85992a41
-/
theorem zeta_p_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p p :=
  S.hzeta_p

/-- The integral lift of `ζ_p` maps to the selected root in `R'`.
@isnad1 id=eq.0h6v.s8.a280b26db71c from=translated src=- shape=a5b5b1d6 vocab=de51558c
-/
@[simp]
theorem algebraMap_zeta_p_int :
    algebraMap (𝓞 R') R' S.zeta_p_int = (S.zeta_p : R'ˣ) :=
  S.zeta_p_int_spec

/-- The integral lift of `ζ_p` is still primitive.
@isnad1 id=isprimit.0h6v.s7.0914c57a9bb7 from=translated src=- shape=fb1907d5 vocab=00baa2ba
-/
theorem zeta_p_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p_int p := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.algebraMap_zeta_p_int] using (IsPrimitiveRoot.coe_units_iff.mpr S.hzeta_p)

/-- The target-field `ℓ`-th root is primitive.
@isnad1 id=isprimit.0h6v.s7.6463612ba832 from=translated src=- shape=10613e62 vocab=9d4c688b
-/
theorem zeta_ell_isPrimitiveRoot : IsPrimitiveRoot S.zeta_ell ℓ :=
  S.hzeta_ell

/-- The integral lift of `ζ_ℓ` is primitive in `𝓞 R'`.
@isnad1 id=isprimit.0h6v.s7.b3c29c207a81 from=translated src=- shape=fea5df44 vocab=1095bf84
-/
theorem zeta_ell_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_ell_int ℓ := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.zeta_ell_int_spec] using S.hzeta_ell

/-- The cardinality divisibility required to define the residue character.
@isnad1 id=dvd.0h6v.s7.9a7e2d9b66b4 from=translated src=- shape=3a92fa4d vocab=cf4a42d3
-/
theorem p_dvd_card_sub_one (S : ConcreteStickelbergerSetup ℓ p k K R') :
    p ∣ Fintype.card k - 1 :=
  S.hdiv

/-- The prime ideal `Q` is available as an instance when working from the
bundle.
@isnad1 id=isprime.0h6v.s7.f0872caf09a0 from=translated src=- shape=767ab5b7 vocab=62c8a10e
-/
protected instance Q_isPrime : S.Q.IsPrime :=
  S.hQ_prime

/-- The rational prime `ℓ` lies in the selected prime ideal.
@isnad1 id=mem.0h6v.s8.5a80e3656203 from=translated src=- shape=3702baf4 vocab=f7250977
-/
theorem ell_mem_Q : (ℓ : 𝓞 R') ∈ S.Q :=
  S.hQ

/-- Powers of the residue characteristic land in the corresponding powers of
the selected prime. This is the elementary nilpotence input used when passing
to `Q`-adic quotients.
@isnad1 id=mem.0h7v.s8.3c590d918c0c from=translated src=- shape=20af3323 vocab=41bae4e9
-/
theorem natCast_ell_pow_mem_Q_pow (N : ℕ) :
    (ℓ : 𝓞 R') ^ N ∈ S.Q ^ N :=
  Ideal.pow_mem_pow S.hQ N

/-- In the quotient modulo `Q^(N+1)`, the residue characteristic is nilpotent.
@isnad1 id=eq.0h7v.s11.5c0c65c54128 from=translated src=- shape=1d9da2c2 vocab=db31b9ee
-/
theorem quotient_natCast_ell_pow_succ_eq_zero (N : ℕ) :
    (Ideal.Quotient.mk (S.Q ^ (N + 1)) (ℓ : 𝓞 R')) ^ (N + 1) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact S.natCast_ell_pow_mem_Q_pow (N + 1)

/-- Nilpotence form of `quotient_natCast_ell_pow_succ_eq_zero`.
@isnad1 id=isnilpot.0h7v.s11.5930d159cd6f from=translated src=- shape=d07ce46b vocab=b139e703
-/
theorem quotient_natCast_ell_isNilpotent (N : ℕ) :
    IsNilpotent (Ideal.Quotient.mk (S.Q ^ (N + 1)) (ℓ : 𝓞 R')) :=
  ⟨N + 1, S.quotient_natCast_ell_pow_succ_eq_zero N⟩

/-- The residue map has kernel `Q`.
@isnad1 id=eq.0h6v.s8.401ec947bf70 from=translated src=- shape=f62eddc5 vocab=4b185270
-/
theorem residueMap_ker_eq : RingHom.ker S.residueMap = S.Q :=
  S.residueMap_ker

/-- Membership in the selected prime is equivalent to vanishing under the
residue map.
@isnad1 id=iff.0h7v.s8.171d67b45df0 from=translated src=- shape=e54813ab vocab=cda47d28
-/
theorem mem_Q_iff_residueMap_eq_zero (x : 𝓞 R') :
    x ∈ S.Q ↔ S.residueMap x = 0 := by
  rw [← S.residueMap_ker_eq, RingHom.mem_ker]

/-- The integral lift of `ζ_p` reduces to the selected finite-field root.
@isnad1 id=eq.0h6v.s8.320e0833c585 from=translated src=- shape=c837a689 vocab=c9c2dda9
-/
@[simp]
theorem residueMap_zeta_p_int : S.residueMap S.zeta_p_int = (S.zeta_k : k) :=
  S.zeta_p_int_residue

/-- The residue map is surjective.
@isnad1 id=surjecti.0h6v.s8.887a96e08879 from=translated src=- shape=a51cb9de vocab=031472d1
-/
theorem residueMap_surjective' : Function.Surjective S.residueMap :=
  S.residueMap_surjective

/-- The residue map identifies the quotient `𝓞 R' / Q` with the chosen
finite-field model `k`.-/
def residueQuotientEquiv : 𝓞 R' ⧸ S.Q ≃+* k :=
  (Ideal.quotientEquiv S.Q (RingHom.ker S.residueMap) (RingEquiv.refl (𝓞 R')) (by
    simpa using S.residueMap_ker)).trans
    (RingHom.quotientKerEquivOfSurjective S.residueMap_surjective)

/--
@isnad1 id=eq.0h7v.s10.63bedc259493 from=translated src=- shape=d4f74a94 vocab=5d4131e0
-/
@[simp]
theorem residueQuotientEquiv_mk (x : 𝓞 R') :
    S.residueQuotientEquiv (Ideal.Quotient.mk S.Q x) = S.residueMap x := by
  simp [residueQuotientEquiv]

/-- Elements outside `Q` become units modulo every positive power of `Q`.
@isnad1 id=isunit.1h8v.s11.31f3cf22fe8a from=translated src=- shape=4ca4b649 vocab=f243372a
-/
theorem quotient_mk_isUnit_of_not_mem_Q (N : ℕ) {s : 𝓞 R'} (hs : s ∉ S.Q) :
    IsUnit (Ideal.Quotient.mk (S.Q ^ (N + 1)) s) := by
  haveI : S.Q.IsMaximal := by
    rw [← S.residueMap_ker_eq]
    exact RingHom.ker_isMaximal_of_surjective S.residueMap S.residueMap_surjective
  exact (Ideal.Quotient.isUnit_mk_pow_iff_notMem (I := S.Q)
    (n := N + 1) (Nat.succ_ne_zero N)).2 hs

/-- The canonical unit in `𝓞 R' / Q^(N+1)` attached to an element outside
`Q`.-/
def quotientUnitOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) : (𝓞 R' ⧸ S.Q ^ (N + 1))ˣ :=
  (S.quotient_mk_isUnit_of_not_mem_Q N hs).unit

/--
@isnad1 id=eq.1h8v.s11.ee14ddbc6fc0 from=translated src=- shape=60d2e1fe vocab=b0696a5c
-/
@[simp]
theorem quotientUnitOfNotMemQ_coe (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) :
    (S.quotientUnitOfNotMemQ N s hs : 𝓞 R' ⧸ S.Q ^ (N + 1)) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) s :=
  (S.quotient_mk_isUnit_of_not_mem_Q N hs).unit_spec

/-- The chosen inverse of an element outside `Q` in the quotient by
`Q^(N+1)`.-/
def quotientInvOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) : 𝓞 R' ⧸ S.Q ^ (N + 1) :=
  ((S.quotientUnitOfNotMemQ N s hs)⁻¹ : (𝓞 R' ⧸ S.Q ^ (N + 1))ˣ)

/--
@isnad1 id=eq.1h8v.s11.c4e020601143 from=translated src=- shape=1b734295 vocab=25ac13e2
-/
@[simp]
theorem quotient_mk_mul_quotientInvOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) s *
        S.quotientInvOfNotMemQ N s hs = 1 := by
  simp [quotientInvOfNotMemQ]

/--
@isnad1 id=eq.1h8v.s11.5d128cb06a04 from=translated src=- shape=5210a5f4 vocab=25ac13e2
-/
@[simp]
theorem quotientInvOfNotMemQ_mul_quotient_mk
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) :
    S.quotientInvOfNotMemQ N s hs *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) s = 1 := by
  simp [quotientInvOfNotMemQ]

/--
@isnad1 id=eq.1h9v.s12.b1c2324251f4 from=translated src=- shape=a71bdf0f vocab=25ac13e2
-/
@[simp]
theorem quotient_mk_mul_denominator_inv_of_not_mem_Q
    (N : ℕ) (x : 𝓞 R') {s : 𝓞 R'} (hs : s ∉ S.Q) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (x * s) *
        S.quotientInvOfNotMemQ N s hs =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  rw [map_mul, mul_assoc, S.quotient_mk_mul_quotientInvOfNotMemQ N s hs, mul_one]

/--
@isnad1 id=eq.1h9v.s12.d447bcfc673a from=translated src=- shape=a5e128f8 vocab=25ac13e2
-/
@[simp]
theorem denominator_inv_mul_quotient_mk_mul_of_not_mem_Q
    (N : ℕ) (x : 𝓞 R') {s : 𝓞 R'} (hs : s ∉ S.Q) :
    S.quotientInvOfNotMemQ N s hs *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (s * x) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  rw [map_mul, ← mul_assoc, S.quotientInvOfNotMemQ_mul_quotient_mk N s hs,
    one_mul]

/-- The quotient map sends every local denominator away from `Q` to a unit.
@isnad1 id=isunit.0h8v.s11.f73a7715be6c from=translated src=- shape=be104d18 vocab=8386ba96
-/
theorem quotient_mk_isUnit_primeCompl
    (N : ℕ) (s : S.Q.primeCompl) :
    IsUnit (Ideal.Quotient.mk (S.Q ^ (N + 1)) (s : 𝓞 R')) :=
  S.quotient_mk_isUnit_of_not_mem_Q N s.property

/-- The canonical map from the localization of `𝓞 R'` away from `Q` to the
finite quotient `𝓞 R' / Q^(N+1)`. This keeps local finite-log fractions inside
the same global quotient used by the Dwork endpoint.-/
def quotientLocalizationAwayQMap (N : ℕ) :
    Localization S.Q.primeCompl →+* (𝓞 R' ⧸ S.Q ^ (N + 1)) :=
  IsLocalization.lift
    (M := S.Q.primeCompl)
    (S := Localization S.Q.primeCompl)
    (P := 𝓞 R' ⧸ S.Q ^ (N + 1))
    (g := Ideal.Quotient.mk (S.Q ^ (N + 1)))
    (S.quotient_mk_isUnit_primeCompl N)

/--
@isnad1 id=eq.0h8v.s12.606c40d028d3 from=translated src=- shape=b6450e11 vocab=261b9f05
-/
@[simp]
theorem quotientLocalizationAwayQMap_algebraMap
    (N : ℕ) (x : 𝓞 R') :
    S.quotientLocalizationAwayQMap N
        (algebraMap (𝓞 R') (Localization S.Q.primeCompl) x) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  simp [quotientLocalizationAwayQMap,
    (IsLocalization.lift_eq
      (M := S.Q.primeCompl)
      (S := Localization S.Q.primeCompl)
      (P := 𝓞 R' ⧸ S.Q ^ (N + 1))
      (g := Ideal.Quotient.mk (S.Q ^ (N + 1)))
      (S.quotient_mk_isUnit_primeCompl N)
      x)]

/-- Evaluate a local fraction with denominator away from `Q` in the finite
quotient.  The denominator is given as an element of the prime complement so
that algebraic identities have canonical denominator proofs.-/
def quotientFractionEvalPrimeCompl
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) :
    𝓞 R' ⧸ S.Q ^ (N + 1) :=
  S.quotientLocalizationAwayQMap N
    (IsLocalization.mk' (Localization S.Q.primeCompl) x s)

/-- Evaluate a local fraction with an explicit proof that the denominator is
outside `Q`.-/
def quotientFractionEval
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ S.Q) :
    𝓞 R' ⧸ S.Q ^ (N + 1) :=
  S.quotientFractionEvalPrimeCompl N x ⟨s, hs⟩

/--
@isnad1 id=eq.0h8v.s11.d6e36cf42ffc from=translated src=- shape=8a8e4fa9 vocab=e69fa630
-/
@[simp]
theorem quotientFractionEvalPrimeCompl_one
    (N : ℕ) (x : 𝓞 R') :
    S.quotientFractionEvalPrimeCompl N x 1 =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  simpa [quotientFractionEvalPrimeCompl] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_one
        (S := Localization S.Q.primeCompl)
        x)

/--
@isnad1 id=eq.0h9v.s12.649506625d7c from=translated src=- shape=deba497c vocab=886a8662
-/
theorem quotientFractionEvalPrimeCompl_den_mul
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (s : 𝓞 R') *
        S.quotientFractionEvalPrimeCompl N x s =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  have h :
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x =
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (s : 𝓞 R') *
          S.quotientFractionEvalPrimeCompl N x s :=
    (IsLocalization.lift_mk'_spec
        (M := S.Q.primeCompl)
        (S := Localization S.Q.primeCompl)
        (P := 𝓞 R' ⧸ S.Q ^ (N + 1))
        (g := Ideal.Quotient.mk (S.Q ^ (N + 1)))
        (hg := S.quotient_mk_isUnit_primeCompl N)
        x
        (S.quotientFractionEvalPrimeCompl N x s)
        s).1 (by
          simp [quotientFractionEvalPrimeCompl, quotientLocalizationAwayQMap])
  exact h.symm

/--
@isnad1 id=eq.1h9v.s12.d91abed298a5 from=translated src=- shape=352b27ae vocab=70882c83
-/
theorem quotientFractionEval_den_mul
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ S.Q) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) s *
        S.quotientFractionEval N x s hs =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  simpa [quotientFractionEval] using
    S.quotientFractionEvalPrimeCompl_den_mul N x ⟨s, hs⟩

/--
@isnad1 id=eq.1h9v.s11.1441c2442dd0 from=translated src=- shape=8e521fb1 vocab=e10bef69
-/
theorem quotientFractionEval_eq_mk_mul_inv
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ S.Q) :
    S.quotientFractionEval N x s hs =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x *
        S.quotientInvOfNotMemQ N s hs := by
  apply (S.quotient_mk_isUnit_of_not_mem_Q N hs).mul_left_inj.mp
  rw [mul_comm (S.quotientFractionEval N x s hs),
    S.quotientFractionEval_den_mul N x s hs, mul_assoc,
    S.quotientInvOfNotMemQ_mul_quotient_mk N s hs, mul_one]

/--
@isnad1 id=eq.0h11v.s11.b885203ee6b5 from=translated src=- shape=c31d2f99 vocab=4e97d128
-/
theorem quotientFractionEvalPrimeCompl_add
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N
        (x₁ * (s₂ : 𝓞 R') + x₂ * (s₁ : 𝓞 R')) (s₁ * s₂) =
      S.quotientFractionEvalPrimeCompl N x₁ s₁ +
        S.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_add] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_add
        (S := Localization S.Q.primeCompl)
        x₁ x₂ s₁ s₂)

/--
@isnad1 id=eq.0h11v.s11.ec957b4c7c16 from=translated src=- shape=c37edc61 vocab=8fbe353a
-/
theorem quotientFractionEvalPrimeCompl_mul
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N (x₁ * x₂) (s₁ * s₂) =
      S.quotientFractionEvalPrimeCompl N x₁ s₁ *
        S.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_mul] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_mul
        (S := Localization S.Q.primeCompl)
        x₁ x₂ s₁ s₂)

/--
@isnad1 id=eq.0h9v.s10.6c0733491b6c from=translated src=- shape=bd2c2a22 vocab=c18f3783
-/
theorem quotientFractionEvalPrimeCompl_neg
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N (-x) s =
      -S.quotientFractionEvalPrimeCompl N x s := by
  simpa [quotientFractionEvalPrimeCompl, map_neg] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_neg
        (S := Localization S.Q.primeCompl)
        x s)

/--
@isnad1 id=eq.0h11v.s11.c95929ea4d7e from=translated src=- shape=d51e7455 vocab=b430b4fe
-/
theorem quotientFractionEvalPrimeCompl_sub
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N
        (x₁ * (s₂ : 𝓞 R') - x₂ * (s₁ : 𝓞 R')) (s₁ * s₂) =
      S.quotientFractionEvalPrimeCompl N x₁ s₁ -
        S.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_sub] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_sub
        (S := Localization S.Q.primeCompl)
        x₁ x₂ s₁ s₂)

/--
@isnad1 id=eq.0h10v.s11.c1d1fe56330c from=translated src=- shape=8e4f3515 vocab=c33e7a31
-/
theorem quotientFractionEvalPrimeCompl_pow
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) (m : ℕ) :
    S.quotientFractionEvalPrimeCompl N (x ^ m) (s ^ m) =
      S.quotientFractionEvalPrimeCompl N x s ^ m := by
  simpa [quotientFractionEvalPrimeCompl, map_pow] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_pow
        (S := Localization S.Q.primeCompl)
        x s m)

/--
@isnad1 id=eq.1h9v.s10.c45f62cabd2a from=translated src=- shape=2a7e9112 vocab=c33e7a31
-/
theorem quotientFractionEvalPrimeCompl_eq_zero_of_mem
    (N : ℕ) {x : 𝓞 R'} (s : S.Q.primeCompl)
    (hx : x ∈ S.Q ^ (N + 1)) :
    S.quotientFractionEvalPrimeCompl N x s = 0 := by
  apply (S.quotient_mk_isUnit_primeCompl N s).mul_left_inj.mp
  rw [zero_mul, mul_comm (S.quotientFractionEvalPrimeCompl N x s),
    S.quotientFractionEvalPrimeCompl_den_mul N x s]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

/--
@isnad1 id=eq.2h9v.s10.896f2d3c2773 from=translated src=- shape=6f77efc3 vocab=247b2cf9
-/
theorem quotientFractionEval_eq_zero_of_mem
    (N : ℕ) {x s : 𝓞 R'} (hs : s ∉ S.Q)
    (hx : x ∈ S.Q ^ (N + 1)) :
    S.quotientFractionEval N x s hs = 0 := by
  simpa [quotientFractionEval] using
    S.quotientFractionEvalPrimeCompl_eq_zero_of_mem N ⟨s, hs⟩ hx

/--
@isnad1 id=eq.1h10v.s9.1a7565e58393 from=translated src=- shape=65ca1d1a vocab=b413e524
-/
theorem quotientFractionEvalPrimeCompl_eq_of_sub_mem
    (N : ℕ) {x y : 𝓞 R'} (s : S.Q.primeCompl)
    (hxy : x - y ∈ S.Q ^ (N + 1)) :
    S.quotientFractionEvalPrimeCompl N x s =
      S.quotientFractionEvalPrimeCompl N y s := by
  apply (S.quotient_mk_isUnit_primeCompl N s).mul_left_inj.mp
  rw [mul_comm (S.quotientFractionEvalPrimeCompl N x s),
    S.quotientFractionEvalPrimeCompl_den_mul N x s,
    mul_comm (S.quotientFractionEvalPrimeCompl N y s),
    S.quotientFractionEvalPrimeCompl_den_mul N y s]
  exact Ideal.Quotient.eq.mpr hxy

/--
@isnad1 id=eq.2h10v.s9.89b626eadb3a from=translated src=- shape=6fff1938 vocab=acbcb62a
-/
theorem quotientFractionEval_eq_of_sub_mem
    (N : ℕ) {x y s : 𝓞 R'} (hs : s ∉ S.Q)
    (hxy : x - y ∈ S.Q ^ (N + 1)) :
    S.quotientFractionEval N x s hs =
      S.quotientFractionEval N y s hs := by
  simpa [quotientFractionEval] using
    S.quotientFractionEvalPrimeCompl_eq_of_sub_mem N ⟨s, hs⟩ hxy

/-- Unit-group form of the residue-field identification.-/
def residueUnitEquiv : (𝓞 R' ⧸ S.Q)ˣ ≃* kˣ :=
  Units.mapEquiv S.residueQuotientEquiv.toMulEquiv

/--
@isnad1 id=eq.0h7v.s11.f75d96e15324 from=translated src=- shape=1a1e6e1a vocab=febf6d5b
-/
@[simp]
theorem residueUnitEquiv_val (u : (𝓞 R' ⧸ S.Q)ˣ) :
    ((S.residueUnitEquiv u : kˣ) : k) =
      S.residueQuotientEquiv (u : 𝓞 R' ⧸ S.Q) := by
  simp [residueUnitEquiv]

/-- The chosen finite field has cardinality `ℓ ^ f`.
@isnad1 id=eq.0h6v.s7.ae1c1408c933 from=translated src=- shape=47f3bbd6 vocab=630e3847
-/
theorem card_k_eq : Fintype.card k = ℓ ^ S.f :=
  S.card_k

/-- The integral lift of `ζ_ℓ` maps to the selected root in `R'`.
@isnad1 id=eq.0h6v.s8.cae45be4a096 from=translated src=- shape=174fc9c9 vocab=cd6a87b1
-/
theorem algebraMap_zeta_ell_int : algebraMap (𝓞 R') R' S.zeta_ell_int = S.zeta_ell :=
  S.zeta_ell_int_spec

/-- The defining equation for `π` in `𝓞 R'`.
@isnad1 id=eq.0h6v.s8.91bcd60518da from=translated src=- shape=a0af1a9b vocab=53d0a1ee
-/
theorem π_def : S.π = S.zeta_ell_int - 1 :=
  S.hπ

/-- The selected prime above `ℓ` contains `π = ζ_ℓ - 1`. This is the
ramification containment available in the mixed cyclotomic field
`ℚ(ζ_p, ζ_ℓ)`.
@isnad1 id=mem.0h6v.s8.9f9adcca525b from=translated src=- shape=1a3027a4 vocab=2028dc52
-/
theorem π_mem_Q : S.π ∈ S.Q := by
  rw [S.hπ]
  exact zeta_sub_one_mem_of_natCast_mem S.zeta_ell_int_isPrimitiveRoot S.hQ

/-- The additive character is expressed in powers of the chosen primitive
`ℓ`-th root.
@isnad1 id=eq.0h7v.s8.4c452727aa39 from=translated src=- shape=9eb33cd1 vocab=6f941034
-/
theorem psi_pow_form (x : k) : S.psi x = S.zeta_ell ^ S.psiExponent x :=
  S.psi_eq_zeta_ell_pow x

/-- Forget the concrete arithmetic data and recover the abstract
`StickelbergerSetup` used by the algebraic Gauss-sum API.-/
def abstractSetup : StickelbergerSetup p k R' where
  zeta_q := S.zeta_k
  hzeta_q := S.hzeta_k
  hdiv := S.hdiv
  zeta_R := S.zeta_p
  hzeta_R := S.hzeta_p
  psi_q := S.psi
  hpsi := S.hpsi

/-- The residue character specialised to the concrete bundle.-/
def residueChar : MulChar k R' :=
  S.abstractSetup.residueChar

/-- The order-`p` Teichmüller representative on the residue ring
`𝓞 R' / Q`, transported through the concrete residue-field model `k`.-/
def teichmuller : (𝓞 R' ⧸ S.Q)ˣ →* R'ˣ :=
  S.residueChar.toUnitHom.comp S.residueUnitEquiv.toMonoidHom

/--
@isnad1 id=eq.0h7v.s11.2d19d0dbca84 from=translated src=- shape=5b13026d vocab=419bb617
-/
@[simp]
theorem teichmuller_apply_coe (u : (𝓞 R' ⧸ S.Q)ˣ) :
    ((S.teichmuller u : R'ˣ) : R') =
      S.residueChar (S.residueQuotientEquiv (u : 𝓞 R' ⧸ S.Q)) := by
  simp [teichmuller]

/--
@isnad1 id=eq.0h7v.s11.8b0b28d69f7d from=translated src=- shape=55fddaca vocab=a2f4e611
-/
@[simp]
theorem teichmuller_apply_mk_unit (u : (𝓞 R')ˣ) :
    ((S.teichmuller (Units.map (Ideal.Quotient.mk S.Q) u) : R'ˣ) : R') =
      S.residueChar (S.residueMap (u : 𝓞 R')) := by
  simp [teichmuller_apply_coe]

/-- Concrete power form of the Teichmüller representative.
@isnad1 id=eq.0h7v.s11.9a891ad5fe63 from=translated src=- shape=c20008dc vocab=e728c121
-/
theorem teichmuller_apply_eq_zeta_p_pow (u : (𝓞 R' ⧸ S.Q)ˣ) :
    ((S.teichmuller u : R'ˣ) : R') =
      ((S.zeta_p : R'ˣ) : R') ^
        (Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
          S.zeta_k S.hzeta_k S.hdiv (S.residueUnitEquiv u)).val := by
  rw [teichmuller_apply_coe, ← residueUnitEquiv_val, residueChar,
    StickelbergerSetup.residueChar, residueMulChar_apply_unit]
  simp [abstractSetup]

/-- The transported Teichmüller representative has order dividing `p`.
@isnad1 id=eq.0h7v.s10.aaff2aa78b09 from=translated src=- shape=68e1b764 vocab=961da301
-/
theorem teichmuller_pow_eq_one (u : (𝓞 R' ⧸ S.Q)ˣ) :
    S.teichmuller u ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, teichmuller_apply_eq_zeta_p_pow, ← pow_mul, mul_comm, pow_mul]
  have hpow : ((S.zeta_p : R'ˣ) : R') ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, S.hzeta_p.pow_eq_one, Units.val_one]
  rw [hpow, one_pow, Units.val_one]

/-- The residue Gauss sum specialised to the concrete bundle.-/
def gaussSum : R' :=
  S.abstractSetup.gaussSum

/-- Accessor: `χ_q^p = 1` for the concrete residue character.
@isnad1 id=eq.0h6v.s8.5c2f92d7ce5a from=translated src=- shape=ffd7a073 vocab=99138e30
-/
theorem residueChar_pow_eq_one : S.residueChar ^ p = 1 :=
  S.abstractSetup.residueChar_pow_eq_one

/-- Accessor: the concrete residue character is non-trivial.
@isnad1 id=ne.0h6v.s8.3abed2830367 from=translated src=- shape=95c10757 vocab=a30fa9e1
-/
theorem residueChar_ne_one : S.residueChar ≠ 1 :=
  S.abstractSetup.residueChar_ne_one

/-- Accessor: the concrete Gauss sum satisfies the abstract norm relation.
@isnad1 id=eq.0h6v.s8.8c640a524396 from=translated src=- shape=53f134e9 vocab=0f68dd67
-/
theorem gaussSum_mul_inv_eq_card :
    S.gaussSum * _root_.gaussSum S.residueChar⁻¹ S.psi⁻¹ = Fintype.card k :=
  S.abstractSetup.gaussSum_mul_inv_eq_card

/-- Accessor: concrete q-adic containment from a congruence of `psi` modulo
an ideal.
@isnad1 id=mem.1h7v.s8.73896c07b36d from=translated src=- shape=f76037c8 vocab=fffb56c8
-/
theorem gaussSum_mem_ideal {I : Ideal R'} (h : ∀ x : k, S.psi x - 1 ∈ I) :
    S.gaussSum ∈ I :=
  S.abstractSetup.gaussSum_mem_ideal h

/-- In the pure `ℓ`-cyclotomic field, every prime above `ℓ` is the prime
generated by `ζ_ℓ - 1`. This is the exact mathlib ramification theorem in the
form needed by the mixed setup's local `ℓ`-cyclotomic part.
@isnad1 id=eq.1h4v.s7.a8213173fadd from=translated src=- shape=d69f8c71 vocab=64cbc599
-/
theorem prime_over_ell_eq_span_zeta_sub_one
    {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {ℓ} ℚ L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ ℓ)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(ℓ : ℤ)})] :
    P = Ideal.span {hζ.toInteger - 1} := by
  haveI : IsCyclotomicExtension {ℓ ^ (0 + 1)} ℚ L := by
    simpa only [zero_add, pow_one] using (inferInstance : IsCyclotomicExtension {ℓ} ℚ L)
  have hζ' : IsPrimitiveRoot ζ (ℓ ^ (0 + 1)) := by
    simpa only [zero_add, pow_one] using hζ
  simpa only [zero_add, pow_one] using
    (IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver
      (p := ℓ) (k := 0) (K := L) hζ' P)

end ConcreteStickelbergerSetup

/-- Conductor-flexible concrete arithmetic data for the Stickelberger
congruence.

This is the same explicit arithmetic payload as `ConcreteStickelbergerSetup`,
but without the exact pair-cyclotomic typeclass
`[IsCyclotomicExtension {p, ℓ} ℚ R']`.  It is intended for enlarged
cyclotomic fields whose conductor contains the required roots while not being
definitionally the pair conductor.-/
structure ConductorFlexibleConcreteStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R'] where
  /-- The residue characteristic is different from the Kummer exponent.-/
  hℓ_ne_p : ℓ ≠ p
  /-- Residue degree, with `#k = ℓ ^ f`.-/
  f : ℕ
  /-- The chosen finite field has cardinality `ℓ ^ f`.-/
  card_k : Fintype.card k = ℓ ^ f
  /-- A primitive `p`-th root of unity in the residue field.-/
  zeta_k : kˣ
  /-- Primitivity of `zeta_k`.-/
  hzeta_k : IsPrimitiveRoot zeta_k p
  /-- The cardinality compatibility needed for the residue character.-/
  hdiv : p ∣ Fintype.card k - 1
  /-- A primitive `p`-th root of unity in `R'`.-/
  zeta_p : R'ˣ
  /-- Primitivity of `zeta_p`.-/
  hzeta_p : IsPrimitiveRoot zeta_p p
  /-- An integral lift of `zeta_p` to `𝓞 R'`.-/
  zeta_p_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`.-/
  zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ)
  /-- A primitive `ℓ`-th root of unity in `R'`, used for the additive character.-/
  zeta_ell : R'
  /-- Primitivity of `zeta_ell`.-/
  hzeta_ell : IsPrimitiveRoot zeta_ell ℓ
  /-- An integral lift of `zeta_ell` to `𝓞 R'`.-/
  zeta_ell_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`.-/
  zeta_ell_int_spec : algebraMap (𝓞 R') R' zeta_ell_int = zeta_ell
  /-- The uniformizer candidate `π = ζ_ℓ - 1`.-/
  π : 𝓞 R'
  /-- Defining equation for `π` in the ring of integers.-/
  hπ : π = zeta_ell_int - 1
  /-- A prime ideal of `𝓞 R'` above `ℓ`.-/
  Q : Ideal (𝓞 R')
  /-- Primality of `Q`.-/
  hQ_prime : Q.IsPrime
  /-- The rational prime `ℓ` lies in `Q`.-/
  hQ : (ℓ : 𝓞 R') ∈ Q
  /-- A concrete residue map onto the finite-field model `k`.-/
  residueMap : 𝓞 R' →+* k
  /-- The residue map is onto the chosen finite field model.-/
  residueMap_surjective : Function.Surjective residueMap
  /-- The kernel of the residue map is `Q`.-/
  residueMap_ker : RingHom.ker residueMap = Q
  /-- Compatibility between the target primitive `p`-th root and the
  residue-field primitive root.-/
  zeta_p_int_residue : residueMap zeta_p_int = (zeta_k : k)
  /-- The primitive additive character on `k`.-/
  psi : AddChar k R'
  /-- Primitivity of the additive character.-/
  hpsi : psi.IsPrimitive
  /-- Exponent function expressing `psi` in powers of `ζ_ℓ`.-/
  psiExponent : k → ℕ
  /-- The additive character has the expected `ζ_ℓ`-power form.-/
  psi_eq_zeta_ell_pow : ∀ x : k, psi x = zeta_ell ^ psiExponent x

namespace ConductorFlexibleConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')

/-- The selected over-prime is prime.
@isnad1 id=isprime.0h6v.s7.a2b8364f512e from=translated src=- shape=19ce28f5 vocab=d489bd88
-/
protected instance Q_isPrime : S.Q.IsPrime :=
  S.hQ_prime

/-- The residue map has kernel `Q`.
@isnad1 id=eq.0h6v.s8.8c029999c35f from=translated src=- shape=877be30c vocab=31e52224
-/
theorem residueMap_ker_eq : RingHom.ker S.residueMap = S.Q :=
  S.residueMap_ker

/-- Membership in the selected prime is equivalent to vanishing under the
residue map.
@isnad1 id=iff.0h7v.s8.ca0f23b62241 from=translated src=- shape=7af13356 vocab=5498283e
-/
theorem mem_Q_iff_residueMap_eq_zero (x : 𝓞 R') :
    x ∈ S.Q ↔ S.residueMap x = 0 := by
  rw [← S.residueMap_ker_eq, RingHom.mem_ker]

/-- The residue map identifies the quotient `𝓞 R' / Q` with the chosen
finite-field model `k`.-/
def residueQuotientEquiv : 𝓞 R' ⧸ S.Q ≃+* k :=
  (Ideal.quotientEquiv S.Q (RingHom.ker S.residueMap) (RingEquiv.refl (𝓞 R')) (by
    simpa using S.residueMap_ker)).trans
    (RingHom.quotientKerEquivOfSurjective S.residueMap_surjective)

/--
@isnad1 id=eq.0h7v.s10.197c4f6f3def from=translated src=- shape=dea97ce5 vocab=6cb3cd79
-/
@[simp]
theorem residueQuotientEquiv_mk (x : 𝓞 R') :
    S.residueQuotientEquiv (Ideal.Quotient.mk S.Q x) = S.residueMap x := by
  simp [residueQuotientEquiv]

/-- Unit-group form of the residue-field identification.-/
def residueUnitEquiv : (𝓞 R' ⧸ S.Q)ˣ ≃* kˣ :=
  Units.mapEquiv S.residueQuotientEquiv.toMulEquiv

/-- Forget the concrete arithmetic data and recover the abstract
`StickelbergerSetup` used by the algebraic Gauss-sum API.-/
def abstractSetup : StickelbergerSetup p k R' where
  zeta_q := S.zeta_k
  hzeta_q := S.hzeta_k
  hdiv := S.hdiv
  zeta_R := S.zeta_p
  hzeta_R := S.hzeta_p
  psi_q := S.psi
  hpsi := S.hpsi

/-- The residue character specialised to the conductor-flexible bundle.-/
def residueChar : MulChar k R' :=
  S.abstractSetup.residueChar

/-- The integral lift of `ζ_p` is primitive in `𝓞 R'`.
@isnad1 id=isprimit.0h6v.s7.5b0eb574dfa0 from=translated src=- shape=cdb12f30 vocab=99b0ae94
-/
theorem zeta_p_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p_int p := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.zeta_p_int_spec] using (IsPrimitiveRoot.coe_units_iff.mpr S.hzeta_p)

/-- Unit form of the integral `p`-th root.-/
def zeta_p_int_unit : (𝓞 R')ˣ :=
  (S.zeta_p_int_isPrimitiveRoot.isUnit (Fact.out : Nat.Prime p).ne_zero).unit

/--
@isnad1 id=eq.0h6v.s7.dccf6f12c3bf from=translated src=- shape=2e78799e vocab=b30a667f
-/
@[simp]
theorem zeta_p_int_unit_coe : (S.zeta_p_int_unit : 𝓞 R') = S.zeta_p_int := by
  simp [zeta_p_int_unit]

/-- The unit lift of `ζ_p` reduces to the selected finite-field root.
@isnad1 id=eq.0h6v.s8.968fac5caa9f from=translated src=- shape=7a0516d2 vocab=d11a5e2f
-/
@[simp]
theorem residueMap_zeta_p_int_unit :
    S.residueMap (S.zeta_p_int_unit : 𝓞 R') = (S.zeta_k : k) := by
  rw [S.zeta_p_int_unit_coe]
  exact S.zeta_p_int_residue

/-- The unit lift of `ζ_p` remains primitive.
@isnad1 id=isprimit.0h6v.s7.0224144d7fb4 from=translated src=- shape=0fe6bd2e vocab=b42503c1
-/
theorem zeta_p_int_unit_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p_int_unit p := by
  simpa [zeta_p_int_unit] using
    S.zeta_p_int_isPrimitiveRoot.isUnit_unit (Fact.out : Nat.Prime p).ne_zero

/-- The residue character with values in the ring of integers.-/
def residueCharInt : MulChar k (𝓞 R') :=
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  residueMulChar S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot

/-- The integral lift of `ζ_ℓ` maps to the selected root in `R'`.
@isnad1 id=eq.0h6v.s8.4d0a71d45aaf from=translated src=- shape=c4c712a8 vocab=78fe3573
-/
theorem algebraMap_zeta_ell_int : algebraMap (𝓞 R') R' S.zeta_ell_int = S.zeta_ell :=
  S.zeta_ell_int_spec

/-- The defining equation for `π` in `𝓞 R'`.
@isnad1 id=eq.0h6v.s7.4137b40a4b81 from=translated src=- shape=64083d35 vocab=84b4d777
-/
theorem π_def : S.π = S.zeta_ell_int - 1 :=
  S.hπ

/-- The integral lift of `ζ_ℓ` is primitive in `𝓞 R'`.
@isnad1 id=isprimit.0h6v.s7.21a6e64f768f from=translated src=- shape=4548d42d vocab=1392d641
-/
theorem zeta_ell_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_ell_int ℓ := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.zeta_ell_int_spec] using S.hzeta_ell

/-- The selected prime above `ℓ` contains `π = ζ_ℓ - 1`.
@isnad1 id=mem.0h6v.s8.d9edb6a311a4 from=translated src=- shape=82d9f573 vocab=e4134558
-/
theorem π_mem_Q : S.π ∈ S.Q := by
  rw [S.π_def]
  exact zeta_sub_one_mem_of_natCast_mem S.zeta_ell_int_isPrimitiveRoot S.hQ

/-- Ideal form of `π_mem_Q`: the principal ideal `(π)` lies below `Q`.
@isnad1 id=le.0h6v.s8.09369838023a from=translated src=- shape=0e930f87 vocab=d9685ced
-/
theorem span_pi_le_Q : Ideal.span ({S.π} : Set (𝓞 R')) ≤ S.Q :=
  (Ideal.span_singleton_le_iff_mem _).mpr S.π_mem_Q

/-- The additive character is expressed in powers of the chosen primitive
`ℓ`-th root.
@isnad1 id=eq.0h7v.s8.3c13a918306d from=translated src=- shape=097a325c vocab=17f46f96
-/
theorem psi_pow_form (x : k) : S.psi x = S.zeta_ell ^ S.psiExponent x :=
  S.psi_eq_zeta_ell_pow x

/-- The integral additive character defined by the exponent form
`ψ(x) = ζ_ℓ ^ psiExponent x`.-/
def psiInt : AddChar k (𝓞 R') where
  toFun x := S.zeta_ell_int ^ S.psiExponent x
  map_zero_eq_one' := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 R') R' (S.zeta_ell_int ^ S.psiExponent 0) =
      algebraMap (𝓞 R') R' (1 : 𝓞 R')
    rw [map_pow, map_one, S.algebraMap_zeta_ell_int]
    simpa [S.psi_pow_form] using (AddChar.map_zero_eq_one S.psi)
  map_add_eq_mul' x y := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 R') R' (S.zeta_ell_int ^ S.psiExponent (x + y)) =
      algebraMap (𝓞 R') R'
        (S.zeta_ell_int ^ S.psiExponent x * S.zeta_ell_int ^ S.psiExponent y)
    rw [map_mul, map_pow, map_pow, map_pow, S.algebraMap_zeta_ell_int]
    calc
      S.zeta_ell ^ S.psiExponent (x + y) = S.psi (x + y) := (S.psi_pow_form (x + y)).symm
      _ = S.psi x * S.psi y := AddChar.map_add_eq_mul S.psi x y
      _ = S.zeta_ell ^ S.psiExponent x * S.zeta_ell ^ S.psiExponent y := by
        rw [S.psi_pow_form x, S.psi_pow_form y]

/-- The concrete Gauss sum as an algebraic integer.-/
def gaussSumInt (a : ℕ) : 𝓞 R' :=
  _root_.gaussSum (S.residueCharInt ^ a) S.psiInt

end ConductorFlexibleConcreteStickelbergerSetup

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- The old exact pair-cyclotomic concrete setup is a special case of the
conductor-flexible concrete API.-/
def toConductorFlexible (S : ConcreteStickelbergerSetup ℓ p k K R') :
    ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' where
  hℓ_ne_p := S.hℓ_ne_p
  f := S.f
  card_k := S.card_k
  zeta_k := S.zeta_k
  hzeta_k := S.hzeta_k
  hdiv := S.hdiv
  zeta_p := S.zeta_p
  hzeta_p := S.hzeta_p
  zeta_p_int := S.zeta_p_int
  zeta_p_int_spec := S.zeta_p_int_spec
  zeta_ell := S.zeta_ell
  hzeta_ell := S.hzeta_ell
  zeta_ell_int := S.zeta_ell_int
  zeta_ell_int_spec := S.zeta_ell_int_spec
  π := S.π
  hπ := S.hπ
  Q := S.Q
  hQ_prime := S.hQ_prime
  hQ := S.hQ
  residueMap := S.residueMap
  residueMap_surjective := S.residueMap_surjective
  residueMap_ker := S.residueMap_ker
  zeta_p_int_residue := S.zeta_p_int_residue
  psi := S.psi
  hpsi := S.hpsi
  psiExponent := S.psiExponent
  psi_eq_zeta_ell_pow := S.psi_eq_zeta_ell_pow

end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular
