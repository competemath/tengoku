module

public import Tengoku.Seed.FieldTheory.Finite.Basic
public import Tengoku.Seed.GroupTheory.SpecificGroups.Cyclic
public import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots
public import Tengoku.Seed.RingTheory.DedekindDomain.Ideal.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Power residue symbols

This file defines the finite-field and prime-ideal pieces of the power
residue symbol API used in the reflection argument. The ideal-level API keeps
the coprimality predicate explicit, so later reciprocity statements can record
their exact local hypotheses without hiding them in typeclass search.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace ResidueSymbol

namespace PowerResidue

open UniqueFactorizationMonoid

variable {k : Type*} [Field k] [Fintype k]
variable {p : ℕ}

/-- The finite-field value `x ^ ((#k - 1) / p)` used in the `p`-th power
residue symbol.-/
def finiteFieldUnit (_hdiv : p ∣ Fintype.card k - 1) (x : kˣ) : kˣ :=
  x ^ ((Fintype.card k - 1) / p)

/--
@isnad1 id=eq.1h3v.s7.34f332156b59 from=translated src=- shape=409b5058 vocab=82613dc3
-/
theorem finiteFieldUnit_pow_eq_one (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    finiteFieldUnit hdiv x ^ p = 1 := by
  apply Units.ext
  change ((x : k) ^ ((Fintype.card k - 1) / p)) ^ p = (1 : k)
  rw [← pow_mul, Nat.div_mul_cancel hdiv]
  exact _root_.FiniteField.pow_card_sub_one_eq_one (x : k) x.ne_zero

/--
@isnad1 id=mem.2h4v.s7.c2c187da888d from=translated src=- shape=89d82750 vocab=19739428
-/
theorem finiteFieldUnit_mem_zpowers [NeZero p] {zeta : kˣ} (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    finiteFieldUnit hdiv x ∈ Subgroup.zpowers zeta := by
  rw [hzeta.zpowers_eq]
  rw [mem_rootsOfUnity]
  exact finiteFieldUnit_pow_eq_one hdiv x

/-- Exponent form of the finite-field power residue symbol with respect to a
chosen primitive `p`-th root of unity. The actual residue-symbol value is
`zeta ^ finiteFieldExponent`.-/
def finiteFieldExponent [NeZero p] (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) : ZMod p :=
  hzeta.zmodEquivZPowers.symm
    (Additive.ofMul ⟨finiteFieldUnit hdiv x, finiteFieldUnit_mem_zpowers hzeta hdiv x⟩)

/-- The exponent form recovers the concrete finite-field unit
`x ^ ((#k - 1) / p)`.
@isnad1 id=eq.2h4v.s7.e09f837e8dd7 from=translated src=- shape=ff3d1d9e vocab=2afae58b
-/
theorem zeta_pow_finiteFieldExponent_val [NeZero p]
    {zeta : kˣ} (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    zeta ^ (finiteFieldExponent zeta hzeta hdiv x).val = finiteFieldUnit hdiv x := by
  have h := hzeta.zmodEquivZPowers.apply_symm_apply
    (Additive.ofMul
      (⟨finiteFieldUnit hdiv x, finiteFieldUnit_mem_zpowers hzeta hdiv x⟩ :
        Subgroup.zpowers zeta))
  have happ := congrArg (fun y : Additive (Subgroup.zpowers zeta) ↦
    ((Additive.toMul y : Subgroup.zpowers zeta) : kˣ)) h
  change ((Additive.toMul
      (hzeta.zmodEquivZPowers (finiteFieldExponent zeta hzeta hdiv x)) :
        Subgroup.zpowers zeta) : kˣ) = finiteFieldUnit hdiv x at happ
  rw [← ZMod.natCast_zmod_val (finiteFieldExponent zeta hzeta hdiv x)] at happ
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat] at happ
  exact happ

/--
@isnad1 id=eq.1h4v.s7.66a8e8417f82 from=translated src=- shape=78c9af4c vocab=9efd2899
-/
theorem finiteFieldUnit_mul (hdiv : p ∣ Fintype.card k - 1) (x y : kˣ) :
    finiteFieldUnit hdiv (x * y) = finiteFieldUnit hdiv x * finiteFieldUnit hdiv y := by
  ext
  simp [finiteFieldUnit, mul_pow]

/--
@isnad1 id=eq.1h2v.s6.2e49d6064249 from=translated src=- shape=0fc80a30 vocab=9ac7fc18
-/
theorem finiteFieldUnit_one (hdiv : p ∣ Fintype.card k - 1) :
    finiteFieldUnit hdiv (1 : kˣ) = 1 := by
  ext
  simp [finiteFieldUnit]

/--
@isnad1 id=eq.1h4v.s7.3567423618cf from=translated src=- shape=4cca4861 vocab=82613dc3
-/
theorem finiteFieldUnit_pow (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) (n : ℕ) :
    finiteFieldUnit hdiv (x ^ n) = (finiteFieldUnit hdiv x) ^ n := by
  induction n with
  | zero => simp [finiteFieldUnit_one]
  | succ k ih => rw [pow_succ, finiteFieldUnit_mul, ih, pow_succ]

/--
@isnad1 id=eq.2h5v.s7.9d407074c06d from=translated src=- shape=2f48805c vocab=e30bcefb
-/
theorem finiteFieldExponent_mul [NeZero p] (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x y : kˣ) :
    finiteFieldExponent zeta hzeta hdiv (x * y) =
      finiteFieldExponent zeta hzeta hdiv x + finiteFieldExponent zeta hzeta hdiv y := by
  apply hzeta.zmodEquivZPowers.injective
  rw [map_add]
  simp only [finiteFieldExponent, AddEquiv.apply_symm_apply]
  ext
  exact congrArg (fun u : kˣ ↦ (u : k)) (finiteFieldUnit_mul hdiv x y)

/--
@isnad1 id=eq.2h3v.s7.d43c3aaf4486 from=translated src=- shape=b7eac856 vocab=b058e47e
-/
theorem finiteFieldExponent_one [NeZero p] (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) :
    finiteFieldExponent zeta hzeta hdiv (1 : kˣ) = 0 := by
  apply hzeta.zmodEquivZPowers.injective
  rw [map_zero]
  simp only [finiteFieldExponent, AddEquiv.apply_symm_apply]
  ext
  simp [finiteFieldUnit_one]

/--
@isnad1 id=eq.2h5v.s7.0b2e7defa2ca from=translated src=- shape=00bf121e vocab=cd6a0c79
-/
theorem finiteFieldExponent_pow [NeZero p] (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) (n : ℕ) :
    finiteFieldExponent zeta hzeta hdiv (x ^ n) =
      n * finiteFieldExponent zeta hzeta hdiv x := by
  induction n with
  | zero => simp [finiteFieldExponent_one]
  | succ k ih =>
    rw [pow_succ, finiteFieldExponent_mul, ih]
    push_cast; ring

/-- **Residue is a p-th power ⟹ exponent vanishes**: if `x = y^p` for some
`y ∈ kˣ`, then `finiteFieldExponent zeta hzeta hdiv x = 0`.
@isnad1 id=eq.3h4v.s7.4fe91c183096 from=translated src=- shape=6b7a5079 vocab=1f4bb05a
-/
theorem finiteFieldExponent_eq_zero_of_isPow [NeZero p]
    (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) {x : kˣ}
    (h_pow : ∃ y : kˣ, x = y ^ p) :
    finiteFieldExponent zeta hzeta hdiv x = 0 := by
  obtain ⟨y, rfl⟩ := h_pow
  rw [finiteFieldExponent_pow, ZMod.natCast_self, zero_mul]

/-- Cyclic-group `p`-th-power criterion.  In a finite cyclic commutative group
`G`, when `p` divides the group order, an element is a `p`-th power iff its
`#G / p`-th power is `1`.
@isnad1 id=iff.1h3v.s6.2b4ebcaa457d from=translated src=- shape=16fd01ac vocab=fe84c3e6
-/
theorem isPow_iff_pow_card_div_eq_one {G : Type*} [CommGroup G]
    [Finite G] [IsCyclic G] {p : ℕ} (hp : p ∣ Nat.card G) (u : G) :
    (∃ v : G, u = v ^ p) ↔ u ^ (Nat.card G / p) = 1 := by
  have hrange : (∃ v : G, u = v ^ p) ↔ u ∈ (powMonoidHom p : G →* G).range := by
    refine ⟨fun ⟨v, hv⟩ ↦ ⟨v, hv.symm⟩, ?_⟩
    rintro ⟨v, hv⟩
    exact ⟨v, hv.symm⟩
  rw [hrange, show u ^ (Nat.card G / p) = (powMonoidHom (Nat.card G / p) : G →* G) u from rfl,
    ← MonoidHom.mem_ker]
  have hcardR : Nat.card (powMonoidHom p : G →* G).range = Nat.card G / p := by
    rw [IsCyclic.card_powMonoidHom_range, Nat.gcd_eq_right hp]
  have hcardK : Nat.card (powMonoidHom (Nat.card G / p) : G →* G).ker =
      Nat.card G / p := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hp)]
  have hsubLE : (powMonoidHom p : G →* G).range ≤
      (powMonoidHom (Nat.card G / p) : G →* G).ker := by
    rintro x ⟨w, rfl⟩
    simp only [MonoidHom.mem_ker, powMonoidHom_apply, ← pow_mul]
    rw [mul_comm, Nat.div_mul_cancel hp]
    exact pow_card_eq_one'
  have hsub : (powMonoidHom p : G →* G).range =
      (powMonoidHom (Nat.card G / p) : G →* G).ker := by
    apply Subgroup.eq_of_le_of_card_ge hsubLE
    rw [hcardR, hcardK]
  rw [hsub]

/-- In a finite field, `x ^ ((#k - 1) / p) = 1` iff `x` is a `p`-th power in
the unit group, provided `p ∣ #k - 1`.
@isnad1 id=iff.1h3v.s7.5969921a0946 from=translated src=- shape=f7f01b87 vocab=21a585b1
-/
theorem finiteFieldUnit_eq_one_iff_isPow [Fact p.Prime]
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    finiteFieldUnit hdiv x = 1 ↔ ∃ y : kˣ, x = y ^ p := by
  classical
  have hcardUnits : Nat.card kˣ = Fintype.card k - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hpdvd : p ∣ Nat.card kˣ := hcardUnits ▸ hdiv
  have hcrit := isPow_iff_pow_card_div_eq_one (G := kˣ) hpdvd x
  rw [hcardUnits] at hcrit
  simpa [finiteFieldUnit, eq_comm] using hcrit.symm

/-- `finiteFieldExponent` vanishes iff the residue unit is `1`.
@isnad1 id=iff.2h4v.s7.8cba752d29bf from=translated src=- shape=2fd89226 vocab=4e8861db
-/
theorem finiteFieldExponent_eq_zero_iff_finiteFieldUnit_eq_one [NeZero p]
    (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    finiteFieldExponent zeta hzeta hdiv x = 0 ↔ finiteFieldUnit hdiv x = 1 := by
  simp only [finiteFieldExponent]
  rw [(hzeta.zmodEquivZPowers).symm.map_eq_zero_iff]
  constructor
  · intro h
    have hh : (⟨finiteFieldUnit hdiv x, finiteFieldUnit_mem_zpowers hzeta hdiv x⟩ :
        Subgroup.zpowers zeta) = 1 := by
      have := congrArg Additive.toMul h
      simpa using this
    exact congrArg Subtype.val hh
  · intro h
    have hh : (⟨finiteFieldUnit hdiv x, finiteFieldUnit_mem_zpowers hzeta hdiv x⟩ :
        Subgroup.zpowers zeta) = 1 := Subtype.ext h
    have := congrArg Additive.ofMul hh
    simpa using this

/-- `finiteFieldExponent` vanishes iff the residue unit is a `p`-th power.
@isnad1 id=iff.2h4v.s7.93ed7049d797 from=translated src=- shape=bc7d8ca2 vocab=258cbba2
-/
theorem finiteFieldExponent_eq_zero_iff_isPow [Fact p.Prime] [NeZero p]
    (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    finiteFieldExponent zeta hzeta hdiv x = 0 ↔ ∃ y : kˣ, x = y ^ p := by
  rw [finiteFieldExponent_eq_zero_iff_finiteFieldUnit_eq_one zeta hzeta hdiv x,
    finiteFieldUnit_eq_one_iff_isPow hdiv x]

/-- **Change of primitive root in `finiteFieldExponent`.**
If `ζ` is a primitive `p`-th root and `ζ^n` is also a primitive `p`-th root,
then `n * finiteFieldExponent (ζ^n) hpow hdiv x = finiteFieldExponent ζ hζ hdiv x`
in `ZMod p`.
@isnad1 id=eq.3h5v.s8.eefed57a254f from=translated src=- shape=14700fac vocab=081d855d
-/
theorem finiteFieldExponent_zeta_pow [Fact p.Prime] [NeZero p]
    {zeta : kˣ} (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) {n : ℕ}
    (hpow : IsPrimitiveRoot (zeta ^ n) p) (x : kˣ) :
    (n : ZMod p) * finiteFieldExponent (zeta ^ n) hpow hdiv x =
      finiteFieldExponent zeta hzeta hdiv x := by
  have h_pow := zeta_pow_finiteFieldExponent_val hpow hdiv x
  have h_zeta := zeta_pow_finiteFieldExponent_val hzeta hdiv x
  rw [← pow_mul] at h_pow
  have h_eq : zeta ^ (n * (finiteFieldExponent (zeta ^ n) hpow hdiv x).val) =
      zeta ^ (finiteFieldExponent zeta hzeta hdiv x).val := h_pow.trans h_zeta.symm
  rw [pow_eq_pow_iff_modEq] at h_eq
  rw [← hzeta.eq_orderOf] at h_eq
  have h_zmod := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h_eq
  push_cast at h_zmod
  simp only [ZMod.natCast_val, ZMod.cast_id] at h_zmod
  exact h_zmod

section PrimeIdeal

variable {R : Type*} [CommRing R]
variable (q : Ideal R) [q.IsMaximal]

/-- A quotient class represented by an element not in the prime ideal, as a
unit of the residue field.-/
def quotientUnitOfNotMem (x : R) (hx : x ∉ q) : (R ⧸ q)ˣ :=
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  Units.mk0 (Ideal.Quotient.mk q x) (by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hx)

/--
@isnad1 id=eq.3h4v.s8.ae5cb09f4575 from=translated src=- shape=55c98129 vocab=df73c2de
-/
theorem quotientUnitOfNotMem_mul {x y : R} (hx : x ∉ q) (hy : y ∉ q)
    (hxy : x * y ∉ q) :
    quotientUnitOfNotMem q (x * y) hxy =
      quotientUnitOfNotMem q x hx * quotientUnitOfNotMem q y hy := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  ext
  simp [quotientUnitOfNotMem]

/-- The `p`-th power residue symbol at a maximal ideal, in exponent form with
respect to a chosen primitive root of unity in the residue field.-/
def primeExponent {p : ℕ} [NeZero p] [Fintype (R ⧸ q)] (zeta_q : (R ⧸ q)ˣ)
    (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card (R ⧸ q) - 1) (x : R) (hx : x ∉ q) : ZMod p := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  exact finiteFieldExponent zeta_q hzeta_q hdiv (quotientUnitOfNotMem q x hx)

/--
@isnad1 id=eq.5h6v.s8.65c44280c4df from=translated src=- shape=0e555436 vocab=91110f0e
-/
theorem primeExponent_mul {p : ℕ} [NeZero p] [Fintype (R ⧸ q)] (zeta_q : (R ⧸ q)ˣ)
    (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card (R ⧸ q) - 1) {x y : R}
    (hx : x ∉ q) (hy : y ∉ q) (hxy : x * y ∉ q) :
    primeExponent q zeta_q hzeta_q hdiv (x * y) hxy =
      primeExponent q zeta_q hzeta_q hdiv x hx +
        primeExponent q zeta_q hzeta_q hdiv y hy := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  rw [primeExponent, primeExponent, primeExponent, ← finiteFieldExponent_mul]
  congr
  exact quotientUnitOfNotMem_mul q hx hy hxy

/--
@isnad1 id=eq.1h2v.s7.139c0fa36216 from=translated src=- shape=fa3bbc5a vocab=9e61ca08
-/
theorem quotientUnitOfNotMem_one {h1 : (1 : R) ∉ q} :
    quotientUnitOfNotMem q (1 : R) h1 = 1 := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  ext
  simp [quotientUnitOfNotMem]

/--
@isnad1 id=eq.3h4v.s8.2be9b7998ff6 from=translated src=- shape=5afaeed6 vocab=642d927f
-/
theorem primeExponent_one {p : ℕ} [NeZero p] [Fintype (R ⧸ q)] (zeta_q : (R ⧸ q)ˣ)
    (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card (R ⧸ q) - 1) (h1 : (1 : R) ∉ q) :
    primeExponent q zeta_q hzeta_q hdiv (1 : R) h1 = 0 := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  rw [primeExponent,
    show quotientUnitOfNotMem q (1 : R) h1 = 1 from quotientUnitOfNotMem_one q]
  exact finiteFieldExponent_one zeta_q hzeta_q hdiv

/--
@isnad1 id=eq.2h4v.s8.f5ac86de9241 from=translated src=- shape=5e826270 vocab=d9a247d8
-/
theorem quotientUnitOfNotMem_pow {x : R} (hx : x ∉ q) (n : ℕ)
    (hxn : x ^ n ∉ q) :
    quotientUnitOfNotMem q (x ^ n) hxn = (quotientUnitOfNotMem q x hx) ^ n := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  ext
  simp [quotientUnitOfNotMem]

/--
@isnad1 id=eq.4h6v.s8.e52944f0f1b6 from=translated src=- shape=871098c1 vocab=558cf661
-/
theorem primeExponent_pow {p : ℕ} [NeZero p] [Fintype (R ⧸ q)] (zeta_q : (R ⧸ q)ˣ)
    (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card (R ⧸ q) - 1) {x : R} (hx : x ∉ q)
    (n : ℕ) (hxn : x ^ n ∉ q) :
    primeExponent q zeta_q hzeta_q hdiv (x ^ n) hxn =
      n * primeExponent q zeta_q hzeta_q hdiv x hx := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  rw [primeExponent, primeExponent, quotientUnitOfNotMem_pow q hx n hxn]
  exact finiteFieldExponent_pow zeta_q hzeta_q hdiv _ n

/-- **Change of primitive root in `primeExponent`.** Direct consequence
of `finiteFieldExponent_zeta_pow`.
@isnad1 id=eq.4h6v.s9.81563de72b03 from=translated src=- shape=507a03b3 vocab=a67191a0
-/
theorem primeExponent_zeta_pow {p : ℕ} [Fact p.Prime] [NeZero p] [Fintype (R ⧸ q)]
    {zeta_q : (R ⧸ q)ˣ} (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card (R ⧸ q) - 1) {n : ℕ}
    (hpow : IsPrimitiveRoot (zeta_q ^ n) p) (α : R) (hα : α ∉ q) :
    (n : ZMod p) * primeExponent q (zeta_q ^ n) hpow hdiv α hα =
      primeExponent q zeta_q hzeta_q hdiv α hα := by
  letI : Field (R ⧸ q) := Ideal.Quotient.field q
  rw [primeExponent, primeExponent]
  exact finiteFieldExponent_zeta_pow hzeta_q hdiv hpow _

end PrimeIdeal

section Ideals

variable {R : Type*} [CommRing R]

/-- An ideal is explicitly coprime to an element when it generates the unit
ideal together with that element.-/
def IsCoprimeToElement (I : Ideal R) (x : R) : Prop :=
  I ⊔ Ideal.span ({x} : Set R) = ⊤

/-- Interface for an ideal-level power residue symbol away from `p * eta`.

The concrete construction by prime-ideal factorization is intentionally kept
separate from the API: downstream reciprocity theorems only need the symbol,
its coprimality domain, and multiplicativity.-/
structure IdealSymbol (p : ℕ) (eta : R) where
  symbol :
    (I : Ideal R) → IsCoprimeToElement I ((p : R) * eta) → ZMod p
  symbol_one :
    ∀ h1 : IsCoprimeToElement (1 : Ideal R) ((p : R) * eta),
      symbol 1 h1 = 0
  symbol_mul :
    ∀ {I J : Ideal R}
      (hI : IsCoprimeToElement I ((p : R) * eta))
      (hJ : IsCoprimeToElement J ((p : R) * eta))
      (hIJ : IsCoprimeToElement (I * J) ((p : R) * eta)),
      symbol (I * J) hIJ = symbol I hI + symbol J hJ

section IdealFactorization

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {p : ℕ}

/-- Extension of a local exponent function to integral ideals by summing over
the normalized prime ideal factors, counted with multiplicity. Only the values
on prime ideals can contribute.-/
def idealExponent (chi : Ideal R → ZMod p)
    (I : Ideal R) : ZMod p :=
  ((normalizedFactors I).map chi).sum

/--
@isnad1 id=eq.2h5v.s7.9b6e172e84d5 from=translated src=- shape=b4d08322 vocab=5a8c5dfd
-/
theorem idealExponent_mul (chi : Ideal R → ZMod p)
    {I J : Ideal R} (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealExponent chi (I * J) =
      idealExponent chi I + idealExponent chi J := by
  simp only [idealExponent]
  rw [normalizedFactors_mul hI hJ]
  simp

/-- Convenience wrapper for local data supplied only on prime ideals.-/
def idealExponentOfPrimeSymbols (chi : (q : Ideal R) → Prime q → ZMod p)
    (I : Ideal R) : ZMod p := by
  classical
  exact idealExponent (fun q ↦ if hq : Prime q then chi q hq else 0) I

/--
@isnad1 id=eq.2h5v.s8.55a2b7a4a558 from=translated src=- shape=7d1dccc5 vocab=65f842a1
-/
theorem idealExponentOfPrimeSymbols_mul (chi : (q : Ideal R) → Prime q → ZMod p)
    {I J : Ideal R} (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealExponentOfPrimeSymbols chi (I * J) =
      idealExponentOfPrimeSymbols chi I + idealExponentOfPrimeSymbols chi J := by
  classical
  simp only [idealExponentOfPrimeSymbols]
  exact idealExponent_mul (fun q ↦ if hq : Prime q then chi q hq else 0) hI hJ

end IdealFactorization

end Ideals

end PowerResidue

end ResidueSymbol
end Reflection
end BernoulliRegular
