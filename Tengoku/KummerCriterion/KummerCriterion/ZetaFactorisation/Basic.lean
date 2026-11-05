module

public import Tengoku.Seed.Data.Fintype.Vector
public import Tengoku.Seed.NumberTheory.DirichletCharacter.Orthogonality
public import Tengoku.Seed.NumberTheory.LSeries.DirichletContinuation
public import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Basic
public import Tengoku.Seed.NumberTheory.NumberField.Ideal.KummerDedekind
import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Ideal
import Tengoku.Seed.RingTheory.Polynomial.Cyclotomic.Factorization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic cyclotomic zeta-factorisation infrastructure

This module contains the setup and prime-by-prime local-factor calculations
`KummerCriterion.ZetaFactorisation`.
-/

@[expose] public section

noncomputable section

open NumberField
open Polynomial
open scoped Topology nonZeroDivisors

namespace KummerCriterion

section ZetaFactorisation

noncomputable instance instFintypeSym (α : Type*) [Finite α] (n : ℕ) :
    Fintype (Sym α n) :=
  Fintype.ofFinite (Sym α n)

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- A chosen multiplicative equivalence between complex-valued Dirichlet
characters mod `p` and the unit group `(ZMod p)ˣ`.-/
noncomputable def dirichletCharacterMulEquivUnits : DirichletCharacter ℂ p ≃* (ZMod p)ˣ := by
  letI : NeZero p := ⟨hp.1.ne_zero⟩
  exact (DirichletCharacter.mulEquiv_units ℂ p).some

/-- There are exactly `p - 1` complex-valued Dirichlet characters modulo `p`.-/
lemma card_dirichletCharacter_complex : Nat.card (DirichletCharacter ℂ p) = p - 1 := by
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime hp.1]

/-- For prime modulus `p`, the `L`-function of the trivial character is
`(1 - p^{-s}) ζ(s)`.-/
lemma LFunction_trivial_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunctionTrivChar p s =
      (1 - (p : ℂ) ^ (-s)) * riemannZeta s := by
  have hpf : Nat.primeFactors p = {p} := by
    simpa using (Nat.primeFactors_prime_pow (p := p) (k := 1) (by decide : (1 : ℕ) ≠ 0) hp.1)
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := p) hs, hpf,
    Finset.prod_singleton]

/-! ### Step A — local factor definitions -/

/-- The rational prime ideal `(ℓ)` inside `ℤ`.-/
noncomputable def rationalPrimeIdeal (ℓ : ℕ) : Ideal ℤ :=
  Ideal.span ({(ℓ : ℤ)} : Set ℤ)

/-- The finite set of prime ideals of `𝓞 K` lying above `(ℓ)`.-/
noncomputable def primesOverFinset (ℓ : ℕ) : Finset (Ideal (𝓞 K)) :=
  IsDedekindDomain.primesOverFinset (rationalPrimeIdeal ℓ) (𝓞 K)

/-- The nontrivial Dirichlet characters mod `p`, as a finite set.-/
noncomputable def nontrivialCharacters : Finset (DirichletCharacter ℂ p) := by
  classical
  exact Finset.univ.erase 1

/-- The even nontrivial Dirichlet characters mod `p`, as a finite set.-/
noncomputable def evenNontrivialCharacters : Finset (DirichletCharacter ℂ p) := by
  classical
  exact Finset.univ.filter fun χ => χ.Even ∧ χ ≠ 1

/-- The odd Dirichlet characters mod `p`, as a finite set.-/
noncomputable def oddCharacters : Finset (DirichletCharacter ℂ p) := by
  classical
  exact Finset.univ.filter fun χ => χ.Odd

/-- The inverse of an odd Dirichlet character stays in `oddCharacters`.-/
theorem inv_mem_oddCharacters (p : ℕ) {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ oddCharacters p) : χ⁻¹ ∈ oddCharacters p := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hχ_odd : χ.Odd := (Finset.mem_filter.mp hχ).2
  rw [DirichletCharacter.Odd] at hχ_odd ⊢
  rw [MulChar.inv_apply_eq_inv', hχ_odd]
  norm_num

/-- The character-side local Euler factor at a rational prime `ℓ`.-/
noncomputable def charLocalFactor (ℓ : ℕ) (s : ℂ) : ℂ :=
  ∏ χ : DirichletCharacter ℂ p, (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))

/-- The even nontrivial part of the character-side local Euler factor.-/
noncomputable def evenCharLocalFactor (ℓ : ℕ) (s : ℂ) : ℂ :=
  Finset.prod (evenNontrivialCharacters (p := p)) fun χ =>
    (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))

/-- The Dedekind-side local Euler factor at a rational prime `ℓ`, written as a
finite product over the primes of `𝓞 K` lying above `(ℓ)`.-/
noncomputable def dedekindLocalFactor (ℓ : ℕ) (s : ℂ) : ℂ :=
  Finset.prod (primesOverFinset K ℓ) fun P => (1 - (Ideal.absNorm P : ℂ) ^ (-s))

/-- The global product of Dirichlet `L`-functions over all characters mod `p`.-/
noncomputable def LProduct (s : ℂ) : ℂ :=
  ∏ χ : DirichletCharacter ℂ p, DirichletCharacter.LFunction χ s

/-- The nontrivial part of the global `L`-product.-/
noncomputable def nontrivialLProduct (s : ℂ) : ℂ :=
  Finset.prod (nontrivialCharacters (p := p)) fun χ => DirichletCharacter.LFunction χ s

/-- The even nontrivial part of the global `L`-product.-/
noncomputable def evenLProduct (s : ℂ) : ℂ :=
  Finset.prod (evenNontrivialCharacters (p := p)) fun χ => DirichletCharacter.LFunction χ s

/-- The odd part of the global `L`-product.-/
noncomputable def oddLProduct (s : ℂ) : ℂ :=
  Finset.prod (oddCharacters (p := p)) fun χ => DirichletCharacter.LFunction χ s

/-- The distinguished primitive `p`-th root of unity viewed in `𝓞 K`.-/
noncomputable def zetaInteger : 𝓞 K :=
  (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger

/-! ### Step B — easy analytic rewrites -/

/-! ### Step C — character-side local factor skeleton -/

/-- If `ℓ` is a prime different from `p`, then `p` and `ℓ` are coprime.-/
lemma coprime_of_prime_ne {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : p.Coprime ℓ :=
  (Nat.coprime_primes hp.out (Fact.out : ℓ.Prime)).mpr (Ne.symm hℓp)

/-- The unit of `(ZMod p)ˣ` represented by a prime `ℓ ≠ p`.-/
noncomputable def unitOfPrimeNe (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime ℓ (coprime_of_prime_ne (p := p) hℓp).symm

/-- The residue-degree candidate on the character side: the order of `ℓ mod p`
inside `(ZMod p)ˣ`.-/
noncomputable def localResidueDegree (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  orderOf (unitOfPrimeNe (p := p) ℓ hℓp)

/-- The expected number of primes above `ℓ ≠ p`, inferred from the character
group cardinality.-/
noncomputable def localPrimeCount (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  Nat.card (DirichletCharacter ℂ p) / localResidueDegree (p := p) ℓ hℓp

lemma localResidueDegree_dvd_card_characters {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    localResidueDegree (p := p) ℓ hℓp ∣ Nat.card (DirichletCharacter ℂ p) := by
  rw [card_dirichletCharacter_complex (p := p)]
  simpa [localResidueDegree, ZMod.card_units p] using
    (orderOf_dvd_card (x := unitOfPrimeNe (p := p) ℓ hℓp))

lemma localPrimeCount_mul_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    localPrimeCount (p := p) ℓ hℓp * localResidueDegree (p := p) ℓ hℓp =
      Nat.card (DirichletCharacter ℂ p) :=
  Nat.div_mul_cancel (localResidueDegree_dvd_card_characters (p := p) hℓp)

/-- Classical polynomial identity in `ℂ`: the product of `(1 - ζ T)` over all
`d`-th roots of unity equals `1 - T^d`.-/
lemma prod_nthRootsFinset_one_sub_mul (d : ℕ) (hd : 0 < d) (T : ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - ζ * T) = 1 - T ^ d := by
  by_cases hT : T = 0
  · subst hT
    simp [zero_pow hd.ne']
  · have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / d)) d :=
      Complex.isPrimitiveRoot_exp d hd.ne'
    have hcard : (Polynomial.nthRootsFinset d (1 : ℂ)).card = d := hζ.card_nthRootsFinset
    have hpoly : Polynomial.X ^ d - 1 = ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ),
        (Polynomial.X - Polynomial.C ζ) := Polynomial.X_pow_sub_one_eq_prod hd hζ
    have heval := congrArg (Polynomial.eval T⁻¹) hpoly
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_prod, Polynomial.eval_C] at heval
    have key : ∀ ζ : ℂ, (1 - ζ * T) = T * (T⁻¹ - ζ) := fun ζ => by field_simp
    rw [Finset.prod_congr rfl (fun ζ _ => key ζ), Finset.prod_mul_distrib,
      Finset.prod_const, hcard, ← heval]
    have hTT : T ^ d * T⁻¹ ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hT, one_pow]
    linear_combination hTT

/-- Helper: if `ω` is a primitive `n`-th root of unity, then for any `a: ℕ`,
`ω^a` is a primitive `(n / gcd(n, a))`-th root of unity.

This generalises `IsPrimitiveRoot.pow_of_coprime` to arbitrary exponents.-/
lemma _root_.IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd
    {M : Type*} [CommMonoid M] {n : ℕ} (hn : 0 < n) (a : ℕ)
    {ω : M} (hω : IsPrimitiveRoot ω n) :
    IsPrimitiveRoot (ω ^ a) (n / n.gcd a) := by
  exact hω.pow_div_gcd a (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left a hn))

/-- Polynomial identity: for `ω` a primitive `n`-th root of unity in `ℂ` and any
`a: ℕ`, `∏_{k = 0..n-1} (1 - ω^{ka} T) = (1 - T^{n/gcd(n,a)})^{gcd(n,a)}`.-/
lemma prod_pow_primRoot_eq_pow {n : ℕ} (hn : 0 < n) (a : ℕ)
    {ω : ℂ} (hω : IsPrimitiveRoot ω n) (T : ℂ) :
    ∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T) =
      (1 - T ^ (n / n.gcd a)) ^ n.gcd a := by
  classical
  set d := n / n.gcd a with hd_def
  set c := n.gcd a with hc_def
  have hc_dvd_n : c ∣ n := Nat.gcd_dvd_left n a
  have hc_dvd_a : c ∣ a := Nat.gcd_dvd_right n a
  have hc_mul_d : c * d = n := Nat.mul_div_cancel' hc_dvd_n
  have hc_pos : 0 < c := Nat.gcd_pos_of_pos_left _ hn
  have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd hn hc_dvd_n) hc_pos
  have hd_dvd_n : d ∣ n := ⟨c, by rw [mul_comm]; exact hc_mul_d.symm⟩
  have hω_a_prim : IsPrimitiveRoot (ω ^ a) d :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn a hω
  have h_period : ∀ k : ℕ, ω ^ (k * a) = ω ^ ((k % d) * a) := by
    intro k
    have hkd : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
    have h_da : ω ^ ((k / d) * (d * a)) = 1 := by
      obtain ⟨a', ha'⟩ := hc_dvd_a
      rw [ha', show (k / d) * (d * (c * a')) = (k / d) * a' * (c * d) from by ring, hc_mul_d]
      exact (hω.pow_eq_one_iff_dvd _).mpr ⟨(k / d) * a', mul_comm _ _⟩
    conv_lhs => rw [hkd]
    rw [show (d * (k / d) + k % d) * a = (k % d) * a + (k / d) * (d * a) from by ring, pow_add,
      h_da, mul_one]
  rw [show (∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T)) =
      ∏ k ∈ Finset.range n, (1 - ω ^ ((k % d) * a) * T) from
    Finset.prod_congr rfl (fun k _ => by rw [← h_period k])]
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := fun k : ℕ => k % d) (t := Finset.range d)
    (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hd_pos))]
  have h_inner : ∀ j ∈ Finset.range d,
      (∏ k ∈ (Finset.range n).filter (fun k => k % d = j), (1 - ω ^ ((k % d) * a) * T)) =
      (1 - ω ^ (j * a) * T) ^ c := by
    intro j hj
    have h_rewrite : ∀ k ∈ (Finset.range n).filter (fun k => k % d = j),
        (1 - ω ^ ((k % d) * a) * T) = (1 - ω ^ (j * a) * T) := fun k hk => by
      rw [Finset.mem_filter] at hk; rw [hk.2]
    rw [Finset.prod_congr rfl h_rewrite, Finset.prod_const]
    congr 1
    rw [Finset.mem_range] at hj
    obtain ⟨c', hcd'⟩ := hd_dvd_n
    have hc_eq : c = c' := by
      have hd_mul : d * c = n := by rw [mul_comm, hc_mul_d]
      exact Nat.eq_of_mul_eq_mul_left hd_pos (by rw [hd_mul, hcd'])
    rw [hc_eq]
    have hset : (Finset.range n).filter (fun k => k % d = j) =
        (Finset.range c').image (fun m => j + m * d) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      refine ⟨fun ⟨hk_lt, hk_mod⟩ => ?_, ?_⟩
      · have hk_dec : k = j + (k / d) * d := by
          have h1 : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
          rw [hk_mod, mul_comm d (k / d)] at h1
          omega
        refine ⟨k / d, ?_, hk_dec.symm⟩
        have h_lt_cd : (k / d) * d < c' * d := by
          have h_le : (k / d) * d ≤ k := Nat.div_mul_le_self k d
          rw [mul_comm c' d, ← hcd']; omega
        exact Nat.lt_of_mul_lt_mul_right h_lt_cd
      · rintro ⟨m, hm_lt, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [hcd', mul_comm]; nlinarith
        · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    rw [hset, Finset.card_image_of_injective _ (fun x y hxy => by simp at hxy; omega),
      Finset.card_range]
  rw [Finset.prod_congr rfl h_inner, Finset.prod_pow]
  congr 1
  have h_inj : Set.InjOn (fun j : ℕ => (ω ^ a) ^ j) ↑(Finset.range d) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    exact hω_a_prim.pow_inj hx hy hxy
  have h_image : Finset.image (fun j : ℕ => (ω ^ a) ^ j) (Finset.range d) =
      Polynomial.nthRootsFinset d (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro ζ hζ
      simp only [Finset.mem_image, Finset.mem_range] at hζ
      obtain ⟨j, _, rfl⟩ := hζ
      rw [Polynomial.mem_nthRootsFinset hd_pos, ← pow_mul, mul_comm j d, pow_mul,
        hω_a_prim.pow_eq_one, one_pow]
    · rw [hω_a_prim.card_nthRootsFinset, Finset.card_image_of_injOn h_inj, Finset.card_range]
  calc ∏ j ∈ Finset.range d, (1 - ω ^ (j * a) * T)
      = ∏ j ∈ Finset.range d, (1 - (ω ^ a) ^ j * T) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [← pow_mul, mul_comm a j]
    _ = ∏ ζ ∈ Finset.image (fun j : ℕ => (ω ^ a) ^ j) (Finset.range d), (1 - ζ * T) := by
        rw [Finset.prod_image h_inj]
    _ = ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - ζ * T) := by rw [h_image]
    _ = 1 - T ^ d := prod_nthRootsFinset_one_sub_mul d hd_pos T

/-- The classical finite-group character identity:
for `u: (ZMod p)ˣ` with `orderOf u = d`, as `χ` ranges over
`DirichletCharacter ℂ p`, the values `χ(u)` hit each `d`-th root of unity
exactly `(p - 1) / d` times, so the product `∏_χ (1 - χ(u) T)` is
`(1 - T^d)^{(p-1)/d}`.-/
lemma prod_characters_eval_eq_pow (u : (ZMod p)ˣ) (T : ℂ) :
    (∏ χ : DirichletCharacter ℂ p, (1 - χ (u : ZMod p) * T)) =
      (1 - T ^ orderOf u) ^ (Nat.card (DirichletCharacter ℂ p) / orderOf u) := by
  classical
  set d := orderOf u with hd_def
  set n := Nat.card (DirichletCharacter ℂ p) with hn_def
  have hn_units : Fintype.card (ZMod p)ˣ = n := by
    rw [hn_def, card_dirichletCharacter_complex (p := p), ZMod.card_units]
  have hn_units' : Nat.card (ZMod p)ˣ = n := by
    rw [Nat.card_eq_fintype_card, hn_units]
  have hn_pos : 0 < n := by rw [← hn_units]; exact Fintype.card_pos
  obtain ⟨g, hg_mon⟩ : ∃ g : (ZMod p)ˣ, ∀ x : (ZMod p)ˣ, x ∈ Submonoid.powers g :=
    IsCyclic.exists_monoid_generator
  have hg_mon' : ∀ x : (ZMod p)ˣ, ∃ m : ℕ, g ^ m = x := fun x => hg_mon x
  obtain ⟨a, ha⟩ := hg_mon' u
  have hg_zpow : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g := fun x => by
    obtain ⟨m, hm⟩ := hg_mon' x
    refine ⟨(m : ℤ), ?_⟩
    change g ^ (m : ℤ) = x
    rw [zpow_natCast]; exact hm
  have hg_order : orderOf g = n := by
    rw [← hn_units']; exact orderOf_eq_card_of_forall_mem_zpowers hg_zpow
  have hd_eq : d = n / n.gcd a := by
    have hfin : IsOfFinOrder g := by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨n, hn_pos, by rw [← hg_order]; exact pow_orderOf_eq_one g⟩
    have : d = orderOf (g ^ a) := by rw [hd_def, ← ha]
    rw [this, hfin.orderOf_pow, hg_order]
  have hn_div_d : n / d = n.gcd a := by
    have hcd : n.gcd a ∣ n := Nat.gcd_dvd_left n a
    rw [hd_eq, Nat.div_div_self hcd hn_pos.ne']
  have hω : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hω_unit : IsUnit ω := hω.isUnit hn_pos.ne'
  set ωu : ℂˣ := hω_unit.unit with hωu_def
  have hωu_val : (ωu : ℂ) = ω := by simp [hωu_def]
  have hωu_roots : ∀ k : ℕ, (ωu ^ k : ℂˣ) ∈ rootsOfUnity n ℂ := by
    intro k
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm]
    have h1 : (ωu ^ n : ℂˣ) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one, hωu_val]
      exact hω.pow_eq_one
    rw [pow_mul, h1, one_pow]
  let χAt : ℕ → DirichletCharacter ℂ p := fun k =>
    MulChar.ofRootOfUnity (M := ZMod p) (R := ℂ) (ζ := ωu ^ k)
      (by rw [hn_units]; exact hωu_roots k) hg_zpow
  have hχAt_g : ∀ k : ℕ, χAt k ((g : (ZMod p)ˣ) : ZMod p) = ω ^ k := fun k => by
    simp only [χAt]
    rw [MulChar.ofRootOfUnity_spec]
    simp [Units.val_pow_eq_pow_val, hωu_val]
  have hχAt_u : ∀ k : ℕ, χAt k (u : ZMod p) = ω ^ (k * a) := fun k => by
    have hu_eq : (u : ZMod p) = ((g : (ZMod p)ˣ) : ZMod p) ^ a := by
      rw [← Units.val_pow_eq_pow_val, ha]
    rw [hu_eq, map_pow, hχAt_g, ← pow_mul]
  have hχAt_inj : Set.InjOn χAt ↑(Finset.range n) := by
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    have hval : χAt j ((g : (ZMod p)ˣ) : ZMod p) = χAt k ((g : (ZMod p)ˣ) : ZMod p) := by
      rw [hjk]
    rw [hχAt_g, hχAt_g] at hval
    exact hω.pow_inj hj hk hval
  have hχAt_surj_onto_univ :
      Finset.image χAt (Finset.range n) = (Finset.univ : Finset (DirichletCharacter ℂ p)) := by
    apply Finset.eq_of_subset_of_card_le
    · exact fun _ _ => Finset.mem_univ _
    · rw [Finset.card_image_of_injOn hχAt_inj, Finset.card_range, Finset.card_univ,
        ← Nat.card_eq_fintype_card]
  have h_transfer : ∏ χ : DirichletCharacter ℂ p, (1 - χ (u : ZMod p) * T) =
      ∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T) := by
    calc ∏ χ : DirichletCharacter ℂ p, (1 - χ (u : ZMod p) * T)
        = ∏ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)),
            (1 - χ (u : ZMod p) * T) := rfl
      _ = ∏ χ ∈ Finset.image χAt (Finset.range n), (1 - χ (u : ZMod p) * T) := by
          rw [hχAt_surj_onto_univ]
      _ = ∏ k ∈ Finset.range n, (1 - (χAt k) (u : ZMod p) * T) := by
          rw [Finset.prod_image hχAt_inj]
      _ = ∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T) := by
          refine Finset.prod_congr rfl (fun k _ => ?_)
          rw [hχAt_u k]
  rw [h_transfer, prod_pow_primRoot_eq_pow hn_pos a hω T, ← hd_eq, hn_div_d]

lemma charLocalFactor_prime_ne_p_via_unit_order {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) {s : ℂ} :
    charLocalFactor (p := p) ℓ s =
      (1 - ((ℓ : ℂ) ^ (-s)) ^ localResidueDegree (p := p) ℓ hℓp) ^
        (Nat.card (DirichletCharacter ℂ p) / localResidueDegree (p := p) ℓ hℓp) := by
  have hval : ((unitOfPrimeNe p ℓ hℓp : (ZMod p)ˣ) : ZMod p) = (ℓ : ZMod p) := by
    simp [unitOfPrimeNe]
  unfold charLocalFactor
  rw [← hval]
  unfold localResidueDegree
  exact prod_characters_eval_eq_pow p (unitOfPrimeNe p ℓ hℓp) ((ℓ : ℂ) ^ (-s))

lemma charLocalFactor_eq_pow_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) {s : ℂ} :
    charLocalFactor (p := p) ℓ s =
      (1 - (ℓ : ℂ) ^ (-(localResidueDegree (p := p) ℓ hℓp : ℂ) * s)) ^
        localPrimeCount (p := p) ℓ hℓp := by
  rw [charLocalFactor_prime_ne_p_via_unit_order (p := p) hℓp,
    show ((ℓ : ℂ) ^ (-s)) ^ localResidueDegree (p := p) ℓ hℓp =
        (ℓ : ℂ) ^ (-((localResidueDegree (p := p) ℓ hℓp : ℂ)) * s) by
      rw [show -((localResidueDegree (p := p) ℓ hℓp : ℂ)) * s =
          (-s) * ((localResidueDegree (p := p) ℓ hℓp : ℕ) : ℂ) by ring,
        Complex.cpow_mul_nat]]
  rfl

/-- At `ℓ = p`, every Dirichlet character `χ` mod `p` vanishes at `(p: ZMod p) = 0`
(since `0` is not a unit), so each factor `(1 - χ(p)·p^{-s})` equals `1` and the
full character-side local factor is `1`. This differs from the Dedekind-side
local factor `1 - p^{-s}` by exactly the `(1 - p^{-s})` factor distinguishing
`LFunctionTrivChar p s` from the primitive `ζ(s)`.-/
lemma charLocalFactor_at_p {s : ℂ} :
    charLocalFactor (p := p) p s = 1 :=
  Finset.prod_eq_one fun χ _ => by
    rw [ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, sub_zero]

/-! ### Step D — Dedekind-side local factor skeleton -/

lemma mem_primesOverFinset_iff {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 K)} :
    P ∈ primesOverFinset K ℓ ↔ P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
  have : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 K)

lemma zetaInteger_isIntegralGenerator :
    Algebra.adjoin ℤ ({zetaInteger (p := p) (K := K)} : Set (𝓞 K)) = ⊤ := by
  exact IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (IsCyclotomicExtension.zeta_spec p ℚ K)

lemma zetaInteger_exponent_eq_one :
    RingOfIntegers.exponent (zetaInteger (p := p) (K := K)) = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr (zetaInteger_isIntegralGenerator (p := p) (K := K))

lemma prime_not_dvd_zetaInteger_exponent {ℓ : ℕ} [Fact ℓ.Prime] :
    ¬ ℓ ∣ RingOfIntegers.exponent (zetaInteger (p := p) (K := K)) := by
  rw [zetaInteger_exponent_eq_one]
  exact Nat.Prime.not_dvd_one (Fact.out : ℓ.Prime)

noncomputable def primesOverEquivMonicFactorsMod (ℓ : ℕ) [Fact ℓ.Prime] :
  Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) ≃
      RingOfIntegers.monicFactorsMod (θ := zetaInteger (p := p) (K := K)) (p := ℓ) :=
  NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K := K) (θ := zetaInteger (p := p) (K := K))
    (p := ℓ) (prime_not_dvd_zetaInteger_exponent (p := p) (K := K) (ℓ := ℓ))

lemma monicFactorsMod_card_eq_localPrimeCount {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (RingOfIntegers.monicFactorsMod (θ := zetaInteger (p := p) (K := K)) (p := ℓ)).card =
      localPrimeCount (p := p) ℓ hℓp := by
  classical
  have hmin : minpoly ℤ (zetaInteger (p := p) (K := K)) = cyclotomic p ℤ := by
    rw [zetaInteger, ← NumberField.RingOfIntegers.minpoly_coe]
    exact (Polynomial.cyclotomic_eq_minpoly (IsCyclotomicExtension.zeta_spec p ℚ K)
      hp.out.pos).symm
  have hcop : ℓ.Coprime p := (coprime_of_prime_ne (p := p) hℓp).symm
  have hFcard : Fintype.card (ZMod ℓ) = ℓ ^ 1 := by
    rw [pow_one]; exact ZMod.card ℓ
  unfold RingOfIntegers.monicFactorsMod
  rw [hmin, Polynomial.map_cyclotomic_int,
    Polynomial.normalizedFactors_cyclotomic_card hFcard hcop]
  unfold localPrimeCount localResidueDegree unitOfPrimeNe
  rw [card_dirichletCharacter_complex (p := p), Nat.totient_prime hp.out,
    ← orderOf_units (y := ZMod.unitOfCoprime _ _),
    ← orderOf_units (y := ZMod.unitOfCoprime ℓ _), ZMod.coe_unitOfCoprime,
    ZMod.coe_unitOfCoprime, pow_one]

lemma ncard_primesOver_at_p_eq_one :
    (Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K)).ncard = 1 :=
  IsCyclotomicExtension.Rat.ncard_primesOver_of_prime p K

lemma primesOver_inertiaDeg_eq_one_at_p (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K)) :
    P.inertiaDeg ℤ = 1 := by
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hP.2
  simpa [rationalPrimeIdeal] using IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime p K P

lemma primesOver_inertiaDeg_eq_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)) :
    P.inertiaDeg ℤ = localResidueDegree (p := p) ℓ hℓp := by
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := hP.2
  have hcop : ¬ ℓ ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq
    (Fact.out : ℓ.Prime) hp.out).mp h)
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd ℓ K P hcop]
  unfold localResidueDegree unitOfPrimeNe
  rw [← orderOf_units]
  rfl

lemma primesOver_ramificationIdx_eq_one {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)) :
    P.ramificationIdx ℤ = 1 := by
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := hP.2
  have hcop : ¬ ℓ ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq
    (Fact.out : ℓ.Prime) hp.out).mp h)
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd ℓ K P hcop

lemma ncard_primesOver_eq_localPrimeCount {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)).ncard =
      localPrimeCount (p := p) ℓ hℓp := by
  classical
  rw [← monicFactorsMod_card_eq_localPrimeCount (p := p) (K := K) hℓp,
    ← Nat.card_coe_set_eq, Nat.card_congr (primesOverEquivMonicFactorsMod (p := p) (K := K) ℓ),
    Nat.card_eq_finsetCard]

lemma dedekindLocalFactor_eq_pow_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) {s : ℂ} :
    dedekindLocalFactor K ℓ s =
      (1 - (ℓ : ℂ) ^ (-(localResidueDegree (p := p) ℓ hℓp : ℂ) * s)) ^
        localPrimeCount (p := p) ℓ hℓp := by
  classical
  have : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hcoe := IsDedekindDomain.coe_primesOverFinset (p := rationalPrimeIdeal ℓ) hne (𝓞 K)
  have hcard_eq : (primesOverFinset K ℓ).card = localPrimeCount (p := p) ℓ hℓp := by
    have h1 := ncard_primesOver_eq_localPrimeCount p K hℓp
    rw [← hcoe, Set.ncard_coe_finset] at h1
    exact h1
  unfold dedekindLocalFactor
  have hprod_eq : ∀ P ∈ primesOverFinset K ℓ,
      (1 - (Ideal.absNorm P : ℂ) ^ (-s)) =
        1 - (ℓ : ℂ) ^ (-(localResidueDegree (p := p) ℓ hℓp : ℂ) * s) := by
    intro P hP
    have hPmem : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
      have : (P : Ideal _) ∈
          (↑(IsDedekindDomain.primesOverFinset (rationalPrimeIdeal ℓ) (𝓞 K)) : Set _) :=
        hP
      rwa [hcoe] at this
    have : P.IsPrime := hPmem.1
    have : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := hPmem.2
    have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(ℓ : ℤ)})
    have habsNorm : Ideal.absNorm P = ℓ ^ (localResidueDegree (p := p) ℓ hℓp) := by
      rw [← primesOver_inertiaDeg_eq_localResidueDegree p K hℓp P hPmem]
      exact (Ideal.pow_inertiaDeg ℓ P).symm
    rw [habsNorm]
    push_cast
    have := Complex.natCast_cpow_natCast_mul ℓ (localResidueDegree (p := p) ℓ hℓp) (-s)
    rw [show -((localResidueDegree (p := p) ℓ hℓp : ℂ)) * s =
        ((localResidueDegree (p := p) ℓ hℓp : ℕ) : ℂ) * (-s) by ring,
      this]
  rw [Finset.prod_congr rfl hprod_eq, Finset.prod_const, hcard_eq]

lemma dedekindLocalFactor_at_p {s : ℂ} :
    dedekindLocalFactor K p s = 1 - (p : ℂ) ^ (-s) := by
  classical
  unfold dedekindLocalFactor primesOverFinset rationalPrimeIdeal
  have hne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hcoe :=
    IsDedekindDomain.coe_primesOverFinset (p := (Ideal.span {(p : ℤ)} : Ideal ℤ)) hne (𝓞 K)
  have hcard : (IsDedekindDomain.primesOverFinset
      (Ideal.span {(p : ℤ)} : Ideal ℤ) (𝓞 K)).card = 1 := by
    have hncard : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard = 1 := by
      simpa [rationalPrimeIdeal] using ncard_primesOver_at_p_eq_one (p := p) (K := K)
    rw [← hcoe] at hncard
    simpa using hncard
  obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hcard
  rw [hP, Finset.prod_singleton]
  have hPmem : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [← hcoe, hP]
    exact Finset.mem_singleton_self P
  have : P.IsPrime := hPmem.1
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := hPmem.2
  have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  have habsNorm : Ideal.absNorm P = p ^ (1 : ℕ) := by
    have hP' : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) := by
      simpa [rationalPrimeIdeal] using hPmem
    rw [← primesOver_inertiaDeg_eq_one_at_p (p := p) (K := K) P hP']
    exact (Ideal.pow_inertiaDeg p P).symm
  rw [habsNorm]
  push_cast
  rw [pow_one]

end ZetaFactorisation

end KummerCriterion
