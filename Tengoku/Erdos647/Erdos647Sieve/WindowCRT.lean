/-
Actual polynomial roots modulo a product of distinct primes.
New proof source: not compiled in the assistant environment.
CRT is a ring equivalence. No averaging, primality distribution, or analytic input is assumed.
-/
import Tengoku.Erdos647.Erdos647Sieve.IntegerWindowRoots
import Tengoku.Erdos647.Erdos647Sieve.PrimeSubsetProducts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

/-- The window expression evaluated in an arbitrary commutative ring.-/
def windowEvaluation {R : Type*} [CommRing R] (H : ℕ) (r : R) : R :=
  ∏ k ∈ Finset.Icc 1 H, (r - (k : R))

/-- Ring homomorphisms commute with the window evaluation.-/
theorem map_windowEvaluation {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (H : ℕ) (r : R) :
    f (windowEvaluation H r) = windowEvaluation H (f r) := by
  simp only [windowEvaluation, map_prod, map_sub, map_natCast]

theorem windowEvaluation_intCast (H d : ℕ) (n : ℤ) :
    (windowPolynomial H n : ZMod d) = windowEvaluation H (n : ZMod d) := by
  simp only [windowPolynomial, windowEvaluation, Int.cast_prod, Int.cast_sub,
    Int.cast_natCast]

/-- Representatives 0,...,d-1 filtered by the ACTUAL polynomial equation.
The definition needs no implicit Fintype/NeZero choice and is also defined at d=0.
Every counting theorem below explicitly requires a positive modulus.-/
def windowRootResidues (H d : ℕ) : Finset (ZMod d) := by
  classical
  exact ((Finset.range d).image (fun k : ℕ => (k : ZMod d))).filter
    (fun r : ZMod d => windowEvaluation H r = 0)

theorem mem_windowRootResidues (H d : ℕ) (hd : 0 < d) (r : ZMod d) :
    r ∈ windowRootResidues H d ↔ windowEvaluation H r = 0 := by
  classical
  letI : NeZero d := ⟨hd.ne'⟩
  have hm : r ∈ (Finset.range d).image (fun k : ℕ => (k : ZMod d)) :=
    Finset.mem_image.mpr ⟨r.val, Finset.mem_range.mpr (ZMod.val_lt r),
      ZMod.natCast_zmod_val r⟩
  simp only [windowRootResidues, Finset.mem_filter, hm, true_and]

/-- Integer casts belong to the root set exactly when the modulus divides F(n).-/
theorem intCast_mem_windowRootResidues_iff
    (H d : ℕ) (hd : 0 < d) (n : ℤ) :
    (n : ZMod d) ∈ windowRootResidues H d ↔
      (d : ℤ) ∣ windowPolynomial H n := by
  rw [mem_windowRootResidues H d hd,
    ← windowEvaluation_intCast H d n,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The new root set agrees with the accepted single-prime residue description.-/
theorem windowRootResidues_eq_primeWindowResidues
    (H p : ℕ) (hp : p.Prime) :
    windowRootResidues H p = primeWindowResidues H p := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply Finset.ext
  intro r
  have hr : ((r.val : ℤ) : ZMod p) = r := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  have heq := (intCast_mem_windowRootResidues_iff H p hp.pos (r.val : ℤ)).trans
    (prime_dvd_window_iff_mem_residues H p (r.val : ℤ) hp)
  simpa only [hr] using heq

theorem card_windowRootResidues_prime (H p : ℕ)
    (hp : p.Prime) (hHp : H < p) :
    (windowRootResidues H p).card = H := by
  rw [windowRootResidues_eq_primeWindowResidues H p hp]
  exact card_primeWindowResidues H p hHp

/-- The empty prime product gives the single residue modulo one, even for H=0.-/
theorem card_windowRootResidues_one (H : ℕ) :
    (windowRootResidues H 1).card = 1 := by
  classical
  unfold windowRootResidues
  rw [Finset.filter_eq_self.mpr (fun _r _hr => Subsingleton.elim _ _)]
  simp

private theorem windowEvaluation_fst {R T : Type*} [CommRing R] [CommRing T]
    (H : ℕ) (r : R × T) :
    (windowEvaluation H r).1 = windowEvaluation H r.1 := by
  exact map_windowEvaluation (RingHom.fst R T) H r

private theorem windowEvaluation_snd {R T : Type*} [CommRing R] [CommRing T]
    (H : ℕ) (r : R × T) :
    (windowEvaluation H r).2 = windowEvaluation H r.2 := by
  exact map_windowEvaluation (RingHom.snd R T) H r

/-- A CRT bijection restricts to a bijection between the polynomial root sets.-/
theorem card_windowRootResidues_mul (H m d : ℕ)
    (hm : 0 < m) (hd : 0 < d) (hcop : Nat.Coprime m d) :
    (windowRootResidues H (m * d)).card =
      (windowRootResidues H m).card * (windowRootResidues H d).card := by
  classical
  let e : ZMod (m * d) ≃+* ZMod m × ZMod d := ZMod.chineseRemainder hcop
  have hmem (r : ZMod (m * d)) :
      r ∈ windowRootResidues H (m * d) ↔
        e r ∈ (windowRootResidues H m) ×ˢ (windowRootResidues H d) := by
    rw [mem_windowRootResidues H (m * d) (Nat.mul_pos hm hd), Finset.mem_product,
      mem_windowRootResidues H m hm, mem_windowRootResidues H d hd]
    have hmap : e (windowEvaluation H r) = windowEvaluation H (e r) :=
      map_windowEvaluation e.toRingHom H r
    constructor
    · intro hz
      have hez : windowEvaluation H (e r) = 0 := by
        rw [← hmap, hz, map_zero]
      constructor
      · have hh := congrArg Prod.fst hez
        simpa only [windowEvaluation_fst, Prod.fst_zero] using hh
      · have hh := congrArg Prod.snd hez
        simpa only [windowEvaluation_snd, Prod.snd_zero] using hh
    · rintro ⟨hl, hr⟩
      apply e.injective
      rw [hmap, map_zero]
      apply Prod.ext
      · simpa only [windowEvaluation_fst, Prod.fst_zero] using hl
      · simpa only [windowEvaluation_snd, Prod.snd_zero] using hr
  calc
    (windowRootResidues H (m * d)).card =
        ((windowRootResidues H m) ×ˢ (windowRootResidues H d)).card :=
      Finset.card_equiv e.toEquiv hmem
    _ = _ := Finset.card_product _ _

/-- Exactly H^|S| roots modulo the product of any finite set of primes exceeding H.
The proof includes S=empty (modulus one) and H=0.-/
theorem card_windowRootResidues_primeSubsetProduct
    (H : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ H < p) :
    (windowRootResidues H (primeSubsetProduct S)).card = H ^ S.card := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty =>
    intro _hS
    simpa only [primeSubsetProduct, Finset.prod_empty, Finset.card_empty, pow_zero]
      using card_windowRootResidues_one H
  | @insert p S hp ih =>
    intro hS
    have hpp := hS p (Finset.mem_insert_self p S)
    have hSp : ∀ q ∈ S, q.Prime ∧ H < q :=
      fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hpr : ∀ q ∈ S, q.Prime := fun q hq => (hSp q hq).1
    have hd := primeSubsetProduct_pos S hpr
    have hcop : Nat.Coprime p (primeSubsetProduct S) := by
      apply hpp.1.coprime_iff_not_dvd.mpr
      intro hdiv
      exact hp ((prime_dvd_primeSubsetProduct_iff_mem S hpr p hpp.1).mp hdiv)
    have hprod : primeSubsetProduct (insert p S) = p * primeSubsetProduct S := by
      simp only [primeSubsetProduct, Finset.prod_insert hp]
    rw [hprod, card_windowRootResidues_mul H p (primeSubsetProduct S) hpp.1.pos hd hcop,
      card_windowRootResidues_prime H p hpp.1 hpp.2, ih hSp,
      Finset.card_insert_of_notMem hp, pow_succ]
    ring

end Erdos647Sieve
end
