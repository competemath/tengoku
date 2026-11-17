/-
Binary rigidity of the complete three-row CRT triangle.

The branch targets in the inert quartic skeleton are `p` and `p^3`.
Odd powers preserve the exact depth of `p^2 - 1`.  Since the concrete
row modulus contains one additional power of two, any pairwise CRT
compatibility forces equality of the two depths.  Hence a complete
three-row triangle has one common binary depth.

At the next binary level, the two row targets have the exact normal forms
`p` and `p + 2^b`.  Thus the row labels determine the complete binary ray.
None of these theorems asserts that the remaining odd Kummer tails are
incompatible.
-/
import Tengoku.AgrawalR5.AgrawalCore.CyclotomicDyadic
import Tengoku.AgrawalR5.AgrawalCore.TwoRowTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- Exact 2-adic depths agree when two positive residues are congruent one
level beyond the smaller depth.-/
theorem exactTwoDepth_eq_of_modEq {a b α β : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha0 : 2 ^ α ∣ a ^ 2 - 1)
    (ha1 : ¬ 2 ^ (α + 1) ∣ a ^ 2 - 1)
    (hb0 : 2 ^ β ∣ b ^ 2 - 1)
    (hb1 : ¬ 2 ^ (β + 1) ∣ b ^ 2 - 1)
    (hmod : a ≡ b [MOD 2 ^ (min α β + 1)]) : α = β := by
  rcases lt_trichotomy α β with hlt | heq | hgt
  · have hmin : min α β = α := min_eq_left (Nat.le_of_lt hlt)
    have hmod' : a ≡ b [MOD 2 ^ (α + 1)] := by
      simpa [hmin] using hmod
    have hsq : a ^ 2 ≡ b ^ 2 [MOD 2 ^ (α + 1)] := hmod'.pow 2
    have hpow : 2 ^ (α + 1) ∣ 2 ^ β := pow_dvd_pow 2 hlt
    have hbdiv : 2 ^ (α + 1) ∣ b ^ 2 - 1 := hpow.trans hb0
    have hbmod : b ^ 2 ≡ 1 [MOD 2 ^ (α + 1)] :=
      (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ b ^ 2)).mpr hbdiv |>.symm
    have hamod : a ^ 2 ≡ 1 [MOD 2 ^ (α + 1)] := hsq.trans hbmod
    exact (ha1 ((Nat.modEq_iff_dvd'
      (by nlinarith : 1 ≤ a ^ 2)).mp hamod.symm)).elim
  · exact heq
  · have hmin : min α β = β := min_eq_right (Nat.le_of_lt hgt)
    have hmod' : b ≡ a [MOD 2 ^ (β + 1)] := by
      simpa [hmin] using hmod.symm
    have hsq : b ^ 2 ≡ a ^ 2 [MOD 2 ^ (β + 1)] := hmod'.pow 2
    have hpow : 2 ^ (β + 1) ∣ 2 ^ α := pow_dvd_pow 2 hgt
    have hadiv : 2 ^ (β + 1) ∣ a ^ 2 - 1 := hpow.trans ha0
    have hamod : a ^ 2 ≡ 1 [MOD 2 ^ (β + 1)] :=
      (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ a ^ 2)).mpr hadiv |>.symm
    have hbmod : b ^ 2 ≡ 1 [MOD 2 ^ (β + 1)] := hsq.trans hamod
    exact (hb1 ((Nat.modEq_iff_dvd'
      (by nlinarith : 1 ≤ b ^ 2)).mp hbmod.symm)).elim

/-- Cubing an odd residue does not change the exact two-primary depth of
its square minus one.-/
theorem exactTwoDepth_cube {p b : ℕ} (hp : 1 ≤ p) (hpodd : Odd p)
    (h0 : 2 ^ b ∣ p ^ 2 - 1)
    (h1 : ¬ 2 ^ (b + 1) ∣ p ^ 2 - 1) :
    2 ^ b ∣ (p ^ 3) ^ 2 - 1 ∧
      ¬ 2 ^ (b + 1) ∣ (p ^ 3) ^ 2 - 1 := by
  have hid : (p ^ 3) ^ 2 - 1 =
      (p ^ 2 - 1) * (p ^ 4 + p ^ 2 + 1) := by
    have hp2 : 1 ≤ p ^ 2 := by nlinarith
    rw [Nat.sub_mul]
    ring_nf
    omega
  have hoddC : Odd (p ^ 4 + p ^ 2 + 1) := by
    rw [Nat.odd_iff]
    have hpm : p % 2 = 1 := Nat.odd_iff.mp hpodd
    simp [Nat.add_mod, Nat.pow_mod, hpm]
  have hcop : Nat.Coprime
      (2 ^ (b + 1)) (p ^ 4 + p ^ 2 + 1) :=
    (Nat.coprime_two_left.mpr hoddC).pow_left _
  constructor
  · rw [hid]
    exact dvd_mul_of_dvd_left h0 _
  · rw [hid]
    intro hd
    exact h1 (hcop.dvd_of_dvd_mul_right hd)

/-- At its exact two-primary depth `b`, an odd square is the nontrivial
lift of one from `2^b` to `2^(b+1)`.-/
theorem square_modEq_one_add_exactTwoPower {p : ℕ} (hp : 2 ≤ p) :
    let b := (p ^ 2 - 1).factorization 2
    p ^ 2 ≡ 1 + 2 ^ b [MOD 2 ^ (b + 1)] := by
  dsimp only
  let d := p ^ 2 - 1
  let b := d.factorization 2
  let c := ordCompl[2] d
  change p ^ 2 ≡ 1 + 2 ^ b [MOD 2 ^ (b + 1)]
  have hp2ge : 4 ≤ p ^ 2 := by nlinarith
  have hd0 : d ≠ 0 := by
    dsimp [d]
    omega
  have hsplit : 2 ^ b * c = d := Nat.ordProj_mul_ordCompl_eq_self d 2
  have hcodd : Odd c :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hd0)
  obtain ⟨k, hk⟩ := hcodd
  have hdecomp :
      p ^ 2 = 2 ^ (b + 1) * k + (1 + 2 ^ b) := by
    calc
      p ^ 2 = d + 1 := by dsimp [d]; omega
      _ = 2 ^ b * c + 1 := by rw [hsplit]
      _ = 2 ^ (b + 1) * k + (1 + 2 ^ b) := by
        rw [hk, pow_succ]
        ring
  rw [hdecomp]
  exact Nat.ModEq.modulus_mul_add

/-- Cubing shifts an odd base by exactly half the next binary modulus.-/
theorem cube_modEq_base_add_exactTwoPower {p : ℕ}
    (hp : 2 ≤ p) (hpodd : Odd p) :
    let b := (p ^ 2 - 1).factorization 2
    p ^ 3 ≡ p + 2 ^ b [MOD 2 ^ (b + 1)] := by
  dsimp only
  let b := (p ^ 2 - 1).factorization 2
  change p ^ 3 ≡ p + 2 ^ b [MOD 2 ^ (b + 1)]
  have hsq := square_modEq_one_add_exactTwoPower hp
  dsimp only at hsq
  have hmul := hsq.mul_left p
  obtain ⟨k, hk⟩ := hpodd
  have hpbit : p * 2 ^ b ≡ 2 ^ b [MOD 2 ^ (b + 1)] := by
    have hdecomp : p * 2 ^ b = 2 ^ (b + 1) * k + 2 ^ b := by
      rw [hk, pow_succ]
      ring
    rw [hdecomp]
    exact Nat.ModEq.modulus_mul_add
  have hadd : p + p * 2 ^ b ≡ p + 2 ^ b [MOD 2 ^ (b + 1)] :=
    (Nat.ModEq.refl p).add hpbit
  calc
    p ^ 3 = p * p ^ 2 := by ring
    _ ≡ p * (1 + 2 ^ b) [MOD 2 ^ (b + 1)] := hmul
    _ = p + p * 2 ^ b := by ring
    _ ≡ p + 2 ^ b [MOD 2 ^ (b + 1)] := hadd

/-- Binary label of the two allowed quartic row targets.-/
def quarticTargetBit (e : ℕ) : ℕ := if e = 3 then 1 else 0

/-- Exact normal form of either allowed quartic target at the first level
above its square depth.-/
theorem rowTarget_modEq_base_add_bit {p e : ℕ}
    (he : e = 1 ∨ e = 3) (hp : 2 ≤ p) (hpodd : Odd p) :
    let b := (p ^ 2 - 1).factorization 2
    p ^ e ≡ p + quarticTargetBit e * 2 ^ b [MOD 2 ^ (b + 1)] := by
  rcases he with rfl | rfl
  · simpa [quarticTargetBit] using
      (Nat.ModEq.refl p :
        p ≡ p [MOD 2 ^ ((p ^ 2 - 1).factorization 2 + 1)])
  · simpa [quarticTargetBit] using
      cube_modEq_base_add_exactTwoPower hp hpodd

/-- The two possible row targets, `p` and `p^3`, have the same exact
two-primary depth.-/
theorem rowTarget_exactTwoDepth {p e : ℕ} (hp : 3 ≤ p)
    (hpodd : Odd p) (he : e = 1 ∨ e = 3) :
    let b := (p ^ 2 - 1).factorization 2
    2 ^ b ∣ (p ^ e) ^ 2 - 1 ∧
      ¬ 2 ^ (b + 1) ∣ (p ^ e) ^ 2 - 1 := by
  dsimp only
  have hp2ge : 9 ≤ p ^ 2 := by nlinarith
  have hp2ne : p ^ 2 - 1 ≠ 0 := by omega
  have h0 : 2 ^ ((p ^ 2 - 1).factorization 2) ∣ p ^ 2 - 1 :=
    Nat.ordProj_dvd _ _
  have h1 : ¬ 2 ^ ((p ^ 2 - 1).factorization 2 + 1) ∣ p ^ 2 - 1 := by
    intro hdvd
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization
      Nat.prime_two hp2ne).mp hdvd
    omega
  rcases he with rfl | rfl
  · simpa using And.intro h0 h1
  · exact exactTwoDepth_cube (by omega) hpodd h0 h1

/-- A dyadic power contained in both order moduli transfers a target
congruence to the exact depth-comparison modulus.-/
theorem rowTargets_force_equal_dyadicDepth
    {p q ep eq Tp Tq : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hpodd : Odd p) (hqodd : Odd q)
    (hep : ep = 1 ∨ ep = 3) (heq : eq = 1 ∨ eq = 3)
    (hTp : 2 ^ ((p ^ 2 - 1).factorization 2 + 1) ∣ Tp)
    (hTq : 2 ^ ((q ^ 2 - 1).factorization 2 + 1) ∣ Tq)
    (hmod : p ^ ep ≡ q ^ eq [MOD Nat.gcd Tp Tq]) :
    (p ^ 2 - 1).factorization 2 =
      (q ^ 2 - 1).factorization 2 := by
  let bp := (p ^ 2 - 1).factorization 2
  let bq := (q ^ 2 - 1).factorization 2
  have hpdepth := rowTarget_exactTwoDepth hp hpodd hep
  have hqdepth := rowTarget_exactTwoDepth hq hqodd heq
  have hpowp : 2 ^ (min bp bq + 1) ∣ Tp := by
    apply dvd_trans (pow_dvd_pow 2 ?_) hTp
    omega
  have hpowq : 2 ^ (min bp bq + 1) ∣ Tq := by
    apply dvd_trans (pow_dvd_pow 2 ?_) hTq
    omega
  have htarget : p ^ ep ≡ q ^ eq [MOD 2 ^ (min bp bq + 1)] :=
    hmod.of_dvd (Nat.dvd_gcd hpowp hpowq)
  exact exactTwoDepth_eq_of_modEq
    (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by omega))
    hpdepth.1 hpdepth.2 hqdepth.1 hqdepth.2 htarget

/-- Once the exact binary depth is fixed, either allowed target `p` or
`p^3` reduces to the same base residue modulo that depth.-/
theorem rowTarget_modEq_base {p e b : ℕ} (he : e = 1 ∨ e = 3)
    (hp : 1 ≤ p) (hdepth : 2 ^ b ∣ p ^ 2 - 1) :
    p ^ e ≡ p [MOD 2 ^ b] := by
  rcases he with rfl | rfl
  · simpa using (Nat.ModEq.refl p : p ≡ p [MOD 2 ^ b])
  · have hsq : p ^ 2 ≡ 1 [MOD 2 ^ b] :=
      (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ p ^ 2)).mpr hdepth |>.symm
    have hmul := hsq.mul_left p
    simpa [pow_succ, mul_assoc] using hmul

/-- **Single dyadic ray for a compatible pair.**

Pairwise target compatibility first forces equality of exact binary
depths and then puts the two underlying prime residues in the same class
modulo that common depth.-/
theorem rowTargets_force_same_dyadicRay
    {p q ep eq Tp Tq : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hpodd : Odd p) (hqodd : Odd q)
    (hep : ep = 1 ∨ ep = 3) (heq : eq = 1 ∨ eq = 3)
    (hTp : 2 ^ ((p ^ 2 - 1).factorization 2 + 1) ∣ Tp)
    (hTq : 2 ^ ((q ^ 2 - 1).factorization 2 + 1) ∣ Tq)
    (hmod : p ^ ep ≡ q ^ eq [MOD Nat.gcd Tp Tq]) :
    let b := (p ^ 2 - 1).factorization 2
    (p ^ 2 - 1).factorization 2 =
        (q ^ 2 - 1).factorization 2
      ∧ p ≡ q [MOD 2 ^ b] := by
  dsimp only
  have hbeq := rowTargets_force_equal_dyadicDepth hp hq hpodd hqodd
    hep heq hTp hTq hmod
  let b := (p ^ 2 - 1).factorization 2
  have hpowp : 2 ^ b ∣ Tp := by
    apply dvd_trans (pow_dvd_pow 2 (by omega)) hTp
  have hpowq : 2 ^ b ∣ Tq := by
    apply dvd_trans (pow_dvd_pow 2 ?_) hTq
    rw [← hbeq]
    omega
  have htargets : p ^ ep ≡ q ^ eq [MOD 2 ^ b] :=
    hmod.of_dvd (Nat.dvd_gcd hpowp hpowq)
  have hpbase : p ^ ep ≡ p [MOD 2 ^ b] :=
    rowTarget_modEq_base hep (by omega) (Nat.ordProj_dvd _ _)
  have hqbase : q ^ eq ≡ q [MOD 2 ^ b] := by
    apply rowTarget_modEq_base heq (by omega)
    have hqord : 2 ^ ((q ^ 2 - 1).factorization 2) ∣ q ^ 2 - 1 :=
      Nat.ordProj_dvd _ _
    simpa [b, hbeq] using hqord
  exact ⟨hbeq, hpbase.symm.trans (htargets.trans hqbase)⟩

/-- **Exact labelled dyadic ray for a compatible pair.**

The target label records the unique half-modulus translation at level
`2^(b+1)`.  This is the complete binary information carried by a pairwise
quartic target congruence.-/
theorem rowTargets_force_exact_dyadicRay
    {p q ep eq Tp Tq : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hpodd : Odd p) (hqodd : Odd q)
    (hep : ep = 1 ∨ ep = 3) (heq : eq = 1 ∨ eq = 3)
    (hTp : 2 ^ ((p ^ 2 - 1).factorization 2 + 1) ∣ Tp)
    (hTq : 2 ^ ((q ^ 2 - 1).factorization 2 + 1) ∣ Tq)
    (hmod : p ^ ep ≡ q ^ eq [MOD Nat.gcd Tp Tq]) :
    let b := (p ^ 2 - 1).factorization 2
    (p ^ 2 - 1).factorization 2 =
        (q ^ 2 - 1).factorization 2
      ∧ p + quarticTargetBit ep * 2 ^ b ≡
        q + quarticTargetBit eq * 2 ^ b [MOD 2 ^ (b + 1)] := by
  dsimp only
  have hbeq := rowTargets_force_equal_dyadicDepth hp hq hpodd hqodd
    hep heq hTp hTq hmod
  let b := (p ^ 2 - 1).factorization 2
  have hpowp : 2 ^ (b + 1) ∣ Tp := by
    simpa [b] using hTp
  have hpowq : 2 ^ (b + 1) ∣ Tq := by
    simpa [b, hbeq] using hTq
  have htargets : p ^ ep ≡ q ^ eq [MOD 2 ^ (b + 1)] :=
    hmod.of_dvd (Nat.dvd_gcd hpowp hpowq)
  have hpnormal := rowTarget_modEq_base_add_bit hep (by omega) hpodd
  have hqnormal := rowTarget_modEq_base_add_bit heq (by omega) hqodd
  dsimp only at hpnormal hqnormal
  exact ⟨hbeq, hpnormal.symm.trans (htargets.trans (by
    simpa [b, hbeq] using hqnormal))⟩

/-- Concrete pairwise form for the quartic row moduli.-/
theorem quarticRowTargets_force_equal_dyadicDepth
    {p q ep eq : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hp5 : p ≠ 5) (hq5 : q ≠ 5)
    (hep : ep = 1 ∨ ep = 3) (heq : eq = 1 ∨ eq = 3)
    (hmod : p ^ ep ≡ q ^ eq
      [MOD Nat.gcd (quarticOrderModulus p hp5)
        (quarticOrderModulus q hq5)]) :
    (p ^ 2 - 1).factorization 2 =
      (q ^ 2 - 1).factorization 2 := by
  have hpge : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hqge : 3 ≤ q := by
    have := (Fact.out : q.Prime).two_le
    omega
  exact rowTargets_force_equal_dyadicDepth hpge hqge
    ((Fact.out : p.Prime).odd_of_ne_two hp2)
    ((Fact.out : q.Prime).odd_of_ne_two hq2)
    hep heq
    (by simpa [pow_two] using
      twoPow_dvd_quarticOrderModulus hp hp2 hp5)
    (by simpa [pow_two] using
      twoPow_dvd_quarticOrderModulus hq hq2 hq5)
    hmod

/-- Concrete single-ray form for the quartic row moduli.-/
theorem quarticRowTargets_force_same_dyadicRay
    {p q ep eq : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hp5 : p ≠ 5) (hq5 : q ≠ 5)
    (hep : ep = 1 ∨ ep = 3) (heq : eq = 1 ∨ eq = 3)
    (hmod : p ^ ep ≡ q ^ eq
      [MOD Nat.gcd (quarticOrderModulus p hp5)
        (quarticOrderModulus q hq5)]) :
    let b := (p ^ 2 - 1).factorization 2
    (p ^ 2 - 1).factorization 2 =
        (q ^ 2 - 1).factorization 2
      ∧ p ≡ q [MOD 2 ^ b] := by
  have hpge : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hqge : 3 ≤ q := by
    have := (Fact.out : q.Prime).two_le
    omega
  exact rowTargets_force_same_dyadicRay hpge hqge
    ((Fact.out : p.Prime).odd_of_ne_two hp2)
    ((Fact.out : q.Prime).odd_of_ne_two hq2)
    hep heq
    (by simpa [pow_two] using
      twoPow_dvd_quarticOrderModulus hp hp2 hp5)
    (by simpa [pow_two] using
      twoPow_dvd_quarticOrderModulus hq hq2 hq5)
    hmod

/-- Concrete exact labelled-ray form for the quartic row moduli.-/
theorem quarticRowTargets_force_exact_dyadicRay
    {p q ep eq : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hp5 : p ≠ 5) (hq5 : q ≠ 5)
    (hep : ep = 1 ∨ ep = 3) (heq : eq = 1 ∨ eq = 3)
    (hmod : p ^ ep ≡ q ^ eq
      [MOD Nat.gcd (quarticOrderModulus p hp5)
        (quarticOrderModulus q hq5)]) :
    let b := (p ^ 2 - 1).factorization 2
    (p ^ 2 - 1).factorization 2 =
        (q ^ 2 - 1).factorization 2
      ∧ p + quarticTargetBit ep * 2 ^ b ≡
        q + quarticTargetBit eq * 2 ^ b [MOD 2 ^ (b + 1)] := by
  have hpge : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hqge : 3 ≤ q := by
    have := (Fact.out : q.Prime).two_le
    omega
  exact rowTargets_force_exact_dyadicRay hpge hqge
    ((Fact.out : p.Prime).odd_of_ne_two hp2)
    ((Fact.out : q.Prime).odd_of_ne_two hq2)
    hep heq
    (by simpa [pow_two] using
      twoPow_dvd_quarticOrderModulus hp hp2 hp5)
    (by simpa [pow_two] using
      twoPow_dvd_quarticOrderModulus hq hq2 hq5)
    hmod

/-- **Common binary depth of a complete three-row triangle.**

Two target compatibilities force all three prime factors to have the same
value of `v_2(p^2 - 1)`.  All remaining freedom lies in odd components
of the order moduli.-/
theorem quarticTriangle_common_dyadicDepth
    {p q r ep eq er : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hr2 : r ≠ 2)
    (hp5 : p ≠ 5) (hq5 : q ≠ 5) (hr5 : r ≠ 5)
    (hep : ep = 1 ∨ ep = 3) (heq : eq = 1 ∨ eq = 3)
    (her : er = 1 ∨ er = 3)
    (hpq : p ^ ep ≡ q ^ eq
      [MOD Nat.gcd (quarticOrderModulus p hp5)
        (quarticOrderModulus q hq5)])
    (hqr : q ^ eq ≡ r ^ er
      [MOD Nat.gcd (quarticOrderModulus q hq5)
        (quarticOrderModulus r hr5)]) :
    (p ^ 2 - 1).factorization 2 =
        (q ^ 2 - 1).factorization 2
      ∧ (q ^ 2 - 1).factorization 2 =
        (r ^ 2 - 1).factorization 2 := by
  exact ⟨
    quarticRowTargets_force_equal_dyadicDepth
      hp hq hp2 hq2 hp5 hq5 hep heq hpq,
    quarticRowTargets_force_equal_dyadicDepth
      hq hr hq2 hr2 hq5 hr5 heq her hqr⟩

/-- **A complete target triangle lies on one dyadic ray.**

Besides sharing one exact binary depth, all three prime bases are
congruent modulo the corresponding power of two.  This classifies the
entire binary component; it does not constrain the remaining odd tails.-/
theorem quarticTriangle_single_dyadicRay
    {p q r ep eq er : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hr2 : r ≠ 2)
    (hp5 : p ≠ 5) (hq5 : q ≠ 5) (hr5 : r ≠ 5)
    (hep : ep = 1 ∨ ep = 3) (heq : eq = 1 ∨ eq = 3)
    (her : er = 1 ∨ er = 3)
    (hpq : p ^ ep ≡ q ^ eq
      [MOD Nat.gcd (quarticOrderModulus p hp5)
        (quarticOrderModulus q hq5)])
    (hqr : q ^ eq ≡ r ^ er
      [MOD Nat.gcd (quarticOrderModulus q hq5)
        (quarticOrderModulus r hr5)]) :
    let b := (p ^ 2 - 1).factorization 2
    (p ^ 2 - 1).factorization 2 =
        (q ^ 2 - 1).factorization 2
      ∧ (q ^ 2 - 1).factorization 2 =
        (r ^ 2 - 1).factorization 2
      ∧ p ≡ q [MOD 2 ^ b]
      ∧ q ≡ r [MOD 2 ^ b] := by
  dsimp only
  have hpqRay := quarticRowTargets_force_same_dyadicRay
    hp hq hp2 hq2 hp5 hq5 hep heq hpq
  have hqrRay := quarticRowTargets_force_same_dyadicRay
    hq hr hq2 hr2 hq5 hr5 heq her hqr
  dsimp only at hpqRay hqrRay
  refine ⟨hpqRay.1, hqrRay.1, hpqRay.2, ?_⟩
  simpa [hpqRay.1] using hqrRay.2

/-- **Complete labelled binary classification of a target triangle.**

At the common depth `b`, each row exponent contributes exactly its
`quarticTargetBit`; the corresponding translated prime residues all agree
modulo `2^(b+1)`.-/
theorem quarticTriangle_exact_dyadicRays
    {p q r ep eq er : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hr2 : r ≠ 2)
    (hp5 : p ≠ 5) (hq5 : q ≠ 5) (hr5 : r ≠ 5)
    (hep : ep = 1 ∨ ep = 3) (heq : eq = 1 ∨ eq = 3)
    (her : er = 1 ∨ er = 3)
    (hpq : p ^ ep ≡ q ^ eq
      [MOD Nat.gcd (quarticOrderModulus p hp5)
        (quarticOrderModulus q hq5)])
    (hqr : q ^ eq ≡ r ^ er
      [MOD Nat.gcd (quarticOrderModulus q hq5)
        (quarticOrderModulus r hr5)]) :
    let b := (p ^ 2 - 1).factorization 2
    (p ^ 2 - 1).factorization 2 =
        (q ^ 2 - 1).factorization 2
      ∧ (q ^ 2 - 1).factorization 2 =
        (r ^ 2 - 1).factorization 2
      ∧ p + quarticTargetBit ep * 2 ^ b ≡
        q + quarticTargetBit eq * 2 ^ b [MOD 2 ^ (b + 1)]
      ∧ q + quarticTargetBit eq * 2 ^ b ≡
        r + quarticTargetBit er * 2 ^ b [MOD 2 ^ (b + 1)] := by
  dsimp only
  have hpqRay := quarticRowTargets_force_exact_dyadicRay
    hp hq hp2 hq2 hp5 hq5 hep heq hpq
  have hqrRay := quarticRowTargets_force_exact_dyadicRay
    hq hr hq2 hr2 hq5 hr5 heq her hqr
  dsimp only at hpqRay hqrRay
  refine ⟨hpqRay.1, hqrRay.1, hpqRay.2, ?_⟩
  simpa [hpqRay.1] using hqrRay.2

/-- **Three literal arithmetic rows force one binary depth.**

Here `P` is the product of the two smaller factors and `q` is the final
factor.  The final row and each multiplied small row first give the two
target transports; the preceding theorem then identifies all three
two-primary depths.  This is the direct arithmetic interface used by the
`k = 3` system.-/
theorem quarticThreeRows_common_dyadicDepth
    {p r q jp jr jq P : ℕ}
    [Fact p.Prime] [Fact r.Prime] [Fact q.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hq2 : q ≠ 2)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hq5 : q ≠ 5)
    (hjp : jp = 0 ∨ jp = 2) (hjr : jr = 0 ∨ jr = 2)
    (hjq : jq = 0 ∨ jq = 2)
    (hfinal : P ≡ q ^ jq [MOD quarticOrderModulus q hq5])
    (hprow : P * q ≡ p ^ (jp + 1)
      [MOD quarticOrderModulus p hp5])
    (hrrow : P * q ≡ r ^ (jr + 1)
      [MOD quarticOrderModulus r hr5]) :
    (p ^ 2 - 1).factorization 2 =
        (q ^ 2 - 1).factorization 2
      ∧ (q ^ 2 - 1).factorization 2 =
        (r ^ 2 - 1).factorization 2 := by
  have hptransport := finalSmallRow_transport hfinal hprow
  have hrtransport := finalSmallRow_transport hfinal hrrow
  have hpq : p ^ (jp + 1) ≡ q ^ (jq + 1)
      [MOD Nat.gcd (quarticOrderModulus p hp5)
        (quarticOrderModulus q hq5)] := by
    simpa [pow_succ] using hptransport.symm
  have hqr : q ^ (jq + 1) ≡ r ^ (jr + 1)
      [MOD Nat.gcd (quarticOrderModulus q hq5)
        (quarticOrderModulus r hr5)] := by
    have h := hrtransport
    rw [Nat.gcd_comm] at h
    simpa [pow_succ] using h
  have hjp' : jp + 1 = 1 ∨ jp + 1 = 3 := by
    rcases hjp with rfl | rfl <;> simp
  have hjr' : jr + 1 = 1 ∨ jr + 1 = 3 := by
    rcases hjr with rfl | rfl <;> simp
  have hjq' : jq + 1 = 1 ∨ jq + 1 = 3 := by
    rcases hjq with rfl | rfl <;> simp
  exact quarticTriangle_common_dyadicDepth
    hp hq hr hp2 hq2 hr2 hp5 hq5 hr5
    hjp' hjq' hjr' hpq hqr

/-- **Three literal arithmetic rows lie on one dyadic ray.**

This is the direct `k = 3` arithmetic interface to the preceding
classification theorem.-/
theorem quarticThreeRows_single_dyadicRay
    {p r q jp jr jq P : ℕ}
    [Fact p.Prime] [Fact r.Prime] [Fact q.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hq2 : q ≠ 2)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hq5 : q ≠ 5)
    (hjp : jp = 0 ∨ jp = 2) (hjr : jr = 0 ∨ jr = 2)
    (hjq : jq = 0 ∨ jq = 2)
    (hfinal : P ≡ q ^ jq [MOD quarticOrderModulus q hq5])
    (hprow : P * q ≡ p ^ (jp + 1)
      [MOD quarticOrderModulus p hp5])
    (hrrow : P * q ≡ r ^ (jr + 1)
      [MOD quarticOrderModulus r hr5]) :
    let b := (p ^ 2 - 1).factorization 2
    (p ^ 2 - 1).factorization 2 =
        (q ^ 2 - 1).factorization 2
      ∧ (q ^ 2 - 1).factorization 2 =
        (r ^ 2 - 1).factorization 2
      ∧ p ≡ q [MOD 2 ^ b]
      ∧ q ≡ r [MOD 2 ^ b] := by
  have hptransport := finalSmallRow_transport hfinal hprow
  have hrtransport := finalSmallRow_transport hfinal hrrow
  have hpq : p ^ (jp + 1) ≡ q ^ (jq + 1)
      [MOD Nat.gcd (quarticOrderModulus p hp5)
        (quarticOrderModulus q hq5)] := by
    simpa [pow_succ] using hptransport.symm
  have hqr : q ^ (jq + 1) ≡ r ^ (jr + 1)
      [MOD Nat.gcd (quarticOrderModulus q hq5)
        (quarticOrderModulus r hr5)] := by
    have h := hrtransport
    rw [Nat.gcd_comm] at h
    simpa [pow_succ] using h
  have hjp' : jp + 1 = 1 ∨ jp + 1 = 3 := by
    rcases hjp with rfl | rfl <;> simp
  have hjr' : jr + 1 = 1 ∨ jr + 1 = 3 := by
    rcases hjr with rfl | rfl <;> simp
  have hjq' : jq + 1 = 1 ∨ jq + 1 = 3 := by
    rcases hjq with rfl | rfl <;> simp
  exact quarticTriangle_single_dyadicRay
    hp hq hr hp2 hq2 hr2 hp5 hq5 hr5
    hjp' hjq' hjr' hpq hqr

/-- **Three literal arithmetic rows have the exact labelled dyadic rays.**

This closes the binary component of the literal `k = 3` system in the
kernel.  Any remaining obstruction must use an odd component of the order
moduli.-/
theorem quarticThreeRows_exact_dyadicRays
    {p r q jp jr jq P : ℕ}
    [Fact p.Prime] [Fact r.Prime] [Fact q.Prime]
    (hp : p % 5 = 2 ∨ p % 5 = 3)
    (hr : r % 5 = 2 ∨ r % 5 = 3)
    (hq : q % 5 = 2 ∨ q % 5 = 3)
    (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hq2 : q ≠ 2)
    (hp5 : p ≠ 5) (hr5 : r ≠ 5) (hq5 : q ≠ 5)
    (hjp : jp = 0 ∨ jp = 2) (hjr : jr = 0 ∨ jr = 2)
    (hjq : jq = 0 ∨ jq = 2)
    (hfinal : P ≡ q ^ jq [MOD quarticOrderModulus q hq5])
    (hprow : P * q ≡ p ^ (jp + 1)
      [MOD quarticOrderModulus p hp5])
    (hrrow : P * q ≡ r ^ (jr + 1)
      [MOD quarticOrderModulus r hr5]) :
    let b := (p ^ 2 - 1).factorization 2
    (p ^ 2 - 1).factorization 2 =
        (q ^ 2 - 1).factorization 2
      ∧ (q ^ 2 - 1).factorization 2 =
        (r ^ 2 - 1).factorization 2
      ∧ p + quarticTargetBit (jp + 1) * 2 ^ b ≡
        q + quarticTargetBit (jq + 1) * 2 ^ b [MOD 2 ^ (b + 1)]
      ∧ q + quarticTargetBit (jq + 1) * 2 ^ b ≡
        r + quarticTargetBit (jr + 1) * 2 ^ b [MOD 2 ^ (b + 1)] := by
  have hptransport := finalSmallRow_transport hfinal hprow
  have hrtransport := finalSmallRow_transport hfinal hrrow
  have hpq : p ^ (jp + 1) ≡ q ^ (jq + 1)
      [MOD Nat.gcd (quarticOrderModulus p hp5)
        (quarticOrderModulus q hq5)] := by
    simpa [pow_succ] using hptransport.symm
  have hqr : q ^ (jq + 1) ≡ r ^ (jr + 1)
      [MOD Nat.gcd (quarticOrderModulus q hq5)
        (quarticOrderModulus r hr5)] := by
    have h := hrtransport
    rw [Nat.gcd_comm] at h
    simpa [pow_succ] using h
  have hjp' : jp + 1 = 1 ∨ jp + 1 = 3 := by
    rcases hjp with rfl | rfl <;> simp
  have hjr' : jr + 1 = 1 ∨ jr + 1 = 3 := by
    rcases hjr with rfl | rfl <;> simp
  have hjq' : jq + 1 = 1 ∨ jq + 1 = 3 := by
    rcases hjq with rfl | rfl <;> simp
  exact quarticTriangle_exact_dyadicRays
    hp hq hr hp2 hq2 hr2 hp5 hq5 hr5
    hjp' hjq' hjr' hpq hqr

end AgrawalCore
