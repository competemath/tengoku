/-
Unrestricted integer prime-root layer for the window polynomial.
New implementation source; not compiled in the assistant environment.
No H<n assumption, no evaluation of omega(0) or tau(0), and no CRT claim yet.
-/
import Tengoku.Erdos647.Erdos647Sieve.Specification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

/-- Prime factor extraction in the integer polynomial at EVERY integer n.
@isnad1 id=iff.1h3v.s6.61c3b4e47351 from=translated src=- shape=05629855 vocab=51abcee2
-/
theorem prime_dvd_window_iff_int (H p : ℕ) (n : ℤ) (hp : p.Prime) :
    (p : ℤ) ∣ windowPolynomial H n ↔
      ∃ k ∈ Finset.Icc 1 H, (p : ℤ) ∣ n - (k : ℤ) := by
  classical
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  constructor
  · intro hd
    exact hpz.exists_mem_finset_dvd hd
  · rintro ⟨k, hk, hdiv⟩
    exact hdiv.trans (Finset.dvd_prod_of_mem (fun k : ℕ => n - (k : ℤ)) hk)

/-- The H possible residue classes, represented without any assumption on n.-/
def primeWindowResidues (H p : ℕ) : Finset (ZMod p) := by
  classical
  exact (Finset.Icc 1 H).image (fun k : ℕ => (k : ZMod p))

/-- Congruence membership exactly characterizes the prime divisibility test.
@isnad1 id=iff.1h3v.s5.0143baedbff3 from=translated src=- shape=9f70b4dc vocab=94f7b9f6
-/
theorem prime_dvd_window_iff_mem_residues (H p : ℕ) (n : ℤ) (hp : p.Prime) :
    (p : ℤ) ∣ windowPolynomial H n ↔ (n : ZMod p) ∈ primeWindowResidues H p := by
  classical
  rw [prime_dvd_window_iff_int H p n hp]
  simp only [primeWindowResidues, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, hd⟩
    have hz : ((n - (k : ℤ) : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (n - (k : ℤ)) p).mpr hd
    have heq : (n : ZMod p) = (k : ZMod p) := by
      apply sub_eq_zero.mp
      simpa only [Int.cast_sub, Int.cast_natCast] using hz
    exact ⟨k, hk, heq.symm⟩
  · rintro ⟨k, hk, heq⟩
    refine ⟨k, hk, (ZMod.intCast_zmod_eq_zero_iff_dvd (n - (k : ℤ)) p).mp ?_⟩
    simp only [Int.cast_sub, Int.cast_natCast, heq, sub_self]

/-- For any modulus p>H, the H classes are distinct. In particular this holds
for each selected prime. The empty-window case H=0 is included.
@isnad1 id=eq.1h2v.s4.33c067a087f9 from=translated src=- shape=26c8e7a4 vocab=876f95c2
-/
theorem card_primeWindowResidues (H p : ℕ) (hHp : H < p) :
    (primeWindowResidues H p).card = H := by
  classical
  have hinj : Set.InjOn (fun k : ℕ => (k : ZMod p)) (Finset.Icc 1 H : Set ℕ) := by
    intro k hk l hl heq
    have hkp : k < p := lt_of_le_of_lt (Finset.mem_Icc.mp hk).2 hHp
    have hlp : l < p := lt_of_le_of_lt (Finset.mem_Icc.mp hl).2 hHp
    have hv := congrArg (fun r : ZMod p => r.val) heq
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hkp, Nat.mod_eq_of_lt hlp] using hv
  unfold primeWindowResidues
  rw [Finset.card_image_of_injOn hinj]
  simp

end Erdos647Sieve
end
