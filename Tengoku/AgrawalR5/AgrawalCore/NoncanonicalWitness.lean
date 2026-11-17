/-
Certificato kernel-puro della parte aritmetica del primo testimone
non canonico trovato nel censimento H4.

Il modulo certifica primalità, inerzia, fattorizzazioni, ammissibilità e
la relazione `p = k + 4rs`. L'ordine esatto della matrice aurea viene
controllato nel replay indipendente v3; non è nascosto in un assioma Lean.
-/
import Tengoku.AgrawalR5.AgrawalCore.Reciprocity
import Tengoku.Seed.Tactic.NormNum.Prime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

def noncanonicalP : ℕ := 18_251_687
def noncanonicalR : ℕ := 158
def noncanonicalE : ℕ := 99_736
def noncanonicalRHalf : ℕ := 79
def noncanonicalEHalf : ℕ := 49_868
def noncanonicalModulus : ℕ := 15_758_288
def noncanonicalK : ℕ := 2_493_399

/--
@isnad1 id=prime.0h0v.s1.193d4c1fb54c from=translated src=- shape=49959d42 vocab=234351d2
-/
theorem noncanonicalP_prime : noncanonicalP.Prime := by
  norm_num [noncanonicalP]

/--
@isnad1 id=eq.0h0v.s5.f66f2daee61f from=translated src=- shape=b50716c6 vocab=62530ddc
-/
theorem noncanonical_factor_p_sub_one :
    noncanonicalP - 1 = 2 * 71 * 79 * 1627 := by
  norm_num [noncanonicalP]

/--
@isnad1 id=eq.0h0v.s6.5148f485bdc7 from=translated src=- shape=87cccd0b vocab=2ad3f8b4
-/
theorem noncanonical_factor_p_add_one :
    noncanonicalP + 1 = 2 ^ 3 * 3 * 7 * 13 * 61 * 137 := by
  norm_num [noncanonicalP]

/--
@isnad1 id=and.0h0v.s5.cc072f8b3cbe from=translated src=- shape=3c7d6a95 vocab=19bb8268
-/
theorem noncanonical_halves :
    noncanonicalR = 2 * noncanonicalRHalf ∧
      noncanonicalE = 2 * noncanonicalEHalf := by
  norm_num [noncanonicalR, noncanonicalE, noncanonicalRHalf,
    noncanonicalEHalf]

/--
@isnad1 id=and.0h0v.s5.a866d6e0a438 from=translated src=- shape=3beb1659 vocab=b994e193
-/
theorem noncanonical_admissible :
    Nat.Coprime noncanonicalRHalf noncanonicalEHalf ∧
      Odd (noncanonicalRHalf + noncanonicalEHalf) ∧
      ¬ 5 ∣ noncanonicalRHalf * noncanonicalEHalf := by
  constructor
  · norm_num [noncanonicalRHalf, noncanonicalEHalf, Nat.Coprime]
  constructor
  · exact ⟨24973, by norm_num [noncanonicalRHalf, noncanonicalEHalf]⟩
  · norm_num [noncanonicalRHalf, noncanonicalEHalf]

/--
@isnad1 id=eq.0h0v.s4.11773589fc78 from=translated src=- shape=53b1b371 vocab=cdb12b19
-/
theorem noncanonical_modulus_eq :
    noncanonicalModulus =
      4 * noncanonicalRHalf * noncanonicalEHalf := by
  norm_num [noncanonicalModulus, noncanonicalRHalf, noncanonicalEHalf]

/--
@isnad1 id=and.0h0v.s5.78e6ce7bb620 from=translated src=- shape=fe334f39 vocab=2530e7bd
-/
theorem noncanonical_gcd_signature :
    Nat.gcd (noncanonicalK - 1) noncanonicalModulus =
        2 * noncanonicalRHalf ∧
      Nat.gcd (noncanonicalK + 1) noncanonicalModulus =
        2 * noncanonicalEHalf := by
  norm_num [noncanonicalK, noncanonicalModulus, noncanonicalRHalf,
    noncanonicalEHalf]

/-- Il testimone smentisce la scorciatoia empirica `p=k`: è al livello
successivo esatto.
@isnad1 id=eq.0h0v.s3.376d2faf05f3 from=translated src=- shape=5f20cedd vocab=9fcddf25
-/
theorem noncanonical_relation :
    noncanonicalP = noncanonicalK + noncanonicalModulus := by
  norm_num [noncanonicalP, noncanonicalK, noncanonicalModulus]

/-- Smentisce anche il possibile bound universale `R*E > p`.
@isnad1 id=lt.0h0v.s3.f669a3554fae from=translated src=- shape=cc017972 vocab=9b293fcd
-/
theorem noncanonical_order_product_lt :
    noncanonicalR * noncanonicalE < noncanonicalP := by
  norm_num [noncanonicalR, noncanonicalE, noncanonicalP]

/-- Il testimone è inerte: quindi non è un controesempio a H4.
@isnad1 id=not.0h0v.s5.253314aded72 from=translated src=- shape=d2c72c8b vocab=6c6247a8
-/
theorem noncanonical_inert :
    ¬ IsSquare (5 : ZMod noncanonicalP) := by
  letI : Fact noncanonicalP.Prime := ⟨noncanonicalP_prime⟩
  apply not_isSquare_five (p := noncanonicalP)
  · norm_num [noncanonicalP]
  · left
    norm_num [noncanonicalP]

/-- Certificato modulare dell'ordine candidato di `5`: il controllo
della potenza e dei due quozienti primi caratterizza l'ordine `158`.
@isnad1 id=and.0h0v.s7.42c8391a7432 from=translated src=- shape=0aaf221a vocab=0258bb73
-/
theorem noncanonical_five_order_certificate :
    (5 : ZMod noncanonicalP) ^ noncanonicalR = 1 ∧
      (5 : ZMod noncanonicalP) ^ (noncanonicalR / 2) ≠ 1 ∧
      (5 : ZMod noncanonicalP) ^ (noncanonicalR / 79) ≠ 1 := by
  change (5 : ZMod 18251687) ^ 158 = 1 ∧
    (5 : ZMod 18251687) ^ 79 ≠ 1 ∧
    (5 : ZMod 18251687) ^ 2 ≠ 1
  constructor
  · set_option maxRecDepth 100000 in decide
  constructor
  · set_option maxRecDepth 100000 in decide
  · decide

/-- La precedente terna di potenze è un certificato completo:
`158 = 2 * 79`, quindi l'ordine di `5` è esattamente `158`.
@isnad1 id=eq.0h0v.s5.7ff96f91ba62 from=translated src=- shape=ee6b6ff7 vocab=f8b93b7c
-/
theorem noncanonical_five_order :
    orderOf (5 : ZMod noncanonicalP) = noncanonicalR := by
  have hc := noncanonical_five_order_certificate
  apply orderOf_eq_of_pow_and_pow_div_prime (by
    norm_num [noncanonicalR]) hc.1
  intro q hq hqdiv
  have hcases : q = 2 ∨ q = 79 := by
    have hfac : q ∣ 2 * 79 := by simpa [noncanonicalR] using hqdiv
    rcases hq.dvd_mul.mp hfac with h2 | h79
    · left
      exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2
    · right
      exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h79
  rcases hcases with rfl | rfl
  · simpa [noncanonicalR] using hc.2.1
  · simpa [noncanonicalR] using hc.2.2

end AgrawalCore
