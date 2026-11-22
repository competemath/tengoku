/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/
module

public import Tengoku.LeanPool.LeanPool.DeadEnds.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Arctan
import Tengoku.Seed.Data.Nat.ChineseRemainder
import Tengoku.Seed.MeasureTheory.Covering.Besicovitch
import Tengoku.Seed.Tactic.Positivity.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LeanPool.DeadEnds.CRT
-/

@[expose] public section

namespace LeanPool.DeadEnds

/-- The modulus M = ∏_{p ∈ S} p² -/
noncomputable def primeSquareProduct (S : Finset Nat.Primes) : ℕ :=
  ∏ p ∈ S, (p : ℕ) ^ 2

/-- Valid residues mod M: residues r such that for all p ∈ S, r mod p² is valid -/
noncomputable def validResiduesMod (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) : Finset ℕ :=
  (Finset.range (primeSquareProduct S)).filter fun r =>
    ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * r + d))

/-- The product of local density factors L = ∏_{p ∈ S} localDensityFactor p b T -/
noncomputable def localDensityProduct (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ S, localDensityFactor (p : ℕ) b T

/-- The local valid residues for a single prime p: residues r in [0, p²) such that
    p² ∤ r and for all d ∈ T, p² ∤ (b * r + d). -/
def localValidResidues (p : ℕ) (b : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.range (p ^ 2)).filter fun r =>
    ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))

/--
@isnad1 id=eq.1h3v.s5.ceaf72860e01 from=translated src=- shape=9655e72e vocab=bf616aad
-/
lemma localValidResidues_card_eq (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (T : Finset ℕ) :
    ((localValidResidues p b T).card : ℝ) = (p : ℝ) ^ 2 * localDensityFactor p b T := by
  have hp2 : ((p ^ 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hp.pos.ne'
  simp only [localDensityFactor, localValidResidues]
  rw [show ((p : ℝ) ^ 2 : ℝ) = (p ^ 2 : ℕ) by norm_cast]
  field_simp [hp2]

/--
@isnad1 id=coprime.1h2v.s5.a53dde37268b from=translated src=- shape=f4edb629 vocab=77162040
-/
lemma prime_sq_coprime (p q : Nat.Primes) (hne : p ≠ q) :
    ((p : ℕ) ^ 2).Coprime ((q : ℕ) ^ 2) := by
  have hpq : (p : ℕ) ≠ (q : ℕ) := fun h => hne (Subtype.ext h)
  exact Nat.Coprime.pow_right 2
    (Nat.Coprime.pow_left 2 ((Nat.coprime_primes p.prop q.prop).mpr hpq))

/--
@isnad1 id=pairwise.0h1v.s6.b8fc83d563df from=translated src=- shape=1e059347 vocab=6a33e408
-/
lemma pairwise_coprime_prime_squares (S : Finset Nat.Primes) :
    (S : Set Nat.Primes).Pairwise (fun p q => ((p : ℕ) ^ 2).Coprime ((q : ℕ) ^ 2)) := by
  intro p _ q _ hpq
  exact prime_sq_coprime p q hpq

/-- The list S.toList satisfies pairwise coprimality for the map p ↦ p².
    Uses `pairwise_coprime_prime_squares` and transfers the set pairwise property to the list.
    Mathlib's `List.pairwise_of_reflexive_of_forall_ne` handles this for symmetric reflexive
    relations,
    but coprimality is not reflexive (unless p² = 1). Instead we use the fact that S.toList.Nodup
    and the set pairwise property directly imply the list pairwise property.
    Specifically, uses `List.Nodup.pairwise_of_set_pairwise : l.Nodup → {x | x ∈ l}.Pairwise r →
    List.Pairwise r l`
    together with `Finset.nodup_toList : ∀ (s : Finset α), s.toList.Nodup` and
    `Finset.coe_toList : ↑s.toList = ↑s` (as sets).
@isnad1 id=pairwise.0h1v.s5.7bd2dd176bf7 from=translated src=- shape=7d73eda7 vocab=90d4fa48
-/
lemma toList_pairwise_coprime_prime_squares (S : Finset Nat.Primes) :
    List.Pairwise (Function.onFun Nat.Coprime (fun p : Nat.Primes => (p : ℕ) ^ 2)) S.toList := by
  apply List.Nodup.pairwise_of_set_pairwise (Finset.nodup_toList S)
  simp only [Finset.mem_toList]
  exact pairwise_coprime_prime_squares S

/--
@isnad1 id=eq.0h1v.s5.95f26fb0f4e6 from=translated src=- shape=58789be0 vocab=093145ee
-/
lemma list_map_prod_eq_primeSquareProduct (S : Finset Nat.Primes) :
    (List.map (fun p : Nat.Primes => (p : ℕ) ^ 2) S.toList).prod = primeSquareProduct S := by
  aesop

/-- Congruence modulo each prime-square factor implies congruence modulo their product.
@isnad1 id=modeq.1h3v.s5.06deade87cf5 from=translated src=- shape=b1b010ed vocab=38f29c4b
-/
lemma modEq_primeSquareProduct_of_forall_modEq (S : Finset Nat.Primes) (r₁ r₂ : ℕ)
    (h : ∀ p ∈ S, r₁ ≡ r₂ [MOD (p : ℕ) ^ 2]) :
    r₁ ≡ r₂ [MOD primeSquareProduct S] := by
  rw [← list_map_prod_eq_primeSquareProduct]
  rw [Nat.modEq_list_map_prod_iff (toList_pairwise_coprime_prime_squares S)]
  simp_all

/-- The CRT remainder map is injective on residues below the product modulus.
@isnad1 id=injon.0h1v.s6.b0bcf36b1089 from=translated src=- shape=7805271e vocab=90f589c1
-/
lemma crtMap_injective_on_range (S : Finset Nat.Primes) :
    Set.InjOn (fun r => fun p (_hp : p ∈ S) => r % ((p : ℕ) ^ 2))
      {r | r < primeSquareProduct S} := by
  intro r₁ hr₁ r₂ hr₂ heq
  have h_modEq : ∀ p ∈ S, r₁ ≡ r₂ [MOD (p : ℕ) ^ 2] :=
    fun p hp => congrFun (congrFun heq p) hp
  exact Nat.ModEq.eq_of_lt_of_lt
    (modEq_primeSquareProduct_of_forall_modEq S r₁ r₂ h_modEq) hr₁ hr₂

/--
@isnad1 id=iff.1h2v.s6.9fea06c9467b from=translated src=- shape=065cd162 vocab=0f4b56fa
-/
lemma dvd_iff_mod_dvd (p : ℕ) (_hp : 0 < p ^ 2) (r : ℕ) :
    p ^ 2 ∣ r ↔ r % (p ^ 2) = 0 :=
  Nat.dvd_iff_mod_eq_zero

/--
@isnad1 id=iff.1h4v.s7.f020a5a8ac54 from=translated src=- shape=517f6695 vocab=b829fdfc
-/
lemma shifted_dvd_iff_mod (p b d r : ℕ) (_hp : 0 < p ^ 2) :
    p ^ 2 ∣ (b * r + d) ↔ p ^ 2 ∣ (b * (r % (p ^ 2)) + d) := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  simp [Nat.add_mod, Nat.mul_mod]

/--
@isnad1 id=iff.0h4v.s8.b99779a720bc from=translated src=- shape=d25d5f19 vocab=6ef47b89
-/
lemma valid_iff_locally_valid (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (r : ℕ) :
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * r + d))) ↔
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ (r % (p : ℕ) ^ 2)) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * (r % (p : ℕ) ^ 2) +
        d))) := by
  constructor
  · intro h p hp
    have hp_pos : 0 < (p : ℕ) ^ 2 := pow_pos (Nat.Prime.pos p.2) 2
    constructor
    · intro hmod
      have hzero : r % (p : ℕ) ^ 2 = 0 :=
        Nat.eq_zero_of_dvd_of_lt hmod (Nat.mod_lt r hp_pos)
      exact (h p hp).1 ((dvd_iff_mod_dvd (p : ℕ) hp_pos r).mpr hzero)
    · intro d hd hmod
      exact (h p hp).2 d hd ((shifted_dvd_iff_mod (p : ℕ) b d r hp_pos).mpr hmod)
  · intro h p hp
    have hp_pos : 0 < (p : ℕ) ^ 2 := pow_pos (Nat.Prime.pos p.2) 2
    constructor
    · intro hr
      have hzero := (dvd_iff_mod_dvd (p : ℕ) hp_pos r).mp hr
      have hmod : (p : ℕ) ^ 2 ∣ r % (p : ℕ) ^ 2 := by
        simp_all
      exact (h p hp).1 hmod
    · intro d hd hr
      exact (h p hp).2 d hd ((shifted_dvd_iff_mod (p : ℕ) b d r hp_pos).mp hr)

/-- For any prime p, p² ≠ 0.
    This is needed to apply `Nat.chineseRemainderOfFinset`.
    Uses `Nat.Prime.pos : ∀ {p : ℕ}, Nat.Prime p → 0 < p` and
    `pow_ne_zero : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [NoZeroDivisors M₀] (n :
    ℕ), a ≠ 0 → a ^ n ≠ 0`.
@isnad1 id=ne.0h1v.s5.5411c14aa9ac from=translated src=- shape=70287146 vocab=e1a05b63
-/
lemma prime_sq_ne_zero (p : Nat.Primes) : (p : ℕ) ^ 2 ≠ 0 := by
  have hp : Nat.Prime p := p.2
  exact pow_ne_zero 2 hp.pos.ne'

/--
@isnad1 id=ex.1h2v.s7.a000312b7436 from=translated src=- shape=efe209fd vocab=48ec788c
-/
lemma crt_surjective (S : Finset Nat.Primes) (t : (p : Nat.Primes) → p ∈ S → ℕ)
    (ht : ∀ p (hp : p ∈ S), t p hp < (p : ℕ) ^ 2) :
    ∃ r, r < primeSquareProduct S ∧ ∀ p (hp : p ∈ S), r % ((p : ℕ) ^ 2) = t p hp := by
  let s : Nat.Primes → ℕ := fun p => (p : ℕ) ^ 2
  let a : Nat.Primes → ℕ := fun p => if h : p ∈ S then t p h else 0
  have hs : ∀ i ∈ S, s i ≠ 0 := fun p _ => prime_sq_ne_zero p
  have hcoprime : (S : Set Nat.Primes).Pairwise (Function.onFun Nat.Coprime s) :=
    pairwise_coprime_prime_squares S
  let r := Nat.chineseRemainderOfFinset a s S hs hcoprime
  use r
  constructor
  · exact Nat.chineseRemainderOfFinset_lt_prod a s hs hcoprime
  · intro p hp
    have hcong : (r : ℕ) ≡ a p [MOD s p] := r.2 p hp
    have ha : a p = t p hp := by simp [a, hp]
    rw [ha] at hcong
    exact Nat.mod_eq_of_modEq hcong (ht p hp)

/--
@isnad1 id=mem.2h5v.s6.fd66c86c734a from=translated src=- shape=7abd71fc vocab=2e68df59
-/
lemma crtMap_mapsTo_pi (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (r : ℕ)
    (hr : r ∈ validResiduesMod b T S) (p : Nat.Primes) (hp : p ∈ S) :
    r % ((p : ℕ) ^ 2) ∈ localValidResidues (p : ℕ) b T := by
  simp only [validResiduesMod, Finset.mem_filter, Finset.mem_range] at hr
  obtain ⟨_, hvalid⟩ := hr
  have hp_cond := hvalid p hp
  have hp_sq_pos : 0 < (p : ℕ) ^ 2 := sq_pos_of_pos p.prop.pos
  have hmod_lt : r % ((p : ℕ) ^ 2) < (p : ℕ) ^ 2 := Nat.mod_lt r hp_sq_pos
  simp only [localValidResidues, Finset.mem_filter, Finset.mem_range]
  refine ⟨hmod_lt, ?_, ?_⟩
  · intro hdvd
    have h_rmod_eq_zero : r % ((p : ℕ) ^ 2) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hmod_lt
    have hdvd_r : (p : ℕ) ^ 2 ∣ r := Nat.dvd_of_mod_eq_zero h_rmod_eq_zero
    exact hp_cond.1 hdvd_r
  · intro d hd hdvd_shifted
    have h_not_dvd := hp_cond.2 d hd
    have hmod : (r % ((p : ℕ) ^ 2)) ≡ r [MOD ((p : ℕ) ^ 2)] := Nat.mod_modEq r ((p : ℕ) ^ 2)
    have hmul : b * (r % ((p : ℕ) ^ 2)) ≡ b * r [MOD ((p : ℕ) ^ 2)] := hmod.mul_left b
    have hadd : b * (r % ((p : ℕ) ^ 2)) + d ≡ b * r + d [MOD ((p : ℕ) ^ 2)] := hmul.add_right d
    have hdvd_equiv : ((p : ℕ) ^ 2 ∣ b * (r % ((p : ℕ) ^ 2)) + d) ↔ ((p : ℕ) ^ 2 ∣ b * r + d) :=
      hadd.dvd_iff dvd_rfl
    exact h_not_dvd (hdvd_equiv.mp hdvd_shifted)

/--
@isnad1 id=not.3h3v.s6.ba1e92407858 from=translated src=- shape=7b798fb6 vocab=0f4b56fa
-/
lemma not_dvd_of_mod_eq_not_dvd (p r f : ℕ) (_hp : 0 < p ^ 2) (hr_eq : r % p ^ 2 = f)
    (hf_ndiv : ¬(p ^ 2 ∣ f)) : ¬(p ^ 2 ∣ r) := by
  intro h_dvd_r
  have h_f_eq_zero : f = 0 := by
    rw [← hr_eq]
    exact Nat.mod_eq_zero_of_dvd h_dvd_r
  exact hf_ndiv (h_f_eq_zero ▸ dvd_zero _)

/--
@isnad1 id=not.3h5v.s7.2f26e8331d54 from=translated src=- shape=6bdfa553 vocab=b829fdfc
-/
lemma not_dvd_shift_of_mod_eq (p b r f d : ℕ) (_hp : 0 < p ^ 2) (hr_eq : r % p ^ 2 = f)
    (hf_shift : ¬(p ^ 2 ∣ b * f + d)) : ¬(p ^ 2 ∣ b * r + d) := by
  intro h
  apply hf_shift
  have : p ^ 2 ∣ b * (r % p ^ 2) + d := (shifted_dvd_iff_mod p b d r _hp).mp h
  rwa [hr_eq] at this

/--
@isnad1 id=ex.1h4v.s7.c1fe2f480d61 from=translated src=- shape=6654a0a3 vocab=2e68df59
-/
lemma crt_inverse_mapsTo (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → p ∈ S → ℕ)
    (hf : ∀ p (hp : p ∈ S), f p hp ∈ localValidResidues (p : ℕ) b T) :
    ∃ r ∈ validResiduesMod b T S, ∀ p (hp : p ∈ S), r % ((p : ℕ) ^ 2) = f p hp := by
  have hf_bound : ∀ p (hp : p ∈ S), f p hp < (p : ℕ) ^ 2 := fun p hp => by
    have h := hf p hp
    simp only [localValidResidues, Finset.mem_filter, Finset.mem_range] at h
    exact h.1
  obtain ⟨r, hr_lt, hr_mod⟩ := crt_surjective S f hf_bound
  refine ⟨r, ?_, hr_mod⟩
  simp only [validResiduesMod, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact hr_lt
  · intro p hp
    have hf_valid := hf p hp
    simp only [localValidResidues, Finset.mem_filter, Finset.mem_range] at hf_valid
    obtain ⟨_, hf_ndiv, hf_shift⟩ := hf_valid
    have hr_eq : r % ((p : ℕ) ^ 2) = f p hp := hr_mod p hp
    have hp_pos : 0 < (p : ℕ) ^ 2 := pow_pos (Nat.Prime.pos p.2) 2
    constructor
    · exact not_dvd_of_mod_eq_not_dvd (p : ℕ) r (f p hp) hp_pos hr_eq hf_ndiv
    · intro d hd
      exact not_dvd_shift_of_mod_eq (p : ℕ) b r (f p hp) d hp_pos hr_eq (hf_shift d hd)

/--
@isnad1 id=nonempty.0h3v.s7.7f1276391e26 from=translated src=- shape=0a3a4598 vocab=2cd4e693
-/
lemma validResidues_equiv_pi (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    Nonempty ((validResiduesMod b T S) ≃ (S.pi (fun p => localValidResidues (p : ℕ) b T))) := by
  have hfwd : ∀ r, r ∈ validResiduesMod b T S →
      (fun p (hp : p ∈ S) => r % ((p : ℕ) ^ 2)) ∈ S.pi (fun p => localValidResidues (p : ℕ) b T) :=
          by
    intro r hr
    rw [Finset.mem_pi]
    intro p hp
    exact crtMap_mapsTo_pi b T S r hr p hp
  let f : (validResiduesMod b T S) → (S.pi (fun p => localValidResidues (p : ℕ) b T)) :=
    fun ⟨r, hr⟩ => ⟨fun p hp => r % ((p : ℕ) ^ 2), hfwd r hr⟩
  have hf_inj : Function.Injective f := by
    intro ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ heq
    simp only [Subtype.mk.injEq]
    have hr₁_lt : r₁ < primeSquareProduct S :=
      Finset.mem_filter.mp hr₁ |>.1 |> Finset.mem_range.mp
    have hr₂_lt : r₂ < primeSquareProduct S :=
      Finset.mem_filter.mp hr₂ |>.1 |> Finset.mem_range.mp
    apply crtMap_injective_on_range S hr₁_lt hr₂_lt
    have heq' := Subtype.mk.injEq _ _ _ _ |>.mp heq
    ext p hp
    have := congrFun₂ heq' p hp
    exact this
  have hf_surj : Function.Surjective f := by
    intro ⟨g, hg⟩
    have hg' : ∀ p (hp : p ∈ S), g p hp ∈ localValidResidues (p : ℕ) b T := by
      simp_all
    obtain ⟨r, hr, hr_eq⟩ := crt_inverse_mapsTo b T S g hg'
    use ⟨r, hr⟩
    apply Subtype.ext
    ext p hp
    exact hr_eq p hp
  exact ⟨Equiv.ofBijective f ⟨hf_inj, hf_surj⟩⟩

/--
@isnad1 id=eq.0h3v.s5.bf69b0d47d51 from=translated src=- shape=da28b60a vocab=26ca67bb
-/
lemma validResiduesMod_card_eq_pi_card (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    (validResiduesMod b T S).card =
      (S.pi (fun p => localValidResidues (p : ℕ) b T)).card := by
  exact Finset.card_eq_of_equiv (validResidues_equiv_pi b T S).some

/-- Valid residue counts factor as the product of local valid residue counts.
@isnad1 id=eq.0h3v.s5.c3c8f30508c4 from=translated src=- shape=7a3fe4dd vocab=daca63e7
-/
lemma validResiduesMod_card_eq_prod (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    ((validResiduesMod b T S).card : ℝ) =
      ∏ p ∈ S, ((localValidResidues (p : ℕ) b T).card : ℝ) := by
  rw [validResiduesMod_card_eq_pi_card]
  simp_all

/--
@isnad1 id=eq.2h3v.s5.b041858a7585 from=translated src=- shape=c56db2c9 vocab=bae6beec
-/
lemma validResidues_card_eq_mul (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) :
    ((validResiduesMod b T S).card : ℝ) =
      (primeSquareProduct S : ℝ) * localDensityProduct b T S := by
  rw [validResiduesMod_card_eq_prod]
  conv_lhs =>
    arg 2
    ext p
    rw [localValidResidues_card_eq p p.prop b T]
  rw [Finset.prod_mul_distrib]
  simp only [primeSquareProduct, localDensityProduct, Nat.cast_prod, Nat.cast_pow]

/--
@isnad1 id=dvd.1h2v.s5.e59132c228a0 from=translated src=- shape=d44a3fad vocab=9d023dfe
-/
lemma prime_sq_dvd_primeSquareProduct (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ S) :
    (p : ℕ) ^ 2 ∣ primeSquareProduct S :=
  Finset.dvd_prod_of_mem _ hp

/--
@isnad1 id=iff.2h4v.s6.af407f71d947 from=translated src=- shape=6b5150b8 vocab=920dfbd6
-/
lemma dvd_iff_of_mod_eq_primeSquareProduct (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ S)
    (N₁ N₂ : ℕ) (hmod : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S) :
    ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) :=
  Nat.ModEq.dvd_iff hmod (prime_sq_dvd_primeSquareProduct S p hp)

/--
@isnad1 id=iff.2h6v.s7.7eb9e3844175 from=translated src=- shape=7f753d1d vocab=752ac3d7
-/
lemma shifted_dvd_iff_of_mod_eq_primeSquareProduct (b d : ℕ) (S : Finset Nat.Primes)
    (p : Nat.Primes) (hp : p ∈ S) (N₁ N₂ : ℕ)
    (hmod : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S) :
    ((p : ℕ) ^ 2 ∣ b * N₁ + d ↔ (p : ℕ) ^ 2 ∣ b * N₂ + d) := by
  have hN : N₁ ≡ N₂ [MOD (p : ℕ) ^ 2] :=
    Nat.ModEq.of_dvd (prime_sq_dvd_primeSquareProduct S p hp) hmod
  exact Nat.ModEq.dvd_iff ((hN.mul_left b).add_right d) dvd_rfl
/--
@isnad1 id=iff.1h5v.s7.e5783cbef4ab from=translated src=- shape=72b336ba vocab=752ac3d7
-/
theorem condition_mod_invariant (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes)
    (N₁ N₂ : ℕ) (hmod : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S) :
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N₁) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N₁ + d)) ↔
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N₂) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N₂ + d)) := by
  constructor <;> intro h p hp
  · constructor
    · rw [← dvd_iff_of_mod_eq_primeSquareProduct S p hp N₁ N₂ hmod]
      exact (h p hp).1
    · intro d hd
      rw [← shifted_dvd_iff_of_mod_eq_primeSquareProduct b d S p hp N₁ N₂ hmod]
      exact (h p hp).2 d hd
  · constructor
    · rw [dvd_iff_of_mod_eq_primeSquareProduct S p hp N₁ N₂ hmod]
      exact (h p hp).1
    · intro d hd
      rw [shifted_dvd_iff_of_mod_eq_primeSquareProduct b d S p hp N₁ N₂ hmod]
      exact (h p hp).2 d hd

end LeanPool.DeadEnds
