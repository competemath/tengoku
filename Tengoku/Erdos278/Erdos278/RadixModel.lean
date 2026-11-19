import Tengoku.Erdos278.Erdos278.RadixCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

/-- The modulus specified by a finite family of coprime radix powers.-/
def radixModulus {β : Type*} [Fintype β] (b e : β → ℕ) : ℕ :=
  univ.lcm (fun j => b j ^ e j)

/--
@isnad1 id=lt.1h3v.s5.953774a83a8c from=translated src=- shape=cdced7da vocab=0bbf4cde
-/
theorem radix_modulus_pos {β : Type*} [Fintype β]
    (b e : β → ℕ) (hb : ∀ j, 0 < b j) : 0 < radixModulus b e := by
  exact Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
    (fun j _ => pow_ne_zero _ (hb j).ne'))

/--
@isnad1 id=eq.1h3v.s5.d68efbd19950 from=translated src=- shape=931a9d24 vocab=ad0df6d1
-/
theorem radix_modulus_eq_product {β : Type*} [Fintype β]
    (b e : β → ℕ) (hc : Pairwise (fun j k => (b j).Coprime (b k))) :
    radixModulus b e = ∏ j, b j ^ e j := by
  exact Finset.lcm_eq_prod (fun j _ k _ hjk => (hc hjk).pow _ _)

/--
@isnad1 id=eq.0h3v.s5.15051b3bc812 from=translated src=- shape=16c11c15 vocab=12ae4f5e
-/
theorem radix_power_gcd (b d e : ℕ) :
    (b^d).gcd (b^e) = b^(min d e) := by
  rcases le_total d e with h | h
  · rw [min_eq_left h, Nat.gcd_eq_left (pow_dvd_pow b h)]
  · rw [min_eq_right h, Nat.gcd_eq_right (pow_dvd_pow b h)]

/-- Shared digits are exactly the gcd coordinates, also for composite radices.
@isnad1 id=eq.2h4v.s6.765287876940 from=translated src=- shape=978e5fc2 vocab=086b0fb3
-/
theorem radix_modulus_gcd {β : Type*} [Fintype β] [DecidableEq β]
    (b e f : β → ℕ) (hb : ∀ j, 0 < b j)
    (hc : Pairwise (fun j k => (b j).Coprime (b k))) :
    (radixModulus b e).gcd (radixModulus b f) =
      radixModulus b (fun j => min (e j) (f j)) := by
  apply Nat.dvd_antisymm
  · change (radixModulus b e).gcd (univ.lcm (fun j => b j ^ f j)) ∣ _
    rw [gcd_finset_lcm univ _ _ (radix_modulus_pos b e hb).ne'
      (fun j _ => pow_ne_zero _ (hb j).ne')]
    apply Finset.lcm_dvd
    intro j _
    rw [Nat.gcd_comm]
    change (b j ^ f j).gcd (univ.lcm (fun k => b k ^ e k)) ∣ _
    rw [gcd_finset_lcm univ _ _
      (pow_ne_zero _ (hb j).ne') (fun k _ => pow_ne_zero _ (hb k).ne')]
    apply Finset.lcm_dvd
    intro k _
    by_cases h : j = k
    · subst k
      rw [radix_power_gcd, min_comm]
      exact Finset.dvd_lcm (mem_univ j)
    · rw [((hc h).pow _ _).gcd_eq_one]
      exact one_dvd _
  · apply Finset.lcm_dvd
    intro j _
    apply Nat.dvd_gcd
    · exact (pow_dvd_pow (b j) (min_le_left _ _)).trans
        (Finset.dvd_lcm (mem_univ j))
    · exact (pow_dvd_pow (b j) (min_le_right _ _)).trans
        (Finset.dvd_lcm (mem_univ j))

/-- Any choice of radix digits can be reconstructed as integer residues.
@isnad1 id=ex.2h5v.s6.53c9880d6b60 from=translated src=- shape=e7003812 vocab=d4bf6c18
-/
theorem radix_digits_reconstruct {r : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (b : β → ℕ) (e : Fin r → β → ℕ) (hb : ∀ j, 0 < b j)
    (hc : Pairwise (fun j k => (b j).Coprime (b k)))
    (u : ∀ j, ℕ → Fin r → Fin (b j)) :
    ∃ a : Fin r → ℤ, ∀ i j,
      a i ≡ (radixPrefix (b j) (fun t => u j t i) (e i j) : ℤ)
        [ZMOD (b j)^(e i j)] := by
  classical
  have hex (i : Fin r) := coprime_local_gluing univ
    (fun j => b j ^ e i j) (fun j _ => pow_ne_zero _ (hb j).ne')
    (fun j => (radixPrefix (b j) (fun t => u j t i) (e i j) : ℤ))
    (fun j _ k _ hjk => (hc hjk).pow _ _)
  exact ⟨fun i => Classical.choose (hex i),
    fun i j => Classical.choose_spec (hex i) j (mem_univ j)⟩

/-- For reconstructed residues, compatibility is agreement on every shared digit.
@isnad1 id=iff.3h8v.s7.9d5a10933d94 from=translated src=- shape=2f1c3c14 vocab=f9b1461e
-/
theorem radix_compatible_iff {r : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (b : β → ℕ) (e : Fin r → β → ℕ) (hb : ∀ j, 0 < b j)
    (hc : Pairwise (fun j k => (b j).Coprime (b k)))
    (u : ∀ j, ℕ → Fin r → Fin (b j)) (a : Fin r → ℤ)
    (ha : ∀ i j, a i ≡ (radixPrefix (b j) (fun t => u j t i) (e i j) : ℤ)
      [ZMOD (b j)^(e i j)]) (i h : Fin r) :
    Compatible (fun i => radixModulus b (e i)) a i h ↔
      ∀ j t, t < e i j → t < e h j → u j t i = u j t h := by
  rw [Compatible, radix_modulus_gcd b (e i) (e h) hb hc, radixModulus,
    modEq_lcm_iff]
  have hj (j : β) :
      a i ≡ a h [ZMOD (b j)^min (e i j) (e h j)] ↔
        ∀ t < min (e i j) (e h j), u j t i = u j t h := by
    have hi := (ha i j).of_dvd (Int.natCast_dvd_natCast.mpr
      (pow_dvd_pow (b j) (min_le_left (e i j) (e h j))))
    have hh := (ha h j).of_dvd (Int.natCast_dvd_natCast.mpr
      (pow_dvd_pow (b j) (min_le_right (e i j) (e h j))))
    have heq : (a i ≡ a h [ZMOD (b j)^min (e i j) (e h j)]) ↔
        ((radixPrefix (b j) (fun t => u j t i) (e i j) : ℤ) ≡
          (radixPrefix (b j) (fun t => u j t h) (e h j) : ℤ)
            [ZMOD (b j)^min (e i j) (e h j)]) :=
      ⟨fun H => hi.symm.trans (H.trans hh), fun H => hi.trans (H.trans hh.symm)⟩
    exact heq.trans (radix_prefix_modEq_iff (hb j) _ _ (min_le_left _ _) (min_le_right _ _))
  simp only [mem_univ, forall_const]
  constructor
  · intro H j t hi hh
    exact (hj j).mp (H j) t (lt_min hi hh)
  · intro H j
    exact (hj j).mpr (fun t ht => H j t (lt_min_iff.mp ht).1 (lt_min_iff.mp ht).2)

/-- Every integer residue, including negative representatives, has such digits.
@isnad1 id=ex.1h3v.s5.2d86e58ce89e from=translated src=- shape=fb579f69 vocab=0cf0aa7f
-/
theorem radix_integer_represents {b : ℕ} (hb : 0 < b) (a : ℤ) (k : ℕ) :
    ∃ u : ℕ → Fin b, a ≡ (radixPrefix b u k : ℤ) [ZMOD b^k] := by
  have hp : (0 : ℤ) < (b^k : ℕ) := by exact_mod_cast pow_pos hb k
  let x : ℕ := (a % (b^k : ℕ)).toNat
  have hx : (x : ℤ) = a % (b^k : ℕ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hp.ne')
  have hlt : x < b^k := by
    have hh := Int.emod_lt_of_pos a hp
    rw [← hx] at hh
    exact_mod_cast hh
  obtain ⟨u, hu⟩ := radix_prefix_represents hb x k
  refine ⟨u, ?_⟩
  rw [Nat.mod_eq_of_lt hlt] at hu
  rw [hu, hx]
  exact (Int.mod_modEq _ _).symm

/--
@isnad1 id=ex.1h5v.s6.536233fa5ba1 from=translated src=- shape=2448c69a vocab=6bf71a0b
-/
theorem radix_residues_encode {r : ℕ} {β : Type*} [Fintype β]
    (b : β → ℕ) (e : Fin r → β → ℕ) (hb : ∀ j, 0 < b j)
    (a : Fin r → ℤ) :
    ∃ u : ∀ j, ℕ → Fin r → Fin (b j), ∀ i j,
      a i ≡ (radixPrefix (b j) (fun t => u j t i) (e i j) : ℤ)
        [ZMOD (b j)^(e i j)] := by
  classical
  have hex (i : Fin r) (j : β) := radix_integer_represents (hb j) (a i) (e i j)
  exact ⟨fun j t i => Classical.choose (hex i j) t,
    fun i j => Classical.choose_spec (hex i j)⟩

end Erdos278
