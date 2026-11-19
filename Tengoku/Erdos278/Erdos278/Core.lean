import Tengoku.Seed.Algebra.GCDMonoid.FinsetLemmas
import Tengoku.Seed.Data.Int.ModEq
import Tengoku.Seed.Data.Int.GCD
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Push
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/yoshiyoyoyo44/erdos278@66ff46ad30c3, `Erdos278/Core.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
Formal verification of the arithmetic core of the supplied candidate for Erdős 278.
This file does not identify a finite optimization reformulation with resolution of
the original open-ended research question.
-/

namespace Erdos278


open Finset

variable {ι : Type*} [DecidableEq ι]

/-- Compatibility at the gcd, including the harmless reflexive diagonal.-/
def Compatible (n : ι → ℕ) (a : ι → ℤ) (i j : ι) : Prop :=
  a i ≡ a j [ZMOD (n i).gcd (n j)]

def IsClique (n : ι → ℕ) (a : ι → ℤ) (s : Finset ι) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, Compatible n a i j

def IsSolution (n : ι → ℕ) (a : ι → ℤ) (s : Finset ι) (z : ℤ) : Prop :=
  ∀ i ∈ s, z ≡ a i [ZMOD n i]

instance compatibleDecidable (n : ι → ℕ) (a : ι → ℤ) (i j : ι) :
    Decidable (Compatible n a i j) := by unfold Compatible; infer_instance

instance cliqueDecidable (n : ι → ℕ) (a : ι → ℤ) (s : Finset ι) :
    Decidable (IsClique n a s) := by unfold IsClique; infer_instance

/--
@isnad1 id=iff.0h5v.s5.bd60b3514af1 from=translated src=- shape=dadc0098 vocab=28069e3a
-/
theorem compatible_iff_dvd (n : ι → ℕ) (a : ι → ℤ) (i j : ι) :
    Compatible n a i j ↔ ((n i).gcd (n j) : ℤ) ∣ a i - a j := by
  rw [Compatible, Int.modEq_comm, Int.modEq_iff_dvd]

/-- Generalized CRT for two moduli, proved using Bézout coefficients.
@isnad1 id=ex.1h4v.s5.1843bef43fa8 from=translated src=- shape=78c8d07f vocab=84c40176
-/
theorem crt_two (m n : ℕ) (a b : ℤ)
    (h : a ≡ b [ZMOD m.gcd n]) :
    ∃ z : ℤ, z ≡ a [ZMOD m] ∧ z ≡ b [ZMOD n] := by
  obtain ⟨k, hk⟩ := h.dvd
  refine ⟨a + m * Nat.gcdA m n * k, ?_, ?_⟩
  · apply Int.modEq_iff_dvd.mpr
    refine ⟨-Nat.gcdA m n * k, ?_⟩
    ring
  · apply Int.modEq_iff_dvd.mpr
    refine ⟨Nat.gcdB m n * k, ?_⟩
    have hb := Nat.gcd_eq_gcd_ab m n
    nlinarith [congrArg (fun t : ℤ => t * k) hb]

/--
@isnad1 id=iff.0h4v.s5.702e01ade163 from=translated src=- shape=b1883bad vocab=e1cb90c5
-/
theorem lcm_dvd_int_iff (s : Finset ι) (n : ι → ℕ) (z : ℤ) :
    ((s.lcm n : ℕ) : ℤ) ∣ z ↔ ∀ i ∈ s, (n i : ℤ) ∣ z := by
  simp only [Int.natCast_dvd, Finset.lcm_dvd_iff]

/--
@isnad1 id=iff.0h5v.s5.811f294ba9fe from=translated src=- shape=877f9921 vocab=b7643f89
-/
theorem modEq_lcm_iff (s : Finset ι) (n : ι → ℕ) (a b : ℤ) :
    a ≡ b [ZMOD (s.lcm n : ℕ)] ↔ ∀ i ∈ s, a ≡ b [ZMOD n i] := by
  simp only [Int.modEq_iff_dvd, lcm_dvd_int_iff]

/--
@isnad1 id=eq.2h4v.s6.f99db9b38d37 from=translated src=- shape=037b6a53 vocab=77776833
-/
theorem gcd_finset_lcm (s : Finset ι) (n : ι → ℕ) (m : ℕ)
    (hm : m ≠ 0) (hn : ∀ i ∈ s, n i ≠ 0) :
    m.gcd (s.lcm n) = s.lcm (fun i => m.gcd (n i)) := by
  have hL : s.lcm n ≠ 0 := Finset.lcm_ne_zero_iff.mpr hn
  have hg : ∀ i ∈ s, m.gcd (n i) ≠ 0 :=
    fun i _ => Nat.gcd_ne_zero_left hm
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_ne_zero_left hm) (Finset.lcm_ne_zero_iff.mpr hg)
  intro p
  rw [Nat.factorization_gcd hm hL, Finsupp.inf_apply,
    Finset.factorization_lcm hn, Finset.factorization_lcm hg]
  have heq : s.sup (fun i => (m.gcd (n i)).factorization p) =
      s.sup (fun i => m.factorization p ⊓ (n i).factorization p) := by
    apply Finset.sup_congr rfl
    intro i hi
    rw [Nat.factorization_gcd hm (hn i hi), Finsupp.inf_apply]
  rw [heq]
  clear hn hL hg heq
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sup_insert, inf_sup_left, ih]

/-- Pairwise compatibility is equivalent to a simultaneous integer solution.
@isnad1 id=iff.1h4v.s5.3a08bfff8afc from=translated src=- shape=8784eb23 vocab=fc732719
-/
theorem generalized_crt (s : Finset ι) (n : ι → ℕ) (a : ι → ℤ)
    (hn : ∀ i ∈ s, n i ≠ 0) :
    (∃ z, IsSolution n a s z) ↔ IsClique n a s := by
  constructor
  · rintro ⟨z, hz⟩ i hi j hj
    exact ((hz i hi).of_dvd (Int.natCast_dvd_natCast.mpr
      (Nat.gcd_dvd_left _ _))).symm.trans
        ((hz j hj).of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)))
  · intro h
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp [IsSolution]⟩
    | @insert i s hi ih =>
      obtain ⟨z, hz⟩ := ih (fun j hj => hn j (mem_insert_of_mem hj))
        (fun j hj k hk => h j (mem_insert_of_mem hj) k (mem_insert_of_mem hk))
      have hcompat : a i ≡ z [ZMOD (n i).gcd (s.lcm n)] := by
        rw [gcd_finset_lcm s n (n i) (hn i (mem_insert_self _ _))
          (fun j hj => hn j (mem_insert_of_mem hj)), modEq_lcm_iff]
        intro j hj
        exact (h i (mem_insert_self _ _) j (mem_insert_of_mem hj)).trans
          (((hz j hj).of_dvd (Int.natCast_dvd_natCast.mpr
            (Nat.gcd_dvd_right _ _))).symm)
      obtain ⟨w, hwi, hwz⟩ := crt_two (n i) (s.lcm n) (a i) z hcompat
      refine ⟨w, ?_⟩
      intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact hwi
      · exact ((modEq_lcm_iff s n w z).mp hwz j hj).trans (hz j hj)

/-- A nonempty intersection is exactly one residue class at the finite lcm.
@isnad1 id=iff.1h6v.s5.760ea1089286 from=translated src=- shape=987360bc vocab=93885160
-/
theorem solution_iff_modEq_lcm (s : Finset ι) (n : ι → ℕ) (a : ι → ℤ)
    {z : ℤ} (hz : IsSolution n a s z) (w : ℤ) :
    IsSolution n a s w ↔ w ≡ z [ZMOD (s.lcm n : ℕ)] := by
  rw [modEq_lcm_iff]
  exact ⟨fun hw i hi => (hw i hi).trans (hz i hi).symm,
    fun hw i hi => (hw i hi).trans (hz i hi)⟩

section Compression

variable [Fintype ι]

/-- The minimal modulus preserving every interaction at vertex i.-/
def interactionModulus (n : ι → ℕ) (i : ι) : ℕ :=
  (univ.erase i).lcm (fun j => (n i).gcd (n j))

/--
@isnad1 id=dvd.1h4v.s5.e7dd0fd0a0b3 from=translated src=- shape=927ef108 vocab=c947c72a
-/
theorem gcd_dvd_interaction (n : ι → ℕ) {i j : ι} (h : j ≠ i) :
    (n i).gcd (n j) ∣ interactionModulus n i :=
  Finset.dvd_lcm (by simp [h])

/--
@isnad1 id=dvd.0h3v.s4.a4ea683087e6 from=translated src=- shape=4e3c613b vocab=4f48307a
-/
theorem interaction_dvd_modulus (n : ι → ℕ) (i : ι) :
    interactionModulus n i ∣ n i :=
  Finset.lcm_dvd (fun _j _ => Nat.gcd_dvd_left _ _)

/--
@isnad1 id=lt.1h3v.s5.d86971bbf94b from=translated src=- shape=464c0ca8 vocab=65bc9c02
-/
theorem interaction_pos (n : ι → ℕ) (hn : ∀ i, 0 < n i) (i : ι) :
    0 < interactionModulus n i :=
  Nat.pos_of_dvd_of_pos (interaction_dvd_modulus n i) (hn i)

/--
@isnad1 id=eq.1h3v.s5.d890b4a25821 from=translated src=- shape=05a6a616 vocab=9fbfecc2
-/
theorem interaction_eq_gcd_lcm (n : ι → ℕ) (hn : ∀ i, n i ≠ 0) (i : ι) :
    interactionModulus n i = (n i).gcd ((univ.erase i).lcm n) :=
  (gcd_finset_lcm _ _ _ (hn i) (fun j _ => hn j)).symm

/--
@isnad1 id=iff.1h6v.s5.e0fbef34d0a7 from=translated src=- shape=0d5857a8 vocab=dc156efb
-/
theorem interaction_compression (n : ι → ℕ) (a b : ι → ℤ)
    (h : ∀ i, a i ≡ b i [ZMOD interactionModulus n i]) (i j : ι) :
    Compatible n a i j ↔ Compatible n b i j := by
  by_cases hij : i = j
  · subst j; simp [Compatible]
  have hi := (h i).of_dvd (Int.natCast_dvd_natCast.mpr
    (gcd_dvd_interaction n (Ne.symm hij)))
  have hj := (h j).of_dvd (Int.natCast_dvd_natCast.mpr
    (gcd_dvd_interaction n hij))
  rw [Nat.gcd_comm (n j) (n i)] at hj
  exact ⟨fun hab => hi.symm.trans (hab.trans hj),
    fun hab => hi.trans (hab.trans hj.symm)⟩

/-- Universal preservation of incident compatibility forces every gcd to divide m.
No assumption m | n i is needed for this stronger minimality statement.
@isnad1 id=dvd.1h4v.s6.aaa60e199f8d from=translated src=- shape=6cdf3ec9 vocab=b9349c0f
-/
theorem interaction_minimal (n : ι → ℕ) (i : ι) (m : ℕ)
    (h : ∀ j, j ≠ i → ∀ x y b : ℤ, x ≡ y [ZMOD m] →
      (x ≡ b [ZMOD (n i).gcd (n j)] ↔ y ≡ b [ZMOD (n i).gcd (n j)])) :
    interactionModulus n i ∣ m := by
  apply Finset.lcm_dvd
  intro j hj
  have hm : (0 : ℤ) ≡ m [ZMOD m] := by simp [Int.ModEq]
  have hd := (h j (mem_erase.mp hj).1 0 m 0 hm).mp (Int.ModEq.refl 0)
  exact Int.natCast_dvd_natCast.mp (Int.modEq_zero_iff_dvd.mp hd)

end Compression

/-- Independent reduction to canonical representatives at each given modulus.
@isnad1 id=iff.0h5v.s5.f05316d08b81 from=translated src=- shape=881d3415 vocab=83584d89
-/
theorem reduce_preserves_compatibility (n : ι → ℕ) (a : ι → ℤ) (i j : ι) :
    Compatible n (fun i => a i % n i) i j ↔ Compatible n a i j := by
  have hi := (Int.mod_modEq (a i) (n i)).of_dvd
    (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left (n i) (n j)))
  have hj := (Int.mod_modEq (a j) (n j)).of_dvd
    (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right (n i) (n j)))
  exact ⟨fun h => hi.symm.trans (h.trans hj),
    fun h => hi.trans (h.trans hj.symm)⟩

/--
@isnad1 id=iff.0h6v.s5.cc5d8dd21726 from=translated src=- shape=2c5804da vocab=5a7fc7bb
-/
theorem translate_preserves_compatibility (n : ι → ℕ) (a : ι → ℤ)
    (t : ℤ) (i j : ι) :
    Compatible n (fun i => a i - t) i j ↔ Compatible n a i j := by
  simp [compatible_iff_dvd]

end Erdos278
