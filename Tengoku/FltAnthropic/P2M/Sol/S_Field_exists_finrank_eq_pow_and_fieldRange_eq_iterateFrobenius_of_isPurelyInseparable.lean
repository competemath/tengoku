import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Field_exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Field_exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable

namespace W8OChildA

variable {E : Type*} [Field E] (p : ℕ) [Fact p.Prime] [CharP E p]

noncomputable def En (n : ℕ) : Subfield E := Subfield.map (iterateFrobenius E p n) ⊤

/--
@isnad1 id=eq.0h2v.s5.a838279149da from=translated src=- shape=8d62bf95 vocab=7059d3f2
-/
lemma En_zero : En p 0 = (⊤ : Subfield E) := by
  ext x
  simp only [En, iterateFrobenius_zero, Subfield.mem_map, RingHom.id_apply, Subfield.mem_top,
    true_and, exists_eq]

/--
@isnad1 id=eq.0h3v.s6.12ceb6e0204d from=translated src=- shape=61e18463 vocab=c4abcc2d
-/
lemma En_succ (n : ℕ) :
    En p (n + 1) = Subfield.map (frobenius E p) (En p n) := by
  rw [En, En, Subfield.map_map, ← iterateFrobenius_one, ← iterateFrobenius_add, Nat.add_comm]

/--
@isnad1 id=eq.0h2v.s5.f56a48c0ab48 from=translated src=- shape=1fc8f458 vocab=e9f46dad
-/
lemma En_one : En p 1 = (frobenius E p).fieldRange := by
  rw [En, iterateFrobenius_one, RingHom.fieldRange_eq_map]

/--
@isnad1 id=le.0h3v.s6.7c9a80835b4b from=translated src=- shape=d766690c vocab=2552b2aa
-/
lemma map_frobenius_le (S : Subfield E) :
    Subfield.map (frobenius E p) S ≤ S := by
  rintro _ ⟨x, hx, rfl⟩
  rw [frobenius_def]
  exact pow_mem hx p

/--
@isnad1 id=le.0h3v.s8.fbcb23f36fbf from=translated src=- shape=a407faf3 vocab=e8b038db
-/
lemma En_exponent_le (S : Subfield E) [IsPurelyInseparable S E]
    [FiniteDimensional S E] :
    En p (IsPurelyInseparable.exponent S E) ≤ S := by
  rintro _ ⟨x, -, rfl⟩
  rw [iterateFrobenius_def]
  obtain ⟨y, hy⟩ := RingHom.mem_range.1 (IsPurelyInseparable.exponent_def' S p x)
  rw [← hy]
  exact y.2

/--
@isnad1 id=le.2h3v.s8.0824bc723616 from=translated src=- shape=5edb6c22 vocab=a107ab22
-/
lemma le_En_one (hp : Module.finrank (frobenius E p).fieldRange E = p)
    (S : Subfield E) [IsPurelyInseparable S E] [FiniteDimensional S E] (hS : S ≠ ⊤) :
    S ≤ En p 1 := by
  have hprime : p.Prime := Fact.out
  have hE1top : (En (E := E) p 1).relfinrank ⊤ = p := by
    rw [Subfield.relfinrank_top_right, En_one]; exact hp
  have hmul := Subfield.relfinrank_mul_relfinrank
    (le_sup_left : En p 1 ≤ En p 1 ⊔ S) (le_top : En p 1 ⊔ S ≤ ⊤)
  rw [hE1top] at hmul
  have hdvd : (En p 1 ⊔ S).relfinrank ⊤ ∣ p := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime hprime).1 hdvd with h1 | h2
  ·
    exfalso
    have htop : (⊤ : Subfield E) ≤ En p 1 ⊔ S := Subfield.relfinrank_eq_one_iff.1 h1
    have key : ∀ n : ℕ, (⊤ : Subfield E) ≤ En p n ⊔ S := by
      intro n
      induction n with
      | zero => rw [En_zero]; exact le_sup_left
      | succ n ih =>
        have hmono : Subfield.map (frobenius E p) ⊤ ≤
            Subfield.map (frobenius E p) (En p n ⊔ S) :=
          (Subfield.gc_map_comap (frobenius E p)).monotone_l ih
        rw [Subfield.map_sup, ← En_succ] at hmono
        have hE1 : En p 1 ≤ En p (n + 1) ⊔ S := by
          rw [En_one, RingHom.fieldRange_eq_map]
          exact hmono.trans (sup_le_sup_left (map_frobenius_le p S) _)
        exact htop.trans (sup_le hE1 le_sup_right)
    have hle : (⊤ : Subfield E) ≤ S :=
      (key (IsPurelyInseparable.exponent S E)).trans (sup_le (En_exponent_le p S) le_rfl)
    exact hS (top_le_iff.1 hle)
  · rw [h2] at hmul
    have h1 : (En p 1).relfinrank (En p 1 ⊔ S) = 1 := by
      have : (En p 1).relfinrank (En p 1 ⊔ S) * p = 1 * p := by rw [hmul, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hprime.pos this
    exact le_sup_right.trans (Subfield.relfinrank_eq_one_iff.1 h1)

/--
@isnad1 id=ex.4h4v.s9.9f2b5a3b1534 from=translated src=- shape=3ab9b6fa vocab=16e90d5c
-/
theorem core (hp : Module.finrank (frobenius E p).fieldRange E = p) :
    ∀ (d : ℕ) (S : Subfield E), IsPurelyInseparable S E → FiniteDimensional S E →
      Module.finrank S E = d → ∃ r : ℕ, d = p ^ r ∧ S = En p r := by
  have hprime : p.Prime := Fact.out
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro S hPI hFD hd
  by_cases hS : S = ⊤
  · subst hS
    refine ⟨0, ?_, (En_zero p).symm⟩
    rw [← hd, pow_zero, ← Subfield.relfinrank_top_right, Subfield.relfinrank_self]
  · have hle : S ≤ En p 1 := le_En_one p hp S hS
    obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Subfield E, S₁ = Subfield.comap (frobenius E p) S := ⟨_, rfl⟩
    have hmap : Subfield.map (frobenius E p) S₁ = S := by
      rw [hS₁]
      apply Subfield.map_comap_eq_self
      rw [← En_one]; exact hle

    have hrel : Module.finrank S E = Module.finrank S₁ E * p := by
      rw [← Subfield.relfinrank_top_right, ← Subfield.relfinrank_top_right,
        ← Subfield.relfinrank_mul_relfinrank hle le_top]
      congr 1
      · rw [En, iterateFrobenius_one, ← hmap, Subfield.relfinrank_map_map]
      · rw [Subfield.relfinrank_top_right, En_one]; exact hp
    have hpos : 0 < Module.finrank S E := Module.finrank_pos
    have hpos₁ : 0 < Module.finrank S₁ E := by
      rcases Nat.eq_zero_or_pos (Module.finrank S₁ E) with h | h
      · rw [h, zero_mul] at hrel; omega
      · exact h
    haveI : FiniteDimensional S₁ E := Module.finite_of_finrank_pos hpos₁
    haveI : IsPurelyInseparable S₁ E := by
      rw [isPurelyInseparable_iff_pow_mem S₁ p]
      intro x
      obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem S p x
      obtain ⟨y, hy⟩ := RingHom.mem_range.1 hn
      have hmem : x ^ p ^ (n + 1) ∈ S₁ := by
        rw [hS₁, Subfield.mem_comap, frobenius_def, pow_succ, pow_mul, ← hy]
        exact pow_mem (pow_mem y.2 _) _
      exact ⟨n + 1, RingHom.mem_range.2 ⟨⟨_, hmem⟩, rfl⟩⟩
    have hlt : Module.finrank S₁ E < d := by
      rw [← hd, hrel]
      have := (Nat.mul_lt_mul_left hpos₁).2 hprime.one_lt
      rwa [mul_one] at this
    obtain ⟨r, hr, hS₁r⟩ := ih _ hlt S₁ ‹_› ‹_› rfl
    refine ⟨r + 1, ?_, ?_⟩
    · rw [← hd, hrel, hr, pow_succ]
    · rw [← hmap, hS₁r, En_succ]

/--
@isnad1 id=ex.1h3v.s8.3f6ca0edff77 from=translated src=- shape=83f9f733 vocab=d4b84a13
-/
theorem main {M E : Type*} [Field M] [Field E] [Algebra M E] [FiniteDimensional M E]
    [IsPurelyInseparable M E] (p : ℕ) [Fact p.Prime] [CharP E p]
    (hp : Module.finrank (frobenius E p).fieldRange E = p) :
    ∃ r : ℕ, Module.finrank M E = p ^ r ∧
      (algebraMap M E).fieldRange = (iterateFrobenius E p r).fieldRange := by
  haveI : CharP M p := (Algebra.charP_iff M E p).2 inferInstance
  have hfr : Module.finrank M E = Module.finrank (algebraMap M E).fieldRange E := by
    refine Algebra.finrank_eq_of_equiv_equiv
      (RingHom.rangeRestrictFieldEquiv (algebraMap M E)) (RingEquiv.refl E) ?_
    ext x; rfl
  haveI : FiniteDimensional (algebraMap M E).fieldRange E :=
    Module.finite_of_finrank_pos (hfr ▸ Module.finrank_pos)
  haveI : IsPurelyInseparable (algebraMap M E).fieldRange E := by
    rw [isPurelyInseparable_iff_pow_mem (algebraMap M E).fieldRange p]
    intro x
    obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem M p x
    obtain ⟨y, hy⟩ := RingHom.mem_range.1 hn
    exact ⟨n, RingHom.mem_range.2 ⟨⟨x ^ p ^ n, RingHom.mem_fieldRange.2 ⟨y, hy⟩⟩, rfl⟩⟩
  obtain ⟨r, hr, hR⟩ := core p hp _ (algebraMap M E).fieldRange ‹_› ‹_› rfl
  exact ⟨r, hfr.trans hr, hR.trans (by rw [En, RingHom.fieldRange_eq_map])⟩

end W8OChildA

/--
@isnad1 id=ex.1h3v.s8.3f6ca0edff77 from=translated src=- shape=83f9f733 vocab=d4b84a13
-/
theorem solution
    {M E : Type*} [Field M] [Field E] [Algebra M E] [FiniteDimensional M E]
    [IsPurelyInseparable M E] (p : ℕ) [Fact p.Prime] [CharP E p]
    (hp : Module.finrank (frobenius E p).fieldRange E = p) :
    ∃ r : ℕ, Module.finrank M E = p ^ r ∧
      (algebraMap M E).fieldRange = (iterateFrobenius E p r).fieldRange :=
  W8OChildA.main p hp
