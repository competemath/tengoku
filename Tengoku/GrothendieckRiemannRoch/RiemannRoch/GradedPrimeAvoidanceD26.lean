/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.GradedAlgebra.Radical
import Tengoku.Seed.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graded prime avoidance (route D26)

Pure algebra, no geometry.  For a `ℕ`-graded commutative ring `A` (`𝒜 : ℕ → σ`) and finitely
many homogeneous primes `p` with a positive-degree homogeneous element outside `p`, there is a
single homogeneous element of positive degree outside all of them.  No infinite-field hypothesis.
Evaluation form: finitely many ring maps `φ i : A →+* K i` into domains with `φ i (A₊) ≠ 0`.
-/

open DirectSum

namespace RiemannRoch.GradedAvoidD26

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/--
@isnad1 id=ex.2h5v.s7.5be55d95d525 from=translated src=- shape=20c9ba2a vocab=cc049286
-/
theorem exists_homogeneous_mem_sdiff {q p : Ideal A} (hq : q.IsHomogeneous 𝒜)
    (hqp : ¬ q ≤ p) : ∃ n x, x ∈ 𝒜 n ∧ x ∈ q ∧ x ∉ p := by
  classical
  rw [SetLike.not_le_iff_exists] at hqp
  obtain ⟨r, hrq, hrp⟩ := hqp
  by_contra hcon
  push Not at hcon
  apply hrp
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  exact Ideal.sum_mem _ fun i _ => hcon i _ (SetLike.coe_mem _) (hq i hrq)

/--
@isnad1 id=ex.2h5v.s8.02d0b58a445a from=translated src=- shape=5477e85f vocab=bd553a3a
-/
theorem exists_homogeneous_mem_forall_not_mem {p : Ideal A} (hp : p.IsPrime)
    (T : Finset (Ideal A)) (hT : ∀ q ∈ T, q.IsHomogeneous 𝒜 ∧ ¬ q ≤ p) :
    ∃ n a, a ∈ 𝒜 n ∧ (∀ q ∈ T, a ∈ q) ∧ a ∉ p := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨0, 1, SetLike.one_mem_graded 𝒜, by simp,
      fun h => hp.ne_top ((Ideal.eq_top_iff_one p).2 h)⟩
  | insert q T hqT ih =>
    obtain ⟨n, a, ha, haT, hap⟩ := ih fun q' h => hT q' (Finset.mem_insert_of_mem h)
    obtain ⟨hqh, hqp⟩ := hT q (Finset.mem_insert_self _ _)
    obtain ⟨e, c, hc, hcq, hcp⟩ := exists_homogeneous_mem_sdiff 𝒜 hqh hqp
    refine ⟨n + e, a * c, SetLike.mul_mem_graded ha hc, ?_, ?_⟩
    · intro q' hq'
      rcases Finset.mem_insert.1 hq' with rfl | h
      · exact Ideal.mul_mem_left _ _ hcq
      · exact Ideal.mul_mem_right _ _ (haT q' h)
    · intro h
      rcases hp.mem_or_mem h with h | h
      · exact hap h
      · exact hcp h

/-- **Graded prime avoidance** (arbitrary base, finite fields allowed).
@isnad1 id=ex.1h4v.s8.43889f7c7dec from=translated src=- shape=d0b66c3c vocab=bd553a3a
-/
theorem graded_prime_avoidance (S : Finset (Ideal A))
    (hS : ∀ p ∈ S, p.IsPrime ∧ p.IsHomogeneous 𝒜 ∧ ∃ e, 1 ≤ e ∧ ∃ h ∈ 𝒜 e, h ∉ p) :
    ∃ m, 1 ≤ m ∧ ∃ f ∈ 𝒜 m, ∀ p ∈ S, f ∉ p := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, le_rfl, 0, zero_mem _, by simp⟩
  obtain ⟨p, hpS, hmin⟩ := S.exists_minimal hne
  obtain ⟨hpp, hph, e, he, h, hh, hhp⟩ := hS p hpS
  obtain ⟨m, hm, f, hf, hfS⟩ :=
    ih (S.erase p) (Finset.erase_ssubset hpS) fun q hq => hS q (Finset.mem_of_mem_erase hq)
  by_cases hfp : f ∈ p
  · have hT : ∀ q ∈ S.erase p, q.IsHomogeneous 𝒜 ∧ ¬ q ≤ p := by
      intro q hq
      have hqp : q ≠ p := Finset.ne_of_mem_erase hq
      have hqS := Finset.mem_of_mem_erase hq
      exact ⟨(hS q hqS).2.1, fun hle => hqp (le_antisymm hle (hmin hqS hle))⟩
    obtain ⟨n, a, ha, haT, hap⟩ := exists_homogeneous_mem_forall_not_mem 𝒜 hpp _ hT
    have ha' : a * h ∈ 𝒜 (n + e) := SetLike.mul_mem_graded ha hh
    have hap' : a * h ∉ p := fun hx => by
      rcases hpp.mem_or_mem hx with hx | hx
      · exact hap hx
      · exact hhp hx
    have hd : 1 ≤ n + e := le_trans he (Nat.le_add_left _ _)
    have h1 : f ^ (n + e) ∈ 𝒜 ((n + e) * m) := by
      simpa using SetLike.pow_mem_graded (n + e) hf
    have h2 : (a * h) ^ m ∈ 𝒜 ((n + e) * m) := by
      simpa [mul_comm] using SetLike.pow_mem_graded m ha'
    refine ⟨(n + e) * m, Nat.mul_pos hd hm |> fun h => h, f ^ (n + e) + (a * h) ^ m,
      add_mem h1 h2, ?_⟩
    intro q hq hg
    by_cases hqp : q = p
    · subst hqp
      have hfd : f ^ (n + e) ∈ q := Ideal.pow_mem_of_mem _ hfp _ hd
      have : (a * h) ^ m ∈ q := by simpa using q.sub_mem hg hfd
      exact hap' ((hS q hq).1.mem_of_pow_mem _ this)
    · have hqE : q ∈ S.erase p := Finset.mem_erase.2 ⟨hqp, hq⟩
      have hax : (a * h) ^ m ∈ q :=
        Ideal.pow_mem_of_mem _ (Ideal.mul_mem_right _ _ (haT q hqE)) _ hm
      have : f ^ (n + e) ∈ q := by simpa using q.sub_mem hg hax
      exact hfS q hqE ((hS q hq).1.mem_of_pow_mem _ this)
  · refine ⟨m, hm, f, hf, fun q hq hfq => ?_⟩
    by_cases hqp : q = p
    · exact hfp (hqp ▸ hfq)
    · exact hfS q (Finset.mem_erase.2 ⟨hqp, hq⟩) hfq

/-- Evaluation form: `φ i : A →+* K i` into domains, each not killing positive degree.
@isnad1 id=ex.1h7v.s8.5a208cac900e from=translated src=- shape=1b136b4b vocab=af2efae4
-/
theorem exists_homogeneous_eval_ne_zero {ι : Type*} (s : Finset ι) {K : ι → Type*}
    [∀ i, CommRing (K i)] [∀ i, IsDomain (K i)] (φ : ∀ i, A →+* K i)
    (hφ : ∀ i ∈ s, ∃ e, 1 ≤ e ∧ ∃ h ∈ 𝒜 e, φ i h ≠ 0) :
    ∃ m, 1 ≤ m ∧ ∃ f ∈ 𝒜 m, ∀ i ∈ s, φ i f ≠ 0 := by
  classical
  let P : ι → Ideal A := fun i => ((RingHom.ker (φ i)).homogeneousCore 𝒜).toIdeal
  obtain ⟨m, hm, f, hf, hfS⟩ := graded_prime_avoidance 𝒜 (s.image P) (by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨e, he, h, hh, hne⟩ := hφ i hi
    refine ⟨(RingHom.ker_isPrime (φ i)).homogeneousCore,
      (Ideal.homogeneousCore 𝒜 _).isHomogeneous, e, he, h, hh, fun hmem => hne ?_⟩
    exact (RingHom.mem_ker).1 (Ideal.toIdeal_homogeneousCore_le 𝒜 _ hmem))
  refine ⟨m, hm, f, hf, fun i hi hz => hfS (P i) (Finset.mem_image_of_mem _ hi) ?_⟩
  exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨m, hf⟩ (RingHom.mem_ker.2 hz)

/-- Progression strengthening: avoiders in every positive multiple of one degree.
@isnad1 id=ex.1h7v.s8.2cef83b4cef9 from=translated src=- shape=4060adf7 vocab=8edbaf5d
-/
theorem exists_homogeneous_eval_ne_zero_progression {ι : Type*} (s : Finset ι)
    {K : ι → Type*} [∀ i, CommRing (K i)] [∀ i, IsDomain (K i)] (φ : ∀ i, A →+* K i)
    (hφ : ∀ i ∈ s, ∃ e, 1 ≤ e ∧ ∃ h ∈ 𝒜 e, φ i h ≠ 0) :
    ∃ m, 1 ≤ m ∧ ∀ j, 1 ≤ j → ∃ f ∈ 𝒜 (j * m), ∀ i ∈ s, φ i f ≠ 0 := by
  obtain ⟨m, hm, f, hf, hfs⟩ := exists_homogeneous_eval_ne_zero 𝒜 s φ hφ
  refine ⟨m, hm, fun j _ => ⟨f ^ j, by simpa using SetLike.pow_mem_graded j hf,
    fun i hi => ?_⟩⟩
  rw [map_pow]
  exact pow_ne_zero _ (hfs i hi)

/-- Products of avoiders are avoiders: degrees form an additive semigroup.
@isnad1 id=ex.2h9v.s8.4f4bb2e0a339 from=translated src=- shape=1573ab14 vocab=9c1b52cd
-/
theorem eval_avoider_mul {ι : Type*} (s : Finset ι) {K : ι → Type*}
    [∀ i, CommRing (K i)] [∀ i, IsDomain (K i)] (φ : ∀ i, A →+* K i) {a b : ℕ}
    (ha : ∃ f ∈ 𝒜 a, ∀ i ∈ s, φ i f ≠ 0) (hb : ∃ f ∈ 𝒜 b, ∀ i ∈ s, φ i f ≠ 0) :
    ∃ f ∈ 𝒜 (a + b), ∀ i ∈ s, φ i f ≠ 0 := by
  obtain ⟨f, hf, hfs⟩ := ha
  obtain ⟨g, hg, hgs⟩ := hb
  exact ⟨f * g, SetLike.mul_mem_graded hf hg, fun i hi => by
    rw [map_mul]; exact mul_ne_zero (hfs i hi) (hgs i hi)⟩

end RiemannRoch.GradedAvoidD26
