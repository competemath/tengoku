/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku
import Tengoku.AndersonConjecture.Anderson.AdicKerEval

/-!
# Adic Completion of a Noetherian Local Ring is Noetherian

For a Noetherian local ring (R, M), the M-adic completion R-hat
is Noetherian. The key facts are that R-hat / M-hat^n is
isomorphic to R / M^n for each n, and that the completion is
M-adically complete, so the Noetherian property lifts by
successive approximation (Atiyah--Macdonald, Prop. 10.11).
-/

open AdicCompletion

open scoped Pointwise

variable {R : Type*} [CommRing R]

/-! ### Part 1: ker(evalₐ I n) = (map f I)ⁿ -/

section KernelEvalₐ

variable (I : Ideal R)

/-- `(map f I)ⁿ ⊆ ker(evalₐ I n)`: elements from I^n evaluate to zero. -/
lemma map_pow_le_ker_evalₐ (n : ℕ) :
    Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) ≤
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  change (evalₐ I n) (of I R r) = 0
  rw [evalₐ_of]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-- `ker(evalₐ M n) = M̂ⁿ` for Noetherian local R. -/
lemma ker_evalₐ_eq [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    RingHom.ker (evalₐ (IsLocalRing.maximalIdeal R) n).toRingHom =
    Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
      (IsLocalRing.maximalIdeal R) ^ n := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hx
    exact mem_map_pow_of_evalₐ_eq_zero R n x hx
  · rw [← Ideal.map_pow]
    exact map_pow_le_ker_evalₐ (IsLocalRing.maximalIdeal R) n

/-- Evaluations are stable along Cauchy sequences. -/
lemma eval_cauchy_stable (f : ℕ → AdicCompletion I R)
    (hf : ∀ {m n : ℕ}, m ≤ n →
      SModEq (I ^ m • (⊤ : Submodule R (AdicCompletion I R))) (f m) (f n))
    {k n : ℕ} (hkn : k ≤ n) :
    evalₐ I k (f n) = evalₐ I k (f k) := by
  have hmem := hf hkn
  rw [SModEq.sub_mem, Ideal.smul_top_eq_map] at hmem
  have := map_pow_le_ker_evalₐ I k hmem
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, sub_eq_zero] at this
  exact this.symm

/-- `factorPow ∘ evalₐ n = evalₐ m` for m ≤ n. -/
lemma factorPow_comp_evalₐ_noeth {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x := by
  apply induction_on I R
    (p := fun x => Ideal.Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x) x
  intro a
  simp only [evalₐ_mk]
  have hfactor : Ideal.Quotient.factorPow I hmn (Ideal.Quotient.mk (I ^ n) (a.1 n)) =
      Ideal.Quotient.mk (I ^ m) (a.1 n) := by
    unfold Ideal.Quotient.factorPow
    simp [Ideal.Quotient.factor_mk]
  rw [hfactor]
  have hcauchy := a.2 hmn
  rw [SModEq.sub_mem] at hcauchy
  have hmem : a.1 m - a.1 n ∈ (I ^ m : Ideal R) := by
    rwa [show I ^ m • (⊤ : Submodule R R) = (I ^ m : Ideal R) by
           ext
           simp] at hcauchy
  rw [Ideal.Quotient.eq]
  rwa [show a.1 n - a.1 m = -(a.1 m - a.1 n) from by ring, neg_mem_iff]

end KernelEvalₐ

/-! ### Part 2: R̂/M̂ⁿ ≅ R/Mⁿ -/

section QuotientIso

variable [IsLocalRing R] [IsNoetherianRing R]

/-- `R̂ / M̂ⁿ ≅ R / Mⁿ` as rings. -/
noncomputable def quotientPowEquiv (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
      (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
        (IsLocalRing.maximalIdeal R)) ^ n ≃+*
    R ⧸ (IsLocalRing.maximalIdeal R) ^ n := by
  have hker := ker_evalₐ_eq (R := R) n
  have hsurj := surjective_evalₐ (IsLocalRing.maximalIdeal R) n
  exact (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)

end QuotientIso

/-! ### Part 3: IsPrecomplete M (AdicCompletion M R) -/

section Precomplete

variable [IsLocalRing R] [IsNoetherianRing R]

end Precomplete

/-! ### Part 4: Main theorem — IsNoetherianRing R̂ -/

section Main

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Generic helper: build a recursive sequence with proof-carrying data.
This is a standalone `def` so its elaboration budget is independent. -/
noncomputable def buildSeq {α : Type*} {P : ℕ → α → Prop}
    (base : { a // P 0 a })
    (step : ∀ K, { a // P K a } → { a // P (K + 1) a }) :
    ∀ K, { a // P K a } :=
  fun K => Nat.rec base (fun K prev => step K prev) K

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Auxiliary: M * FN(n) ≤ FN(n+1) for the leading-term filtration FN. -/
lemma filtration_smul_le
    (Mi : Ideal R) (J : Ideal (AdicCompletion Mi R))
    (FN : ℕ → Ideal R)
    (hFN_def : ∀ n, FN n = Mi ^ n ⊓ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J))
    (n : ℕ) :
    Mi * FN n ≤ FN (n + 1) := by
  rw [Ideal.mul_le]
  intro m hm r hr_mem
  have hr_pow : r ∈ Mi ^ n := by rw [hFN_def] at hr_mem
                                 exact hr_mem.1
  have hr_comap : r ∈ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J) := by rw [hFN_def] at hr_mem
                                                       exact hr_mem.2
  rw [hFN_def]
  refine ⟨?_, ?_⟩
  · rw [pow_succ']
    exact Ideal.mul_mem_mul hm hr_pow
  · obtain ⟨y, hyJ, hyr⟩ := (Ideal.mem_map_iff_of_surjective _
      (surjective_evalₐ Mi (n + 1))).mp hr_comap
    have hmyJ : of Mi R m * y ∈ J := J.mul_mem_left _ hyJ
    apply (Ideal.mem_map_iff_of_surjective _
      (surjective_evalₐ Mi (n + 1 + 1))).mpr
    refine ⟨of Mi R m * y, hmyJ, ?_⟩
    have hlhs : evalₐ Mi (n + 1 + 1) (of Mi R m * y) =
        Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) m * evalₐ Mi (n + 1 + 1) y := by
      simp [map_mul, evalₐ_of]
    rw [hlhs]
    have hfp_y : Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1))
        (evalₐ Mi (n + 1 + 1) y) = evalₐ Mi (n + 1) y :=
      factorPow_comp_evalₐ_noeth Mi (Nat.le_succ (n + 1)) y
    have hfp_r : Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1))
        (Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r) =
        Ideal.Quotient.mk (Mi ^ (n + 1)) r := by
      unfold Ideal.Quotient.factorPow
      simp [Ideal.Quotient.factor_mk]
    have hdiff_quot : evalₐ Mi (n + 1 + 1) y - Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r ∈
        RingHom.ker (Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1))) := by
      rw [RingHom.mem_ker, map_sub, hfp_y, hfp_r, hyr, sub_self]
    rw [show Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) from rfl,
      Ideal.Quotient.factor_ker] at hdiff_quot
    obtain ⟨s, hs, hseq⟩ := (Ideal.mem_map_iff_of_surjective _
      Ideal.Quotient.mk_surjective).mp hdiff_quot
    suffices h0 : Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) m *
        (evalₐ Mi (n + 1 + 1) y - Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r) = 0 by
      have := h0
      rw [mul_sub] at this
      rw [show Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) m *
          Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r =
          Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) (m * r) from by rw [← map_mul]] at this
      exact sub_eq_zero.mp this
    have hseq' : Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) s =
        evalₐ Mi (n + 1 + 1) y - Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r := hseq
    rw [← hseq', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    rw [show n + 1 + 1 = (n + 1).succ from rfl, pow_succ']
    exact Ideal.mul_mem_mul hm hs

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Auxiliary: lift elements of Mi^K • FN(n0) to I₀ with evalₐ compatibility. -/
lemma smul_lift_of_filtration
    (Mi : Ideal R)
    (n0 K : ℕ)
    (FN_n0 : Ideal R)
    (S_F : Finset R) (hS_F : Ideal.span ↑S_F = FN_n0)
    (I₀ : Ideal (AdicCompletion Mi R))
    (hlift_span : ∀ t : R, t ∈ (Ideal.span ↑S_F : Ideal R) →
        ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
        evalₐ Mi (n0 + 1) δ = Ideal.Quotient.mk (Mi ^ (n0 + 1)) t)
    (r' : R) (hr' : r' ∈ (Mi ^ K • (FN_n0 : Submodule R R) : Submodule R R)) :
    ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
      evalₐ Mi (n0 + K + 1) δ =
      Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) r' := by
  refine Submodule.smul_induction_on hr' ?_ ?_
  · intro m hm s hs
    have hs_span : s ∈ (Ideal.span ↑S_F : Ideal R) :=
      hS_F ▸ hs
    obtain ⟨δ_s, hδ_s_I, hδ_s_eq⟩ := hlift_span s hs_span
    refine ⟨of Mi R m * δ_s, I₀.mul_mem_left _ hδ_s_I, ?_⟩
    rw [map_mul, evalₐ_of]
    have hdiff_ker : evalₐ Mi (n0 + K + 1) δ_s -
        Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) s ∈
        RingHom.ker (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (show n0 + 1 ≤ n0 + K + 1 by omega))) := by
      rw [RingHom.mem_ker, map_sub,
        show Ideal.Quotient.factor _ (evalₐ Mi (n0 + K + 1) δ_s) =
          evalₐ Mi (n0 + 1) δ_s from factorPow_comp_evalₐ_noeth Mi (by omega) δ_s,
        hδ_s_eq, Ideal.Quotient.factor_mk, sub_self]
    rw [Ideal.Quotient.factor_ker] at hdiff_ker
    have hmk_kills : Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) m *
        (evalₐ Mi (n0 + K + 1) δ_s -
          Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) s) = 0 := by
      obtain ⟨q, hq_mem, hq_eq⟩ := (Ideal.mem_map_iff_of_surjective _
        Ideal.Quotient.mk_surjective).mp hdiff_ker
      rw [← hq_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_pow_right (by omega)
        (show m * q ∈ Mi ^ (K + (n0 + 1)) by
           rw [pow_add]
           exact Ideal.mul_mem_mul hm hq_mem)
    rw [mul_sub] at hmk_kills
    rw [sub_eq_zero.mp hmk_kills, show m • s = m * s from rfl, ← map_mul]
  · intro a b ⟨δa, hδaI, hδaeq⟩ ⟨δb, hδbI, hδbeq⟩
    exact ⟨δa + δb, I₀.add_mem hδaI hδbI, by rw [map_add, hδaeq, hδbeq, map_add]⟩

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Auxiliary: extract a representative r ∈ Mi^K • FN_n0 from e ∈ Mhat^(n0+K) ∩ J. -/
lemma extract_filtration_rep
    (Mi : Ideal R) (J : Ideal (AdicCompletion Mi R))
    (FN : ℕ → Ideal R) (n0 K : ℕ)
    (hFN_def : ∀ n, FN n = Mi ^ n ⊓ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J))
    (FN_n0_sub : Submodule R R)
    (hn0_pow : ∀ K, Mi ^ K • FN_n0_sub = (fun n => (FN n : Submodule R R)) (n0 + K))
    (Mhat : Ideal (AdicCompletion Mi R))
    (hker_eq : ∀ N, RingHom.ker (evalₐ Mi N).toRingHom = Mhat ^ N)
    (e : AdicCompletion Mi R) (he : e ∈ Mhat ^ (n0 + K)) (heJ : e ∈ J) :
    ∃ r : R, r ∈ (Mi ^ K • FN_n0_sub : Submodule R R) ∧
      evalₐ Mi (n0 + K + 1) e = Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) r := by
  have he_ker : evalₐ Mi (n0 + K) e = 0 := by
    have : e ∈ RingHom.ker (evalₐ Mi (n0 + K)).toRingHom := hker_eq _ ▸ he
    rwa [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
  have he_factor : Ideal.Quotient.factorPow Mi (Nat.le_succ (n0 + K))
      (evalₐ Mi (n0 + K + 1) e) = 0 :=
    (factorPow_comp_evalₐ_noeth Mi (Nat.le_succ (n0 + K)) e).trans he_ker
  have he_in_map : evalₐ Mi (n0 + K + 1) e ∈
      Ideal.map (Ideal.Quotient.mk (Mi ^ (n0 + K + 1))) (Mi ^ (n0 + K)) := by
    have hfp : Ideal.Quotient.factorPow Mi (Nat.le_succ (n0 + K)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n0 + K))) := rfl
    rw [hfp] at he_factor
    rwa [← Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (Nat.le_succ (n0 + K))),
      RingHom.mem_ker]
  obtain ⟨r, hr_pow, hr_eq⟩ := (Ideal.mem_map_iff_of_surjective _
    Ideal.Quotient.mk_surjective).mp he_in_map
  have hr_FN : r ∈ FN (n0 + K) := by
    rw [hFN_def]
    exact ⟨hr_pow, by change r ∈ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n0 + K + 1)))
                        (Ideal.map (evalₐ Mi (n0 + K + 1)).toRingHom J)
                      rw [Ideal.mem_comap]
                      rw [hr_eq]
                      exact Ideal.mem_map_of_mem _ heJ⟩
  have hr_in_smul : r ∈ (Mi ^ K • FN_n0_sub : Submodule R R) := by
    rw [hn0_pow]
    exact (hFN_def (n0 + K) ▸ hr_FN : r ∈ (FN (n0 + K) : Submodule R R))
  exact ⟨r, hr_in_smul, hr_eq.symm⟩

end Main
