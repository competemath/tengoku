import Tengoku.ErdosLean.ErdosLean.DuffinSchaeffer.Parts.GoodSubgraph
import Tengoku.ErdosLean.ErdosLean.DuffinSchaeffer.Parts.Anatomy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Duffin–Schaeffer — Part 18: the edge bound (KM Prop. 6.3 via §7, and Prop. 5.4)

-/

open Finset

namespace DuffinSchaeffer

/-! ### Auxiliary lemmas (racing prover) -/

/--
@isnad1 id=eq.1h3v.s6.2be72c82f308 from=translated src=- shape=90221d99 vocab=474ebcf5
-/
theorem alt63_prod_fact (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (q : ℕ) :
    (∏ p ∈ P, p ^ f p).factorization q = if q ∈ P then f q else 0 := by
  classical
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (hP p hp).ne_zero),
    Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (g := fun p => if p = q then f p else 0)]
  · exact Finset.sum_ite_eq' P q f
  · intro p hp
    rw [Nat.factorization_pow, (hP p hp).factorization, Finsupp.smul_apply,
      Finsupp.single_apply]
    split_ifs <;> simp

/--
@isnad1 id=dvd.3h3v.s6.34b3a823059f from=translated src=- shape=e92fd032 vocab=c85dcf33
-/
theorem alt63_prod_dvd (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ) (hv : v ≠ 0)
    (hd : ∀ p ∈ P, p ^ f p ∣ v) : (∏ p ∈ P, p ^ f p) ∣ v := by
  classical
  have h0 : (∏ p ∈ P, p ^ f p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun p hp => pow_ne_zero _ (hP p hp).ne_zero)
  rw [← Nat.factorization_le_iff_dvd h0 hv, Finsupp.le_def]
  intro q
  rw [alt63_prod_fact P f hP q]
  split_ifs with hq
  · exact ((hP q hq).pow_dvd_iff_le_factorization hv).1 (hd q hq)
  · exact Nat.zero_le _

/--
@isnad1 id=lt.1h2v.s5.022f10c7bc9f from=translated src=- shape=2de6e37a vocab=6497adf6
-/
theorem alt63_prod_pos (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 < ∏ p ∈ P, p ^ f p :=
  Finset.prod_pos (fun p hp => pow_pos (hP p hp).pos _)

/-- Counting multiples of `a` up to `M`.
@isnad1 id=le.2h3v.s6.759c7b90916f from=translated src=- shape=3ee35dc1 vocab=e42fec6c
-/
theorem alt63_card_dvd_le (S : Finset ℕ) (a M : ℕ) (ha : 0 < a)
    (hS : ∀ v ∈ S, 0 < v ∧ a ∣ v ∧ v ≤ M) : (S.card : ℝ) ≤ (M : ℝ) / a := by
  have hinj : Set.InjOn (fun v => v / a) S := by
    intro x hx y hy hxy
    simp only at hxy
    obtain ⟨-, hax, -⟩ := hS x hx
    obtain ⟨-, hay, -⟩ := hS y hy
    rw [← Nat.div_mul_cancel hax, ← Nat.div_mul_cancel hay, hxy]
  have hsub : S.image (fun v => v / a) ⊆ Icc 1 (M / a) := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨hv0, hav, hvM⟩ := hS v hv
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd hv0 hav) ha, Nat.div_le_div_right hvM⟩
  have h1 : S.card ≤ M / a := by
    rw [← Finset.card_image_of_injOn hinj]
    calc (S.image (fun v => v / a)).card ≤ (Icc 1 (M / a)).card := Finset.card_le_card hsub
      _ = M / a := by simp
  calc (S.card : ℝ) ≤ ((M / a : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (M : ℝ) / a := Nat.cast_div_le

/-- `1 - x ≥ e^{-2x}` for `0 ≤ x ≤ 1/2`.
@isnad1 id=le.2h1v.s6.1178bb2db5b7 from=translated src=- shape=2ff9909f vocab=459e50bf
-/
theorem alt63_exp_le_one_sub (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have h1 : 0 < 1 - x := by linarith
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : -2 * x ≤ 1 - (1 - x)⁻¹ := by
    rw [← div_one (1 : ℝ), one_div_one, ← one_div]
    rw [show (1 : ℝ) - 1 / (1 - x) = -x / (1 - x) by field_simp; ring]
    rw [le_div_iff₀ h1]
    nlinarith
  calc Real.exp (-2 * x) ≤ Real.exp (Real.log (1 - x)) := Real.exp_le_exp.2 (le_trans h3 h2)
    _ = 1 - x := Real.exp_log h1

/-- `φ(v)/v = ∏_{p | v} (1 - 1/p)` in `ℝ`.
@isnad1 id=eq.0h1v.s5.71cc91fdd4e1 from=translated src=- shape=f01920cd vocab=f7b65907
-/
theorem alt63_totient_real (n : ℕ) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  exact h

namespace GCDGraph

/--
@isnad1 id=eq.2h2v.s6.4973d510f658 from=translated src=- shape=b7f4ffed vocab=75375e44
-/
theorem alt63_gcd_eq (H : GCDGraph) (hR : H.R = ∅) (e : ℕ × ℕ) (he : e ∈ H.E) :
    Nat.gcd e.1 e.2 = ∏ p ∈ H.P, p ^ min (H.f p) (H.g p) := by
  classical
  obtain ⟨hv, hw⟩ := Finset.mem_product.1 (H.E_sub he)
  have hv0 := H.V_pos _ hv
  have hg0 : Nat.gcd e.1 e.2 ≠ 0 := (Nat.gcd_pos_of_pos_left _ hv0).ne'
  have hp0 : (∏ p ∈ H.P, p ^ min (H.f p) (H.g p)) ≠ 0 :=
    (alt63_prod_pos H.P _ H.P_prime).ne'
  apply Nat.eq_of_factorization_eq hg0 hp0
  intro q
  rw [alt63_prod_fact H.P _ H.P_prime q]
  split_ifs with hq
  · exact H.gcd_E q hq e he
  · rw [Nat.factorization_eq_zero_iff]
    by_contra hc
    push Not at hc
    obtain ⟨hqp, hqd, -⟩ := hc
    have : q ∈ H.R := by
      unfold R
      refine Finset.mem_sdiff.2 ⟨Finset.mem_biUnion.2 ⟨e, he, ?_⟩, hq⟩
      exact Nat.mem_primeFactors.2 ⟨hqp, hqd, hg0⟩
    rw [hR] at this
    exact absurd this (Finset.notMem_empty q)

/--
@isnad1 id=eq.0h1v.s6.5b04332680fa from=translated src=- shape=0263935f vocab=b3c26c56
-/
theorem alt63_X_mul (H : GCDGraph) :
    (∏ p ∈ H.P, p ^ H.fgDist p) * (∏ p ∈ H.P, p ^ min (H.f p) (H.g p)) ^ 2 =
      H.aProd * H.bProd := by
  unfold aProd bProd
  rw [sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  unfold fgDist
  omega

/--
@isnad1 id=eq.0h1v.s8.1e8190fb141c from=translated src=- shape=cec5c20b vocab=f921c7fb
-/
theorem alt63_quality_eq (H : GCDGraph) :
    H.quality = H.density ^ 10 * wsum H.μ H.V * wsum H.μ H.W *
      ((∏ p ∈ H.P, (p : ℝ) ^ H.fgDist p) /
        ((∏ p ∈ H.P, (1 - (if H.f p = H.g p ∧ 1 ≤ H.f p then 1 / (p : ℝ) else 0)) ^ 2) *
          ∏ p ∈ H.P, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) := by
  unfold quality qualityFactor
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]

end GCDGraph

/-! ### Deduction of Proposition 6.3 from Proposition 7.1 (KM §7) -/

/--
@isnad1 id=le.2h3v.s7.d187eb12ed9e from=translated src=- shape=3feccf9e vocab=90ea5be0
-/
theorem alt63_Lsum_split (t : ℝ) (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    Lsum t x y ≤ ∑ p ∈ x.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p +
      ∑ p ∈ y.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p := by
  classical
  unfold Lsum
  have hsub : (coprimePart x y).primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) ⊆
      x.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) ∪
        y.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hpd, -⟩, htp⟩ := hp
    unfold coprimePart at hpd
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2
        ⟨hpp, h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)), hx.ne'⟩, htp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2
        ⟨hpp, h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)), hy.ne'⟩, htp⟩)
  calc _ ≤ ∑ p ∈ (x.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) ∪
          y.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ))), (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := alt84_sum_union_le _ _ _ (fun _ => by positivity)

/-- Counting "bad" multiples of `a` up to `M`.
@isnad1 id=le.4h5v.s7.7aeae8adae8b from=translated src=- shape=cd7f71a8 vocab=f06e5ebf
-/
theorem alt63_count (S : Finset ℕ) (a M : ℕ) (ha : 0 < a) (bad : ℕ → Prop) [DecidablePred bad]
    (D : ℝ) (hD : 0 ≤ D)
    (hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x)
    (hS : ∀ v ∈ S, 0 < v ∧ a ∣ v ∧ v ≤ M ∧ bad (v / a)) :
    (S.card : ℝ) ≤ D * ((M : ℝ) / a) := by
  rcases S.eq_empty_or_nonempty with h | ⟨v0, hv0⟩
  · rw [h, Finset.card_empty, Nat.cast_zero]; positivity
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hMa : 1 ≤ (M : ℝ) / a := by
    obtain ⟨h0, hd, hM, -⟩ := hS v0 hv0
    rw [le_div_iff₀ haR, one_mul]
    exact_mod_cast (Nat.le_of_dvd h0 hd).trans hM
  have hinj : Set.InjOn (fun v => v / a) S := by
    intro x hx y hy hxy
    simp only at hxy
    obtain ⟨-, hax, -⟩ := hS x hx
    obtain ⟨-, hay, -⟩ := hS y hy
    rw [← Nat.div_mul_cancel hax, ← Nat.div_mul_cancel hay, hxy]
  have hsub : S.image (fun v => v / a) ⊆ (Icc 1 ⌊(M : ℝ) / a⌋₊).filter bad := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨hv0, hav, hvM, hb⟩ := hS v hv
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.div_pos (Nat.le_of_dvd hv0 hav) ha, ?_⟩, hb⟩
    rw [Nat.floor_div_eq_div]
    exact Nat.div_le_div_right hvM
  calc (S.card : ℝ) = ((S.image (fun v => v / a)).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ (((Icc 1 ⌊(M : ℝ) / a⌋₊).filter bad).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ D * ((M : ℝ) / a) := hcount _ hMa

/--
@isnad1 id=eq.0h1v.s5.183e2b6cc841 from=translated src=- shape=6f269b1b vocab=db37fc01
-/
theorem alt63_esum_eq (G : GCDGraph) :
    esum G.μ G.E = G.density * (wsum G.μ G.V * wsum G.μ G.W) := by
  unfold GCDGraph.density
  rcases eq_or_ne (wsum G.μ G.V * wsum G.μ G.W) 0 with h | h
  · rw [h, mul_zero]
    have := GCDGraph.alt_esum_le G.μ_nonneg G.E_sub
    rw [h] at this
    exact le_antisymm this (GCDGraph.alt_esum_nonneg G.μ_nonneg _)
  · rw [div_mul_cancel₀ _ h]

/-- One fibre `{(v, w) ∈ E}` over a fixed `w`, restricted to bad `v / a`.
@isnad1 id=le.6h8v.s8.7a2d47152754 from=translated src=- shape=a699824c vocab=c84665a4
-/
theorem alt63_fiber (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t)
    (m : ℕ) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m) (bad : ℕ → Prop) [DecidablePred bad]
    (D : ℝ) (hD : 0 ≤ D)
    (hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x)
    (w : ℕ) (F : Finset (ℕ × ℕ)) (hF : ∀ e ∈ F, e ∈ H.E ∧ e.2 = w ∧ bad (e.1 / H.aProd)) :
    (F.card : ℝ) * ψ w ≤ D * t * m / H.aProd := by
  classical
  have ha : 0 < H.aProd := alt63_prod_pos H.P H.f H.P_prime
  have haR : (0 : ℝ) < H.aProd := by exact_mod_cast ha
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · rw [hFe, Finset.card_empty, Nat.cast_zero, zero_mul]; positivity
  set S := F.image Prod.fst with hSdef
  have hSne : S.Nonempty := hFne.image _
  have hvmS : S.max' hSne ∈ S := S.max'_mem hSne
  obtain ⟨e0, he0F, he0v⟩ := Finset.mem_image.1 hvmS
  obtain ⟨he0E, he0w, -⟩ := hF e0 he0F
  have hinj : Set.InjOn Prod.fst (F : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have h1 := (hF x hx).2.1
    have h2 := (hF y hy).2.1
    exact Prod.ext hxy (h1.trans h2.symm)
  have hcard : F.card = S.card := (Finset.card_image_of_injOn hinj).symm
  have hcS : (S.card : ℝ) ≤ D * (((S.max' hSne : ℕ) : ℝ) / H.aProd) := by
    apply alt63_count S H.aProd (S.max' hSne) ha bad D hD hcount
    intro v hv
    obtain ⟨e, heF, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨heE, -, hb⟩ := hF e heF
    have hv := (Finset.mem_product.1 (H.E_sub heE)).1
    exact ⟨H.V_pos _ hv, alt63_prod_dvd H.P H.f H.P_prime _ (H.V_pos _ hv).ne'
      (fun p hp => H.dvd_V p hp _ hv), S.le_max' _ (Finset.mem_image_of_mem _ heF), hb⟩
  have hψw : ((S.max' hSne : ℕ) : ℝ) * ψ w ≤ t * m := by
    have h := hM e0 he0E
    unfold Mqr at h
    rw [← he0v, ← he0w]
    exact le_trans (le_max_right _ _) h
  calc (F.card : ℝ) * ψ w = S.card * ψ w := by rw [hcard]
    _ ≤ D * (((S.max' hSne : ℕ) : ℝ) / H.aProd) * ψ w := mul_le_mul_of_nonneg_right hcS (hψ w)
    _ = D / H.aProd * (((S.max' hSne : ℕ) : ℝ) * ψ w) := by ring
    _ ≤ D / H.aProd * (t * m) := mul_le_mul_of_nonneg_left hψw (by positivity)
    _ = D * t * m / H.aProd := by ring

/--
@isnad1 id=le.5h6v.s8.e15de946b7f0 from=translated src=- shape=60c4bf5b vocab=07004828
-/
theorem alt63_sum_fst (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t)
    (m : ℕ) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m) (bad : ℕ → Prop) [DecidablePred bad]
    (D : ℝ) (hD : 0 ≤ D)
    (hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x) :
    ∑ e ∈ H.E.filter (fun e => bad (e.1 / H.aProd)), ψ e.2 ≤
      H.W.card * (D * t * m / H.aProd) := by
  classical
  have hmaps : ∀ e ∈ H.E.filter (fun e => bad (e.1 / H.aProd)), e.2 ∈ H.W := fun e he =>
    (Finset.mem_product.1 (H.E_sub (Finset.mem_filter.1 he).1)).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ w ∈ H.W, D * t * m / H.aProd := by
        apply Finset.sum_le_sum
        intro w _
        rw [Finset.sum_congr rfl (g := fun _ => ψ w)
          (fun e he => by rw [(Finset.mem_filter.1 he).2]), Finset.sum_const, nsmul_eq_mul]
        apply alt63_fiber H ψ hψ t ht m hM bad D hD hcount w
        intro e he
        simp only [Finset.mem_filter] at he
        exact ⟨he.1.1, he.2, he.1.2⟩
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/--
@isnad1 id=le.3h5v.s7.7b4036ad60ca from=translated src=- shape=1495cbdd vocab=4601512d
-/
theorem alt63_sum_snd (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t)
    (m : ℕ) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m) (bad : ℕ → Prop) [DecidablePred bad] :
    ∑ e ∈ H.E.filter (fun e => bad (e.2 / H.bProd)), ψ e.2 ≤
      (H.W.filter (fun w => bad (w / H.bProd))).card * (t * m / H.aProd) := by
  classical
  have hmaps : ∀ e ∈ H.E.filter (fun e => bad (e.2 / H.bProd)),
      e.2 ∈ H.W.filter (fun w => bad (w / H.bProd)) := fun e he =>
    Finset.mem_filter.2 ⟨(Finset.mem_product.1 (H.E_sub (Finset.mem_filter.1 he).1)).2,
      (Finset.mem_filter.1 he).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ w ∈ H.W.filter (fun w => bad (w / H.bProd)), t * m / H.aProd := by
        apply Finset.sum_le_sum
        intro w _
        rw [Finset.sum_congr rfl (g := fun _ => ψ w)
          (fun e he => by rw [(Finset.mem_filter.1 he).2]), Finset.sum_const, nsmul_eq_mul]
        have h := alt63_fiber H ψ hψ t ht m hM (fun _ => True) 1 zero_le_one
          (fun x hx => by
            rw [Finset.filter_true_of_mem (fun _ _ => trivial), Nat.card_Icc, one_mul]
            simp only [add_tsub_cancel_right]
            exact Nat.floor_le (by linarith))
          w (((H.E.filter (fun e => bad (e.2 / H.bProd))).filter (fun e => e.2 = w)))
          (fun e he => by
            simp only [Finset.mem_filter] at he
            exact ⟨he.1.1, he.2, trivial⟩)
        rwa [one_mul] at h
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end DuffinSchaeffer
