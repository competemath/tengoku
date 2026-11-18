import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvPolynomial_CrossingResolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_CrossingQuotient_exists_algEquiv_quotient_span_U_and_span_V_polynomial.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_CrossingQuotient_exists_algEquiv_quotient_span_U_and_span_V_polynomial

set_option autoImplicit false

namespace CrossingResolutionBranch

open MvPolynomial MvPolynomial.CrossingQuotient

variable {W : Type*} [CommRing W] (s : W)

/--
@isnad1 id=eq.0h3v.s12.f76f43e28df3 from=translated src=- shape=d7d847a1 vocab=911d00c7
-/
theorem mk_C_eq (w : W) : mk s (C w) = algebraMap W (CrossingQuotient W s) w := by
  change mk s (algebraMap W (MvPolynomial (Fin 2) W) w) = _
  exact AlgHom.commutes _ w

/--
@isnad1 id=ex.0h3v.s12.c2a14df172b7 from=translated src=- shape=97eb3db4 vocab=0e87926f
-/
theorem exists_normalForm (f : CrossingQuotient W s) :
    ∃ p q : Polynomial W, f = Polynomial.aeval (U s) p + V s * Polynomial.aeval (V s) q := by
  obtain ⟨F, rfl⟩ := mk_surjective s f
  induction F using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Polynomial.C a, 0, ?_⟩
    simp only [Polynomial.aeval_C, map_zero, mul_zero, add_zero]
    exact mk_C_eq s a
  | add p q hp hq =>
    obtain ⟨p₁, q₁, h₁⟩ := hp
    obtain ⟨p₂, q₂, h₂⟩ := hq
    refine ⟨p₁ + p₂, q₁ + q₂, ?_⟩
    rw [map_add, h₁, h₂, map_add, map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨P, Q, hPQ⟩ := hp
    have hxy := U_mul_V s
    fin_cases i
    · refine ⟨Polynomial.X * P + Polynomial.C (s * Q.coeff 0), Polynomial.C s * Q.divX, ?_⟩
      have hQ : Polynomial.aeval (V s) Q = V s * Polynomial.aeval (V s) Q.divX +
          algebraMap W _ (Q.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [map_mul, hPQ]
      simp only [Fin.zero_eta, Fin.isValue, map_add, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C]
      rw [hQ]
      change _ * U s = U s * _ + _ + _
      linear_combination (Polynomial.aeval (V s) Q.divX * V s + (algebraMap W _ (Q.coeff 0))) * hxy
    · refine ⟨Polynomial.C s * P.divX, Polynomial.C (P.coeff 0) + Polynomial.X * Q, ?_⟩
      have hP : Polynomial.aeval (U s) P = U s * Polynomial.aeval (U s) P.divX +
          algebraMap W _ (P.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add P]
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [map_mul, hPQ]
      simp only [Fin.mk_one, Fin.isValue, map_add, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C]
      rw [hP]
      change _ * V s = _
      linear_combination (Polynomial.aeval (U s) P.divX) * hxy

variable (I : Ideal W)

/--
@isnad1 id=eq.1h3v.s8.a5de2f82a508 from=translated src=- shape=49cdb961 vocab=48c3c340
-/
theorem algebraMap_quot_s (hs : s ∈ I) : algebraMap W (Polynomial (W ⧸ I)) s = 0 := by
  rw [Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr hs, map_zero]

noncomputable def branchY (hs : s ∈ I) : CrossingQuotient W s →ₐ[W] Polynomial (W ⧸ I) :=
  CrossingQuotient.lift s 0 Polynomial.X (by rw [zero_mul, algebraMap_quot_s s I hs])

noncomputable def branchX (hs : s ∈ I) : CrossingQuotient W s →ₐ[W] Polynomial (W ⧸ I) :=
  CrossingQuotient.lift s Polynomial.X 0 (by rw [mul_zero, algebraMap_quot_s s I hs])

/--
@isnad1 id=eq.1h3v.s11.51d1d9b0ca9a from=translated src=- shape=2ee7f7b0 vocab=889d1bae
-/
@[scoped simp] theorem branchY_U (hs : s ∈ I) : branchY s I hs (U s) = 0 := lift_U _ _ _ _
/--
@isnad1 id=eq.1h3v.s11.5c0fb88bf6c5 from=translated src=- shape=9b32dff5 vocab=9d7b2339
-/
@[scoped simp] theorem branchY_V (hs : s ∈ I) : branchY s I hs (V s) = Polynomial.X := lift_V _ _ _ _
/--
@isnad1 id=eq.1h3v.s11.ad2c5940b1b3 from=translated src=- shape=9b32dff5 vocab=b630b3a0
-/
@[scoped simp] theorem branchX_U (hs : s ∈ I) : branchX s I hs (U s) = Polynomial.X := lift_U _ _ _ _
/--
@isnad1 id=eq.1h3v.s11.99fe7619520c from=translated src=- shape=2ee7f7b0 vocab=925efef9
-/
@[scoped simp] theorem branchX_V (hs : s ∈ I) : branchX s I hs (V s) = 0 := lift_V _ _ _ _

/--
@isnad1 id=eq.1h4v.s12.7ea2c6b94920 from=translated src=- shape=f2a0776b vocab=9a0be163
-/
theorem branchY_aeval_U (hs : s ∈ I) (p : Polynomial W) : branchY s I hs (Polynomial.aeval (U s) p) =
    Polynomial.C (algebraMap W (W ⧸ I) (p.coeff 0)) := by
  rw [← Polynomial.aeval_algHom_apply, branchY_U, ← Polynomial.coeff_zero_eq_aeval_zero',
    Polynomial.algebraMap_apply]

/--
@isnad1 id=eq.1h4v.s12.9d83f38b26f4 from=translated src=- shape=8e397dc5 vocab=33e3143a
-/
theorem branchY_aeval_V (hs : s ∈ I) (q : Polynomial W) :
    branchY s I hs (Polynomial.aeval (V s) q) = q.map (algebraMap W (W ⧸ I)) := by
  rw [← Polynomial.aeval_algHom_apply, branchY_V, Polynomial.aeval_X_left_eq_map]

/--
@isnad1 id=eq.1h4v.s12.0f6edd90b32c from=translated src=- shape=8e397dc5 vocab=3aa6ccf5
-/
theorem branchX_aeval_U (hs : s ∈ I) (p : Polynomial W) :
    branchX s I hs (Polynomial.aeval (U s) p) = p.map (algebraMap W (W ⧸ I)) := by
  rw [← Polynomial.aeval_algHom_apply, branchX_U, Polynomial.aeval_X_left_eq_map]

/--
@isnad1 id=surjecti.1h3v.s11.3703edb1a8c9 from=translated src=- shape=f91f5880 vocab=1348307e
-/
theorem branchY_surjective (hs : s ∈ I) : Function.Surjective (branchY s I hs) := fun g => by
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (algebraMap W (W ⧸ I))
    Ideal.Quotient.mk_surjective g
  exact ⟨Polynomial.aeval (V s) G, by rw [branchY_aeval_V, hG]⟩

/--
@isnad1 id=surjecti.1h3v.s11.d62a68e6af60 from=translated src=- shape=f91f5880 vocab=d99ac0f3
-/
theorem branchX_surjective (hs : s ∈ I) : Function.Surjective (branchX s I hs) := fun g => by
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (algebraMap W (W ⧸ I))
    Ideal.Quotient.mk_surjective g
  exact ⟨Polynomial.aeval (U s) G, by rw [branchX_aeval_U, hG]⟩

/--
@isnad1 id=mem.1h5v.s8.93fe3134eec7 from=translated src=- shape=6fd9ce1e vocab=f1e7123f
-/
theorem aeval_mem_map_of_map_eq_zero {A : Type*} [CommRing A] [Algebra W A] (a : A)
    {q : Polynomial W} (hq : q.map (algebraMap W (W ⧸ I)) = 0) :
    Polynomial.aeval a q ∈ I.map (algebraMap W A) := by
  have hmem : q ∈ RingHom.ker (Polynomial.mapRingHom (algebraMap W (W ⧸ I))) := hq
  rw [Polynomial.ker_mapRingHom, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at hmem
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  refine Ideal.sum_mem _ (fun n _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
  exact (Ideal.mem_map_C_iff.mp hmem) n

/--
@isnad1 id=eq.1h3v.s13.acfdcbe8e3cc from=translated src=- shape=2c8d57aa vocab=df06a573
-/
theorem ker_branchY (hs : s ∈ I) : RingHom.ker (branchY s I hs) =
    Ideal.span {U s} ⊔ I.map (algebraMap W (CrossingQuotient W s)) := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨p, q, rfl⟩ := exists_normalForm s f
    rw [map_add, map_mul, branchY_aeval_U, branchY_V, branchY_aeval_V] at hf
    have hq : q.map (algebraMap W (W ⧸ I)) = 0 := by
      ext n
      have := congrArg (fun g => Polynomial.coeff g (n+1)) hf
      simpa [Polynomial.coeff_C, Polynomial.coeff_X_mul] using this
    have hp0 : algebraMap W (W ⧸ I) (p.coeff 0) = 0 := by
      have := congrArg (fun g => Polynomial.coeff g 0) hf
      simpa [hq] using this
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hp0
    have hP : Polynomial.aeval (U s) p = U s * Polynomial.aeval (U s) p.divX +
        algebraMap W _ (p.coeff 0) := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add p]
      simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [hP]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hp0)
    · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (aeval_mem_map_of_map_eq_zero I _ hq))
  · rw [sup_le_iff, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, branchY_U,
      Ideal.map_le_iff_le_comap]
    refine ⟨rfl, fun w hw => ?_⟩
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Polynomial.algebraMap_apply,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hw, map_zero]

/--
@isnad1 id=eq.1h3v.s13.a2ce458c8dea from=translated src=- shape=2c8d57aa vocab=96d032c6
-/
theorem ker_branchX (hs : s ∈ I) : RingHom.ker (branchX s I hs) =
    Ideal.span {V s} ⊔ I.map (algebraMap W (CrossingQuotient W s)) := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨p, q, rfl⟩ := exists_normalForm s f
    rw [map_add, map_mul, branchX_aeval_U, branchX_V, zero_mul, add_zero] at hf
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mem_sup_right (aeval_mem_map_of_map_eq_zero I _ hf)
    · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · rw [sup_le_iff, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, branchX_V,
      Ideal.map_le_iff_le_comap]
    refine ⟨rfl, fun w hw => ?_⟩
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Polynomial.algebraMap_apply,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hw, map_zero]

/--
@isnad1 id=mem.0h2v.s12.b879377457d0 from=translated src=- shape=34ab73cc vocab=b87727f5
-/
theorem algebraMap_mem_span_U : algebraMap W (CrossingQuotient W s) s ∈ Ideal.span {U s} := by
  rw [← U_mul_V]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/--
@isnad1 id=mem.0h2v.s12.c68c3b161c28 from=translated src=- shape=34ab73cc vocab=3b70f549
-/
theorem algebraMap_mem_span_V : algebraMap W (CrossingQuotient W s) s ∈ Ideal.span {V s} := by
  rw [← U_mul_V]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/--
@isnad1 id=le.0h2v.s12.8c2e338d1bbc from=translated src=- shape=76c2c3ee vocab=43c7c134
-/
theorem map_span_le_span_U :
    (Ideal.span {s}).map (algebraMap W (CrossingQuotient W s)) ≤ Ideal.span {U s} := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  exact algebraMap_mem_span_U s

/--
@isnad1 id=le.0h2v.s12.c7789307075d from=translated src=- shape=76c2c3ee vocab=93099a77
-/
theorem map_span_le_span_V :
    (Ideal.span {s}).map (algebraMap W (CrossingQuotient W s)) ≤ Ideal.span {V s} := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  exact algebraMap_mem_span_V s

/--
@isnad1 id=eq.0h2v.s11.be3293e6a7db from=translated src=- shape=828cdd46 vocab=260bf756
-/
theorem ker_branchY_self : RingHom.ker (branchY s (Ideal.span {s}) (Ideal.mem_span_singleton_self s))
    = Ideal.span {U s} := by
  rw [ker_branchY, sup_eq_left]; exact map_span_le_span_U s

/--
@isnad1 id=eq.0h2v.s11.4bd77202c5f7 from=translated src=- shape=828cdd46 vocab=09412e1d
-/
theorem ker_branchX_self : RingHom.ker (branchX s (Ideal.span {s}) (Ideal.mem_span_singleton_self s))
    = Ideal.span {V s} := by
  rw [ker_branchX, sup_eq_left]; exact map_span_le_span_V s

end CrossingResolutionBranch
open scoped _root_.P2MW.S_MvPolynomial_CrossingQuotient_exists_algEquiv_quotient_span_U_and_span_V_polynomial.CrossingResolutionBranch

namespace CrossingResolutionR3a

open MvPolynomial MvPolynomial.CrossingQuotient CrossingResolutionBranch in
/--
@isnad1 id=and.0h2v.s16.cd692a2b7786 from=translated src=- shape=a109ba53 vocab=d2969b2b
-/
theorem main {W : Type*} [CommRing W] (t : W) :
    (∃ E : (MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.U t}) ≃ₐ[W]
        Polynomial (W ⧸ Ideal.span {t}),
        E (Ideal.Quotient.mk (Ideal.span {MvPolynomial.CrossingQuotient.U t})
          (MvPolynomial.CrossingQuotient.V t)) = Polynomial.X) ∧
    (∃ E : (MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.V t}) ≃ₐ[W]
        Polynomial (W ⧸ Ideal.span {t}),
        E (Ideal.Quotient.mk (Ideal.span {MvPolynomial.CrossingQuotient.V t})
          (MvPolynomial.CrossingQuotient.U t)) = Polynomial.X) := by
  have hs : t ∈ Ideal.span {t} := Ideal.mem_span_singleton_self t
  refine ⟨⟨(Ideal.quotientEquivAlgOfEq W (ker_branchY_self t).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (branchY_surjective t _ hs)), ?_⟩,
    ⟨(Ideal.quotientEquivAlgOfEq W (ker_branchX_self t).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (branchX_surjective t _ hs)), ?_⟩⟩
  · rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
      Ideal.quotientKerAlgEquivOfSurjective_mk, branchY_V]
  · rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
      Ideal.quotientKerAlgEquivOfSurjective_mk, branchX_U]

end CrossingResolutionR3a
open scoped _root_.P2MW.S_MvPolynomial_CrossingQuotient_exists_algEquiv_quotient_span_U_and_span_V_polynomial.CrossingResolutionBranch

open MvPolynomial MvPolynomial.CrossingQuotient in

/--
@isnad1 id=and.0h2v.s16.cd692a2b7786 from=translated src=- shape=a109ba53 vocab=d2969b2b
-/
theorem solution
    {W : Type*} [CommRing W] (t : W) :
    (∃ E : (CrossingQuotient W t ⧸ Ideal.span {U t}) ≃ₐ[W] Polynomial (W ⧸ Ideal.span {t}),
        E (Ideal.Quotient.mk (Ideal.span {U t}) (V t)) = Polynomial.X) ∧
    (∃ E : (CrossingQuotient W t ⧸ Ideal.span {V t}) ≃ₐ[W] Polynomial (W ⧸ Ideal.span {t}),
        E (Ideal.Quotient.mk (Ideal.span {V t}) (U t)) = Polynomial.X) :=
  CrossingResolutionR3a.main t
