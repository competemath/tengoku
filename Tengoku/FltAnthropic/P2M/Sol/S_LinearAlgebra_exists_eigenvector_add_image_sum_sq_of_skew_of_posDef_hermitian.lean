import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LinearAlgebra_exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LinearAlgebra_exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian

set_option autoImplicit false

noncomputable section

namespace WsB
namespace EIG

section Piece

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/--
@isnad1 id=eq.2h4v.s8.468344a5bcc3 from=translated src=- shape=1a422c5b vocab=3ef83c02
-/
theorem form_zero_left (M₀ : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    {n : W} (hn : n ∈ M₀) : B 0 n = 0 := by
  have h := hlin (-1) 0 M₀.zero_mem 0 M₀.zero_mem n hn
  rw [smul_zero, add_zero] at h
  linear_combination h

def orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) : Submodule ℂ W where
  carrier := {w | w ∈ M₀ ∧ ∀ n ∈ N, B w n = 0}
  add_mem' {a b} ha hb := ⟨M₀.add_mem ha.1 hb.1, fun n hn => by
    have h := hlin 1 a ha.1 b hb.1 n (hNM hn)
    rw [one_smul, one_mul, ha.2 n hn, hb.2 n hn, add_zero] at h
    exact h⟩
  zero_mem' := ⟨M₀.zero_mem, fun n hn => form_zero_left M₀ B hlin (hNM hn)⟩
  smul_mem' z a ha := ⟨M₀.smul_mem z ha.1, fun n hn => by
    have h := hlin z a ha.1 0 M₀.zero_mem n (hNM hn)
    rw [add_zero, ha.2 n hn, mul_zero, zero_add, form_zero_left M₀ B hlin (hNM hn)] at h
    exact h⟩

/--
@isnad1 id=iff.2h5v.s8.00555944f89a from=translated src=- shape=73476d04 vocab=9f06ab8f
-/
theorem mem_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (w : W) : w ∈ orthoIn M₀ N B hlin hNM ↔ w ∈ M₀ ∧ ∀ n ∈ N, B w n = 0 := Iff.rfl

/--
@isnad1 id=ex.4h4v.s9.5210237b0789 from=translated src=- shape=5e5a60df vocab=c6ca7cdc
-/
theorem exists_ne_zero_mem_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hNM : N ≤ M₀) [FiniteDimensional ℂ M₀] (hlt : N < M₀) :
    ∃ w ∈ orthoIn M₀ N B hlin hNM, w ≠ 0 := by
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNM

  let b := Module.finBasis ℂ N
  let φ : M₀ →ₗ[ℂ] (Fin (Module.finrank ℂ N) → ℂ) :=
    { toFun := fun w i => B w (b i)
      map_add' := fun x y => by
        funext i
        have h := hlin 1 x x.2 y y.2 (b i) (hNM (b i).2)
        rw [one_smul, one_mul] at h
        simpa using h
      map_smul' := fun z x => by
        funext i
        have h := hlin z x x.2 0 M₀.zero_mem (b i) (hNM (b i).2)
        rw [add_zero, form_zero_left M₀ B hlin (hNM (b i).2), add_zero] at h
        simpa using h }

  have hker : ∀ x : M₀, φ x = 0 → (x : W) ∈ orthoIn M₀ N B hlin hNM := by
    intro x hx
    refine ⟨x.2, fun n hn => ?_⟩

    have hrepr : (⟨n, hn⟩ : N) = ∑ i, b.repr ⟨n, hn⟩ i • b i := (b.sum_repr ⟨n, hn⟩).symm
    have hn' : n = ∑ i, b.repr ⟨n, hn⟩ i • (b i : W) := by
      have := congrArg Subtype.val hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this

    have hsum : ∀ (s : Finset (Fin (Module.finrank ℂ N))),
        B (∑ i ∈ s, b.repr ⟨n, hn⟩ i • (b i : W)) x = ∑ i ∈ s, b.repr ⟨n, hn⟩ i * B (b i) x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact form_zero_left M₀ B hlin x.2
      | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
        have hmem : (∑ i ∈ s, b.repr ⟨n, hn⟩ i • (b i : W)) ∈ M₀ :=
          M₀.sum_mem fun i _ => M₀.smul_mem _ (hNM (b i).2)
        exact hlin _ _ (hNM (b j).2) _ hmem x x.2
    have hBn : B n x = ∑ i, b.repr ⟨n, hn⟩ i * B (b i) x := by
      conv_lhs => rw [hn']
      exact hsum Finset.univ
    rw [hsymm n (hNM hn) x x.2, hBn]
    have hzero : (∑ i, b.repr ⟨n, hn⟩ i * B (b i) x) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi : B (b i) x = 0 := by
        rw [hsymm x x.2 (b i) (hNM (b i).2)]
        have := congrFun hx i
        simp only [Pi.zero_apply] at this
        change B x (b i) = 0 at this
        rw [this, map_zero]
      rw [hi, mul_zero]
    rw [hzero, map_zero]

  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank ℂ (LinearMap.range φ) ≤ Module.finrank ℂ N := by
    calc Module.finrank ℂ (LinearMap.range φ) ≤ Module.finrank ℂ (Fin (Module.finrank ℂ N) → ℂ) :=
          Submodule.finrank_le _
      _ = Module.finrank ℂ N := by simp
  have hlt' : Module.finrank ℂ N < Module.finrank ℂ M₀ := Submodule.finrank_lt_finrank_of_lt hlt
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker φ) := by omega
  have hnebot : LinearMap.ker φ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnebot
  exact ⟨(x : W), hker x (LinearMap.mem_ker.1 hx), fun h => hx0 (Subtype.ext h)⟩

/--
@isnad1 id=eq.4h4v.s9.22fd61d890c0 from=translated src=- shape=470e34c8 vocab=c270f70f
-/
theorem sup_orthoIn_eq (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (hNM : N ≤ M₀) [FiniteDimensional ℂ M₀] :
    N ⊔ orthoIn M₀ N B hlin hNM = M₀ := by
  have hPM : orthoIn M₀ N B hlin hNM ≤ M₀ := fun w hw => ((mem_orthoIn M₀ N B hlin hNM w).1 hw).1
  refine le_antisymm (sup_le hNM hPM) ?_
  by_contra hcon
  have hlt : N ⊔ orthoIn M₀ N B hlin hNM < M₀ := lt_of_le_of_ne (sup_le hNM hPM) fun h => hcon h.ge
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_mem_orthoIn M₀ (N ⊔ orthoIn M₀ N B hlin hNM) B hlin hsymm
    (sup_le hNM hPM) hlt
  obtain ⟨hwM, hwperp⟩ := (mem_orthoIn M₀ _ B hlin (sup_le hNM hPM) w).1 hw
  have hwP : w ∈ orthoIn M₀ N B hlin hNM :=
    (mem_orthoIn M₀ N B hlin hNM w).2 ⟨hwM, fun n hn => hwperp n (Submodule.mem_sup_left hn)⟩
  have hself : B w w = 0 := hwperp w (Submodule.mem_sup_right hwP)
  have := hpos w hwM hw0
  rw [hself, Complex.zero_re] at this
  exact lt_irrefl _ this

/--
@isnad1 id=mem.6h6v.s9.dc006c3242f9 from=translated src=- shape=ca1b5db9 vocab=9f06ab8f
-/
theorem orthoIn_mapsTo_of_symm (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (T : W → W) (hTM : ∀ w ∈ M₀, T w ∈ M₀) (hTN : ∀ n ∈ N, T n ∈ N)
    (hsym : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (T w) w' = B w (T w')) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, T w ∈ orthoIn M₀ N B hlin hNM := by
  intro w hw
  obtain ⟨hwM, hperp⟩ := (mem_orthoIn M₀ N B hlin hNM w).1 hw
  refine (mem_orthoIn M₀ N B hlin hNM (T w)).2 ⟨hTM w hwM, fun n hn => ?_⟩
  rw [hsym w hwM n (hNM hn)]
  exact hperp (T n) (hTN n hn)

/--
@isnad1 id=ex.7h6v.s10.34bd377a613f from=translated src=- shape=76b939ab vocab=da64b97b
-/
theorem exists_eigen_decomposition :
    ∀ (n : ℕ) (M₀ : Submodule ℂ W) [FiniteDimensional ℂ M₀], Module.finrank ℂ M₀ = n →
      ∀ (B : W → W → ℂ),
        (∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') →
        (∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w')) →
        (∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re) →
        ∀ (Ω : W →ₗ[ℂ] W), (∀ w ∈ M₀, Ω w ∈ M₀) → (∀ w ∈ M₀, ∀ w' ∈ M₀, B (Ω w) w' = B w (Ω w')) →
          ∀ z ∈ M₀, ∃ (s : Finset ℂ) (f : ℂ → W),
            (∀ μ ∈ s, f μ ∈ M₀ ∧ Ω (f μ) = μ • f μ) ∧ z = ∑ μ ∈ s, f μ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M₀ _ hn B hlin hsymm hpos Ω hΩM hΩsymm z hz
  by_cases hn0 : n = 0
  ·
    have hbot : M₀ = ⊥ := Submodule.finrank_eq_zero.1 (hn.trans hn0)
    rw [hbot] at hz
    refine ⟨∅, fun _ => 0, fun μ hμ => absurd hμ (by simp), ?_⟩
    rw [Finset.sum_empty]; exact (Submodule.mem_bot ℂ).1 hz

  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  haveI : Nontrivial M₀ := by
    rw [← Module.finrank_pos_iff (R := ℂ)]; omega
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Ω.restrict hΩM)
  obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
  have hyW : Ω (y : W) = c • (y : W) := by
    have h := hy.apply_eq_smul
    have h' := congrArg Subtype.val h
    rw [LinearMap.restrict_apply] at h'
    simpa using h'
  have hy0 : (y : W) ≠ 0 := fun h => hy.2 (Subtype.ext h)

  set N : Submodule ℂ W := Submodule.span ℂ {(y : W)} with hNdef
  have hNM : N ≤ M₀ := by
    rw [hNdef, Submodule.span_le]; intro w hw; rw [Set.mem_singleton_iff] at hw; rw [hw]; exact y.2
  have hNΩ : ∀ m ∈ N, Ω m ∈ N := by
    intro m hm
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hm
    rw [map_smul, hyW]
    exact N.smul_mem a (N.smul_mem c (Submodule.mem_span_singleton_self (y : W)))
  have hFM : orthoIn M₀ N B hlin hNM ≤ M₀ := fun w hw => ((mem_orthoIn M₀ N B hlin hNM w).1 hw).1
  haveI : FiniteDimensional ℂ (orthoIn M₀ N B hlin hNM) := Submodule.finiteDimensional_of_le hFM
  have hyF : (y : W) ∉ orthoIn M₀ N B hlin hNM := by
    intro hyF
    have h := ((mem_orthoIn M₀ N B hlin hNM _).1 hyF).2 (y : W) (Submodule.mem_span_singleton_self _)
    have hp := hpos (y : W) y.2 hy0
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  have hFlt : orthoIn M₀ N B hlin hNM < M₀ := lt_of_le_of_ne hFM fun h => hyF (by rw [h]; exact y.2)
  have hFrank : Module.finrank ℂ (orthoIn M₀ N B hlin hNM) < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hFlt

  have hdec := sup_orthoIn_eq M₀ N B hlin hsymm hpos hNM
  rw [← hdec] at hz
  obtain ⟨m, hm, x, hx, rfl⟩ := Submodule.mem_sup.1 hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hm

  have hFΩ : ∀ w ∈ orthoIn M₀ N B hlin hNM, Ω w ∈ orthoIn M₀ N B hlin hNM :=
    orthoIn_mapsTo_of_symm M₀ N B hlin hNM Ω hΩM hNΩ hΩsymm
  obtain ⟨s, f, hf, hxsum⟩ := ih (Module.finrank ℂ (orthoIn M₀ N B hlin hNM)) hFrank
    (orthoIn M₀ N B hlin hNM) rfl B
    (fun z w₁ h₁ w₂ h₂ w' h' => hlin z w₁ (hFM h₁) w₂ (hFM h₂) w' (hFM h'))
    (fun w hw w' hw' => hsymm w (hFM hw) w' (hFM hw'))
    (fun w hw => hpos w (hFM hw)) Ω hFΩ
    (fun w hw w' hw' => hΩsymm w (hFM hw) w' (hFM hw')) x hx

  classical
  refine ⟨insert c s, fun μ => (if μ ∈ s then f μ else 0) + (if μ = c then a • (y : W) else 0), ?_, ?_⟩
  · intro μ hμ
    constructor
    · refine M₀.add_mem ?_ ?_
      · split_ifs with h
        · exact hFM (hf μ h).1
        · exact M₀.zero_mem
      · split_ifs with h
        · exact M₀.smul_mem a y.2
        · exact M₀.zero_mem
    · rw [map_add, smul_add]
      congr 1
      · split_ifs with h
        · exact (hf μ h).2
        · simp
      · split_ifs with h
        · rw [map_smul, hyW, h, smul_comm]
        · simp
  · rw [Finset.sum_add_distrib]
    have h1 : ∑ μ ∈ insert c s, (if μ ∈ s then f μ else 0) = ∑ μ ∈ s, f μ := by
      by_cases hcs : c ∈ s
      · rw [Finset.insert_eq_of_mem hcs]
        exact Finset.sum_congr rfl fun μ hμ => ite_eq_left hμ
      · rw [Finset.sum_insert hcs, ite_eq_right hcs, zero_add]
        exact Finset.sum_congr rfl fun μ hμ => ite_eq_left hμ
    have h2 : ∑ μ ∈ insert c s, (if μ = c then a • (y : W) else 0) = a • (y : W) := by
      rw [Finset.sum_ite_eq' (insert c s) c]
      exact ite_eq_left (Finset.mem_insert_self c s)
    rw [h1, h2, ← hxsum, add_comm]

end Piece

section KerIm

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/--
@isnad1 id=ex.6h6v.s10.f2f5781ebb51 from=translated src=- shape=2a4f67f4 vocab=6d69714a
-/
theorem exists_eigen_add_image (M₀ : Submodule ℂ W) [FiniteDimensional ℂ M₀] (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (Ω : W →ₗ[ℂ] W) (hΩM : ∀ w ∈ M₀, Ω w ∈ M₀) (hΩsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (Ω w) w' = B w (Ω w'))
    (c : ℂ) (z : W) (hz : z ∈ M₀) :
    ∃ k ∈ M₀, Ω k = c • k ∧ ∃ x ∈ M₀, z = k + (Ω x - c • x) := by
  classical
  obtain ⟨s, f, hf, hzs⟩ := exists_eigen_decomposition (Module.finrank ℂ M₀) M₀ rfl B hlin hsymm hpos Ω hΩM hΩsymm z hz
  refine ⟨if c ∈ s then f c else 0, ?_, ?_, ∑ μ ∈ s.erase c, (μ - c)⁻¹ • f μ, ?_, ?_⟩
  · split_ifs with h
    · exact (hf c h).1
    · exact M₀.zero_mem
  · split_ifs with h
    · exact (hf c h).2
    · simp
  · exact M₀.sum_mem (fun μ hμ => M₀.smul_mem _ (hf μ (Finset.mem_of_mem_erase hμ)).1)
  · have hIm : Ω (∑ μ ∈ s.erase c, (μ - c)⁻¹ • f μ) - c • ∑ μ ∈ s.erase c, (μ - c)⁻¹ • f μ =
        ∑ μ ∈ s.erase c, f μ := by
      rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun μ hμ => ?_)
      have hne : μ - c ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hμ)
      rw [map_smul, (hf μ (Finset.mem_of_mem_erase hμ)).2, smul_smul, smul_smul, ← sub_smul]
      rw [show (μ - c)⁻¹ * μ - c * (μ - c)⁻¹ = 1 by field_simp, one_smul]
    rw [hIm, hzs]
    by_cases h : c ∈ s
    · rw [ite_eq_left h, ← Finset.add_sum_erase s f h]
    · rw [ite_eq_right h, zero_add, Finset.erase_eq_of_notMem h]

end KerIm

end WsB.EIG

/--
@isnad1 id=ex.6h7v.s10.0eb938dd7393 from=translated src=- shape=6a464a6c vocab=fd68a46c
-/
theorem solution
    (V : Type*) [AddCommGroup V] [Module ℂ V] (M₀ : Submodule ℂ V) [Module.Finite ℂ M₀]
    (B : V → V → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (ι : Type*) [Fintype ι] (θ : ι → (V →ₗ[ℂ] V))
    (hθM : ∀ i : ι, ∀ w ∈ M₀, θ i w ∈ M₀)
    (hskew : ∀ i : ι, ∀ w ∈ M₀, ∀ w' ∈ M₀, B (θ i w) w' = -B w (θ i w'))
    (c : ℂ) (z : V) (hz : z ∈ M₀) :
    ∃ k ∈ M₀, ∃ x ∈ M₀, (∑ i : ι, θ i * θ i) k = c • k ∧ z = k + ((∑ i : ι, θ i * θ i) x - c • x) := by
  classical
  set Ω : V →ₗ[ℂ] V := ∑ i : ι, θ i * θ i with hΩ
  have hΩM : ∀ w ∈ M₀, Ω w ∈ M₀ := by
    intro w hw
    rw [hΩ, LinearMap.sum_apply]
    exact M₀.sum_mem (fun i _ => hθM i _ (hθM i w hw))
  have hΩsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (Ω w) w' = B w (Ω w') := by
    intro w hw w' hw'

    have hB0 : ∀ u ∈ M₀, B 0 u = 0 := fun u hu => WsB.EIG.form_zero_left M₀ B hlin hu
    have haddL : ∀ a ∈ M₀, ∀ b ∈ M₀, ∀ u ∈ M₀, B (a + b) u = B a u + B b u := by
      intro a ha b hb u hu; have h := hlin 1 a ha b hb u hu; rw [one_smul, one_mul] at h; exact h
    have haddR : ∀ u ∈ M₀, ∀ a ∈ M₀, ∀ b ∈ M₀, B u (a + b) = B u a + B u b := by
      intro u hu a ha b hb
      rw [hsymm (a + b) (M₀.add_mem ha hb) u hu, hsymm a ha u hu, hsymm b hb u hu, haddL a ha b hb u hu, map_add]
    have hsumL : ∀ (s : Finset ι) (f : ι → V), (∀ i, f i ∈ M₀) → ∀ u ∈ M₀, B (∑ i ∈ s, f i) u = ∑ i ∈ s, B (f i) u := by
      intro s f hf u hu
      induction s using Finset.induction_on with
      | empty => simp [hB0 u hu]
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, haddL _ (hf a) _ (M₀.sum_mem fun i _ => hf i) u hu, ih]
    have hsumR : ∀ (s : Finset ι) (f : ι → V), (∀ i, f i ∈ M₀) → ∀ u ∈ M₀, B u (∑ i ∈ s, f i) = ∑ i ∈ s, B u (f i) := by
      intro s f hf u hu
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        rw [hsymm 0 M₀.zero_mem u hu, hB0 u hu, map_zero]
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, haddR u hu _ (hf a) _ (M₀.sum_mem fun i _ => hf i), ih]
    rw [hΩ, LinearMap.sum_apply, LinearMap.sum_apply,
      hsumL _ (fun i => (θ i * θ i) w) (fun i => hθM i _ (hθM i w hw)) w' hw',
      hsumR _ (fun i => (θ i * θ i) w') (fun i => hθM i _ (hθM i w' hw')) w hw]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Module.End.mul_apply, Module.End.mul_apply, hskew i _ (hθM i w hw) w' hw', hskew i w hw _ (hθM i w' hw'), neg_neg]
  haveI : FiniteDimensional ℂ M₀ := inferInstance
  obtain ⟨k, hk, hkeig, x, hx, hzx⟩ := WsB.EIG.exists_eigen_add_image M₀ B hlin hsymm hpos Ω hΩM hΩsymm c z hz
  exact ⟨k, hk, x, hx, hkeig, hzx⟩
