import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.Tails.MultilinearBasic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tails of bounded multilinear forms on `ℓ^∞(ℕ)`

Under `NSC 𝕜`, over a complete nonarchimedean field, every bounded multilinear form `Φ` on
`ℓ^∞(ℕ, 𝕜)` of any arity has the tail property (`tail_multilinear`): for every `ε > 0` there is
`N` with `‖Φ u‖ ≤ ε` whenever all `‖u j‖ ≤ 1` and some `u j` vanishes below `N`. The proof is an
induction on the arity: the case of one variable is `tail_functional`; in the inductive step a
failure of the tail property is pushed to witnesses supported in finite windows far out
(`claim_all_slots`, `claim_window`), and gluing the first slots of these witnesses into one
vector `x` contradicts the tail property of the form with the first slot frozen at `x`.
-/

namespace AlternatingAnalytic.Tails

open BoundedContinuousFunction Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable [IsUltrametricDist 𝕜] [CompleteSpace 𝕜]

/--
@isnad1 id=tailat.1h1v.s5.de2de383d06e from=translated src=- shape=4b421f38 vocab=cbd3f23b
-/
theorem tailAt_one (h : NSC 𝕜) : TailAt 𝕜 1 := by
  intro Φ C hΦ ε hε
  obtain ⟨N, hN⟩ := tail_functional h (slotCLM hΦ (fun _ => 0) 0) ε hε
  refine ⟨N, ?_⟩
  rintro u hu ⟨j, hj⟩
  have hj0 : j = 0 := Subsingleton.elim _ _
  subst hj0
  have hueq : u = Function.update (fun _ => (0 : Linf 𝕜)) 0 (u 0) := by
    funext m
    have hm : m = 0 := Subsingleton.elim _ _
    subst hm
    simp
  rw [hueq]
  simpa using hN (u 0) (hu 0) hj

section Claims

variable {D : ℕ} {Φ : (Fin (D + 1) → Linf 𝕜) → 𝕜} {C ε : ℝ}

omit [CompleteSpace 𝕜] in
/-- If the tail property fails with margin `ε`, then it fails with all slots supported
arbitrarily far out.
@isnad1 id=ex.4h6v.s8.a11390cdf311 from=translated src=- shape=2d6b2d94 vocab=1a10ab9a
-/
theorem claim_all_slots (hΦ : IsBddML Φ C) (hε : 0 < ε) (ih : TailAt 𝕜 D)
    (hF : ∀ N : ℕ, ∃ u : Fin (D + 1) → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) ∧
      (∃ j, ∀ i < N, u j i = 0) ∧ ε < ‖Φ u‖) (M : ℕ) :
    ∃ u : Fin (D + 1) → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) ∧ (∀ j, ∀ i < M, u j i = 0) ∧ ε < ‖Φ u‖ := by
  classical
  -- thresholds for the forms obtained by freezing one slot at a unit vector
  have hTh0 : ∀ (j : Fin (D + 1)) (i : ℕ), ∃ N : ℕ, ∀ w : Fin D → Linf 𝕜, (∀ l, ‖w l‖ ≤ 1) →
      (∃ l, ∀ t < N, w l t = 0) → ‖freezeSlot Φ j (basisVec 𝕜 i) w‖ ≤ ε :=
    fun j i => ih _ _ (hΦ.freezeSlot j (basisVec 𝕜 i)) ε hε
  choose Th hTh using hTh0
  have R : ∀ k : ℕ, ∀ M N : ℕ, ∃ u : Fin (D + 1) → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) ∧
      (∀ j : Fin (D + 1), (j : ℕ) < k → ∀ i < M, u j i = 0) ∧
      (∃ j, ∀ i < N, u j i = 0) ∧ ε < ‖Φ u‖ := by
    intro k
    induction k with
    | zero =>
        intro M N
        obtain ⟨u, h1, h2, h3⟩ := hF N
        exact ⟨u, h1, fun j hj => absurd hj (Nat.not_lt_zero _), h2, h3⟩
    | succ k ihk =>
        intro M N
        by_cases hk : k < D + 1
        · obtain ⟨jk, hjk⟩ : ∃ jk : Fin (D + 1), (jk : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
          obtain ⟨N', hN'N, hN'M, hN'T⟩ :
              ∃ N' : ℕ, N ≤ N' ∧ M ≤ N' ∧ ∀ i < M, Th jk i ≤ N' := by
            refine ⟨max (max N M) ((Finset.range M).sup (Th jk)), ?_, ?_, ?_⟩
            · exact le_trans (le_max_left N M) (le_max_left _ _)
            · exact le_trans (le_max_right N M) (le_max_left _ _)
            · intro i hi
              exact le_trans (Finset.le_sup (Finset.mem_range.mpr hi)) (le_max_right _ _)
          obtain ⟨u, hu1, hu2, ⟨j0, hj0⟩, hu4⟩ := ihk M N'
          have hsplit : Φ u = Φ (Function.update u jk (headOf M (u jk)))
              + Φ (Function.update u jk (tailOf M (u jk))) := by
            have hadd := hΦ.add u jk (headOf M (u jk)) (tailOf M (u jk))
            rwa [headOf_add_tailOf, Function.update_eq_self] at hadd
          by_cases hcase : ε < ‖Φ (Function.update u jk (tailOf M (u jk)))‖
          · refine ⟨Function.update u jk (tailOf M (u jk)), ?_, ?_, ?_, hcase⟩
            · intro j
              by_cases hj : j = jk
              · subst hj
                rw [Function.update_self]
                exact (norm_tailOf_le _ _).trans (hu1 j)
              · rw [Function.update_of_ne hj]; exact hu1 j
            · intro j hj i hi
              by_cases hjkj : j = jk
              · subst hjkj
                rw [Function.update_self]
                exact tailOf_apply_of_lt _ hi
              · rw [Function.update_of_ne hjkj]
                refine hu2 j ?_ i hi
                have hne : (j : ℕ) ≠ k := fun hc => hjkj (Fin.val_injective (hc.trans hjk.symm))
                omega
            · by_cases hj0k : j0 = jk
              · refine ⟨jk, fun i hi => ?_⟩
                rw [Function.update_self, tailOf_apply]
                split_ifs with h1
                · rfl
                · rw [← hj0k]
                  exact hj0 i (by omega)
              · refine ⟨j0, fun i hi => ?_⟩
                rw [Function.update_of_ne hj0k]
                exact hj0 i (by omega)
          · exfalso
            push Not at hcase
            have hA : ε < ‖Φ (Function.update u jk (headOf M (u jk)))‖ := by
              by_contra hcon
              push Not at hcon
              have hmax := IsUltrametricDist.norm_add_le_max
                (Φ (Function.update u jk (headOf M (u jk))))
                (Φ (Function.update u jk (tailOf M (u jk))))
              rw [← hsplit] at hmax
              have : ‖Φ u‖ ≤ ε := hmax.trans (max_le hcon hcase)
              linarith
            have hAsum : Φ (Function.update u jk (headOf M (u jk)))
                = ∑ i ∈ Finset.range M, (u jk i) * Φ (Function.update u jk (basisVec 𝕜 i)) := by
              rw [headOf_eq_sum, hΦ.update_sum]
              exact Finset.sum_congr rfl fun i _ => hΦ.smul u jk (u jk i) (basisVec 𝕜 i)
            rw [hAsum] at hA
            have hMpos : 0 < M := by
              rcases Nat.eq_zero_or_pos M with rfl | hM
              · rw [Finset.range_zero, Finset.sum_empty, norm_zero] at hA; linarith
              · exact hM
            obtain ⟨i0, hi0mem, hi0⟩ :=
              IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
                ⟨0, Finset.mem_range.mpr hMpos⟩
                (fun i => (u jk i) * Φ (Function.update u jk (basisVec 𝕜 i)))
            have hi0M : i0 < M := Finset.mem_range.mp hi0mem
            have hfi0 : ε < ‖(u jk i0) * Φ (Function.update u jk (basisVec 𝕜 i0))‖ :=
              lt_of_lt_of_le hA hi0
            have hu0 : u jk i0 ≠ 0 := by
              intro hz
              rw [hz, zero_mul, norm_zero] at hfi0
              linarith
            have hj0ne : j0 ≠ jk := by
              intro hc
              exact hu0 (hc ▸ hj0 i0 (by omega))
            have hnorm : ε < ‖Φ (Function.update u jk (basisVec 𝕜 i0))‖ := by
              refine lt_of_lt_of_le hfi0 ?_
              rw [norm_mul]
              exact mul_le_of_le_one_left (norm_nonneg _)
                (((u jk).norm_coe_le_norm i0).trans (hu1 jk))
            obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hj0ne
            have hw : Φ (Function.update u jk (basisVec 𝕜 i0))
                = freezeSlot Φ jk (basisVec 𝕜 i0) (fun l => u (jk.succAbove l)) := by
              rw [update_eq_insertNth]; rfl
            have hle := hTh jk i0 (fun l => u (jk.succAbove l)) (fun l => hu1 _)
              ⟨l0, fun t ht => by rw [hl0]; exact hj0 t (by have := hN'T i0 hi0M; omega)⟩
            rw [hw] at hnorm
            linarith
        · obtain ⟨u, hu1, hu2, hu3, hu4⟩ := ihk M N
          refine ⟨u, hu1, ?_, hu3, hu4⟩
          intro j hj i hi
          have hjlt := j.isLt
          exact hu2 j (by omega) i hi
  obtain ⟨u, hu1, hu2, -, hu4⟩ := R (D + 1) M M
  exact ⟨u, hu1, fun j i hi => hu2 j j.isLt i hi, hu4⟩

/-- The witnesses of `claim_all_slots` can moreover be supported in a finite window `[M, M')`.
@isnad1 id=ex.4h6v.s9.f15e76dd1fe3 from=translated src=- shape=6cf1d65e vocab=d4970ac3
-/
theorem claim_window (h : NSC 𝕜) (hΦ : IsBddML Φ C) (hε : 0 < ε)
    (hc1 : ∀ M : ℕ, ∃ u : Fin (D + 1) → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) ∧ (∀ j, ∀ i < M, u j i = 0) ∧
      ε < ‖Φ u‖) (M : ℕ) :
    ∃ (M' : ℕ) (u : Fin (D + 1) → Linf 𝕜), M < M' ∧ (∀ j, ‖u j‖ ≤ 1) ∧
      (∀ j, ∀ i < M, u j i = 0) ∧ (∀ j, ∀ i, M' ≤ i → u j i = 0) ∧ ε < ‖Φ u‖ := by
  classical
  have S : ∀ k : ℕ, ∃ (M' : ℕ) (u : Fin (D + 1) → Linf 𝕜), M < M' ∧ (∀ j, ‖u j‖ ≤ 1) ∧
      (∀ j, ∀ i < M, u j i = 0) ∧
      (∀ j : Fin (D + 1), (j : ℕ) < k → ∀ i, M' ≤ i → u j i = 0) ∧ ε < ‖Φ u‖ := by
    intro k
    induction k with
    | zero =>
        obtain ⟨u, h1, h2, h3⟩ := hc1 M
        exact ⟨M + 1, u, by omega, h1, h2, fun j hj => absurd hj (Nat.not_lt_zero _), h3⟩
    | succ k ihk =>
        obtain ⟨M', u, hMM', hu1, hu2, hu3, hu4⟩ := ihk
        by_cases hk : k < D + 1
        · obtain ⟨jk, hjk⟩ : ∃ jk : Fin (D + 1), (jk : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
          obtain ⟨N0, hN0⟩ := tail_functional h (slotCLM hΦ u jk) ε hε
          have hMax : M' ≤ max M' N0 := le_max_left _ _
          have hMax' : N0 ≤ max M' N0 := le_max_right _ _
          have hsplit : Φ u = Φ (Function.update u jk (headOf (max M' N0) (u jk)))
              + Φ (Function.update u jk (tailOf (max M' N0) (u jk))) := by
            have hadd := hΦ.add u jk (headOf (max M' N0) (u jk)) (tailOf (max M' N0) (u jk))
            rwa [headOf_add_tailOf, Function.update_eq_self] at hadd
          have htail : ‖Φ (Function.update u jk (tailOf (max M' N0) (u jk)))‖ ≤ ε := by
            refine hN0 (tailOf (max M' N0) (u jk)) ((norm_tailOf_le _ _).trans (hu1 jk)) ?_
            intro i hi
            exact tailOf_apply_of_lt _ (by omega)
          refine ⟨max M' N0, Function.update u jk (headOf (max M' N0) (u jk)), by omega, ?_, ?_,
            ?_, ?_⟩
          · intro j
            by_cases hj : j = jk
            · subst hj
              rw [Function.update_self]
              exact (norm_headOf_le _ _).trans (hu1 j)
            · rw [Function.update_of_ne hj]; exact hu1 j
          · intro j i hi
            by_cases hj : j = jk
            · subst hj
              rw [Function.update_self, headOf_apply]
              split_ifs
              · exact hu2 j i hi
              · rfl
            · rw [Function.update_of_ne hj]; exact hu2 j i hi
          · intro j hj i hi
            by_cases hjkj : j = jk
            · subst hjkj
              rw [Function.update_self, headOf_apply]
              split_ifs with hc
              · exact absurd hc (by omega)
              · rfl
            · rw [Function.update_of_ne hjkj]
              have hne : (j : ℕ) ≠ k := fun hc => hjkj (Fin.val_injective (hc.trans hjk.symm))
              exact hu3 j (by omega) i (by omega)
          · by_contra hcon
            push Not at hcon
            have hmax := IsUltrametricDist.norm_add_le_max
              (Φ (Function.update u jk (headOf (max M' N0) (u jk))))
              (Φ (Function.update u jk (tailOf (max M' N0) (u jk))))
            rw [← hsplit] at hmax
            have : ‖Φ u‖ ≤ ε := hmax.trans (max_le hcon htail)
            linarith
        · refine ⟨M', u, hMM', hu1, hu2, ?_, hu4⟩
          intro j hj i hi
          have hjlt := j.isLt
          exact hu3 j (by omega) i hi
  obtain ⟨M', u, h1, h2, h3, h4, h5⟩ := S (D + 1)
  exact ⟨M', u, h1, h2, h3, fun j i hi => h4 j j.isLt i hi, h5⟩

end Claims

/--
@isnad1 id=tailat.3h2v.s6.0d684bd209e6 from=translated src=- shape=23b07826 vocab=b0752b35
-/
theorem tailAt_succ (h : NSC 𝕜) {D : ℕ} (hD : 0 < D) (ih : TailAt 𝕜 D) : TailAt 𝕜 (D + 1) := by
  classical
  intro Φ C hΦ ε hε
  by_contra hcon
  push Not at hcon
  -- witnesses supported in finite windows
  have hc2 := claim_window h hΦ hε (claim_all_slots hΦ hε ih hcon)
  choose W Z hW hZ1 hZ2 hZ3 hZ4 using hc2
  -- tail thresholds for the forms obtained by freezing slot `0`
  have hT0 : ∀ v : Linf 𝕜, ∃ N : ℕ, ∀ w : Fin D → Linf 𝕜, (∀ l, ‖w l‖ ≤ 1) →
      (∃ l, ∀ t < N, w l t = 0) → ‖freezeSlot Φ 0 v w‖ ≤ ε :=
    fun v => ih _ _ (hΦ.freezeSlot 0 v) ε hε
  choose T hT using hT0
  -- tail thresholds for the functionals in slot `0`
  have hS0 : ∀ u : Fin (D + 1) → Linf 𝕜, ∃ N : ℕ, ∀ y : Linf 𝕜, ‖y‖ ≤ 1 → (∀ i < N, y i = 0) →
      ‖Φ (Function.update u 0 y)‖ ≤ ε := by
    intro u
    obtain ⟨N, hN⟩ := tail_functional h (slotCLM hΦ u 0) ε hε
    exact ⟨N, fun y hy1 hy2 => by simpa using hN y hy1 hy2⟩
  choose Sf hS using hS0
  -- the increasing sequence of window endpoints
  obtain ⟨Mseq, hM0, hMstep⟩ : ∃ Mseq : ℕ → ℕ, Mseq 0 = 0 ∧
      ∀ s, Mseq (s + 1) = max (W (Mseq s)) (max (Sf (Z (Mseq s))) (T (Z (Mseq s) 0))) :=
    ⟨fun s => Nat.rec 0 (fun _ Ms => max (W Ms) (max (Sf (Z Ms)) (T (Z Ms 0)))) s, rfl,
      fun _ => rfl⟩
  have hWle : ∀ s, W (Mseq s) ≤ Mseq (s + 1) := by
    intro s; rw [hMstep]; exact le_max_left _ _
  have hSle : ∀ s, Sf (Z (Mseq s)) ≤ Mseq (s + 1) := by
    intro s; rw [hMstep]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hTle : ∀ s, T (Z (Mseq s) 0) ≤ Mseq (s + 1) := by
    intro s; rw [hMstep]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hmono : ∀ s, Mseq s < Mseq (s + 1) := fun s => lt_of_lt_of_le (hW _) (hWle s)
  have hMle : ∀ s t : ℕ, s ≤ t → Mseq s ≤ Mseq t :=
    fun s t hst => monotone_nat_of_le_succ (fun n => (hmono n).le) hst
  have hMge : ∀ s, s ≤ Mseq s := by
    intro s
    induction s with
    | zero => omega
    | succ t iht => have := hmono t; omega
  -- the glued diagonal vector
  obtain ⟨x, hxnorm, hxapp⟩ : ∃ x : Linf 𝕜, ‖x‖ ≤ 1 ∧
      ∀ i, x i = ∑ r ∈ Finset.range (i + 1), (Z (Mseq r) 0) i := by
    have hxbd : ∀ i : ℕ, ‖∑ r ∈ Finset.range (i + 1), (Z (Mseq r) 0) i‖ ≤ 1 := by
      intro i
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro r _
      exact ((Z (Mseq r) 0).norm_coe_le_norm i).trans (hZ1 _ _)
    exact ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun i => ∑ r ∈ Finset.range (i + 1), (Z (Mseq r) 0) i) 1 hxbd,
      (BoundedContinuousFunction.norm_le zero_le_one).mpr hxbd, fun i => rfl⟩
  -- the coordinates of `x` in the window of index `s`
  have hxwin : ∀ (s i : ℕ), i < Mseq (s + 1) →
      x i = ∑ r ∈ Finset.range (s + 1), (Z (Mseq r) 0) i := by
    intro s i hi
    rw [hxapp]
    have h1 : ∑ r ∈ Finset.range (i + 1), (Z (Mseq r) 0) i
        = ∑ r ∈ Finset.range (max (i + 1) (s + 1)), (Z (Mseq r) 0) i := by
      refine Finset.sum_subset (fun r hr => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hr) (le_max_left _ _))) ?_
      intro r _ hr
      rw [Finset.mem_range] at hr
      exact hZ2 _ _ i (by have := hMge r; omega)
    have h2 : ∑ r ∈ Finset.range (s + 1), (Z (Mseq r) 0) i
        = ∑ r ∈ Finset.range (max (i + 1) (s + 1)), (Z (Mseq r) 0) i := by
      refine Finset.sum_subset (fun r hr => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hr) (le_max_right _ _))) ?_
      intro r _ hr
      rw [Finset.mem_range] at hr
      exact hZ2 _ _ i (lt_of_lt_of_le hi (hMle _ _ (by omega)))
    rw [h1, ← h2]
  -- the decomposition of `x` adapted to the window of index `s`
  have hdecomp : ∀ s : ℕ, x = (∑ r ∈ Finset.range s, (Z (Mseq r) 0)) + (Z (Mseq s) 0)
      + tailOf (Mseq (s + 1)) x := by
    intro s
    ext i
    rw [Linf.add_apply, Linf.add_apply, Linf.sum_apply, tailOf_apply]
    by_cases hi : i < Mseq (s + 1)
    · rw [ite_eq_left hi, add_zero, ← Finset.sum_range_succ]
      exact hxwin s i hi
    · rw [ite_eq_right hi]
      have hzero : ∀ r ∈ Finset.range (s + 1), (Z (Mseq r) 0) i = 0 := by
        intro r hr
        rw [Finset.mem_range] at hr
        refine hZ3 _ _ i ?_
        have h1 : W (Mseq r) ≤ Mseq (r + 1) := hWle r
        have h2 : Mseq (r + 1) ≤ Mseq (s + 1) := hMle _ _ (by omega)
        omega
      have hsum : ∑ r ∈ Finset.range (s + 1), (Z (Mseq r) 0) i = 0 :=
        Finset.sum_eq_zero hzero
      rw [Finset.sum_range_succ] at hsum
      rw [hsum, zero_add]
  -- the "off-diagonal" part is small
  have hP : ∀ s : ℕ,
      ‖Φ (Function.update (Z (Mseq s)) 0 (∑ r ∈ Finset.range s, (Z (Mseq r) 0)))‖ ≤ ε := by
    intro s
    rw [hΦ.update_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε.le ?_
    intro r hr
    rw [Finset.mem_range] at hr
    have hw : Φ (Function.update (Z (Mseq s)) 0 (Z (Mseq r) 0))
        = freezeSlot Φ 0 (Z (Mseq r) 0)
          (fun l => Z (Mseq s) ((0 : Fin (D + 1)).succAbove l)) := by
      rw [update_eq_insertNth]; rfl
    rw [hw]
    refine hT (Z (Mseq r) 0) _ (fun l => hZ1 _ _) ⟨⟨0, hD⟩, fun t ht => ?_⟩
    refine hZ2 _ _ t ?_
    have h1 : T (Z (Mseq r) 0) ≤ Mseq (r + 1) := hTle r
    have h2 : Mseq (r + 1) ≤ Mseq s := hMle _ _ (by omega)
    omega
  -- the far tail is small
  have hR : ∀ s : ℕ,
      ‖Φ (Function.update (Z (Mseq s)) 0 (tailOf (Mseq (s + 1)) x))‖ ≤ ε := by
    intro s
    refine hS (Z (Mseq s)) _ ((norm_tailOf_le _ _).trans hxnorm) (fun i hi => ?_)
    exact tailOf_apply_of_lt _ (by have := hSle s; omega)
  -- hence the diagonal values stay big
  have hbig : ∀ s : ℕ, ε < ‖Φ (Function.update (Z (Mseq s)) 0 x)‖ := by
    intro s
    by_contra hcon2
    push Not at hcon2
    have hsplit : Φ (Function.update (Z (Mseq s)) 0 x)
        = Φ (Function.update (Z (Mseq s)) 0 (∑ r ∈ Finset.range s, (Z (Mseq r) 0)))
          + Φ (Z (Mseq s))
          + Φ (Function.update (Z (Mseq s)) 0 (tailOf (Mseq (s + 1)) x)) := by
      conv_lhs => rw [hdecomp s]
      rw [hΦ.add, hΦ.add, Function.update_eq_self]
    have hQ : Φ (Z (Mseq s))
        = Φ (Function.update (Z (Mseq s)) 0 x)
          + (-(Φ (Function.update (Z (Mseq s)) 0 (∑ r ∈ Finset.range s, (Z (Mseq r) 0))))
             + -(Φ (Function.update (Z (Mseq s)) 0 (tailOf (Mseq (s + 1)) x)))) := by
      rw [hsplit]; ring
    have hle : ‖Φ (Z (Mseq s))‖ ≤ ε := by
      rw [hQ]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hcon2 ?_)
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, norm_neg]
      exact max_le (hP s) (hR s)
    have := hZ4 (Mseq s)
    linarith
  -- but freezing slot `0` at `x` gives a form of smaller arity, whose tail bound applies
  obtain ⟨Nx, hNx⟩ := ih _ _ (hΦ.freezeSlot 0 x) ε hε
  have hxfr : Φ (Function.update (Z (Mseq Nx)) 0 x)
      = freezeSlot Φ 0 x (fun l => Z (Mseq Nx) ((0 : Fin (D + 1)).succAbove l)) := by
    rw [update_eq_insertNth]; rfl
  have hfin := hNx (fun l => Z (Mseq Nx) ((0 : Fin (D + 1)).succAbove l)) (fun l => hZ1 _ _)
    ⟨⟨0, hD⟩, fun t ht => hZ2 _ _ t (by have := hMge Nx; omega)⟩
  have hbg := hbig Nx
  rw [hxfr] at hbg
  linarith

/-- Tails of bounded multilinear forms of any arity.
@isnad1 id=ex.3h5v.s7.b64831a429cc from=translated src=- shape=874976fb vocab=09d254c7
-/
theorem tail_multilinear (h : NSC 𝕜) : ∀ (d : ℕ) (Φ : (Fin d → Linf 𝕜) → 𝕜) (C : ℝ), IsBddML Φ C →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ u : Fin d → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) →
      (∃ j, ∀ i < N, u j i = 0) → ‖Φ u‖ ≤ ε := by
  have key : ∀ d : ℕ, TailAt 𝕜 d := by
    intro d
    induction d with
    | zero => exact tailAt_zero
    | succ D ihD =>
        rcases Nat.eq_zero_or_pos D with rfl | hD
        · exact tailAt_one h
        · exact tailAt_succ h hD ihD
  exact fun d => key d

end AlternatingAnalytic.Tails
