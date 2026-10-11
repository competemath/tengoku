import Tengoku.OpenaiMath.OAI.NumberTheory.GaussianMoat.WalkPackage

namespace OAI

universe uOmega uKappa uIota uAlpha uBeta uGamma

namespace GaussianMoat
open scoped BigOperators Classical

lemma finite_entropy_telescope (n : ℕ) (a b : ℕ → ℝ) (ε : ℝ)
    (hnext : ∀ j<n, a (j+1)≤b j+ε) (hb : 0≤b n) :
    (∑ j∈Finset.range (n+1), (a j-b j)) ≤ a 0+n*ε := by
  have h : (∑ j∈Finset.range (n+1), (a j-b j)) ≤ a 0+n*ε-b n := by
    clear hb
    induction n with
    | zero => simp
    | succ n ih =>
      have hn := ih (fun j hj => hnext j (by omega))
      have hh := hnext n (by omega)
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
      linarith only [hn,hh]
  linarith only [h,hb]

theorem word_entropy_rate_monotone {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (f : ι → GaussianInt) (hf : ∀ i, f i≠0) {L K N : ℕ}
    (hL : 0<L) (hK : 0<K) (hdiv : L∣K) (hKN : K≤N) {ε : ℝ} (hε : 0≤ε)
    (herr : ∀ a<K, 2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L:ℝ)*Real.log (latticeBall D).card+
        2*∑ i, Real.log (f i).norm.natAbs) ≤ ε) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    P.cHf (fun v => incrementWord z K (t v.1+v.2.val))
      (fun v i => residueCode (f i) (z (t v.1+v.2.val))) / K ≤
    P.cHf (fun v => incrementWord z L (t v.1+v.2.val))
      (fun v i => residueCode (f i) (z (t v.1+v.2.val))) / L + ε := by
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
  let Q := fun v i => residueCode (f i) (z (u v))
  let H := P.cHf (fun v => incrementWord z L (u v)) Q
  obtain ⟨m,hm⟩ := hdiv
  have hm' : K=m*L := by simpa [Nat.mul_comm] using hm
  have hmp : 0 < m := by nlinarith only [hK,hm]
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hmR : (0:ℝ) < m := by exact_mod_cast hmp
  have hblock := incrementWord_blocks_entropy P u z f L m hL
  have hsum : (∑ j : Fin m, P.cHf (fun v => incrementWord z L (u v+j.val*L))
      (fun v i => residueCode (f i) (z (u v+j.val*L)))) ≤ (m:ℝ)*(H+ε) := by
    have hh (j : Fin m) : P.cHf (fun v => incrementWord z L (u v+j.val*L))
        (fun v i => residueCode (f i) (z (u v+j.val*L))) ≤ H+ε := by
      have hj : j.val*L<K := by rw [hm']; exact Nat.mul_lt_mul_of_pos_right j.isLt hL
      have hs := word_residue_smoothing p t z hz f hf L N (j.val*L) (by omega)
      dsimp only at hs
      change P.cHf _ _ ≤ H+_+_ at hs
      have he := herr (j.val*L) hj
      linarith only [hs,he]
    have hh' := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hh j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh'
  have htotal := hblock.trans hsum
  have hd := div_le_div_of_nonneg_right htotal (show (0:ℝ)≤ m*L by positivity)
  have he : (m:ℝ)*(H+ε)/((m:ℝ)*L)=(H+ε)/L := by field_simp
  rw [he,add_div] at hd
  have hel : ε/(L:ℝ)≤ε := div_le_self hε (by exact_mod_cast hL)
  rw [hm',Nat.cast_mul]
  change P.cHf (fun v => incrementWord z (m*L) (u v)) Q / ((m:ℝ)*L) ≤ H/L+ε
  linarith only [hd,hel]

lemma FinLaw.cIf_refinement {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω]
    (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ)
    (h : ∀ ω ν, X ω = X ν → O ω = O ν) :
    p.cIf X Y O = p.cHf Y O - p.cHf Y X := by
  rw [p.cIf_comm]
  unfold FinLaw.cIf
  congr 1
  apply p.cHf_congr_fibers Y Y (fun ω => (O ω,X ω)) X
  · intro ω ν; rfl
  · intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨And.right,fun hx => ⟨h ω ν hx,hx⟩⟩

theorem common_law_information_telescope {Ω : Type uOmega} [Fintype Ω]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (F : ℕ → Finset GaussianInt) (hF : ∀ j, F j ⊆ F (j+1))
    (hf : ∀ j, ∀ f ∈ F j, f ≠ 0) (L : ℕ → ℕ) (n N : ℕ)
    (hL : ∀ j ≤ n, 0 < L j) (hdiv : ∀ j < n, L j ∣ L (j+1))
    (hN : ∀ j ≤ n, L j ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ j < n, ∀ a < L (j+1),
      2*Real.binEntropy ((a:ℝ)/(N+1)) + ((a:ℝ)/(N+1))*
        ((L j:ℝ)*Real.log (latticeBall D).card +
          2*∑ f ∈ F (j+1), Real.log f.norm.natAbs) ≤ ε) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
    (∑ j ∈ Finset.range (n+1),
      P.cIf (fun v (f : F (j+1)) => residueCode f.val (z (u v)))
        (fun v => incrementWord z (L j) (u v))
        (fun v (f : F j) => residueCode f.val (z (u v))) / L j) ≤
      Real.log (latticeBall D).card + n*ε := by
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
  let Q := fun j => fun v (f : F j) => residueCode f.val (z (u v))
  let a := fun j => P.cHf (fun v => incrementWord z (L j) (u v)) (Q j) / L j
  let b := fun j => P.cHf (fun v => incrementWord z (L j) (u v)) (Q (j+1)) / L j
  have hnext (j : ℕ) (hj : j < n) : a (j+1) ≤ b j+ε := by
    dsimp only [a,b,Q,u,P]
    apply word_entropy_rate_monotone p t z hz (fun f : F (j+1) => f.val)
      (fun f => hf _ _ f.property) (hL j (by omega)) (hL (j+1) (by omega))
      (hdiv j hj) (hN (j+1) (by omega)) hε
    intro k hk
    convert herr j hj k hk using 1
    rw [Finset.sum_coe_sort (F (j+1)) (fun f : GaussianInt => Real.log f.norm.natAbs)]
  have hb : 0 ≤ b n := div_nonneg (P.cHf_nonneg _ _) (Nat.cast_nonneg _)
  have hi (j : ℕ) : P.cIf (Q (j+1)) (fun v => incrementWord z (L j) (u v)) (Q j) /
      L j = a j-b j := by
    rw [P.cIf_refinement,sub_div]
    intro v w hv
    funext f
    exact congrFun hv ⟨f.val,hF j f.property⟩
  have ht := finite_entropy_telescope n a b ε hnext hb
  have ha : a 0 ≤ Real.log (latticeBall D).card := by
    apply (div_le_iff₀ (show (0:ℝ) < L 0 by exact_mod_cast hL 0 (by omega))).mpr
    have hh := (P.cHf_le_Hf (fun v => incrementWord z (L 0) (u v)) (Q 0)).trans
      (boundedWord_entropy_le P u z hz (L 0))
    simpa only [mul_comm] using hh
  change (∑ j ∈ Finset.range (n+1), P.cIf (Q (j+1))
    (fun v => incrementWord z (L j) (u v)) (Q j) / L j) ≤ _
  simp only [hi]
  linarith only [ht,ha]

noncomputable def TimeLaw.info {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (P : TimeLaw)
    (X : ℕ → α) (Y : ℕ → β) (O : ℕ → γ) : ℝ :=
  P.law.cIf (fun t => X t.val) (fun t => Y t.val) (fun t => O t.val)

lemma TimeLaw.advance_info {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (P : TimeLaw) (K : ForwardKernel)
    (X : ℕ → α) (Y : ℕ → β) (O : ℕ → γ) :
    (P.advance K).info X Y O=(P.law.joint (fun a => K.law a.val)).cIf
      (fun v => X (v.1.val+v.2.val)) (fun v => Y (v.1.val+v.2.val))
      (fun v => O (v.1.val+v.2.val)) := by
  unfold TimeLaw.info TimeLaw.advance
  rw [FinLaw.cIf_map]
  rfl

lemma commonSchedule_smooth (z : ℕ → GaussianInt) (ns : List ℕ) (N : ℕ) :
    commonSchedule z ns N=(commonSchedule z ns 0).then (smoothingKernel N) := by
  simpa only [List.append_nil,commonSchedule,List.foldr_nil] using commonSchedule_append z ns [] N

theorem schedule_information_telescope (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (ns : List ℕ) (N n : ℕ)
    (F : ℕ → Finset GaussianInt) (hF : ∀ j, F j⊆F (j+1))
    (hf : ∀ j, ∀ f∈F j, f≠0) (L : ℕ → ℕ)
    (hL : ∀ j≤n, 0<L j) (hdiv : ∀ j<n, L j∣L (j+1)) (hN : ∀ j≤n, L j≤N)
    {ε : ℝ} (hε : 0≤ε)
    (herr : ∀ j<n, ∀ a<L (j+1), 2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L j:ℝ)*Real.log (latticeBall D).card+
        2*∑ f∈F (j+1), Real.log f.norm.natAbs)≤ε) :
    let P := (TimeLaw.at 0).advance (commonSchedule z ns N)
    (∑ j∈Finset.range (n+1), P.info
      (fun a (f : F (j+1)) => residueCode f.val (z a)) (incrementWord z (L j))
      (fun a (f : F j) => residueCode f.val (z a)) / L j)≤
        Real.log (latticeBall D).card+n*ε := by
  let Q := (TimeLaw.at 0).advance (commonSchedule z ns 0)
  have h := common_law_information_telescope Q.law (fun t => t.val) z hz F hF hf L n N
    hL hdiv hN hε herr
  dsimp only
  rw [commonSchedule_smooth,TimeLaw.advance_then]
  simp only [TimeLaw.advance_info]
  exact h

end GaussianMoat

end OAI
