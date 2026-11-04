import Tengoku.GeneralStochToDet.stoch_to_det.Duality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# §3. Reduction to connected supports

Lemma 3.1 says `T` and `τ` are both additive over the connected components of
the bipartite support graph, and concludes that it suffices to prove
`T ≤ C τ` on connected supports.

`stoch_to_det.Main` consumes §3 through the consequence, `reduce_to_connected`, rather
than through the two additivity identities.

The reduction quantifies over laws on the same `α × β` — a component is a law
on the ambient product that vanishes off the component — so no alphabet
transport arises. See the support-handling note in `stoch_to_det.Functionals`.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A **component decomposition** of `p`: a finite family of laws `p i` with
weights `a i`, whose supports are the connected components of `support p`.

The two `hcol`/`hrow` fields encode the key observation: components occupy
disjoint columns and disjoint rows, so
the component index `K` is a function of `X` alone *and* of `Y` alone. That is
what makes the `(≥)` direction work.-/
structure ComponentDecomp (p : α × β → ℝ) where
  /-- Index type of the components.-/
  κ : Type
  /-- Finiteness of the index type.-/
  fin : Fintype κ
  /-- Decidable equality on the index type.-/
  dec : DecidableEq κ
  /-- Component masses `αᵢ`.-/
  wt : κ → ℝ
  /-- Conditional laws `p⁽ⁱ⁾`.-/
  part : κ → (α × β → ℝ)
  /-- The masses form a law.-/
  wt_isPMF : IsPMF wt
  /-- Each part is a law.-/
  part_isPMF : ∀ i, IsPMF (part i)
  /-- The parts reconstruct `p`.-/
  mixture : ∀ z, ∑ i, wt i * part i z = p z
  /-- Each part has connected support.-/
  part_connected : ∀ i, IsConnected (support (part i))
  /-- Distinct components use disjoint columns.-/
  hcol : ∀ i j z z', z ∈ support (part i) → z' ∈ support (part j) → z.1 = z'.1 → i = j
  /-- Distinct components use disjoint rows.-/
  hrow : ∀ i j z z', z ∈ support (part i) → z' ∈ support (part j) → z.2 = z'.2 → i = j

attribute [instance] ComponentDecomp.fin ComponentDecomp.dec

private def componentRel (S : Finset (α × β))
    (z z' : {z // z ∈ S}) : Prop :=
  Relation.ReflTransGen (fun a b => Adj a.1 b.1) z z'

private lemma adj_symm {z z' : α × β} (h : Adj z z') : Adj z' z := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

private noncomputable def componentSetoid (S : Finset (α × β)) :
    Setoid {z // z ∈ S} where
  r := componentRel S
  iseqv := by
    refine ⟨fun _ => Relation.ReflTransGen.refl, ?_,
      fun hab hbc => Relation.ReflTransGen.trans hab hbc⟩
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        exact Relation.ReflTransGen.trans
          (r := fun a b : {z // z ∈ S} => Adj a.1 b.1)
          (Relation.ReflTransGen.single (adj_symm hbc)) ih

/-- Every finite law admits a component decomposition.
@isnad1 id=nonempty.1h3v.s5.a2c78f916f9b from=translated src=- shape=38743cc5 vocab=e290ad7e
-/
theorem exists_componentDecomp {p : α × β → ℝ} (hp : IsPMF p) :
    Nonempty (ComponentDecomp p) := by
  classical
  let S := support p
  have hS : S.Nonempty := by
    by_contra h
    have hzero : ∀ z, p z = 0 := by
      intro z
      have hz : z ∉ S := by simpa [Finset.not_nonempty_iff_eq_empty.mp h]
      simpa [S, support] using hz
    have hmass : mass p = 0 := by simp [mass, hzero]
    linarith [hp.total]
  let z0 : {z // z ∈ S} := ⟨hS.choose, hS.choose_spec⟩
  let s : Setoid {z // z ∈ S} := componentSetoid S
  letI : DecidableRel ((· ≈ ·) : {z // z ∈ S} → {z // z ∈ S} → Prop) :=
    Classical.decRel _
  let Q := Quotient s
  letI : Fintype Q := Quotient.fintype s
  let eQ : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let κ := Fin (Fintype.card Q)
  let k : α × β → κ := fun z =>
    eQ (if hz : z ∈ S then (Quotient.mk'' ⟨z, hz⟩ : Q)
      else (Quotient.mk'' z0 : Q))
  let a : κ → ℝ := push k p
  have ha_pos : ∀ i, 0 < a i := by
    intro i
    obtain ⟨z, hz⟩ := Quotient.exists_rep (eQ.symm i)
    have hpz : 0 < p z.1 := by
      have hpz_ne : p z.1 ≠ 0 := by simpa [S, support] using z.2
      exact lt_of_le_of_ne (hp.nonneg z.1) (Ne.symm hpz_ne)
    have hle : p z.1 ≤ push k p (k z.1) := by
      unfold push
      exact Finset.single_le_sum (fun w _ => hp.nonneg w) (by simp)
    have hk : k z.1 = eQ (Quotient.mk'' z : Q) := by
      simp [k, z.2]
    have hi : eQ (Quotient.mk'' z : Q) = i := by
      calc
        eQ (Quotient.mk'' z : Q) = eQ (eQ.symm i) := congrArg eQ hz
        _ = i := eQ.apply_symm_apply i
    simpa [a, hk, hi] using lt_of_lt_of_le hpz hle
  let q : κ → (α × β → ℝ) := fun i z =>
    if k z = i then (a i)⁻¹ * p z else 0
  have hq_pmf : ∀ i, IsPMF (q i) := by
    intro i
    constructor
    · intro z
      simp only [q]
      split
      · exact mul_nonneg (inv_nonneg.mpr (ha_pos i).le) (hp.nonneg z)
      · exact le_rfl
    · unfold mass
      have hfiber : (∑ z, if k z = i then p z else 0) = push k p i := by
        simp [push, Finset.sum_filter]
      simp only [q]
      calc
        (∑ z, if k z = i then (a i)⁻¹ * p z else 0) =
            (a i)⁻¹ * ∑ z, if k z = i then p z else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z _
              split <;> simp_all
        _ = (a i)⁻¹ * a i := by rw [hfiber]
        _ = 1 := inv_mul_cancel₀ (ha_pos i).ne'
  have hsupp : ∀ i z, z ∈ support (q i) ↔ z ∈ S ∧ k z = i := by
    intro i z
    have hai : (a i)⁻¹ ≠ 0 := inv_ne_zero (ha_pos i).ne'
    simp [support, q, S, hai, and_comm]
  have hsame_of_adj {z z' : α × β} (hz : z ∈ S) (hz' : z' ∈ S)
      (hadj : Adj z z') : k z = k z' := by
    let zs : {z // z ∈ S} := ⟨z, hz⟩
    let zs' : {z // z ∈ S} := ⟨z', hz'⟩
    have hquot : (Quotient.mk'' zs : Q) = (Quotient.mk'' zs' : Q) := by
      apply Quotient.sound
      change componentRel S zs zs'
      exact Relation.ReflTransGen.single hadj
    simpa [k, zs, zs', hz, hz'] using congrArg eQ hquot
  have hq_conn : ∀ i, IsConnected (support (q i)) := by
    intro i z hz z' hz'
    have hzS : z ∈ S := (hsupp i z).mp hz |>.1
    have hz'S : z' ∈ S := (hsupp i z').mp hz' |>.1
    have hkz : k z = i := (hsupp i z).mp hz |>.2
    have hkz' : k z' = i := (hsupp i z').mp hz' |>.2
    let zs : {z // z ∈ S} := ⟨z, hzS⟩
    let zs' : {z // z ∈ S} := ⟨z', hz'S⟩
    have hquot : (Quotient.mk'' zs : Q) = (Quotient.mk'' zs' : Q) := by
      apply eQ.injective
      simpa [k, zs, zs', hzS, hz'S] using hkz.trans hkz'.symm
    have hrel : componentRel S zs zs' := Quotient.exact hquot
    clear hquot hkz'
    have aux : ∀ t : {z // z ∈ S}, componentRel S zs t → k zs.1 = i →
        k t.1 = i ∧
          Relation.ReflTransGen
            (fun u v => u ∈ support (q i) ∧ v ∈ support (q i) ∧ Adj u v)
            zs.1 t.1 := by
      intro t ht hstart
      induction ht with
      | refl => exact ⟨hstart, Relation.ReflTransGen.refl⟩
      | @tail u v huv hadj ih =>
          have hkv : k v.1 = i := (hsame_of_adj u.2 v.2 hadj).symm.trans ih.1
          refine ⟨hkv, ih.2.tail ⟨?_, ?_, hadj⟩⟩
          · exact (hsupp i u.1).2 ⟨u.2, ih.1⟩
          · exact (hsupp i v.1).2 ⟨v.2, hkv⟩
    have hstart : k zs.1 = i := by simpa [zs] using hkz
    simpa [zs, zs'] using (aux zs' hrel hstart).2
  refine ⟨{
    κ := κ
    fin := inferInstance
    dec := inferInstance
    wt := a
    part := q
    wt_isPMF := isPMF_push hp
    part_isPMF := hq_pmf
    mixture := ?_
    part_connected := hq_conn
    hcol := ?_
    hrow := ?_ }⟩
  · intro z
    rw [Finset.sum_eq_single (k z)]
    · simp [q, (ha_pos (k z)).ne']
    · intro i _ hi
      simp [q, Ne.symm hi]
    · simp
  · intro i j z z' hz hz' hxy
    have hi : k z = i := (hsupp i z).mp hz |>.2
    have hj : k z' = j := (hsupp j z').mp hz' |>.2
    have hkk := hsame_of_adj ((hsupp i z).mp hz |>.1)
      ((hsupp j z').mp hz' |>.1) (Or.inl hxy)
    rw [hi, hj] at hkk
    exact hkk
  · intro i j z z' hz hz' hxy
    have hi : k z = i := (hsupp i z).mp hz |>.2
    have hj : k z' = j := (hsupp j z').mp hz' |>.2
    have hkk := hsame_of_adj ((hsupp i z).mp hz |>.1)
      ((hsupp j z').mp hz' |>.1) (Or.inr hxy)
    rw [hi, hj] at hkk
    exact hkk

private noncomputable def glueLatent {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : ∀ i, Latent (D.part i)) : Latent p where
  ι := Σ i, (V i).ι
  fin := inferInstance
  dec := inferInstance
  prior := fun w => D.wt w.1 * (V w.1).prior w.2
  comp := fun w => (V w.1).comp w.2
  prior_isPMF := by
    constructor
    · intro w
      exact mul_nonneg (D.wt_isPMF.nonneg w.1) ((V w.1).prior_isPMF.nonneg w.2)
    · unfold mass
      rw [Fintype.sum_sigma]
      simp_rw [← Finset.mul_sum]
      have ht : ∀ i, ∑ v, (V i).prior v = 1 := fun i => by
        simpa [mass] using (V i).prior_isPMF.total
      simp_rw [ht, mul_one]
      simpa [mass] using D.wt_isPMF.total
  comp_isPMF := fun w => (V w.1).comp_isPMF w.2
  mixture := by
    intro z
    rw [Fintype.sum_sigma]
    simp_rw [mul_assoc, ← Finset.mul_sum, (V _).mixture]
    exact D.mixture z

private lemma componentDecomp_nonempty {p : α × β → ℝ} (D : ComponentDecomp p) :
    Nonempty D.κ := by
  by_contra h
  letI : IsEmpty D.κ := not_nonempty_iff.mp h
  have ht := D.wt_isPMF.total
  simp [mass] at ht

private noncomputable def componentIndex {p : α × β → ℝ} (D : ComponentDecomp p)
    (z : α × β) : D.κ :=
  if h : ∃ i, z ∈ support (D.part i) then Classical.choose h
  else Classical.choice (componentDecomp_nonempty D)

private lemma componentIndex_eq {p : α × β → ℝ} (D : ComponentDecomp p)
    {i : D.κ} {z : α × β} (hz : z ∈ support (D.part i)) :
    componentIndex D z = i := by
  rw [componentIndex]
  split
  · rename_i h
    exact D.hcol (Classical.choose h) i z z (Classical.choose_spec h) hz rfl
  · rename_i h
    exact (h ⟨i, hz⟩).elim

private lemma part_eq_zero_of_index_ne {p : α × β → ℝ} (D : ComponentDecomp p)
    {i : D.κ} {z : α × β} (h : componentIndex D z ≠ i) : D.part i z = 0 := by
  by_contra hz
  exact h (componentIndex_eq D (by simpa [support] using hz))

private lemma component_slice {p : α × β → ℝ} (D : ComponentDecomp p)
    (i : D.κ) (z : α × β) :
    (if componentIndex D z = i then p z else 0) = D.wt i * D.part i z := by
  classical
  by_cases hk : componentIndex D z = i
  · rw [ite_eq_left hk, ← D.mixture z]
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hkj : componentIndex D z ≠ j := by simpa [hk] using Ne.symm hji
      simp [part_eq_zero_of_index_ne D hkj]
    · simp
  · rw [ite_eq_right hk, part_eq_zero_of_index_ne D hk, mul_zero]

private lemma push_mixture {ι γ δ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype γ] [DecidableEq δ] (a : ι → ℝ) (q : ι → γ → ℝ) (m : γ → ℝ)
    (hmix : ∀ x, ∑ i, a i * q i x = m x) (f : γ → δ) (d : δ) :
    ∑ i, a i * push f (q i) d = push f m d := by
  unfold push
  simp_rw [← hmix, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma push_part_componentIndex {p : α × β → ℝ} (D : ComponentDecomp p)
    (i j : D.κ) :
    push (componentIndex D) (D.part i) j = if i = j then 1 else 0 := by
  classical
  rw [push, Finset.sum_filter]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    calc
      (∑ z, if componentIndex D z = i then D.part i z else 0) =
          ∑ z, D.part i z := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : componentIndex D z = i
        · simp [hz]
        · simp [hz, part_eq_zero_of_index_ne D hz]
      _ = 1 := by simpa [mass] using (D.part_isPMF i).total
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : componentIndex D z = j
    · have hzi : componentIndex D z ≠ i := by simpa [hz] using Ne.symm hij
      simp [hz, part_eq_zero_of_index_ne D hzi]
    · simp [hz]

private lemma push_componentIndex {p : α × β → ℝ} (D : ComponentDecomp p) :
    push (componentIndex D) p = D.wt := by
  funext i
  calc
    push (componentIndex D) p i =
        ∑ j, D.wt j * push (componentIndex D) (D.part j) i :=
      (push_mixture D.wt D.part p D.mixture (componentIndex D) i).symm
    _ = D.wt i := by simp [push_part_componentIndex]

private noncomputable def fiberWeight {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (v : V.ι) (i : D.κ) : ℝ :=
  push (componentIndex D) (V.comp v) i

private lemma fiberWeight_isPMF {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (v : V.ι) : IsPMF (fiberWeight D V v) := by
  exact isPMF_push (V.comp_isPMF v)

private noncomputable def fiberLaw {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (v : V.ι) (i : D.κ) : α × β → ℝ :=
  if h : fiberWeight D V v i = 0 then D.part i
  else fun z => if componentIndex D z = i then (fiberWeight D V v i)⁻¹ * V.comp v z else 0

private lemma comp_eq_zero_of_fiberWeight_zero {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (v : V.ι) (i : D.κ)
    {z : α × β} (hrho : fiberWeight D V v i = 0)
    (hz : componentIndex D z = i) : V.comp v z = 0 := by
  have hle : V.comp v z ≤ fiberWeight D V v i := by
    unfold fiberWeight push
    exact Finset.single_le_sum (fun w _ => (V.comp_isPMF v).nonneg w) (by simp [hz])
  rw [hrho] at hle
  exact le_antisymm hle ((V.comp_isPMF v).nonneg z)

private lemma fiberLaw_isPMF {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (v : V.ι) (i : D.κ) : IsPMF (fiberLaw D V v i) := by
  classical
  by_cases hrho : fiberWeight D V v i = 0
  · simpa [fiberLaw, hrho] using D.part_isPMF i
  · constructor
    · intro z
      simp only [fiberLaw, dite_eq_right hrho]
      split
      · exact mul_nonneg (inv_nonneg.mpr ((fiberWeight_isPMF D V v).nonneg i))
          ((V.comp_isPMF v).nonneg z)
      · exact le_rfl
    · unfold mass
      have hfiber :
          (∑ z, if componentIndex D z = i then V.comp v z else 0) =
            fiberWeight D V v i := by
        simp [fiberWeight, push, Finset.sum_filter]
      simp only [fiberLaw, dite_eq_right hrho]
      calc
        (∑ z, if componentIndex D z = i then
            (fiberWeight D V v i)⁻¹ * V.comp v z else 0) =
            (fiberWeight D V v i)⁻¹ *
              ∑ z, if componentIndex D z = i then V.comp v z else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          split <;> simp_all
        _ = (fiberWeight D V v i)⁻¹ * fiberWeight D V v i := by rw [hfiber]
        _ = 1 := inv_mul_cancel₀ hrho

private lemma fiberWeight_mul_fiberLaw {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (v : V.ι) (i : D.κ) (z : α × β) :
    fiberWeight D V v i * fiberLaw D V v i z =
      if componentIndex D z = i then V.comp v z else 0 := by
  classical
  by_cases hrho : fiberWeight D V v i = 0
  · by_cases hz : componentIndex D z = i
    · simp [fiberLaw, hrho, hz, comp_eq_zero_of_fiberWeight_zero D V v i hrho hz]
    · simp [fiberLaw, hrho, hz]
  · by_cases hz : componentIndex D z = i
    · simp only [fiberLaw, dite_eq_right hrho, ite_eq_left hz]
      rw [← mul_assoc, mul_inv_cancel₀ hrho, one_mul]
    · simp [fiberLaw, hrho, hz]

private lemma weighted_fiberWeight {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (i : D.κ) :
    ∑ v, V.prior v * fiberWeight D V v i = D.wt i := by
  calc
    (∑ v, V.prior v * fiberWeight D V v i) =
        push (componentIndex D) p i :=
      push_mixture V.prior V.comp p V.mixture (componentIndex D) i
    _ = D.wt i := by rw [push_componentIndex D]

private noncomputable def conditionalLatent {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (i : D.κ) (hwt : D.wt i ≠ 0) :
    Latent (D.part i) where
  ι := V.ι
  fin := inferInstance
  dec := inferInstance
  prior := fun v => (D.wt i)⁻¹ * V.prior v * fiberWeight D V v i
  comp := fun v => fiberLaw D V v i
  prior_isPMF := by
    constructor
    · intro v
      exact mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (D.wt_isPMF.nonneg i)) (V.prior_isPMF.nonneg v))
        ((fiberWeight_isPMF D V v).nonneg i)
    · unfold mass
      calc
        (∑ v, (D.wt i)⁻¹ * V.prior v * fiberWeight D V v i) =
            (D.wt i)⁻¹ * ∑ v, V.prior v * fiberWeight D V v i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          ring
        _ = (D.wt i)⁻¹ * D.wt i := by rw [weighted_fiberWeight D V i]
        _ = 1 := inv_mul_cancel₀ hwt
  comp_isPMF := fun v => fiberLaw_isPMF D V v i
  mixture := by
    intro z
    calc
      (∑ v, ((D.wt i)⁻¹ * V.prior v * fiberWeight D V v i) *
          fiberLaw D V v i z) =
          (D.wt i)⁻¹ * ∑ v, V.prior v *
            (fiberWeight D V v i * fiberLaw D V v i z) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = (D.wt i)⁻¹ * ∑ v, V.prior v *
            (if componentIndex D z = i then V.comp v z else 0) := by
        simp_rw [fiberWeight_mul_fiberLaw]
      _ = (D.wt i)⁻¹ * (if componentIndex D z = i then p z else 0) := by
        congr 1
        by_cases hz : componentIndex D z = i
        · simp [hz, V.mixture]
        · simp [hz]
      _ = (D.wt i)⁻¹ * (D.wt i * D.part i z) := by rw [component_slice D i z]
      _ = D.part i z := by
        rw [← mul_assoc, inv_mul_cancel₀ hwt, one_mul]

private noncomputable def restrictLatent {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (i : D.κ) : Latent (D.part i) :=
  if hwt : D.wt i = 0 then Latent.const (D.part_isPMF i)
  else conditionalLatent D V i hwt

end stoch_to_det
