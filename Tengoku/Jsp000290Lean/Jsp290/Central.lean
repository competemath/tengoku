import Tengoku.Jsp000290Lean.Jsp290.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Central intervals for indexed subset sums. The mathematical source is Geneson,
arXiv:2609.25107v1, Section 4. Cuts use the zero-based prefix convention in Defs.
The finite-potential formulation below uses uniform threshold transitions rather
than sequences of states or a choice of a recurrent potential value.
-/

namespace Jsp290
namespace Central

open Finset

/--
@isnad1 id=strictmo.1h1v.s5.4031abed8152 from=translated src=- shape=c80a7580 vocab=962f4607
-/
theorem prefixSum_strictMono {a : Sequence} (ha : ∀ i, 0 < a i) :
    StrictMono (PrefixSum a) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [prefixSum_succ]
  exact lt_add_of_pos_right _ (ha n)

/-- A central missing sum is just below an earlier prefix total.
@isnad1 id=ex.7h4v.s7.8c6f92b4030e from=translated src=- shape=b4e36cc1 vocab=da3fb896
-/
theorem locate_missing {a : Sequence} (hm : Monotone a) (ha : ∀ i, 0 < a i)
    {T : ℤ} (hT : 1 ≤ T) (hc : ∀ x : ℤ, T ≤ x → Represents a x)
    {N : ℕ} {x : ℤ} (hx : T ≤ x) (hxN : x ≤ PrefixSum a N - T)
    (hmiss : ¬ PrefixRep a N x) :
    ∃ j < N, ∃ u : ℤ, 0 ≤ u ∧ u < T ∧ x = PrefixSum a j - u := by
  have hex : ∃ i : ℕ, x + T ≤ PrefixSum a i := ⟨N, by omega⟩
  let i := Nat.find hex
  have hi : x + T ≤ PrefixSum a i := Nat.find_spec hex
  have hiN : i ≤ N := Nat.find_min' hex (by omega)
  have hi0 : 0 < i := by
    by_contra h
    have : i = 0 := by omega
    rw [this, prefixSum_zero] at hi
    omega
  let j := i - 1
  have hij : i = j + 1 := by omega
  have hj : j < i := by omega
  have hprev : PrefixSum a j < x + T := by
    have := Nat.find_min hex hj
    omega
  have hsum : PrefixSum a i = PrefixSum a j + a j := by
    rw [hij, prefixSum_succ]
  have hy : T ≤ PrefixSum a i - x := by omega
  have hlarge : a j ≤ PrefixSum a i - x := by
    by_contra h
    have hsmall : PrefixSum a i - x < a j := by omega
    have hr := prefixRep_of_represents_lt (fun t => le_of_lt (ha t)) hm (hc _ hy) hsmall
    have hh := (hr.mono (by omega : j ≤ i)).complement
    have hh : PrefixRep a i x := by convert hh using 1 <;> ring
    exact hmiss (hh.mono hiN)
  refine ⟨j, by omega, PrefixSum a j - x, ?_, ?_, ?_⟩ <;> omega

/-- Finitely many global representations can be placed in one prefix.
@isnad1 id=ex.0h2v.s5.50b4cbcf0d60 from=translated src=- shape=018a904f vocab=93e2263e
-/
theorem finite_representations (a : Sequence) (X : Finset ℤ) :
    ∃ J : ℕ, ∀ x ∈ X, Represents a x → PrefixRep a J x := by
  classical
  induction X using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x X hx ih =>
    obtain ⟨J, hJ⟩ := ih
    by_cases hr : Represents a x
    · obtain ⟨K, hK⟩ := represents_iff_exists_prefix.mp hr
      refine ⟨max J K, ?_⟩
      intro y hy hry
      rcases mem_insert.mp hy with rfl | hy
      · exact hK.mono (le_max_right _ _)
      · exact (hJ y hy hry).mono (le_max_left _ _)
    · refine ⟨J, ?_⟩
      intro y hy hry
      rcases mem_insert.mp hy with rfl | hy
      · exact (hr hry).elim
      · exact hJ y hy hry

/--
@isnad1 id=ex.0h2v.s5.3d86657d2edc from=translated src=- shape=f662000c vocab=6066953c
-/
theorem small_representations (a : Sequence) (T : ℤ) :
    ∃ J : ℕ, ∀ x : ℤ, 0 ≤ x → x < T → Represents a x → PrefixRep a J x := by
  obtain ⟨J, hJ⟩ := finite_representations a (Ico 0 T)
  exact ⟨J, fun x hx hxT hr => hJ x (mem_Ico.mpr ⟨hx, hxT⟩) hr⟩

/-- A globally represented sum missing from a prefix must be at least its next term.
@isnad1 id=le.4h3v.s5.115509b95ca0 from=translated src=- shape=bb70c049 vocab=c6064f6a
-/
theorem next_le_missing {a : Sequence} (hm : Monotone a) (ha : ∀ i, 0 < a i)
    {N : ℕ} {x : ℤ} (hx : Represents a x) (hmiss : ¬ PrefixRep a N x) : a N ≤ x := by
  by_contra h
  exact hmiss (prefixRep_of_represents_lt (fun i => le_of_lt (ha i)) hm hx (by omega))

/-- A state records a nonempty finite cluster of globally missing positive labels.-/
structure State (a : Sequence) (T : ℤ) where
  cut : ℕ
  last : ℕ
  labels : Finset ℤ
  cut_lt : cut < last
  nonempty : labels.Nonempty
  label_spec : ∀ e ∈ labels, 1 ≤ e ∧ e < T ∧ ¬ Represents a e
  missing : ∀ e ∈ labels, ¬ PrefixRep a last (PrefixSum a cut - e)

def State.Constant {a : Sequence} {T : ℤ} (s : State a T) : Prop :=
  ∀ i, s.cut ≤ i → i < s.last → a i = a s.cut

def State.Normalized {a : Sequence} {T : ℤ} (s : State a T) : Prop :=
  s.Constant → s.cut = 0 ∨ a (s.cut - 1) < a s.cut

noncomputable def State.least {a : Sequence} {T : ℤ} (s : State a T) : ℤ :=
  s.labels.min' s.nonempty

/--
@isnad1 id=mem.0h3v.s4.3b52a1bb5afb from=translated src=- shape=1aff97f9 vocab=83bf1f03
-/
theorem State.least_mem {a : Sequence} {T : ℤ} (s : State a T) :
    s.least ∈ s.labels := min'_mem _ _

/--
@isnad1 id=le.0h3v.s4.d8d7980398cf from=translated src=- shape=171962e3 vocab=59c1082e
-/
theorem State.least_pos {a : Sequence} {T : ℤ} (s : State a T) : 1 ≤ s.least :=
  (s.label_spec _ s.least_mem).1

/--
@isnad1 id=lt.0h3v.s4.2921bc977750 from=translated src=- shape=7b60ecfe vocab=add5b552
-/
theorem State.least_lt {a : Sequence} {T : ℤ} (s : State a T) : s.least < T :=
  (s.label_spec _ s.least_mem).2.1

noncomputable def State.potential {a : Sequence} {T : ℤ} (s : State a T) : ℤ := by
  classical
  exact if s.Constant then (T + 1) * s.labels.card + s.least
    else (T + 1) * (s.labels.card + 1)

/--
@isnad1 id=le.1h3v.s4.eb0a030d7d25 from=translated src=- shape=16a00ee0 vocab=0d6ee26d
-/
theorem State.potential_nonneg {a : Sequence} {T : ℤ} (hT : 1 ≤ T)
    (s : State a T) : 0 ≤ s.potential := by
  have hp := s.least_pos
  have hc : 0 ≤ (s.labels.card : ℤ) := by positivity
  unfold State.potential
  split_ifs <;> nlinarith

/--
@isnad1 id=le.1h3v.s6.20533a5acae4 from=translated src=- shape=a7f55afb vocab=0777bb7c
-/
theorem State.potential_le {a : Sequence} {T : ℤ} (hT : 1 ≤ T)
    (s : State a T) :
    s.potential ≤ (T + 1) * ((Ico (1 : ℤ) T).card + 1) := by
  have hsub : s.labels ⊆ Ico 1 T := by
    intro e he
    exact mem_Ico.mpr ⟨(s.label_spec e he).1, (s.label_spec e he).2.1⟩
  have hc : (s.labels.card : ℤ) ≤ (Ico (1 : ℤ) T).card := by
    exact_mod_cast card_le_card hsub
  have hp := s.least_lt
  unfold State.potential
  split_ifs <;> nlinarith

/--
@isnad1 id=le.1h4v.s5.4f99a37816e9 from=translated src=- shape=e3bb4fda vocab=ad59d54c
-/
theorem State.least_le {a : Sequence} {T : ℤ} (s : State a T)
    {e : ℤ} (he : e ∈ s.labels) : s.least ≤ e :=
  min'_le s.labels e he

/--
@isnad1 id=eq.1h5v.s5.fdbf4a8ca478 from=translated src=- shape=07d7bc7b vocab=13ced2cb
-/
theorem State.least_translate {a : Sequence} {T : ℤ} (s t : State a T) (c : ℤ)
    (hlabels : t.labels = s.labels.image (fun e => e + c)) : t.least = s.least + c := by
  classical
  have hmem : s.least + c ∈ t.labels := by
    rw [hlabels]
    exact mem_image.mpr ⟨s.least, s.least_mem, rfl⟩
  have hupper := t.least_le hmem
  have htmem := t.least_mem
  rw [hlabels] at htmem
  obtain ⟨e, he, heq⟩ := mem_image.mp htmem
  have hlower := s.least_le he
  omega

/--
@isnad1 id=eq.2h4v.s5.5bcc5c9a977b from=translated src=- shape=6571d8d7 vocab=ae0077bf
-/
theorem State.potential_congr {a : Sequence} {T : ℤ} (s t : State a T)
    (hlabels : t.labels = s.labels) (htype : t.Constant ↔ s.Constant) :
    t.potential = s.potential := by
  classical
  have hleast : t.least = s.least := by
    have hh := t.least_le (show s.least ∈ t.labels by rw [hlabels]; exact s.least_mem)
    have hh' := s.least_le (show t.least ∈ s.labels by rw [← hlabels]; exact t.least_mem)
    omega
  by_cases hc : s.Constant
  · have htc := htype.mpr hc
    simp [State.potential, hc, htc, hlabels, hleast]
  · have htc : ¬ t.Constant := fun hh => hc (htype.mp hh)
    simp [State.potential, hc, htc, hlabels, hleast]

/-- Move a constant cut to the first occurrence of its available value.
The output type and labels are unchanged, including when no move is needed.
@isnad1 id=ex.1h3v.s6.2cdf66b47404 from=translated src=- shape=4ae78ec1 vocab=26c53df7
-/
theorem State.normalization {a : Sequence} {T : ℤ} (hm : Monotone a)
    (s : State a T) :
    ∃ t : State a T, t.Normalized ∧ t.labels = s.labels ∧
      (t.Constant ↔ s.Constant) ∧
      (∀ K, a K < a s.cut → K < t.cut) := by
  classical
  by_cases hc : s.Constant
  · have hex : ∃ p, a p = a s.cut := ⟨s.cut, rfl⟩
    let p := Nat.find hex
    have hp : a p = a s.cut := Nat.find_spec hex
    have hpj : p ≤ s.cut := Nat.find_min' hex rfl
    have hcut : s.cut < s.last := s.cut_lt
    have hmiss : ∀ e ∈ s.labels, ¬ PrefixRep a (p + 1) (PrefixSum a p - e) := by
      intro e he hr
      by_cases hpeq : p = s.cut
      · apply s.missing e he
        simpa [hpeq] using hr.mono (by omega : p + 1 ≤ s.last)
      · have hpj' : p + 1 ≤ s.cut := by omega
        have hfirst : PrefixRep a (p + 1) (a p + e) := by
          have hh := hr.complement
          rw [prefixSum_succ] at hh
          convert hh using 1 <;> ring
        have hh := (hfirst.mono hpj').complement
        have hh := hh.add_term (le_refl s.cut) s.cut_lt
        apply s.missing e he
        convert hh using 1 <;> omega
    let t : State a T :=
      ⟨p, p + 1, s.labels, by omega, s.nonempty, s.label_spec, hmiss⟩
    have htc : t.Constant := by
      intro i hip hip'
      have : i = p := by change p ≤ i at hip; change i < p + 1 at hip'; omega
      subst i
      rfl
    refine ⟨t, ?_, rfl, iff_of_true htc hc, ?_⟩
    · intro _
      change p = 0 ∨ a (p - 1) < a p
      by_cases hp0 : p = 0
      · exact Or.inl hp0
      · right
        have hm' := hm (Nat.sub_le p 1)
        have hne : a (p - 1) ≠ a p := by
          intro heq
          have hh := Nat.find_min hex (show p - 1 < p by omega)
          exact hh (heq.trans hp)
        omega
    · intro K hK
      change K < p
      by_contra hh
      have hh := hm (show p ≤ K by omega)
      omega
  · refine ⟨s, (fun hh => (hc hh).elim), rfl, Iff.rfl, ?_⟩
    intro K hK
    by_contra hh
    have hh := hm (show s.cut ≤ K by omega)
    omega

/-- A gap after an available value is bounded by every missing label.
The larger value need not occur in the certifying prefix.
@isnad1 id=le.6h5v.s6.c6e2cca56808 from=translated src=- shape=773f309c vocab=2ba8eb83
-/
theorem State.value_gap {a : Sequence} {T : ℤ}
    (hm : Monotone a) (ha : ∀ i, 0 < a i)
    (hc : ∀ x : ℤ, T ≤ x → Represents a x)
    (s : State a T) (hlarge : T ≤ a s.cut)
    {v : ℤ} (hv : ∀ i, a i ≤ a s.cut ∨ v ≤ a i) :
    ∀ e ∈ s.labels, v - a s.cut ≤ e := by
  classical
  intro e he
  by_contra hbad
  have hepos := (s.label_spec e he).1
  obtain ⟨F, hF⟩ := hc (a s.cut + e) (by omega)
  have hsmall : ∀ i ∈ F, a i < a s.cut := by
    intro i hi
    have hle : a i ≤ ∑ k ∈ F, a k := single_le_sum (fun k _ => le_of_lt (ha k)) hi
    have hai : a i ≤ a s.cut := by
      rcases hv i with h | h
      · exact h
      · omega
    by_contra hn
    have heq : a i = a s.cut := by omega
    apply (s.label_spec e he).2.2
    refine ⟨F.erase i, ?_⟩
    have hh := sum_erase_add F a hi
    omega
  have hpre : PrefixRep a s.cut (a s.cut + e) := by
    refine ⟨F, ?_, hF⟩
    intro i hi
    apply mem_range.mpr
    by_contra hn
    have hh := hm (show s.cut ≤ i by omega)
    have hh' := hsmall i hi
    omega
  have hh := hpre.complement.add_term (le_refl s.cut) s.cut_lt
  apply s.missing e he
  convert hh using 1 <;> ring

/--
@isnad1 id=ex.2h3v.s6.988fcc9a20dc from=translated src=- shape=da3888fb vocab=d05f1683
-/
theorem State.distinct_value {a : Sequence} {T : ℤ} (hm : Monotone a)
    (s : State a T) (hc : ¬ s.Constant) :
    ∃ i : ℕ, s.cut < i ∧ i < s.last ∧ a s.cut < a i ∧
      (∀ k, a k ≤ a s.cut ∨ a i ≤ a k) := by
  classical
  have hex : ∃ i, a s.cut < a i := by
    by_contra hn
    push_neg at hn
    apply hc
    intro i hi hi'
    exact le_antisymm (hn i) (hm hi)
  let i := Nat.find hex
  have hval : a s.cut < a i := Nat.find_spec hex
  have hj : s.cut < i := by
    by_contra hn
    have hh := hm (show i ≤ s.cut by omega)
    omega
  have hiN : i < s.last := by
    by_contra hn
    apply hc
    intro k hk hk'
    have hki : k < i := by omega
    have hh := Nat.find_min hex hki
    have hh' := hm hk
    omega
  refine ⟨i, hj, hiN, hval, ?_⟩
  intro k
  by_cases hki : i ≤ k
  · exact Or.inr (hm hki)
  · left
    have hh := Nat.find_min hex (show k < i by omega)
    omega

/-- A narrow, sufficiently high cluster of missing sums shares one earlier cut.
All size thresholds are explicit, so this lemma is uniform over the cluster.
@isnad1 id=ex.9h5v.s8.ae2fa7ba5f53 from=translated src=- shape=8620427a vocab=a60e641b
-/
theorem align_cluster {a : Sequence} (hm : Monotone a) (ha : ∀ i, 0 < a i)
    {T : ℤ} (hT : 1 ≤ T) (hc : ∀ x : ℤ, T ≤ x → Represents a x)
    {Q j : ℕ} (hsmall : ∀ u : ℤ, 0 ≤ u → u < T → Represents a u → PrefixRep a Q u)
    (hbig : 3 * T < a Q)
    (R : Finset ℤ) (hne : R.Nonempty)
    (hR : ∀ x ∈ R, T ≤ x ∧ PrefixSum a Q < x ∧
      x ≤ PrefixSum a j - T ∧ ¬ PrefixRep a j x)
    (hwidth : ∀ x ∈ R, ∀ y ∈ R, x - y ≤ 2 * T) :
    ∃ t : State a T, Q < t.cut ∧ t.last = j ∧
      t.labels = R.image (fun x => PrefixSum a t.cut - x) ∧
      t.labels.card = R.card := by
  classical
  have hsmono := prefixSum_mono (fun i => le_of_lt (ha i))
  have hloc : ∀ x ∈ R, ∃ l : ℕ, ∃ u : ℤ,
      Q < l ∧ l < j ∧ 1 ≤ u ∧ u < T ∧ ¬ Represents a u ∧ x = PrefixSum a l - u := by
    intro x hx
    obtain ⟨hxT, hxQ, hxj, hxmiss⟩ := hR x hx
    obtain ⟨l, hlj, u, hu0, huT, hxu⟩ := locate_missing hm ha hT hc hxT hxj hxmiss
    have hQl : Q < l := by
      by_contra hn
      have hh := hsmono (show l ≤ Q by omega)
      omega
    have humiss : ¬ Represents a u := by
      intro hu
      have hh := (hsmall u hu0 huT hu).mono (le_of_lt hQl)
      have hh := hh.complement.mono (le_of_lt hlj)
      exact hxmiss (by simpa [hxu] using hh)
    have hu1 : 1 ≤ u := by
      by_contra hn
      have : u = 0 := by omega
      exact humiss (this ▸ represents_zero a)
    exact ⟨l, u, hQl, hlj, hu1, huT, humiss, hxu⟩
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨l, u₀, hQl, hlj, hu₀1, hu₀T, hu₀miss, hx₀u⟩ := hloc x₀ hx₀
  have haligned : ∀ x ∈ R, ∃ u : ℤ,
      1 ≤ u ∧ u < T ∧ ¬ Represents a u ∧ x = PrefixSum a l - u := by
    intro x hx
    obtain ⟨k, u, hQk, hkj, hu1, huT, humiss, hxu⟩ := hloc x hx
    have hkl : k = l := by
      rcases lt_trichotomy k l with hlt | heq | hgt
      · have hs := hsmono (show k + 1 ≤ l by omega)
        rw [prefixSum_succ] at hs
        have hav := hm (le_of_lt hQk)
        have hw := hwidth x₀ hx₀ x hx
        omega
      · exact heq
      · have hs := hsmono (show l + 1 ≤ k by omega)
        rw [prefixSum_succ] at hs
        have hav := hm (le_of_lt hQl)
        have hw := hwidth x hx x₀ hx₀
        omega
    exact ⟨u, hu1, huT, humiss, by simpa [hkl] using hxu⟩
  let E := R.image (fun x => PrefixSum a l - x)
  have hE : E.Nonempty := ⟨PrefixSum a l - x₀, mem_image.mpr ⟨x₀, hx₀, rfl⟩⟩
  have hEspec : ∀ e ∈ E, 1 ≤ e ∧ e < T ∧ ¬ Represents a e := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    obtain ⟨u, hu1, huT, humiss, hxu⟩ := haligned x hx
    have : PrefixSum a l - x = u := by omega
    simpa [this] using And.intro hu1 (And.intro huT humiss)
  have hEmiss : ∀ e ∈ E, ¬ PrefixRep a j (PrefixSum a l - e) := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    have := (hR x hx).2.2.2
    convert this using 1 <;> ring
  let t : State a T := ⟨l, j, E, hlj, hE, hEspec, hEmiss⟩
  refine ⟨t, hQl, rfl, rfl, ?_⟩
  change (R.image (fun x => PrefixSum a l - x)).card = R.card
  apply card_image_of_injective
  intro x y hxy
  change PrefixSum a l - x = PrefixSum a l - y at hxy
  omega

/-- The transition from a normalized constant state, before final normalization.
@isnad1 id=ex.12h4v.s7.7dc148c62a77 from=translated src=- shape=1f0b5344 vocab=05a98e40
-/
theorem constant_transition {a : Sequence} (hm : Monotone a) (ha : ∀ i, 0 < a i)
    {T : ℤ} (hT : 1 ≤ T) (hc : ∀ x : ℤ, T ≤ x → Represents a x)
    {Q : ℕ} (hsmall : ∀ u : ℤ, 0 ≤ u → u < T → Represents a u → PrefixRep a Q u)
    (hbig : 3 * T < a Q) (hSQ : T ≤ PrefixSum a Q)
    (s : State a T) (hn : s.Normalized) (hconst : s.Constant)
    (hj : 0 < s.cut) (hterm : T ≤ a s.cut)
    (hslack : PrefixSum a Q + 2 * T < PrefixSum a s.cut - a s.cut) :
    ∃ t : State a T, Q < t.cut ∧ s.potential < t.potential := by
  classical
  let R := s.labels.image (fun e => PrefixSum a s.cut - a s.cut - e)
  have hRne : R.Nonempty := s.nonempty.image _
  have hR : ∀ x ∈ R, T ≤ x ∧ PrefixSum a Q < x ∧
      x ≤ PrefixSum a s.cut - T ∧ ¬ PrefixRep a s.cut x := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    obtain ⟨he1, heT, _⟩ := s.label_spec e he
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro hr
    have hh := hr.add_term (le_refl s.cut) s.cut_lt
    apply s.missing e he
    convert hh using 1 <;> ring
  have hwidth : ∀ x ∈ R, ∀ y ∈ R, x - y ≤ 2 * T := by
    intro x hx y hy
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hy
    obtain ⟨he1, heT, _⟩ := s.label_spec e he
    obtain ⟨hf1, hfT, _⟩ := s.label_spec f hf
    omega
  obtain ⟨t, hQt, htlast, htlabels, htcard⟩ :=
    align_cluster hm ha hT hc hsmall hbig R hRne hR hwidth
  have htcut : t.cut < s.cut := by simpa [htlast] using t.cut_lt
  have hcard : t.labels.card = s.labels.card := by
    rw [htcard]
    change (s.labels.image (fun e => PrefixSum a s.cut - a s.cut - e)).card = _
    apply card_image_of_injective
    intro e f hef
    change PrefixSum a s.cut - a s.cut - e = PrefixSum a s.cut - a s.cut - f at hef
    omega
  have htranslate : t.labels = s.labels.image
      (fun e => e + (a s.cut - (PrefixSum a s.cut - PrefixSum a t.cut))) := by
    rw [htlabels]
    change (s.labels.image (fun e => PrefixSum a s.cut - a s.cut - e)).image
      (fun x => PrefixSum a t.cut - x) = _
    rw [image_image]
    congr 1
    funext e
    dsimp
    ring
  have hleast := s.least_translate t _ htranslate
  refine ⟨t, hQt, ?_⟩
  by_cases htc : t.Constant
  · have hprev : a (s.cut - 1) < a s.cut := by
      rcases hn hconst with hh | hh
      · omega
      · exact hh
    have hsame : a (s.cut - 1) = a t.cut := by
      apply htc
      · omega
      · rw [htlast]
        omega
    have hgapvalues : ∀ k, a k ≤ a t.cut ∨ a s.cut ≤ a k := by
      intro k
      by_cases hkj : k < s.cut
      · left
        have hh := hm (show k ≤ s.cut - 1 by omega)
        omega
      · exact Or.inr (hm (by omega))
    have htlargeterm : T ≤ a t.cut := by
      have hh := hm (le_of_lt hQt)
      omega
    have hgap := t.value_gap hm ha hc htlargeterm hgapvalues t.least t.least_mem
    have hleastT := s.least_lt
    have hsteplength : s.cut = t.cut + 1 := by
      by_contra hnstep
      have htwo : t.cut + 2 ≤ s.cut := by omega
      have hsum := prefixSum_mono (fun i => le_of_lt (ha i)) htwo
      have hsame' : a (t.cut + 1) = a t.cut := by
        apply htc
        · omega
        · rw [htlast]
          omega
      rw [show t.cut + 2 = (t.cut + 1) + 1 by omega,
        prefixSum_succ, prefixSum_succ, hsame'] at hsum
      have hav := hm (le_of_lt hQt)
      omega
    have hsum : PrefixSum a s.cut = PrefixSum a t.cut + a t.cut := by
      rw [hsteplength, prefixSum_succ]
    have hincr : s.least < t.least := by omega
    simp only [State.potential, ite_eq_left hconst, ite_eq_left htc, hcard]
    omega
  · have hleastT := s.least_lt
    simp only [State.potential, ite_eq_left hconst, ite_eq_right htc, hcard]
    nlinarith

/-- Two available values strictly increase the number of missing labels.
@isnad1 id=ex.10h4v.s7.c445fd11e442 from=translated src=- shape=b9d6ea6f vocab=fb9ba671
-/
theorem distinct_transition {a : Sequence} (hm : Monotone a) (ha : ∀ i, 0 < a i)
    {T : ℤ} (hT : 1 ≤ T) (hc : ∀ x : ℤ, T ≤ x → Represents a x)
    {Q : ℕ} (hsmall : ∀ u : ℤ, 0 ≤ u → u < T → Represents a u → PrefixRep a Q u)
    (hbig : 3 * T < a Q) (hSQ : T ≤ PrefixSum a Q)
    (s : State a T) (hconst : ¬ s.Constant) (hterm : T ≤ a s.cut)
    (hslack : PrefixSum a Q + 2 * T < PrefixSum a s.cut - a s.cut) :
    ∃ t : State a T, Q < t.cut ∧ s.potential < t.potential := by
  classical
  obtain ⟨i, hji, hiN, hval, hvalues⟩ := s.distinct_value hm hconst
  have hgap := s.value_gap hm ha hc hterm hvalues s.least s.least_mem
  have hleastT := s.least_lt
  let F := s.labels.image (fun e => PrefixSum a s.cut - a s.cut - e)
  let G := s.labels.image (fun e => PrefixSum a s.cut - a i - e)
  let R := F ∪ G
  have hRne : R.Nonempty := (s.nonempty.image _).mono (subset_union_left : F ⊆ R)
  have hparam : ∀ x ∈ R, ∃ e ∈ s.labels, ∃ v : ℤ,
      a s.cut ≤ v ∧ v ≤ a s.cut + T ∧ x = PrefixSum a s.cut - v - e := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨e, he, rfl⟩ := mem_image.mp hx
      exact ⟨e, he, a s.cut, le_rfl, by omega, rfl⟩
    · obtain ⟨e, he, rfl⟩ := mem_image.mp hx
      exact ⟨e, he, a i, by omega, by omega, rfl⟩
  have hR : ∀ x ∈ R, T ≤ x ∧ PrefixSum a Q < x ∧
      x ≤ PrefixSum a s.cut - T ∧ ¬ PrefixRep a s.cut x := by
    intro x hx
    have hbounds : T ≤ x ∧ PrefixSum a Q < x ∧ x ≤ PrefixSum a s.cut - T := by
      obtain ⟨e, he, v, hvlo, hvhi, hxe⟩ := hparam x hx
      obtain ⟨he1, heT, _⟩ := s.label_spec e he
      exact ⟨by omega, by omega, by omega⟩
    refine ⟨hbounds.1, hbounds.2.1, hbounds.2.2, ?_⟩
    intro hr
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨e, he, hxe⟩ := mem_image.mp hx
      have hh := hr.add_term (le_refl s.cut) s.cut_lt
      apply s.missing e he
      convert hh using 1 <;> omega
    · obtain ⟨e, he, hxe⟩ := mem_image.mp hx
      have hh := hr.add_term (le_of_lt hji) hiN
      apply s.missing e he
      convert hh using 1 <;> omega
  have hwidth : ∀ x ∈ R, ∀ y ∈ R, x - y ≤ 2 * T := by
    intro x hx y hy
    obtain ⟨e, he, v, hvlo, hvhi, hxe⟩ := hparam x hx
    obtain ⟨f, hf, w, hwlo, hwhi, hyf⟩ := hparam y hy
    obtain ⟨he1, heT, _⟩ := s.label_spec e he
    obtain ⟨hf1, hfT, _⟩ := s.label_spec f hf
    omega
  obtain ⟨t, hQt, htlast, htlabels, htcard⟩ :=
    align_cluster hm ha hT hc hsmall hbig R hRne hR hwidth
  have hcardF : F.card = s.labels.card := by
    apply card_image_of_injective
    intro e f hef
    change PrefixSum a s.cut - a s.cut - e = PrefixSum a s.cut - a s.cut - f at hef
    omega
  let emax := s.labels.max' s.nonempty
  have hemax : emax ∈ s.labels := max'_mem _ _
  let z := PrefixSum a s.cut - a i - emax
  have hzG : z ∈ G := mem_image.mpr ⟨emax, hemax, rfl⟩
  have hzF : z ∉ F := by
    intro hz
    obtain ⟨e, he, hez⟩ := mem_image.mp hz
    have hem : e ≤ emax := le_max' s.labels e he
    dsimp [z] at hez
    omega
  have hinsert : insert z F ⊆ R := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_union_right F hzG
    · exact mem_union_left G hx
  have hcstrict : s.labels.card < t.labels.card := by
    have hh := card_le_card hinsert
    rw [card_insert_of_notMem hzF, hcardF] at hh
    omega
  have hcstrict' : (s.labels.card : ℤ) + 1 ≤ t.labels.card := by exact_mod_cast hcstrict
  have htpos := t.least_pos
  refine ⟨t, hQt, ?_⟩
  unfold State.potential
  rw [ite_eq_right hconst]
  split_ifs <;> nlinarith

/-- The state transition preserves an arbitrarily prescribed lower cut bound.
This is the quantified replacement for recurring-state subsequences.
@isnad1 id=ex.6h3v.s7.e7243134abca from=translated src=- shape=23588fda vocab=a63f2cff
-/
theorem uniform_transition {a : Sequence} (hm : Monotone a) (ha : ∀ i, 0 < a i)
    {T : ℤ} (hT : 1 ≤ T) (hc : ∀ x : ℤ, T ≤ x → Represents a x)
    (hu : ∀ C : ℤ, ∃ i : ℕ, C < a i) (hd : DivergingSlack a) :
    ∀ K : ℕ, ∃ J : ℕ, ∀ s : State a T, s.Normalized → J ≤ s.cut →
      ∃ t : State a T, t.Normalized ∧ K ≤ t.cut ∧ s.potential < t.potential := by
  classical
  intro K
  obtain ⟨Jrep, hrep⟩ := small_representations a T
  obtain ⟨i, hi⟩ := hu (max (3 * T) (a K))
  let Q := max (i + 1) Jrep
  have hiQ : i + 1 ≤ Q := le_max_left _ _
  have hrepQ : Jrep ≤ Q := le_max_right _ _
  have hQa := hm (show i ≤ Q by omega)
  have hbig : 3 * T < a Q := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hi hQa)
  have hKbig : a K < a Q := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hi hQa)
  have hsmall : ∀ u : ℤ, 0 ≤ u → u < T → Represents a u → PrefixRep a Q u :=
    fun u hu0 huT hr => (hrep u hu0 huT hr).mono hrepQ
  have hSQ : T ≤ PrefixSum a Q := by
    have hh := prefixSum_mono (fun k => le_of_lt (ha k)) hiQ
    rw [prefixSum_succ] at hh
    have hh' := prefixSum_nonneg (fun k => le_of_lt (ha k)) i
    have hhi : 3 * T < a i := lt_of_le_of_lt (le_max_left _ _) hi
    omega
  obtain ⟨Jslack, hslack⟩ := hd (PrefixSum a Q + 2 * T + 1)
  refine ⟨max Jslack (Q + 1), ?_⟩
  intro s hn hs
  have hsJ : Jslack ≤ s.cut := le_trans (le_max_left _ _) hs
  have hsQ : Q + 1 ≤ s.cut := le_trans (le_max_right _ _) hs
  have hterm : T ≤ a s.cut := by
    have hh := hm (show Q ≤ s.cut by omega)
    omega
  have hslack' : PrefixSum a Q + 2 * T < PrefixSum a s.cut - a s.cut := by
    have hh := hslack s.cut hsJ
    omega
  have hstep : ∃ t : State a T, Q < t.cut ∧ s.potential < t.potential := by
    by_cases hcst : s.Constant
    · exact constant_transition hm ha hT hc hsmall hbig hSQ s hn hcst (by omega) hterm hslack'
    · exact distinct_transition hm ha hT hc hsmall hbig hSQ s hcst hterm hslack'
  obtain ⟨t, htQ, hpot⟩ := hstep
  obtain ⟨t', htn, hlabels, htype, hcut⟩ := t.normalization hm
  have hlarge : a K < a t.cut := lt_of_lt_of_le hKbig (hm (le_of_lt htQ))
  have hpoteq := t.potential_congr t' hlabels htype
  exact ⟨t', htn, le_of_lt (hcut K hlarge), by omega⟩

/-- Failure of central coverage yields normalized states at arbitrarily high cuts.
@isnad1 id=ex.6h3v.s6.df1fff5df7bf from=translated src=- shape=2bd06da9 vocab=97f57a6c
-/
theorem unbounded_states_of_failure {a : Sequence} (hm : Monotone a) (ha : ∀ i, 0 < a i)
    {T : ℤ} (hT : 1 ≤ T) (hc : ∀ x : ℤ, T ≤ x → Represents a x)
    (hu : ∀ C : ℤ, ∃ i : ℕ, C < a i) (hn : ¬ CentralIntervals a T) :
    ∀ K : ℕ, ∃ s : State a T, s.Normalized ∧ K ≤ s.cut := by
  classical
  have hbad : ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ ∃ x : ℤ,
      T ≤ x ∧ x ≤ PrefixSum a N - T ∧ ¬ PrefixRep a N x := by
    simpa only [CentralIntervals, not_exists, not_forall, Classical.not_imp, exists_prop] using hn
  intro K
  obtain ⟨Jrep, hrep⟩ := small_representations a T
  obtain ⟨i, hi⟩ := hu (a K)
  let L := max Jrep i
  have hrepL : Jrep ≤ L := le_max_left _ _
  have hiL : i ≤ L := le_max_right _ _
  have hLbig : a K < a L := lt_of_lt_of_le hi (hm hiL)
  obtain ⟨N₀, hN₀⟩ := hu (PrefixSum a L)
  obtain ⟨N, hNN, x, hxT, hxN, hxmiss⟩ := hbad N₀
  have hNx : a N ≤ x := next_le_missing hm ha (hc x hxT) hxmiss
  have hNL : PrefixSum a L < a N := lt_of_lt_of_le hN₀ (hm hNN)
  obtain ⟨j, hjN, u, hu0, huT, hxu⟩ := locate_missing hm ha hT hc hxT hxN hxmiss
  have hLj : L < j := by
    by_contra hh
    have hh' := prefixSum_mono (fun k => le_of_lt (ha k)) (show j ≤ L by omega)
    omega
  have humiss : ¬ Represents a u := by
    intro hr
    have hh := (hrep u hu0 huT hr).mono (le_trans hrepL (le_of_lt hLj))
    have hh := hh.complement.mono (le_of_lt hjN)
    exact hxmiss (by simpa [hxu] using hh)
  have hu1 : 1 ≤ u := by
    by_contra hh
    have : u = 0 := by omega
    exact humiss (this ▸ represents_zero a)
  let s : State a T :=
    { cut := j
      last := N
      labels := {u}
      cut_lt := hjN
      nonempty := singleton_nonempty u
      label_spec := by intro e he; simp only [mem_singleton] at he; subst e; exact ⟨hu1, huT, humiss⟩
      missing := by intro e he; simp only [mem_singleton] at he; subst e; simpa [← hxu] using hxmiss }
  obtain ⟨t, htn, _, _, htcut⟩ := s.normalization hm
  have hlarge : a K < a s.cut := lt_of_lt_of_le hLbig (hm (le_of_lt hLj))
  exact ⟨t, htn, le_of_lt (htcut K hlarge)⟩

/-- An abstract finite-potential principle with explicit uniform escape thresholds.
@isnad1 id=ex.3h4v.s6.ec61a7cda099 from=translated src=- shape=c614739a vocab=0e1f62c8
-/
theorem bounded_potential_no_unbounded_states {S : Type*} (cut : S → ℕ) (pot : S → ℤ)
    (M : ℤ) (hbound : ∀ s, pot s ≤ M)
    (hgrow : ∀ K : ℕ, ∃ J : ℕ, ∀ s : S, J ≤ cut s →
      ∃ s' : S, K ≤ cut s' ∧ pot s < pot s')
    (hpos : ∀ s : S, 0 ≤ pot s) : ∃ K : ℕ, ∀ s : S, cut s < K := by
  by_contra hn
  push_neg at hn
  have harb : ∀ p : ℕ, ∀ K : ℕ, ∃ s : S, K ≤ cut s ∧ (p : ℤ) ≤ pot s := by
    intro p
    induction p with
    | zero =>
      intro K
      obtain ⟨s, hs⟩ := hn K
      exact ⟨s, hs, by simpa using hpos s⟩
    | succ p ih =>
      intro K
      obtain ⟨J, hJ⟩ := hgrow K
      obtain ⟨s, hs, hp⟩ := ih J
      obtain ⟨s', hs', hh⟩ := hJ s hs
      exact ⟨s', hs', by push_cast; omega⟩
  obtain ⟨s, _, hs⟩ := harb (M.toNat + 1) 0
  have hh := hbound s
  have hnM : M ≤ (M.toNat : ℤ) := Int.self_le_toNat M
  push_cast at hs
  omega

/-- Geneson's central-interval theorem for the unbounded-term branch.
@isnad1 id=centrali.6h2v.s6.a91d87fd5a93 from=translated src=- shape=f7cfec9b vocab=baf3c5d2
-/
theorem central_intervals_unbounded {a : Sequence} (hm : Monotone a)
    (ha : ∀ i, 0 < a i) {T : ℤ} (hT : 1 ≤ T)
    (hc : ∀ x : ℤ, T ≤ x → Represents a x)
    (hd : DivergingSlack a) (hu : ∀ C : ℤ, ∃ i : ℕ, C < a i) :
    CentralIntervals a T := by
  classical
  let S := {s : State a T // s.Normalized}
  let M : ℤ := (T + 1) * ((Ico (1 : ℤ) T).card + 1)
  have hgrow : ∀ K : ℕ, ∃ J : ℕ, ∀ s : S, J ≤ s.val.cut →
      ∃ t : S, K ≤ t.val.cut ∧ s.val.potential < t.val.potential := by
    intro K
    obtain ⟨J, hJ⟩ := uniform_transition hm ha hT hc hu hd K
    refine ⟨J, ?_⟩
    intro s hs
    obtain ⟨t, htn, hKt, hpot⟩ := hJ s.val s.property hs
    exact ⟨⟨t, htn⟩, hKt, hpot⟩
  obtain ⟨K, hK⟩ := bounded_potential_no_unbounded_states
    (fun s : S => s.val.cut) (fun s : S => s.val.potential) M
    (fun s => s.val.potential_le hT) hgrow (fun s => s.val.potential_nonneg hT)
  by_contra hn
  obtain ⟨s, hsn, hKs⟩ := unbounded_states_of_failure hm ha hT hc hu hn K
  have hh := hK ⟨s, hsn⟩
  change s.cut < K at hh
  omega

end Central
end Jsp290
