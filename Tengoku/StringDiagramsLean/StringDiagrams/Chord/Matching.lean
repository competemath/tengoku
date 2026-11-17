import Tengoku.StringDiagramsLean.StringDiagrams.Chord.Realisation
import Tengoku.Seed.Logic.Equiv.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chord diagrams and perfect matchings

A perfect matching of the positions `0, …, n - 1` is a fixed-point-free involution
`σ : Equiv.Perm (Fin n)` (`IsMatching`). This file identifies pairings (`Valid` states) with
matchings together with a labelling of the positions by letters:

* `ofMatching σ lab`: the state of a matching `σ` with letters `lab : Fin n → α` (position `i`
  carries the arc id `min i (σ i)` and the letter `lab i`); it is a pairing
  (`valid_ofMatching`) in which `i` and `j` are joined exactly when `σ i = j`
  (`same_ofMatching`).
* `matchingOf s hv hn`: the matching of a pairing `s` of length `n` (each position goes to its
  partner), and `lettersOf s hn` its letters; `same_iff_matchingOf`, `isMatching_matchingOf`.
* The two constructions are inverse to each other: `matchingOf_ofMatching`,
  `lettersOf_ofMatching`, and `iso_ofMatching_matchingOf` (a pairing agrees with the state of its
  matching up to relabelling of the arc ids). Two pairings are related by such a relabelling
  (`Iso`) if and only if they have the same matching and the same letters (`iso_iff`).

Consequently the canonical diagram is a function of the matching and the letters
(`canon_ofMatching_matchingOf`), it realises the matching (`run_canon_ofMatching`,
`matchingOf_run_canon`), and the normal form theorem can be stated in terms of matchings
(`equiv_canon_matching_or_reducible`).
-/

namespace StringDiagrams.Chord

variable {α : Type*} {n : ℕ}

/-- A perfect matching of `Fin n`: a fixed-point-free involution.-/
structure IsMatching (σ : Equiv.Perm (Fin n)) : Prop where
  involutive : Function.Involutive σ
  ne_self : ∀ i, σ i ≠ i

/--
@isnad1 id=iso.2h4v.s4.9b61c0170503 from=translated src=- shape=4a5c722e vocab=d5599d94
-/
theorem Iso.trans {s s' s'' : List (ℕ × α)} (h : Iso s s') (h' : Iso s' s'') : Iso s s'' :=
  ⟨h.1.trans h'.1, fun i j => (h.2 i j).trans (h'.2 i j)⟩

/--
@isnad1 id=iso.0h2v.s3.6027b8cff3c2 from=translated src=- shape=87708fa8 vocab=d5599d94
-/
theorem Iso.refl (s : List (ℕ × α)) : Iso s s := ⟨rfl, fun _ _ => Iff.rfl⟩

/-! ## The state of a matching -/

section OfMatching

/-- The state of a matching `σ` with letters `lab`: position `i` carries the arc id
`min i (σ i)` (the left end of its arc) and the letter `lab i`.-/
def ofMatching (σ : Equiv.Perm (Fin n)) (lab : Fin n → α) : List (ℕ × α) :=
  List.ofFn fun i => (min (i : ℕ) (σ i : ℕ), lab i)

variable (σ : Equiv.Perm (Fin n)) (lab : Fin n → α)

/--
@isnad1 id=eq.0h4v.s4.a70f68e54319 from=translated src=- shape=4b35e144 vocab=62d5dfd9
-/
@[simp] theorem length_ofMatching : (ofMatching σ lab).length = n := List.length_ofFn

/--
@isnad1 id=eq.1h5v.s6.38488c8cde49 from=translated src=- shape=a1d942b0 vocab=0c6ff23d
-/
theorem getElem_ofMatching (i : ℕ) (h : i < (ofMatching σ lab).length) :
    (ofMatching σ lab)[i] =
      (min i (σ ⟨i, by simpa using h⟩ : ℕ), lab ⟨i, by simpa using h⟩) := by
  simp [ofMatching]

/--
@isnad1 id=eq.0h5v.s6.946752ab87ca from=translated src=- shape=e253402e vocab=4d32ffed
-/
theorem idAt_ofMatching (i : ℕ) :
    idAt (ofMatching σ lab) i = if h : i < n then some (min i (σ ⟨i, h⟩ : ℕ)) else none := by
  unfold idAt
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h), getElem_ofMatching]; rfl
  · rw [List.getElem?_eq_none (by simpa using h)]; rfl

/--
@isnad1 id=eq.0h4v.s5.facc5518df26 from=translated src=- shape=9ae56ea2 vocab=8925fd52
-/
@[simp] theorem map_snd_ofMatching : (ofMatching σ lab).map Prod.snd = List.ofFn lab := by
  simp [ofMatching, List.map_ofFn, Function.comp_def]

variable {σ}

/-- For a fixed-point-free involution, `min i (σ i) = min j (σ j)` with `i ≠ j` forces
`σ i = j`.-/
theorem IsMatching.eq_of_min_eq (hσ : IsMatching σ) {i j : Fin n} (hij : i ≠ j)
    (h : min (i : ℕ) (σ i : ℕ) = min (j : ℕ) (σ j : ℕ)) : σ i = j := by
  by_contra hne
  have h1 : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
  have h2 : (σ i : ℕ) ≠ j := fun e => hne (Fin.ext e)
  have h3 : (σ i : ℕ) ≠ σ j := fun e => hij (σ.injective (Fin.ext e))
  have h4 : (σ j : ℕ) ≠ i := fun e => hne (by rw [← Fin.ext e, hσ.involutive])
  omega

/-- In the state of a matching, positions `i` and `j` are joined exactly when `σ i = j`.
@isnad1 id=iff.1h6v.s6.b512026fd9e0 from=translated src=- shape=eb1c2e00 vocab=00f2583f
-/
theorem same_ofMatching_iff (hσ : IsMatching σ) {i j : ℕ} :
    Same (ofMatching σ lab) i j ↔ ∃ (hi : i < n) (hj : j < n), σ ⟨i, hi⟩ = ⟨j, hj⟩ := by
  simp only [Same, idAt_ofMatching]
  constructor
  · rintro ⟨hne, hi, he⟩
    have hi' : i < n := by by_contra h; simp [h] at hi
    have hj' : j < n := by
      by_contra h; rw [dite_eq_right h, dite_eq_left hi'] at he; cases he
    rw [dite_eq_left hi', dite_eq_left hj', Option.some_inj] at he
    exact ⟨hi', hj', hσ.eq_of_min_eq (fun e => hne (congrArg Fin.val e)) he⟩
  · rintro ⟨hi, hj, he⟩
    have hne : i ≠ j := fun e => hσ.ne_self ⟨i, hi⟩ (by rw [he]; exact Fin.ext e.symm)
    have hj' : σ ⟨j, hj⟩ = ⟨i, hi⟩ := by rw [← he, hσ.involutive]
    refine ⟨hne, by simp [hi], ?_⟩
    rw [dite_eq_left hi, dite_eq_left hj, he, hj']
    simp [min_comm]

/-- In the state of a matching, positions `i` and `j` are joined exactly when `σ i = j`.
@isnad1 id=iff.1h6v.s6.262bb6ed5a52 from=translated src=- shape=789ff296 vocab=dd3ce039
-/
theorem same_ofMatching (hσ : IsMatching σ) (i j : Fin n) :
    Same (ofMatching σ lab) i j ↔ σ i = j := by
  rw [same_ofMatching_iff lab hσ]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨i.2, j.2, h⟩⟩

/-- The state of a matching is a pairing.
@isnad1 id=valid.1h4v.s4.333972562c85 from=translated src=- shape=4822d482 vocab=4800161c
-/
theorem valid_ofMatching (hσ : IsMatching σ) : Valid (ofMatching σ lab) := by
  intro i hi
  rw [length_ofMatching] at hi
  refine ⟨σ ⟨i, hi⟩, (same_ofMatching_iff lab hσ).2 ⟨hi, (σ ⟨i, hi⟩).2, rfl⟩, fun j hj => ?_⟩
  obtain ⟨_, hj', h⟩ := (same_ofMatching_iff lab hσ).1 hj
  rw [h]

/-- If the letters at the two ends of each arc are `a` (left end) and `d a` (right end), the
state of the matching is `Lettered`.
@isnad1 id=lettered.2h5v.s6.a077e09724dd from=translated src=- shape=d8f0ce8d vocab=68a71ad6
-/
theorem lettered_ofMatching {d : α → α} (hσ : IsMatching σ)
    (hlab : ∀ i : Fin n, (i : ℕ) < σ i → lab (σ i) = d (lab i)) : Lettered d (ofMatching σ lab) := by
  intro i j hij hlt
  obtain ⟨hi, hj, h⟩ := (same_ofMatching_iff lab hσ).1 hij
  rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem?_eq_getElem (by simpa using hi),
    getElem_ofMatching, getElem_ofMatching]
  simp only [Option.map_some, Function.comp_apply, Option.some_inj]
  have := hlab ⟨i, hi⟩ (by rw [h]; exact hlt)
  rwa [h] at this

end OfMatching

/-! ## The matching of a pairing -/

section MatchingOf

variable {s : List (ℕ × α)} (hv : Valid s) (hn : s.length = n)

/-- The partner of a position in a pairing of length `n`.-/
noncomputable def partner (i : Fin n) : Fin n :=
  ⟨Classical.choose (hv.exists (show (i : ℕ) < s.length by rw [hn]; exact i.2)), by
    have := (Classical.choose_spec (hv.exists (show (i : ℕ) < s.length by rw [hn]; exact i.2))).lt_right
    omega⟩

/--
@isnad1 id=same.2h4v.s5.f6a6b93a3829 from=translated src=- shape=9666a58d vocab=a816281a
-/
theorem same_partner (i : Fin n) : Same s i (partner hv hn i) :=
  Classical.choose_spec (hv.exists (show (i : ℕ) < s.length by rw [hn]; exact i.2))

/--
@isnad1 id=iff.2h5v.s5.144a9aa7cf06 from=translated src=- shape=a1ef3e8e vocab=a816281a
-/
theorem partner_eq_iff (i j : Fin n) : partner hv hn i = j ↔ Same s i j := by
  constructor
  · rintro rfl; exact same_partner hv hn i
  · intro h; exact Fin.ext (hv.unique (same_partner hv hn i) h)

/--
@isnad1 id=involuti.2h3v.s4.4b444479e815 from=translated src=- shape=0d043b85 vocab=947ef7be
-/
theorem partner_involutive : Function.Involutive (partner hv hn) := fun i =>
  (partner_eq_iff hv hn _ _).2 (same_partner hv hn i).symm

/-- The matching of a pairing of length `n`: each position goes to its partner.-/
noncomputable def matchingOf : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (partner hv hn) (partner_involutive hv hn)

/--
@isnad1 id=eq.2h4v.s6.5b5ce7758ab0 from=translated src=- shape=b7ca7348 vocab=4badd712
-/
theorem matchingOf_apply (i : Fin n) : matchingOf hv hn i = partner hv hn i := rfl

/-- The matching of a pairing sends `i` to `j` exactly when `i` and `j` are joined.
@isnad1 id=iff.2h5v.s6.c9e1a9bcbca9 from=translated src=- shape=2fd1f201 vocab=bd74eb15
-/
theorem same_iff_matchingOf (i j : Fin n) : Same s i j ↔ matchingOf hv hn i = j :=
  (partner_eq_iff hv hn i j).symm

/--
@isnad1 id=ismatchi.2h3v.s4.77086ad6c788 from=translated src=- shape=3757475e vocab=f1a051ef
-/
theorem isMatching_matchingOf : IsMatching (matchingOf hv hn) :=
  ⟨partner_involutive hv hn, fun i h => (same_partner hv hn i).ne (congrArg Fin.val h).symm⟩

/-- The letters of a state of length `n`.-/
def lettersOf (s : List (ℕ × α)) (hn : s.length = n) (i : Fin n) : α :=
  (s[(i : ℕ)]'(by rw [hn]; exact i.2)).2

/--
@isnad1 id=eq.1h3v.s5.cac1c81dd335 from=translated src=- shape=f3eb30b1 vocab=0f16a25d
-/
theorem map_snd_eq_ofFn_lettersOf (s : List (ℕ × α)) (hn : s.length = n) :
    s.map Prod.snd = List.ofFn (lettersOf s hn) := by
  apply List.ext_getElem (by simp [hn])
  intro i h1 h2
  simp [lettersOf]

end MatchingOf

/-! ## The correspondence -/

section Correspondence

variable {σ : Equiv.Perm (Fin n)}

/-- The matching of the state of a matching `σ` is `σ`.
@isnad1 id=eq.3h4v.s5.8ab1312502e6 from=translated src=- shape=e8429da8 vocab=98f2dc05
-/
theorem matchingOf_ofMatching (hσ : IsMatching σ) (lab : Fin n → α)
    (hv : Valid (ofMatching σ lab)) (hn : (ofMatching σ lab).length = n) :
    matchingOf hv hn = σ :=
  Equiv.ext fun i => ((same_iff_matchingOf hv hn i _).1 ((same_ofMatching lab hσ i _).2 rfl))

/-- The letters of the state of a matching with letters `lab` are `lab`.
@isnad1 id=eq.1h4v.s5.2366d5c47b26 from=translated src=- shape=a003bc55 vocab=466b7881
-/
theorem lettersOf_ofMatching (lab : Fin n → α) (hn : (ofMatching σ lab).length = n) :
    lettersOf (ofMatching σ lab) hn = lab := by
  funext i
  simp [lettersOf, getElem_ofMatching]

/-- The state of a matching determines the matching and the letters.
@isnad1 id=iff.2h6v.s5.fd8eee1b7499 from=translated src=- shape=0d01df9f vocab=65aac1e7
-/
theorem ofMatching_inj {τ : Equiv.Perm (Fin n)} (hσ : IsMatching σ) (hτ : IsMatching τ)
    {lab lab' : Fin n → α} : ofMatching σ lab = ofMatching τ lab' ↔ σ = τ ∧ lab = lab' := by
  constructor
  · intro h
    have hn : (ofMatching σ lab).length = n := length_ofMatching σ lab
    refine ⟨?_, ?_⟩
    · rw [← matchingOf_ofMatching hσ lab (valid_ofMatching lab hσ) hn]
      rw [← matchingOf_ofMatching hτ lab' (valid_ofMatching lab' hτ) (length_ofMatching τ lab')]
      congr 1
    · rw [← lettersOf_ofMatching lab hn, ← lettersOf_ofMatching lab' (length_ofMatching τ lab')]
      congr 1
  · rintro ⟨rfl, rfl⟩; rfl

variable {s : List (ℕ × α)} (hv : Valid s) (hn : s.length = n)

/-- A pairing agrees with the state of its matching and letters, up to relabelling of the arc
ids.
@isnad1 id=iso.2h3v.s5.e3c7fa22b23c from=translated src=- shape=1ee014a5 vocab=8f423fe7
-/
theorem iso_ofMatching_matchingOf : Iso (ofMatching (matchingOf hv hn) (lettersOf s hn)) s := by
  refine ⟨by rw [map_snd_ofMatching, map_snd_eq_ofFn_lettersOf s hn], fun i j => ?_⟩
  rw [same_ofMatching_iff _ (isMatching_matchingOf hv hn)]
  constructor
  · rintro ⟨hi, hj, h⟩
    exact (same_iff_matchingOf hv hn ⟨i, hi⟩ ⟨j, hj⟩).2 h
  · intro h
    have hi : i < n := hn ▸ h.lt_left
    have hj : j < n := hn ▸ h.lt_right
    exact ⟨hi, hj, (same_iff_matchingOf hv hn ⟨i, hi⟩ ⟨j, hj⟩).1 h⟩

/-- Two pairings of length `n` agree up to relabelling of the arc ids if and only if they have
the same matching and the same letters.
@isnad1 id=iff.4h4v.s6.e4acc32df546 from=translated src=- shape=b76a8397 vocab=ab307e5c
-/
theorem iso_iff {s' : List (ℕ × α)} (hv' : Valid s') (hn' : s'.length = n) :
    Iso s s' ↔ matchingOf hv hn = matchingOf hv' hn' ∧ lettersOf s hn = lettersOf s' hn' := by
  constructor
  · intro h
    refine ⟨Equiv.ext fun i => ?_, funext fun i => ?_⟩
    · exact ((same_iff_matchingOf hv' hn' i _).1
        ((h.2 i _).1 ((same_iff_matchingOf hv hn i _).2 rfl))).symm
    · exact h.snd_getElem _ _
  · rintro ⟨h1, h2⟩
    have e := iso_ofMatching_matchingOf hv' hn'
    rw [← h1, ← h2] at e
    exact (iso_ofMatching_matchingOf hv hn).symm.trans e

/-- The canonical diagram of a pairing is that of its matching and letters.
@isnad1 id=eq.2h3v.s5.1269aae94e69 from=translated src=- shape=f498b6b0 vocab=5fc35635
-/
theorem canon_ofMatching_matchingOf :
    canon (ofMatching (matchingOf hv hn) (lettersOf s hn)) = canon s :=
  canon_eq_of_iso (iso_ofMatching_matchingOf hv hn)

end Correspondence

/-! ## Canonical diagrams of matchings -/

section Canon

variable {d : α → α} {σ : Equiv.Perm (Fin n)} {lab : Fin n → α}

/-- **The canonical diagram of a matching realises it.** If the letters at the two ends of each
arc of the matching `σ` are `a` (left end) and `d a` (right end), the canonical diagram fits on
the empty state, joins exactly the positions `i` and `σ i`, and produces the letters `lab`.
@isnad1 id=and.2h5v.s7.71e3fcf61011 from=translated src=- shape=c36a33ff vocab=3a1be1ef
-/
theorem run_canon_ofMatching (hσ : IsMatching σ)
    (hlab : ∀ i : Fin n, (i : ℕ) < σ i → lab (σ i) = d (lab i)) :
    Fits 0 (canon (ofMatching σ lab)) ∧
      (∀ i j : Fin n, Same (run d (canon (ofMatching σ lab))) i j ↔ σ i = j) ∧
      (run d (canon (ofMatching σ lab))).map Prod.snd = List.ofFn lab := by
  obtain ⟨hf, hiso⟩ := run_canon (d := d) _ (Nat.lt_succ_self _) (valid_ofMatching lab hσ)
    (lettered_ofMatching lab hσ hlab)
  refine ⟨hf, fun i j => ?_, by rw [hiso.1, map_snd_ofMatching]⟩
  rw [hiso.2, same_ofMatching lab hσ]

/-- The matching of the final state of the canonical diagram of a matching `σ` is `σ`.
@isnad1 id=eq.4h5v.s7.ec554040f1c9 from=translated src=- shape=a67ad5e3 vocab=dba686a2
-/
theorem matchingOf_run_canon (hσ : IsMatching σ)
    (hlab : ∀ i : Fin n, (i : ℕ) < σ i → lab (σ i) = d (lab i))
    (hv : Valid (run d (canon (ofMatching σ lab))))
    (hn : (run d (canon (ofMatching σ lab))).length = n) : matchingOf hv hn = σ :=
  Equiv.ext fun i =>
    (same_iff_matchingOf hv hn i _).1 (((run_canon_ofMatching hσ hlab).2.1 i _).2 rfl)

/-- **The normal form theorem for matchings.** Every diagram of cups and crossings that fits on
the empty state is reducible or equivalent to the canonical diagram of the matching and the
letters of its final state.
@isnad1 id=or.1h3v.s6.573d244a9013 from=translated src=- shape=89095372 vocab=6bb38b1b
-/
theorem equiv_canon_matching_or_reducible {D : List (Move α)} (hf : Fits 0 D) :
    Reducible D ∨ Equiv D (canon (ofMatching (matchingOf (inv_run (d := d) hf).1 rfl)
      (lettersOf (run d D) rfl))) := by
  rw [canon_ofMatching_matchingOf]
  exact equiv_canon_or_reducible hf

end Canon

end StringDiagrams.Chord
