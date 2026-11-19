/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Signs.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import Tengoku.Jsp000198Lean.EmptyPentagon.Enumeration
import Tengoku.Jsp000198Lean.EmptyPentagon.Quadrilateral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kernel-checked sign implications on five points

A *literal* `(i, j, k, b)` states that the orientation of `(p i, p j, p k)` is positive iff `b`.
`impHoldsAll hyps concl` decides, by enumerating all `1024` sign vectors on the ten sorted
triples and discarding the inconsistent ones, whether the literals `hyps` force the literal
`concl`.  `sign_imp` transfers a positive verdict to real points in general position.
-/

namespace Horton

/-- A literal `(i, j, k, b)`: the orientation of `(p i, p j, p k)` is positive iff `b`.-/
abbrev Lit := Fin 5 × Fin 5 × Fin 5 × Bool

/-- Boolean truth value of a literal on an abstract sign vector.-/
def litB (σ : Fin 5 → Fin 5 → Fin 5 → Bool) (l : Lit) : Bool := σ l.1 l.2.1 l.2.2.1 == l.2.2.2

/-- The three indices of a literal are pairwise distinct.-/
def litDistinct (l : Lit) : Bool := l.1 != l.2.1 && l.1 != l.2.2.1 && l.2.1 != l.2.2.1

/-- Boolean implication `hyps → concl` evaluated on `σ`.-/
def impB (hyps : List Lit) (concl : Lit) (σ : Fin 5 → Fin 5 → Fin 5 → Bool) : Bool :=
  !(hyps.all (litB σ)) || litB σ concl

/-- The implication on the sign vector of a bit vector, vacuous when it is inconsistent.-/
def impCheck (hyps : List Lit) (concl : Lit) (v : Nat → Bool) : Bool :=
  !consistentB (ofBits v) || impB hyps concl (ofBits v)

/-- `true` iff all literals have distinct indices and the implication `hyps → concl` holds on
every consistent sign vector on the ten sorted triples.-/
def impHoldsAll (hyps : List Lit) (concl : Lit) : Bool :=
  (hyps.all litDistinct && litDistinct concl) &&
  allBools fun b0 => allBools fun b1 => allBools fun b2 => allBools fun b3 =>
    allBools fun b4 => allBools fun b5 => allBools fun b6 => allBools fun b7 =>
    allBools fun b8 => allBools fun b9 => impCheck hyps concl (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)

/-- Real-point meaning of a literal.-/
def LitHolds (p : Fin 5 → Point) (l : Lit) : Prop :=
  (0 < orient (p l.1) (p l.2.1) (p l.2.2.1)) ↔ l.2.2.2 = true

/-- A positive orientation gives a positive literal.
@isnad1 id=litholds.1h4v.s6.47dd890792da from=translated src=- shape=269a2602 vocab=96ed25e5
-/
theorem litHolds_pos (p : Fin 5 → Point) (i j k : Fin 5) (h : 0 < orient (p i) (p j) (p k)) :
    LitHolds p (i, j, k, true) :=
  ⟨fun _ => rfl, fun _ => h⟩

/-- A negative orientation gives a negative literal.
@isnad1 id=litholds.1h4v.s6.dc5b59f6d57e from=translated src=- shape=ee4daa13 vocab=68ac0e43
-/
theorem litHolds_neg (p : Fin 5 → Point) (i j k : Fin 5) (h : orient (p i) (p j) (p k) < 0) :
    LitHolds p (i, j, k, false) :=
  ⟨fun h' => absurd h' (not_lt.2 h.le), fun h' => Bool.noConfusion h'⟩

/-- No hypotheses to discharge.
@isnad1 id=litholds.1h2v.s4.0427a3b45f38 from=translated src=- shape=b433b1cf vocab=dee798d3
-/
theorem litHolds_nil (p : Fin 5 → Point) : ∀ l ∈ ([] : List Lit), LitHolds p l :=
  fun _ h => nomatch h

/-- Discharge the hypotheses of a sign implication one literal at a time.
@isnad1 id=litholds.3h4v.s5.eb47873f22c2 from=translated src=- shape=7478dd7b vocab=635de4e5
-/
theorem litHolds_cons {p : Fin 5 → Point} {l : Lit} {ls : List Lit} (h : LitHolds p l)
    (hs : ∀ l' ∈ ls, LitHolds p l') : ∀ l' ∈ l :: ls, LitHolds p l' :=
  List.forall_mem_cons.2 ⟨h, hs⟩

/--
@isnad1 id=iff.0h1v.s7.121a81cd82fb from=translated src=- shape=13b9a694 vocab=ce5ced6f
-/
theorem litDistinct_iff (l : Lit) :
    litDistinct l = true ↔ l.1 ≠ l.2.1 ∧ l.1 ≠ l.2.2.1 ∧ l.2.1 ≠ l.2.2.1 := by
  simp only [litDistinct, Bool.and_eq_true, bne_iff_ne, ne_eq, and_assoc]

/--
@isnad1 id=eq.3h2v.s7.ba008087adda from=translated src=- shape=276668e8 vocab=fa77c7a8
-/
theorem litB_ofBits_encode (σ : Fin 5 → Fin 5 → Fin 5 → Bool)
    (h1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ j i k = !σ i j k)
    (h2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → σ i k j = !σ i j k)
    (l : Lit) (hd : litDistinct l = true) : litB (ofBits (encode σ)) l = litB σ l := by
  obtain ⟨h12, h13, h23⟩ := (litDistinct_iff l).1 hd
  simp only [litB, ofBits_encode σ h1 h2 _ _ _ h12 h13 h23]

/--
@isnad1 id=iff.0h2v.s4.06978eabd73e from=translated src=- shape=21969e0a vocab=64ac3192
-/
theorem litB_orientSign_iff (p : Fin 5 → Point) (l : Lit) :
    litB (orientSign p) l = true ↔ LitHolds p l := by
  obtain ⟨i, j, k, b⟩ := l
  cases b <;> simp [litB, LitHolds, orientSign]

/--
@isnad1 id=and.1h2v.s5.cd95d5cba34d from=translated src=- shape=926de6eb vocab=8bdc47cd
-/
theorem impHoldsAll_distinct (hyps : List Lit) (concl : Lit)
    (hall : impHoldsAll hyps concl = true) :
    (∀ l ∈ hyps, litDistinct l = true) ∧ litDistinct concl = true := by
  simp only [impHoldsAll, Bool.and_eq_true, List.all_eq_true] at hall
  exact hall.1

/--
@isnad1 id=eq.1h12v.s5.c158dbca3ac0 from=translated src=- shape=beb07fc4 vocab=b9b0324e
-/
theorem impCheck_of_impHoldsAll (hyps : List Lit) (concl : Lit)
    (hall : impHoldsAll hyps concl = true) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) :
    impCheck hyps concl (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) = true := by
  simp only [impHoldsAll, Bool.and_eq_true] at hall
  exact allBools_true (allBools_true (allBools_true (allBools_true (allBools_true (allBools_true
    (allBools_true (allBools_true (allBools_true (allBools_true hall.2 b0) b1) b2) b3) b4) b5)
    b6) b7) b8) b9

/-- A sign implication verified on all consistent abstract sign vectors holds for real points in
general position.
@isnad1 id=litholds.3h3v.s5.58dfa2db485b from=translated src=- shape=9f9d152d vocab=d74479ba
-/
theorem sign_imp (hyps : List Lit) (concl : Lit) (hall : impHoldsAll hyps concl = true)
    (p : Fin 5 → Point) (hgp : IndexedGP p) (hh : ∀ l ∈ hyps, LitHolds p l) :
    LitHolds p concl := by
  have hc := consistent_orientSign hgp
  have h := impCheck_of_impHoldsAll hyps concl hall (encode (orientSign p) 0)
    (encode (orientSign p) 1) (encode (orientSign p) 2) (encode (orientSign p) 3)
    (encode (orientSign p) 4) (encode (orientSign p) 5) (encode (orientSign p) 6)
    (encode (orientSign p) 7) (encode (orientSign p) 8) (encode (orientSign p) 9)
  have hd := impHoldsAll_distinct hyps concl hall
  rw [impCheck, ofBits_mk10, consistentB_of _ hc] at h
  simp only [Bool.not_true, Bool.false_or, impB, Bool.or_eq_true, Bool.not_eq_true',
    List.all_eq_false] at h
  rw [litB_ofBits_encode _ hc.1 hc.2.1 concl hd.2, litB_orientSign_iff] at h
  rcases h with ⟨l, hl, hf⟩ | h
  · rw [litB_ofBits_encode _ hc.1 hc.2.1 l (hd.1 l hl), (litB_orientSign_iff p l).2 (hh l hl)]
      at hf
    exact absurd hf (by decide)
  · exact h

/-- Convenience form of `sign_imp` with a positive conclusion.
@isnad1 id=lt.3h5v.s6.5ec057f2c6d6 from=translated src=- shape=46b64856 vocab=24b165e6
-/
theorem sign_imp_pos (hyps : List Lit) (i j k : Fin 5)
    (hall : impHoldsAll hyps (i, j, k, true) = true) (p : Fin 5 → Point) (hgp : IndexedGP p)
    (hh : ∀ l ∈ hyps, LitHolds p l) : 0 < orient (p i) (p j) (p k) :=
  (sign_imp hyps (i, j, k, true) hall p hgp hh).2 rfl

/-- Convenience form of `sign_imp` with a negative conclusion.
@isnad1 id=lt.3h5v.s6.da38dba08eb4 from=translated src=- shape=f5bb7120 vocab=3717d320
-/
theorem sign_imp_neg (hyps : List Lit) (i j k : Fin 5)
    (hall : impHoldsAll hyps (i, j, k, false) = true) (p : Fin 5 → Point) (hgp : IndexedGP p)
    (hh : ∀ l ∈ hyps, LitHolds p l) : orient (p i) (p j) (p k) < 0 := by
  have h := sign_imp hyps (i, j, k, false) hall p hgp hh
  obtain ⟨hij, hik, hjk⟩ :=
    (litDistinct_iff (i, j, k, false)).1 (impHoldsAll_distinct _ _ hall).2
  have hne := hgp i j k hij hik hjk
  simp only [LitHolds, Bool.false_eq_true, iff_false, not_lt] at h
  exact lt_of_le_of_ne h hne

/-! ### Smoke tests -/

end Horton
