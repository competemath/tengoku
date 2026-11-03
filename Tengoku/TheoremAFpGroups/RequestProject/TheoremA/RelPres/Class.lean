module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.RelPres.Oracle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Raw words, relative presentations and the class `C_R`

* `RawWord A := List (A × Bool)` — raw signed words.  **Convention:** `(a, true)` is the
  positive letter `a` and `(a, false)` is `a⁻¹` (this is also Mathlib's `FreeGroup.mk`
  convention, so `RawWord.eval = FreeGroup.mk`).
* `chi R`, `oracle R = {chi R}` — the total characteristic function of `R : Set ℕ` (values `0`,
  `1`, lifted with `Part.some`) and the singleton oracle set.  Defining `chi R` classically does
  not assert that `R` is computable: it is only ever used as an oracle.
* `IsEnumerator R e` — `e : ℕ →. RawWord (Fin n)` is partial recursive relative to `oracle R`,
  with outputs coded by the structural `Primcodable` instance on `List (Fin n × Bool)`.
* `enumRelators e` — the interpreted relator set `{eval w | ∃ k, w ∈ e k}` (possibly empty).
* `ClassCR R B` — `B` is isomorphic to `PresentedGroup (enumRelators e)` for some `n` and some
  `R`-enumerator `e` on `n` generators.
* `extendEnum e ρ hs` — rename the outputs of `e` along `ρ` and add a fixed finite list `hs` of
  raw relators; `IsEnumerator.extendEnum` and `enumRelators_extendEnum`.
-/

@[expose] public section

namespace TheoremA.RelPres

universe u

/-! ### Raw words -/

/-- Raw signed words over the alphabet `A`; `(a, true)` means `a`, `(a, false)` means `a⁻¹`.-/
abbrev RawWord (A : Type*) := List (A × Bool)

namespace RawWord

variable {A A' : Type*}

/-- Evaluation of a raw word in the free group.-/
def eval (w : RawWord A) : FreeGroup A := FreeGroup.mk w

/-- Formal inverse: reverse the list and flip every sign.-/
def inv (w : RawWord A) : RawWord A := (w.map fun p => (p.1, !p.2)).reverse

/-- Renaming along an alphabet map.-/
def rename (f : A → A') (w : RawWord A) : RawWord A' := w.map fun p => (f p.1, p.2)

/--
@isnad1 id=eq.0h1v.s4.03a46b4e06a8 from=translated src=- shape=3db1e86a vocab=7578dc45
-/
@[simp] theorem eval_nil : eval ([] : RawWord A) = 1 := rfl

/--
@isnad1 id=eq.0h3v.s5.30b91aae5a26 from=translated src=- shape=4d45420e vocab=330bfb10
-/
@[simp] theorem eval_append (v w : RawWord A) : eval (v ++ w) = eval v * eval w :=
  FreeGroup.mul_mk.symm

/--
@isnad1 id=eq.0h2v.s4.64326d90aa75 from=translated src=- shape=663936d3 vocab=834300a2
-/
@[simp] theorem eval_pos (a : A) : eval [(a, true)] = FreeGroup.of a := rfl

/--
@isnad1 id=eq.0h2v.s4.102e08f43672 from=translated src=- shape=a2a045b3 vocab=d7b7cb49
-/
@[simp] theorem eval_neg (a : A) : eval [(a, false)] = (FreeGroup.of a)⁻¹ := by
  simp [eval, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

/--
@isnad1 id=eq.0h2v.s4.07ec72689676 from=translated src=- shape=af983816 vocab=3e458ee8
-/
@[simp] theorem eval_inv (w : RawWord A) : eval (inv w) = (eval w)⁻¹ := by
  simp only [eval, FreeGroup.inv_mk, FreeGroup.invRev, inv]

/--
@isnad1 id=eq.0h4v.s6.ce0df5edf300 from=translated src=- shape=26149876 vocab=7c181277
-/
@[simp] theorem eval_rename (f : A → A') (w : RawWord A) :
    eval (rename f w) = FreeGroup.map f (eval w) := by
  simp only [eval, rename, FreeGroup.map.mk]

/-- Every free-group element is represented by a raw word.
@isnad1 id=surjecti.0h1v.s3.7bf56d8f587f from=translated src=- shape=fc766b23 vocab=298a5324
-/
theorem eval_surjective : Function.Surjective (eval : RawWord A → FreeGroup A) := by
  intro x
  induction x using Quot.ind with
  | mk w => exact ⟨w, rfl⟩

/-- Renaming along any map between finite alphabets is primitive recursive.
@isnad1 id=primrec.0h3v.s5.67b7b0a3e5e2 from=translated src=- shape=1f22ccfb vocab=4bd2a369
-/
theorem primrec_rename {n m : ℕ} (f : Fin n → Fin m) :
    Primrec (rename f : RawWord (Fin n) → RawWord (Fin m)) :=
  Primrec.list_map Primrec.id
    (Primrec.pair ((Primrec.dom_finite f).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

end RawWord

/-! ### Oracles, enumerators and the class `C_R` -/

open Classical in
/-- The total characteristic function of `R` (values `0`, `1`), as a partial function.-/
noncomputable def chi (R : Set ℕ) : ℕ →. ℕ := fun k => Part.some (if k ∈ R then 1 else 0)

/-- The singleton oracle set `{χ_R}`.-/
def oracle (R : Set ℕ) : Set (ℕ →. ℕ) := {chi R}

/-- `e` is an enumerator relative to `R`: it is partial recursive in `{χ_R}`, with raw words
coded by the structural `Primcodable` coding of `List (Fin n × Bool)`.-/
def IsEnumerator (R : Set ℕ) {n : ℕ} (e : ℕ →. RawWord (Fin n)) : Prop :=
  RecursiveIn (oracle R) fun k => (e k).map Encodable.encode

/-- The interpreted relator set `S_e = {eval w | ∃ k, w ∈ e k}`.-/
def enumRelators {n : ℕ} (e : ℕ →. RawWord (Fin n)) : Set (FreeGroup (Fin n)) :=
  {x | ∃ k, ∃ w ∈ e k, w.eval = x}

/-- **The class `C_R`**: groups with a presentation on finitely many generators whose relators
are enumerated by a partial function recursive in the oracle `{χ_R}`.-/
def ClassCR (R : Set ℕ) (B : Type u) [Group B] : Prop :=
  ∃ (n : ℕ) (e : ℕ →. RawWord (Fin n)), IsEnumerator R e ∧
    Nonempty (PresentedGroup (enumRelators e) ≃* B)

variable {R : Set ℕ}

/-- `C_R` is invariant under group isomorphism.
@isnad1 id=classcr.1h4v.s5.fa457f9f78a4 from=translated src=- shape=48bae4f6 vocab=ff39e224
-/
theorem ClassCR.of_mulEquiv {B B' : Type u} [Group B] [Group B'] (h : ClassCR R B)
    (f : B ≃* B') : ClassCR R B' := by
  obtain ⟨n, e, he, ⟨ψ⟩⟩ := h
  exact ⟨n, e, he, ⟨ψ.trans f⟩⟩

/--
@isnad1 id=iff.0h4v.s5.dcaba1bf809d from=translated src=- shape=af0172bd vocab=ff39e224
-/
theorem ClassCR.congr {B B' : Type u} [Group B] [Group B'] (f : B ≃* B') :
    ClassCR R B ↔ ClassCR R B' :=
  ⟨fun h => h.of_mulEquiv f, fun h => h.of_mulEquiv f.symm⟩

/-- The images of the displayed generators generate the group.
@isnad1 id=eq.0h4v.s7.4ade3e2a3b4f from=translated src=- shape=84ef4972 vocab=ae2b1e10
-/
theorem closure_range_presentation {n : ℕ} {S : Set (FreeGroup (Fin n))} {B : Type*} [Group B]
    (ψ : PresentedGroup S ≃* B) :
    Subgroup.closure (Set.range fun i => ψ (PresentedGroup.of i)) = ⊤ := by
  have h := congrArg (Subgroup.map (ψ : PresentedGroup S →* B))
    (PresentedGroup.closure_range_of S)
  rw [MonoidHom.map_closure, ← Set.range_comp,
    Subgroup.map_top_of_surjective _ ψ.surjective] at h
  exact h

/-- Members of `C_R` are finitely generated.
@isnad1 id=fg.1h2v.s4.f5148f30157b from=translated src=- shape=53f902a1 vocab=d1b67933
-/
theorem ClassCR.fg {B : Type u} [Group B] (h : ClassCR R B) : Group.FG B := by
  obtain ⟨n, e, -, ⟨ψ⟩⟩ := h
  rw [Group.fg_iff]
  exact ⟨_, closure_range_presentation ψ, Set.finite_range _⟩

/-- Members of `C_R` are countable.
@isnad1 id=countabl.1h2v.s3.04687f990f33 from=translated src=- shape=53f902a1 vocab=a321e1d9
-/
theorem ClassCR.countable {B : Type u} [Group B] (h : ClassCR R B) : Countable B := by
  obtain ⟨n, e, -, ⟨ψ⟩⟩ := h
  have : Countable (PresentedGroup (enumRelators e)) :=
    Function.Surjective.countable (QuotientGroup.mk_surjective)
  exact ψ.symm.injective.countable

/-! ### Renaming and finitely many extra relators -/

/-- Rename the outputs of `e` along `ρ` and add the finite list `hs`:
`e'(2k) = map (rename ρ) (e k)`, `e'(2k+1) = hs[k]` (or divergence if `k ≥ hs.length`).
The parity test is made **before** `e` is called.-/
def extendEnum {n m : ℕ} (e : ℕ →. RawWord (Fin n)) (ρ : Fin n → Fin m)
    (hs : List (RawWord (Fin m))) : ℕ →. RawWord (Fin m) := fun k =>
  bif k.bodd then (hs[k.div2]? : Part (RawWord (Fin m))) else (e k.div2).map (RawWord.rename ρ)

/--
@isnad1 id=iff.0h6v.s6.84431a98e5ce from=translated src=- shape=60d23089 vocab=ce710fc8
-/
theorem mem_extendEnum_iff {n m : ℕ} (e : ℕ →. RawWord (Fin n)) (ρ : Fin n → Fin m)
    (hs : List (RawWord (Fin m))) (w : RawWord (Fin m)) :
    (∃ k, w ∈ extendEnum e ρ hs k) ↔ (∃ k, ∃ v ∈ e k, RawWord.rename ρ v = w) ∨ w ∈ hs := by
  constructor
  · rintro ⟨k, hk⟩
    unfold extendEnum at hk
    cases hb : k.bodd <;> simp only [hb, Bool.cond_true, Bool.cond_false] at hk
    · obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).1 hk
      exact Or.inl ⟨_, v, hv, rfl⟩
    · right
      have hk' : hs[k.div2]? = some w := by simpa [Part.mem_ofOption] using hk
      exact List.mem_of_getElem? hk'
  · rintro (⟨k, v, hv, rfl⟩ | hw)
    · refine ⟨Nat.bit false k, ?_⟩
      simp only [extendEnum, Nat.bodd_bit, Nat.div2_bit, Bool.cond_false]
      exact Part.mem_map _ hv
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
      refine ⟨Nat.bit true i, ?_⟩
      simp only [extendEnum, Nat.bodd_bit, Nat.div2_bit, Bool.cond_true]
      rw [List.getElem?_eq_getElem hi]
      exact Part.mem_some _

/-- **Range of the extended enumerator.**
@isnad1 id=eq.0h5v.s7.feb7ec16c1b0 from=translated src=- shape=dbf3fe9a vocab=8027c8f1
-/
theorem enumRelators_extendEnum {n m : ℕ} (e : ℕ →. RawWord (Fin n)) (ρ : Fin n → Fin m)
    (hs : List (RawWord (Fin m))) :
    enumRelators (extendEnum e ρ hs) =
      FreeGroup.map ρ '' enumRelators e ∪ RawWord.eval '' {w | w ∈ hs} := by
  ext x
  constructor
  · rintro ⟨k, w, hw, rfl⟩
    rcases (mem_extendEnum_iff e ρ hs w).1 ⟨k, hw⟩ with ⟨k', v, hv, rfl⟩ | hw'
    · exact Or.inl ⟨_, ⟨k', v, hv, rfl⟩, (RawWord.eval_rename ρ v).symm⟩
    · exact Or.inr ⟨w, hw', rfl⟩
  · rintro (⟨_, ⟨k, v, hv, rfl⟩, rfl⟩ | ⟨w, hw, rfl⟩)
    · obtain ⟨k', hk'⟩ := (mem_extendEnum_iff e ρ hs _).2 (Or.inl ⟨k, v, hv, rfl⟩)
      exact ⟨k', _, hk', RawWord.eval_rename ρ v⟩
    · obtain ⟨k', hk'⟩ := (mem_extendEnum_iff e ρ hs w).2 (Or.inr hw)
      exact ⟨k', w, hk', rfl⟩

/-- A fixed finite table of raw words is computable (as a partial function `ℕ →. ℕ` of
codes, diverging beyond the table).
@isnad1 id=partrec.0h2v.s6.d9ffddf43d96 from=translated src=- shape=33acdc57 vocab=ea6913cb
-/
theorem partrec_table {m : ℕ} (hs : List (RawWord (Fin m))) :
    Nat.Partrec fun k => ((hs[k]?).map Encodable.encode : Part ℕ) := by
  apply Partrec.nat_iff.1
  exact Computable.ofOption (Primrec.option_map
    (Primrec.list_getElem?.comp (Primrec.const hs) Primrec.id)
    (Primrec.encode.comp Primrec.snd).to₂).to_comp

end TheoremA.RelPres
