/-
# The diamond lemma for linear rewriting

A **linear rewriting system** (`Rewriting`) on a set `M` of monomials: a well-founded transitive
relation `lt` and, for each monomial `m`, a set `red m` of one-step reductions, vectors of
`M →₀ R` supported on monomials smaller than `m`. Its ideal (`Rewriting.ideal`) is spanned by
the differences `single m 1 - v` with `v ∈ red m`; a monomial is irreducible (`Rewriting.Irr`)
when it has no reduction.

* **Spanning** (`Rewriting.sup_eq_top`): every vector is congruent modulo the ideal to a
  combination of irreducible monomials, by well-founded induction.
* **The normal form** (`Rewriting.nf`), defined by well-founded recursion with a chosen reduction
  at each reducible monomial; it is congruent to the identity modulo the ideal
  (`Rewriting.nf_sub_mem`) and takes values in the irreducible monomials
  (`Rewriting.nf_mem_supported`).
* **The diamond lemma of Bergman** (`Rewriting.resolvable_iff`): the irreducible monomials span
  a complement of the ideal if and only if every ambiguity is resolvable relative to the order
  (`Rewriting.Resolvable`): two reductions of a monomial `m` differ by an element of the span of
  the differences at the monomials smaller than `m`. Then the normal form vanishes exactly on the
  ideal (`Rewriting.nf_eq_zero_iff`), and the irreducible monomials are a basis of the quotient
  (`Rewriting.basis`).

The order need not be total, and nothing is assumed about the ring beyond `Ring`.
-/
import Tengoku.Seed.LinearAlgebra.Finsupp.Supported
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination
import Tengoku.Seed.LinearAlgebra.Projection
import Tengoku.Seed.LinearAlgebra.Basis.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Operad

/-- **A linear rewriting system** on the monomials `M`: a well-founded transitive relation `lt`
and, for each monomial `m`, a set `red m` of one-step reductions, vectors supported on the
monomials smaller than `m`.-/
structure Rewriting (R : Type*) [Ring R] (M : Type*) where
  /-- the order on the monomials-/
  lt : M → M → Prop
  /-- the order is well-founded-/
  wf : WellFounded lt
  /-- the order is transitive-/
  trans : ∀ {a b c : M}, lt a b → lt b c → lt a c
  /-- the one-step reductions of a monomial-/
  red : M → Set (M →₀ R)
  /-- reductions only involve smaller monomials-/
  red_lt : ∀ {m : M} {v : M →₀ R}, v ∈ red m → ∀ m' ∈ v.support, lt m' m

namespace Rewriting

open Finsupp

variable {R : Type*} [Ring R] {M : Type*} (S : Rewriting R M)

/-- **The rewriting ideal on a set `s` of monomials**: the span of the differences
`single m 1 - v` with `m ∈ s` and `v ∈ red m`.-/
noncomputable def idealOn (s : Set M) : Submodule R (M →₀ R) :=
  Submodule.span R {x | ∃ m ∈ s, ∃ v ∈ S.red m, x = single m 1 - v}

/-- **The rewriting ideal**: the span of the differences `single m 1 - v` with `v ∈ red m`.-/
noncomputable def ideal : Submodule R (M →₀ R) := S.idealOn Set.univ

/-- **The monomials smaller than `m`.**-/
def below (m : M) : Set M := {m' | S.lt m' m}

/-- **The irreducible monomials**: those with no reduction.-/
def Irr : Set M := {m | S.red m = ∅}

/-- **Every ambiguity is resolvable** relative to the order: two reductions of a monomial `m`
differ by an element of the rewriting ideal on the monomials smaller than `m`.-/
def Resolvable : Prop :=
  ∀ m, ∀ v ∈ S.red m, ∀ v' ∈ S.red m, v - v' ∈ S.idealOn (S.below m)

/-- A set of monomials is **downward closed**.-/
def IsDown (s : Set M) : Prop := ∀ m ∈ s, ∀ m', S.lt m' m → m' ∈ s

/--
@isnad1 id=isdown.0h4v.s4.0839051e215d from=translated src=- shape=577996db vocab=2ba1d539
-/
lemma isDown_below (m : M) : S.IsDown (S.below m) := fun _ h _ h' => S.trans h' h

/--
@isnad1 id=isdown.0h3v.s4.9ddeb19cd64d from=translated src=- shape=77c16275 vocab=3e9130cd
-/
lemma isDown_univ : S.IsDown Set.univ := fun _ _ _ _ => trivial

/--
@isnad1 id=le.1h5v.s7.e8cc8426e650 from=translated src=- shape=d8e24826 vocab=b30187eb
-/
lemma idealOn_mono {s t : Set M} (h : s ⊆ t) : S.idealOn s ≤ S.idealOn t :=
  Submodule.span_mono fun _ ⟨m, hm, v, hv, e⟩ => ⟨m, h hm, v, hv, e⟩

/--
@isnad1 id=le.0h4v.s7.ef8f63d50586 from=translated src=- shape=2a7c075e vocab=db87974d
-/
lemma idealOn_le_ideal (s : Set M) : S.idealOn s ≤ S.ideal :=
  S.idealOn_mono (Set.subset_univ s)

/--
@isnad1 id=mem.2h6v.s8.7dd39a0deb16 from=translated src=- shape=f8b0abfe vocab=8cf419e8
-/
lemma sub_mem_idealOn {s : Set M} {m : M} (hm : m ∈ s) {v : M →₀ R} (hv : v ∈ S.red m) :
    single m 1 - v ∈ S.idealOn s :=
  Submodule.subset_span ⟨m, hm, v, hv, rfl⟩

/--
@isnad1 id=mem.1h5v.s8.4679cf8785b6 from=translated src=- shape=d599987b vocab=c4f8fe8c
-/
lemma sub_mem_ideal {m : M} {v : M →₀ R} (hv : v ∈ S.red m) : single m 1 - v ∈ S.ideal :=
  S.sub_mem_idealOn (Set.mem_univ m) hv

/--
@isnad1 id=mem.1h5v.s8.8f9d83de185d from=translated src=- shape=809d978e vocab=6fcdaa43
-/
lemma red_mem_supported {m : M} {v : M →₀ R} (hv : v ∈ S.red m) :
    v ∈ supported R R (S.below m) :=
  (mem_supported R v).2 fun m' hm' => S.red_lt hv m' hm'

/--
@isnad1 id=iff.0h4v.s5.6349fa2623d0 from=translated src=- shape=f091ca06 vocab=09bd4e1f
-/
lemma mem_irr_iff {m : M} : m ∈ S.Irr ↔ ¬ (S.red m).Nonempty := by
  rw [Set.not_nonempty_iff_eq_empty]; rfl

omit S in
/-- A vector supported on a set of monomials whose basis vectors lie in a submodule lies in
it.
@isnad1 id=mem.2h5v.s9.f6ea54ec5e11 from=translated src=- shape=b1af906f vocab=b98b8f2b
-/
lemma mem_of_supported {N : Submodule R (M →₀ R)} {s : Set M} (h : ∀ m ∈ s, single m 1 ∈ N)
    {v : M →₀ R} (hv : v ∈ supported R R s) : v ∈ N := by
  rw [supported_eq_span_single] at hv
  exact Submodule.span_le.2 (by rintro _ ⟨m, hm, rfl⟩; exact h m hm) hv

/-! ## Spanning -/

/-- **Spanning**: on a downward closed set `s` of monomials, every basis vector is congruent
modulo the rewriting ideal on `s` to a combination of irreducible monomials.
@isnad1 id=mem.2h5v.s9.0d374a6c325e from=translated src=- shape=18c7317e vocab=52c3fceb
-/
theorem single_mem_sup {s : Set M} (hs : S.IsDown s) (m : M) (hm : m ∈ s) :
    single m 1 ∈ supported R R S.Irr ⊔ S.idealOn s := by
  induction m using S.wf.induction with
  | _ m ih =>
  by_cases h : (S.red m).Nonempty
  · obtain ⟨v, hv⟩ := h
    have hv' : v ∈ supported R R S.Irr ⊔ S.idealOn s :=
      mem_of_supported (fun m' hm' => ih m' hm' (hs m hm m' hm')) (S.red_mem_supported hv)
    have := Submodule.add_mem _ (Submodule.mem_sup_right (S.sub_mem_idealOn hm hv)) hv'
    rwa [sub_add_cancel] at this
  · exact Submodule.mem_sup_left (single_mem_supported R 1 (S.mem_irr_iff.2 h))

/--
@isnad1 id=le.1h4v.s9.d99531f23bc5 from=translated src=- shape=a7e8cec6 vocab=125e5eea
-/
theorem supported_le_sup {s : Set M} (hs : S.IsDown s) :
    supported R R s ≤ supported R R S.Irr ⊔ S.idealOn s :=
  fun _ hv => mem_of_supported (fun m hm => S.single_mem_sup hs m hm) hv

/-- **The irreducible monomials and the ideal span everything.**
@isnad1 id=eq.0h3v.s8.5da3d1ace624 from=translated src=- shape=6cdd1885 vocab=ef2d8688
-/
theorem sup_eq_top : supported R R S.Irr ⊔ S.ideal = ⊤ :=
  eq_top_iff.2 fun v _ => S.supported_le_sup S.isDown_univ (by rw [supported_univ]; trivial)

/-! ## The normal form -/

open Classical in
/-- **The normal form of a monomial**, by well-founded recursion: an irreducible monomial is its
own normal form; a reducible one has the normal form of a chosen reduction.-/
noncomputable def nfMono : M → (M →₀ R) :=
  S.wf.fix fun m rec =>
    if h : (S.red m).Nonempty then
      h.some.sum fun m' c => if hm' : S.lt m' m then c • rec m' hm' else 0
    else single m 1

/-- **The normal form**, the linear extension of `nfMono`.-/
noncomputable def nf : (M →₀ R) →ₗ[R] (M →₀ R) := linearCombination R S.nfMono

/--
@isnad1 id=eq.0h5v.s8.9f2a2aa667b0 from=translated src=- shape=bdac6d9a vocab=2370f62d
-/
lemma nf_single (m : M) (c : R) : S.nf (single m c) = c • S.nfMono m :=
  linearCombination_single R c m

/--
@isnad1 id=eq.0h4v.s8.892acf15eba4 from=translated src=- shape=fa15bd51 vocab=b5600654
-/
lemma nf_apply (v : M →₀ R) : S.nf v = v.sum fun m c => c • S.nfMono m :=
  linearCombination_apply R v

/--
@isnad1 id=eq.1h4v.s8.aeec6bfa2f39 from=translated src=- shape=cee9a2f7 vocab=6087cce4
-/
lemma nfMono_of_nonempty {m : M} (h : (S.red m).Nonempty) : S.nfMono m = S.nf h.some := by
  classical
  rw [nfMono, WellFounded.fix_eq, dite_eq_left h, nf_apply]
  exact sum_congr fun m' hm' => by rw [dite_eq_left (S.red_lt h.some_mem m' hm')]; rfl

/--
@isnad1 id=eq.1h4v.s6.9135e6849dcb from=translated src=- shape=82eb46fc vocab=1e36ab51
-/
lemma nfMono_of_irr {m : M} (h : m ∈ S.Irr) : S.nfMono m = single m 1 := by
  classical
  rw [nfMono, WellFounded.fix_eq, dite_eq_right (S.mem_irr_iff.1 h)]

/--
@isnad1 id=eq.1h4v.s8.a3cbe6d1d490 from=translated src=- shape=06b34533 vocab=b2acc551
-/
lemma nf_single_of_irr {m : M} (h : m ∈ S.Irr) : S.nf (single m 1) = single m 1 := by
  rw [nf_single, one_smul, S.nfMono_of_irr h]

/-- The normal form is the identity on the combinations of irreducible monomials.
@isnad1 id=eq.1h4v.s8.5438ca4d860c from=translated src=- shape=6f63f34a vocab=fa3e0e42
-/
lemma nf_of_mem_supported {v : M →₀ R} (hv : v ∈ supported R R S.Irr) : S.nf v = v :=
  mem_of_supported (N := LinearMap.eqLocus S.nf LinearMap.id)
    (fun _ hm => S.nf_single_of_irr hm) hv

/-- The normal form of a monomial is a combination of irreducible monomials.
@isnad1 id=mem.0h4v.s7.0059358c6fe0 from=translated src=- shape=7f193813 vocab=287c54a6
-/
lemma nfMono_mem_supported (m : M) : S.nfMono m ∈ supported R R S.Irr := by
  induction m using S.wf.induction with
  | _ m ih =>
  by_cases h : (S.red m).Nonempty
  · rw [S.nfMono_of_nonempty h]
    refine mem_of_supported (N := (supported R R S.Irr).comap S.nf) (fun m' hm' => ?_)
      (S.red_mem_supported h.some_mem)
    rw [Submodule.mem_comap, nf_single, one_smul]
    exact ih m' hm'
  · rw [S.nfMono_of_irr (S.mem_irr_iff.2 h)]
    exact single_mem_supported R 1 (S.mem_irr_iff.2 h)

/-- **The normal form is a combination of irreducible monomials.**
@isnad1 id=mem.0h4v.s8.6c44131261f2 from=translated src=- shape=0e06586a vocab=fa3e0e42
-/
lemma nf_mem_supported (v : M →₀ R) : S.nf v ∈ supported R R S.Irr :=
  mem_of_supported (s := Set.univ) (N := (supported R R S.Irr).comap S.nf)
    (fun m _ => by rw [Submodule.mem_comap, nf_single, one_smul]; exact S.nfMono_mem_supported m)
    (by rw [supported_univ]; trivial)

/--
@isnad1 id=mem.0h4v.s7.5973bdc47073 from=translated src=- shape=e361c710 vocab=7dfb3b55
-/
lemma nfMono_sub_mem (m : M) : S.nfMono m - single m 1 ∈ S.ideal := by
  induction m using S.wf.induction with
  | _ m ih =>
  by_cases h : (S.red m).Nonempty
  · rw [S.nfMono_of_nonempty h]
    have h1 : S.nf h.some - h.some ∈ S.ideal := by
      refine mem_of_supported (N := S.ideal.comap (S.nf - LinearMap.id)) (fun m' hm' => ?_)
        (S.red_mem_supported h.some_mem)
      rw [Submodule.mem_comap, LinearMap.sub_apply, nf_single, one_smul]
      exact ih m' hm'
    have := Submodule.sub_mem _ h1 (S.sub_mem_ideal h.some_mem)
    rwa [sub_sub_sub_cancel_right] at this
  · rw [S.nfMono_of_irr (S.mem_irr_iff.2 h), sub_self]
    exact Submodule.zero_mem _

/-- **The normal form is congruent to the identity** modulo the ideal.
@isnad1 id=mem.0h4v.s8.5444ef24e94e from=translated src=- shape=854a0486 vocab=fc7bdb7c
-/
lemma nf_sub_mem (v : M →₀ R) : S.nf v - v ∈ S.ideal :=
  mem_of_supported (s := Set.univ) (N := S.ideal.comap (S.nf - LinearMap.id))
    (fun m _ => by
      rw [Submodule.mem_comap, LinearMap.sub_apply, nf_single, one_smul]
      exact S.nfMono_sub_mem m)
    (by rw [supported_univ]; trivial)

/-- **The normal form stays in a set closed under reduction.**
@isnad1 id=mem.2h5v.s8.9456e354495d from=translated src=- shape=82e1f1f7 vocab=ebcdaa8d
-/
lemma nfMono_mem_of_closed {s : Set M} (hs : ∀ m ∈ s, ∀ v ∈ S.red m, v ∈ supported R R s) :
    ∀ m ∈ s, S.nfMono m ∈ supported R R s := by
  intro m
  induction m using S.wf.induction with
  | _ m ih =>
  intro hm
  by_cases h : (S.red m).Nonempty
  · rw [S.nfMono_of_nonempty h]
    have hsupp : h.some ∈ supported R R (s ∩ S.below m) := by
      rw [supported_inter]
      exact ⟨hs m hm _ h.some_mem, S.red_mem_supported h.some_mem⟩
    refine mem_of_supported (N := (supported R R s).comap S.nf) (fun m' hm' => ?_) hsupp
    rw [Submodule.mem_comap, nf_single, one_smul]
    exact ih m' hm'.2 hm'.1
  · rw [S.nfMono_of_irr (S.mem_irr_iff.2 h)]
    exact single_mem_supported R 1 hm

/-- **The normal form maps the combinations of a set closed under reduction into
themselves.**
@isnad1 id=mem.2h5v.s9.c60181a53e1c from=translated src=- shape=3784eb60 vocab=df5e71cb
-/
lemma nf_mem_of_closed {s : Set M} (hs : ∀ m ∈ s, ∀ v ∈ S.red m, v ∈ supported R R s)
    {v : M →₀ R} (hv : v ∈ supported R R s) : S.nf v ∈ supported R R s :=
  mem_of_supported (N := (supported R R s).comap S.nf)
    (fun m hm => by
      rw [Submodule.mem_comap, nf_single, one_smul]
      exact S.nfMono_mem_of_closed hs m hm) hv

/-- **The normal form of a reducible monomial lies strictly below it.**
@isnad1 id=mem.1h4v.s7.5033cf6096e4 from=translated src=- shape=83969f40 vocab=c3c17322
-/
lemma nfMono_mem_below {m : M} (h : (S.red m).Nonempty) :
    S.nfMono m ∈ supported R R (S.below m) := by
  rw [S.nfMono_of_nonempty h]
  refine S.nf_mem_of_closed (fun m' hm' v hv => ?_) (S.red_mem_supported h.some_mem)
  have hsub : S.below m' ⊆ S.below m := fun _ h' => S.trans h' hm'
  exact supported_mono hsub (S.red_mem_supported hv)

/-! ## The diamond lemma -/

/--
@isnad1 id=le.1h4v.s9.01625faefe0d from=translated src=- shape=142d754e vocab=8cad7dbf
-/
lemma idealOn_le_ker {s : Set M} (h : ∀ m ∈ s, ∀ v ∈ S.red m, S.nf v = S.nfMono m) :
    S.idealOn s ≤ LinearMap.ker S.nf :=
  Submodule.span_le.2 fun _ ⟨m, hm, v, hv, e⟩ => by
    rw [e, SetLike.mem_coe, LinearMap.mem_ker, map_sub, nf_single, one_smul, h m hm v hv,
      sub_self]

variable {S}

/-- **All reductions of a monomial have the same normal form** when every ambiguity is
resolvable.
@isnad1 id=eq.2h5v.s8.84106ed48011 from=translated src=- shape=15979a0a vocab=678456e1
-/
theorem Resolvable.nf_red (hS : S.Resolvable) (m : M) : ∀ v ∈ S.red m, S.nf v = S.nfMono m := by
  induction m using S.wf.induction with
  | _ m ih =>
  intro v hv
  have hne : (S.red m).Nonempty := ⟨v, hv⟩
  have := S.idealOn_le_ker (fun m' hm' => ih m' hm') (hS m v hv _ hne.some_mem)
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  rw [this, S.nfMono_of_nonempty hne]

/-- **The normal form vanishes on the ideal** when every ambiguity is resolvable.
@isnad1 id=le.1h3v.s8.b16431038b3d from=translated src=- shape=3f48dfad vocab=92bdfa33
-/
theorem Resolvable.ideal_le_ker (hS : S.Resolvable) : S.ideal ≤ LinearMap.ker S.nf :=
  S.idealOn_le_ker fun m _ => hS.nf_red m

/-- **The diamond lemma**, independence: when every ambiguity is resolvable, no nonzero
combination of irreducible monomials lies in the ideal.
@isnad1 id=disjoint.1h3v.s7.d3884016b3ca from=translated src=- shape=a0e4377f vocab=18ed09b7
-/
theorem Resolvable.disjoint (hS : S.Resolvable) : Disjoint (supported R R S.Irr) S.ideal :=
  Submodule.disjoint_def.2 fun v h1 h2 => by
    rw [← S.nf_of_mem_supported h1]
    exact hS.ideal_le_ker h2

/-- **The diamond lemma**: when every ambiguity is resolvable, the irreducible monomials span a
complement of the ideal.
@isnad1 id=iscompl.1h3v.s7.65324c408094 from=translated src=- shape=a0e4377f vocab=0170eff9
-/
theorem Resolvable.isCompl (hS : S.Resolvable) : IsCompl (supported R R S.Irr) S.ideal :=
  ⟨hS.disjoint, codisjoint_iff.2 S.sup_eq_top⟩

/-- **The converse of the diamond lemma**: if no nonzero combination of irreducible monomials
lies in the ideal, every ambiguity is resolvable.
@isnad1 id=resolvab.1h3v.s7.30caefd32ed5 from=translated src=- shape=79f5c70c vocab=18ed09b7
-/
theorem resolvable_of_disjoint (h : Disjoint (supported R R S.Irr) S.ideal) : S.Resolvable := by
  intro m v hv v' hv'
  have hsub : v - v' ∈ supported R R (S.below m) :=
    Submodule.sub_mem _ (S.red_mem_supported hv) (S.red_mem_supported hv')
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (S.supported_le_sup (S.isDown_below m) hsub)
  have hI : v - v' ∈ S.ideal := by
    have := Submodule.sub_mem _ (S.sub_mem_ideal hv') (S.sub_mem_ideal hv)
    rwa [sub_sub_sub_cancel_left] at this
  have ha' : a ∈ S.ideal := by
    have := Submodule.sub_mem _ hI (S.idealOn_le_ideal _ hb)
    rwa [← hab, add_sub_cancel_right] at this
  rw [← hab, Submodule.disjoint_def.1 h a ha ha', zero_add]
  exact hb

/-- **The diamond lemma of Bergman**: the irreducible monomials span a complement of the
rewriting ideal if and only if every ambiguity is resolvable relative to the order.
@isnad1 id=iff.0h3v.s7.ff6793d4b532 from=translated src=- shape=a27e3d36 vocab=0170eff9
-/
theorem resolvable_iff : S.Resolvable ↔ IsCompl (supported R R S.Irr) S.ideal :=
  ⟨Resolvable.isCompl, fun h => resolvable_of_disjoint h.disjoint⟩

/-- **The normal form decides membership in the ideal.**
@isnad1 id=iff.1h4v.s8.ff65eff746fd from=translated src=- shape=594aa15b vocab=15d12dc8
-/
theorem Resolvable.nf_eq_zero_iff (hS : S.Resolvable) {v : M →₀ R} :
    S.nf v = 0 ↔ v ∈ S.ideal := by
  refine ⟨fun h => ?_, fun h => hS.ideal_le_ker h⟩
  have := Submodule.neg_mem _ (S.nf_sub_mem v)
  rwa [h, zero_sub, neg_neg] at this

/-- **Two vectors are congruent modulo the ideal if and only if they have the same normal
form.**
@isnad1 id=iff.1h5v.s9.308b7f520625 from=translated src=- shape=f8292498 vocab=97800e5a
-/
theorem Resolvable.nf_eq_nf_iff (hS : S.Resolvable) {v w : M →₀ R} :
    S.nf v = S.nf w ↔ v - w ∈ S.ideal := by
  rw [← hS.nf_eq_zero_iff, map_sub, sub_eq_zero]

/-- **The irreducible monomials are a basis of the quotient** by the rewriting ideal, when
every ambiguity is resolvable.-/
noncomputable def Resolvable.basis (hS : S.Resolvable) :
    Module.Basis S.Irr R ((M →₀ R) ⧸ S.ideal) :=
  .ofRepr ((Submodule.quotientEquivOfIsCompl S.ideal _ hS.isCompl.symm).trans
    (supportedEquivFinsupp S.Irr))

/--
@isnad1 id=eq.1h4v.s9.21de5489bff3 from=translated src=- shape=ae468d01 vocab=52f8663b
-/
theorem Resolvable.basis_apply (hS : S.Resolvable) (m : S.Irr) :
    hS.basis m = Submodule.Quotient.mk (single (m : M) 1) := by
  simp only [Resolvable.basis, Module.Basis.coe_ofRepr]
  rw [LinearEquiv.symm_trans_apply, Submodule.quotientEquivOfIsCompl_symm_apply,
    supportedEquivFinsupp_symm_single]

end Rewriting

end Operad
