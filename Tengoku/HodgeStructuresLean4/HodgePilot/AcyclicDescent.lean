import Tengoku.HodgeStructuresLean4.HodgePilot.Betti
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Acyclic-resolution descent: a generic homological tool

This module is a **generic acyclic-resolution descent tool over an abelian
category with `HasExt`**, instantiable at abelian sheaves on a site with a
terminal object and, further, at abelian sheaves on a topological space.

Given an ℕ-indexed cochain complex `K` over an abelian category `C`, a *kernel
decomposition* (`Decomp K`) is a family of short exact sequences
`0 ⟶ Cyc i ⟶ K.X i ⟶ Cyc (i+1) ⟶ 0` through which the differentials factor.
From such a decomposition and any object `Z` we construct the **edge map**
sending a degree-`n` cocycle of the hom-complex `Hom(Z, K^•)` to a class in
`Ext Z (Cyc 0) n` (`Decomp.edge`), by lifting through the kernel and composing
with the `n`-fold extension class (`Decomp.chainClass`).  The Ext long exact
sequences make the induced map on cohomology bijective whenever the terms
`K.X i` are `Z`-acyclic (`Subsingleton (Ext Z (K.X i) (m+1))`):

* `Decomp.edgeHomologyEquiv` — in positive degrees, an additive equivalence
  from the `(n+1)`-st cohomology of `Hom(Z, K^•)` (cocycles mod coboundaries)
  onto `Ext Z (Cyc 0) (n+1)`;
* `Decomp.edgeZeroEquiv` — in degree `0`, with no acyclicity hypothesis;
* `decompOfExact` — a `Decomp` built from an exact augmented complex
  `F ⟶ K^0 ⟶ K^1 ⟶ ⋯` with mono augmentation, with `Cyc 0 = F` *on the nose*
  (`decompOfExact_cyc_zero` is `rfl`).

For abelian sheaves the anchor object of `Sheaf.H` is the constant sheaf at
`ULift ℤ`, and on a site with terminal object `T` the hom-group out of it is
identified with the sections over `T` via the pin's `Sheaf.H.equiv₀`
(`homEquivSections`).  Transporting cocycles and coboundaries along this
identification re-spells the source of the edge equivalence as the cohomology
of the literal **global-sections complex** `Γ(T, K^•)`:

* `descentEquiv` / `descentZeroEquiv` — for an ℕ-indexed complex `K` of
  abelian sheaves whose terms have vanishing higher sheaf cohomology
  (hypothesis `Subsingleton (Sheaf.H (K.X i) (m+1))`), together with an exact
  mono-augmented complex `F ⟶ K^0 ⟶ ⋯`, an additive equivalence from the
  `n`-th cohomology of the global-sections complex onto `Sheaf.H F n`: the
  module computes `Sheaf.H F n` from the global sections of an acyclic
  resolution, where *both* the exactness of the augmented complex and the
  acyclicity of its terms are explicit hypotheses, consumed and not proven
  here;
* `spaceDescentEquiv` / `spaceDescentZeroEquiv` — the instantiation at abelian
  sheaves on a topological space, with the exactness hypotheses in stalkwise
  form (via `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`) and the terminal
  object `⊤ : Opens X` (via `HodgePilot.Betti.opensTopTerminal`).

## Claim discipline

This file is a generic homological tool about *sheaf cohomology* (`Sheaf.H`,
an `Ext`-group) and hom-complexes; the word "resolution" above refers solely
to hypothesis packages (exactness and acyclicity assumptions) that this module
consumes — no exactness and no acyclicity of any particular complex is proven
here.  Nothing here identifies sheaf cohomology with singular cohomology in
any degree, and nothing here makes the Hodge conjecture statable.
-/

open CategoryTheory Abelian CategoryTheory.Limits Opposite

universe w' w v u

noncomputable section

namespace HodgePilot.AcyclicDescent

section Generic

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Kernel decomposition data of an ℕ-indexed cochain complex `K`: objects
`Cyc i` with `0 ⟶ Cyc i ⟶ K.X i ⟶ Cyc (i+1) ⟶ 0` short exact and the
differential factoring as `d = π ≫ ι`.  This is the interface consumed by the
descent machinery below; `decompOfExact` constructs an instance from an exact
augmented complex.-/
structure Decomp (K : CochainComplex C ℕ) where
  /-- The cycle objects; `Cyc 0` is the augmentation object.-/
  Cyc : ℕ → C
  /-- The kernel inclusions `Cyc i ⟶ K.X i`.-/
  ι : ∀ i, Cyc i ⟶ K.X i
  /-- The epimorphisms `K.X i ⟶ Cyc (i+1)`.-/
  π : ∀ i, K.X i ⟶ Cyc (i + 1)
  /-- Each `ι ≫ π` vanishes.-/
  ι_π : ∀ i, ι i ≫ π i = 0
  /-- The differential factors through the decomposition.-/
  fac : ∀ i, K.d i (i + 1) = π i ≫ ι (i + 1)
  /-- Each `0 ⟶ Cyc i ⟶ K.X i ⟶ Cyc (i+1) ⟶ 0` is short exact.-/
  shortExact : ∀ i, (ShortComplex.mk (ι i) (π i) (ι_π i)).ShortExact

namespace Decomp

variable {K : CochainComplex C ℕ} (D : Decomp K)

/-- The short complexes of the decomposition.-/
abbrev S (i : ℕ) : ShortComplex C := ShortComplex.mk (D.ι i) (D.π i) (D.ι_π i)

/-- The short complexes of the decomposition are short exact.
@isnad1 id=shortexa.0h4v.s5.9f2ff96aebc2 from=translated src=- shape=df8d9a53 vocab=d4cb694e
-/
lemma hSE (i : ℕ) : (D.S i).ShortExact := D.shortExact i

/--
@isnad1 id=mono.0h4v.s6.5e6994b85908 from=translated src=- shape=9b62901d vocab=0db679ea
-/
instance mono_ι (i : ℕ) : Mono (D.ι i) := (D.hSE i).mono_f

variable (Z : C)

/-- Cocycle conditions: against the differential iff against the epi `π`.
@isnad1 id=iff.0h6v.s9.035dc1378ab5 from=translated src=- shape=325ff625 vocab=53e7c177
-/
lemma cocycle_iff {n : ℕ} (x : Z ⟶ K.X n) :
    x ≫ K.d n (n + 1) = 0 ↔ x ≫ D.π n = 0 := by
  rw [D.fac n, ← Category.assoc]
  constructor
  · intro h
    exact zero_of_comp_mono (D.ι (n + 1)) h
  · intro h
    rw [h, Limits.zero_comp]

/-- The canonical lift of a cocycle through the kernel `Cyc n ⟶ K.X n`.-/
def toCyc {n : ℕ} (x : Z ⟶ K.X n) (hx : x ≫ D.π n = 0) :
    Z ⟶ D.Cyc n :=
  (KernelFork.IsLimit.lift' ((D.hSE n).exact.fIsKernel) x hx).1

/--
@isnad1 id=eq.1h6v.s8.40cdd5363776 from=translated src=- shape=3244fc4d vocab=83bc5b99
-/
@[simp] lemma toCyc_ι {n : ℕ} (x : Z ⟶ K.X n) (hx : x ≫ D.π n = 0) :
    D.toCyc Z x hx ≫ D.ι n = x :=
  (KernelFork.IsLimit.lift' ((D.hSE n).exact.fIsKernel) x hx).2

/-- Uniqueness of the kernel lift.
@isnad1 id=eq.2h7v.s8.fd91bd1012cd from=translated src=- shape=7d9468f8 vocab=83bc5b99
-/
lemma toCyc_unique {n : ℕ} (x : Z ⟶ K.X n) (hx : x ≫ D.π n = 0)
    (z : Z ⟶ D.Cyc n) (hz : z ≫ D.ι n = x) : z = D.toCyc Z x hx := by
  apply (cancel_mono (D.ι n)).1
  rw [hz, D.toCyc_ι]

/-- Post-composition with `π n`, as a homomorphism of hom-groups.-/
def compπ (n : ℕ) : (Z ⟶ K.X n) →+ (Z ⟶ D.Cyc (n + 1)) :=
  AddMonoidHom.mk' (fun x => x ≫ D.π n) (fun x y => by simp)

/-- Cocycles at level `n`: homs `Z ⟶ K.X n` killed by `π n` (equivalently, by
the differential — `cocycle_iff`).-/
def cocycles (n : ℕ) : AddSubgroup (Z ⟶ K.X n) :=
  (D.compπ Z n).ker

/-- Post-composition with the differential, as a homomorphism of hom-groups.-/
def compd (n : ℕ) : (Z ⟶ K.X n) →+ (Z ⟶ K.X (n + 1)) :=
  AddMonoidHom.mk' (fun y => y ≫ K.d n (n + 1)) (fun x y => by simp)

/-- Coboundaries at level `n + 1`: the range of post-composition with the
differential out of level `n`.-/
def coboundaries (n : ℕ) : AddSubgroup (Z ⟶ K.X (n + 1)) :=
  (compd (K := K) Z n).range

section WithExt

variable [HasExt.{w} C]

/-- The `n`-fold composite extension class `Ext (Cyc n) (Cyc 0) n` of the
decomposition, by explicit `Nat.rec` (starting from `Ext.mk₀ (𝟙 _)` and
composing with the extension classes of the short exact sequences).-/
def chainClass (n : ℕ) : Ext (D.Cyc n) (D.Cyc 0) n :=
  Nat.rec (motive := fun k => Ext (D.Cyc k) (D.Cyc 0) k)
    (Ext.mk₀ (𝟙 _))
    (fun k ih => ((D.hSE k).extClass).comp ih (show 1 + k = k + 1 by omega)) n

/--
@isnad1 id=eq.0h3v.s7.0a0444b870a4 from=translated src=- shape=feb46dfb vocab=93e33580
-/
@[simp] lemma chainClass_zero : D.chainClass 0 = Ext.mk₀ (𝟙 _) := rfl

/--
@isnad1 id=eq.0h4v.s7.23a9596ecf7c from=translated src=- shape=5d6b107f vocab=0e34b982
-/
@[simp] lemma chainClass_succ (n : ℕ) :
    D.chainClass (n + 1) =
      ((D.hSE n).extClass).comp (D.chainClass n) (show 1 + n = n + 1 by omega) :=
  rfl

/-- **The edge map** (elementwise): a degree-`n` cocycle of `Hom(Z, K^•)`
yields a class in `Ext Z (Cyc 0) n`, by lifting through the kernel and
composing with the `n`-fold extension class.-/
def edge {n : ℕ} (x : Z ⟶ K.X n) (hx : x ≫ D.π n = 0) :
    Ext Z (D.Cyc 0) n :=
  (Ext.mk₀ (D.toCyc Z x hx)).comp (D.chainClass n) (zero_add n)

/-- Additivity of the edge map in the cocycle.
@isnad1 id=eq.2h7v.s9.6eabffc0baf5 from=translated src=- shape=d4a555cc vocab=133c5981
-/
lemma edge_add {n : ℕ} (x y : Z ⟶ K.X n) (hx : x ≫ D.π n = 0)
    (hy : y ≫ D.π n = 0) :
    D.edge Z (x + y) (by rw [Preadditive.add_comp, hx, hy, add_zero]) =
      D.edge Z x hx + D.edge Z y hy := by
  have h1 : D.toCyc Z (x + y) (by rw [Preadditive.add_comp, hx, hy, add_zero]) =
      D.toCyc Z x hx + D.toCyc Z y hy := by
    symm
    apply D.toCyc_unique
    rw [Preadditive.add_comp, D.toCyc_ι, D.toCyc_ι]
  rw [edge, edge, edge, h1, Ext.mk₀_add, Ext.add_comp]

/-- Coboundaries die under the edge map.
@isnad1 id=eq.1h6v.s9.d95a29c29fd4 from=translated src=- shape=1ab4c99b vocab=80570273
-/
lemma edge_coboundary {n : ℕ} (y : Z ⟶ K.X n)
    (hx : (y ≫ K.d n (n + 1)) ≫ D.π (n + 1) = 0) :
    D.edge Z (y ≫ K.d n (n + 1)) hx = 0 := by
  have h1 : D.toCyc Z (y ≫ K.d n (n + 1)) hx = y ≫ D.π n := by
    symm
    apply D.toCyc_unique
    rw [Category.assoc, ← D.fac n]
  have h2 : (Ext.mk₀ (D.π n)).comp
      (((D.hSE n).extClass).comp (D.chainClass n) (show 1 + n = n + 1 by omega))
      (zero_add (n + 1)) = 0 :=
    (D.hSE n).comp_extClass_assoc _ _
  rw [edge, h1, ← Ext.mk₀_comp_mk₀, D.chainClass_succ,
    Ext.comp_assoc_of_second_deg_zero, h2, Ext.comp_zero]

/-- Dimension shifting: composition with the extension class of the `i`-th
short exact sequence is bijective
`Ext Z (Cyc (i+1)) (m+1) → Ext Z (Cyc i) (m+2)` when the middle terms are
`Z`-acyclic (from the pin's Ext long exact sequences; no derived category
enters).
@isnad1 id=bijectiv.1h6v.s10.2c96a489d1f8 from=translated src=- shape=dfd8f0ba vocab=5c379f93
-/
lemma postcomp_extClass_bijective
    (hAc : ∀ i m, Subsingleton (Ext.{w} Z (K.X i) (m + 1))) (i m : ℕ) :
    Function.Bijective
      (((D.hSE i).extClass).postcomp Z (show (m + 1) + 1 = m + 2 from rfl) :
        Ext Z (D.Cyc (i + 1)) (m + 1) →+ Ext Z (D.Cyc i) (m + 2)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    replace hx : x.comp ((D.hSE i).extClass) rfl = 0 := hx
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ Z (D.hSE i) x rfl hx
    haveI := hAc i m
    rw [Subsingleton.elim x₂ 0, Ext.zero_comp] at hx₂
    exact hx₂.symm
  · intro e
    haveI := hAc i (m + 1)
    obtain ⟨x₃, hx₃⟩ :=
      Ext.covariant_sequence_exact₁ Z (D.hSE i) e (Subsingleton.elim _ 0) rfl
    exact ⟨x₃, hx₃⟩

/-- Composition with the `n`-fold chain class is bijective on `Ext`-groups of
positive source degree (the target degree `c` is kept general to dodge
`ℕ`-addition definitional-equality traps).
@isnad1 id=bijectiv.2h7v.s9.9a4d81c4484f from=translated src=- shape=7c8af0dd vocab=37309776
-/
lemma postcomp_chainClass_bijective
    (hAc : ∀ i m, Subsingleton (Ext.{w} Z (K.X i) (m + 1))) :
    ∀ (n m c : ℕ) (h : (m + 1) + n = c),
    Function.Bijective ((D.chainClass n).postcomp Z h :
      Ext Z (D.Cyc n) (m + 1) →+ Ext Z (D.Cyc 0) c) := by
  intro n
  induction n with
  | zero =>
    intro m c h
    obtain rfl : m + 1 = c := h
    constructor
    · intro x y hxy
      calc x = x.comp (D.chainClass 0) (add_zero (m + 1)) :=
            (Ext.comp_mk₀_id x).symm
        _ = y.comp (D.chainClass 0) (add_zero (m + 1)) := hxy
        _ = y := Ext.comp_mk₀_id y
    · intro e
      exact ⟨e, Ext.comp_mk₀_id e⟩
  | succ n IH =>
    intro m c h
    have hstep := D.postcomp_extClass_bijective Z hAc n m
    have hrest := IH (m + 1) c (by omega)
    have heq : ⇑((D.chainClass (n + 1)).postcomp Z h) =
        ⇑((D.chainClass n).postcomp Z (show (m + 2) + n = c by omega)) ∘
          ⇑(((D.hSE n).extClass).postcomp Z
            (show (m + 1) + 1 = m + 2 from rfl)) := by
      funext x
      exact (Ext.comp_assoc x ((D.hSE n).extClass) (D.chainClass n)
        (show (m + 1) + 1 = m + 2 from rfl) (show 1 + n = n + 1 by omega)
        (show (m + 1) + 1 + n = c by omega)).symm
    rw [heq]
    exact hrest.comp hstep

/-- **Surjectivity** of the edge map in positive degrees, given `Z`-acyclicity
of the terms of `K`: every class in `Ext Z (Cyc 0) (n+1)` is hit by a cocycle.
@isnad1 id=ex.1h6v.s9.2e0eda5f6174 from=translated src=- shape=dab4a285 vocab=1504777d
-/
theorem edge_surjective
    (hAc : ∀ i m, Subsingleton (Ext.{w} Z (K.X i) (m + 1))) (n : ℕ)
    (e : Ext Z (D.Cyc 0) (n + 1)) :
    ∃ (x : Z ⟶ K.X (n + 1)) (hx : x ≫ D.π (n + 1) = 0), D.edge Z x hx = e := by
  obtain ⟨e₁, he₁⟩ :=
    (D.postcomp_chainClass_bijective Z hAc n 0 (n + 1) (by omega)).2 e
  haveI := hAc n 0
  obtain ⟨x₀, hx₀⟩ :=
    Ext.covariant_sequence_exact₁ Z (D.hSE n) e₁ (Subsingleton.elim _ 0) rfl
  refine ⟨(Ext.addEquiv₀ x₀) ≫ D.ι (n + 1), ?_, ?_⟩
  · rw [Category.assoc, D.ι_π, Limits.comp_zero]
  · have htc : D.toCyc Z ((Ext.addEquiv₀ x₀) ≫ D.ι (n + 1))
        (by rw [Category.assoc, D.ι_π, Limits.comp_zero]) = Ext.addEquiv₀ x₀ :=
      (D.toCyc_unique Z _ _ _ rfl).symm
    rw [edge, htc, Ext.mk₀_addEquiv₀_apply, D.chainClass_succ,
      ← Ext.comp_assoc x₀ ((D.hSE n).extClass) (D.chainClass n)
        (show 0 + 1 = 1 from rfl) (show 1 + n = n + 1 by omega)
        (show 0 + 1 + n = n + 1 by omega),
      hx₀]
    exact he₁

/-- **The kernel** of the edge map in positive degrees is exactly the
coboundaries, given `Z`-acyclicity of the terms of `K`.
@isnad1 id=iff.2h6v.s9.835f407193ab from=translated src=- shape=fb52271c vocab=8109736d
-/
theorem edge_eq_zero_iff
    (hAc : ∀ i m, Subsingleton (Ext.{w} Z (K.X i) (m + 1))) (n : ℕ)
    (x : Z ⟶ K.X (n + 1)) (hx : x ≫ D.π (n + 1) = 0) :
    D.edge Z x hx = 0 ↔ ∃ y : Z ⟶ K.X n, y ≫ K.d n (n + 1) = x := by
  constructor
  · intro h0
    have h1 : ((Ext.mk₀ (D.toCyc Z x hx)).comp ((D.hSE n).extClass)
        (zero_add 1)).comp (D.chainClass n) (show 1 + n = n + 1 by omega) = 0 :=
      (Ext.comp_assoc (Ext.mk₀ (D.toCyc Z x hx)) ((D.hSE n).extClass)
        (D.chainClass n) (zero_add 1) (show 1 + n = n + 1 by omega)
        (show 0 + 1 + n = n + 1 by omega)).trans h0
    have h2 : (Ext.mk₀ (D.toCyc Z x hx)).comp ((D.hSE n).extClass)
        (zero_add 1) = 0 :=
      (injective_iff_map_eq_zero _).1
        (D.postcomp_chainClass_bijective Z hAc n 0 (n + 1) (by omega)).1 _ h1
    obtain ⟨y₀, hy₀⟩ := Ext.covariant_sequence_exact₃ Z (D.hSE n) _ rfl h2
    refine ⟨Ext.addEquiv₀ y₀, ?_⟩
    have h3 : (Ext.addEquiv₀ y₀) ≫ D.π n = D.toCyc Z x hx := by
      apply (Ext.mk₀_bijective _ _).1
      rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
      exact hy₀
    rw [D.fac n, ← Category.assoc, h3]
    exact D.toCyc_ι Z x hx
  · rintro ⟨y, rfl⟩
    exact D.edge_coboundary Z y hx

/-- Degree zero: the edge map is injective on cocycles (no acyclicity
needed).
@isnad1 id=eq.3h6v.s9.b0579b84eeac from=translated src=- shape=ae342498 vocab=c04d9358
-/
theorem edge_zero_injective (x x' : Z ⟶ K.X 0) (hx : x ≫ D.π 0 = 0)
    (hx' : x' ≫ D.π 0 = 0) (h : D.edge Z x hx = D.edge Z x' hx') : x = x' := by
  rw [edge, edge, chainClass_zero, Ext.comp_mk₀_id, Ext.comp_mk₀_id] at h
  have h2 := (Ext.mk₀_bijective Z (D.Cyc 0)).1 h
  rw [← D.toCyc_ι Z x hx, ← D.toCyc_ι Z x' hx', h2]

/-- Degree zero: the edge map is surjective onto `Ext Z (Cyc 0) 0` (no
acyclicity needed).
@isnad1 id=ex.0h5v.s9.57d9f5c9093a from=translated src=- shape=0f80e9ed vocab=c04d9358
-/
theorem edge_zero_surjective (e : Ext Z (D.Cyc 0) 0) :
    ∃ (x : Z ⟶ K.X 0) (hx : x ≫ D.π 0 = 0), D.edge Z x hx = e := by
  refine ⟨(Ext.addEquiv₀ e) ≫ D.ι 0, ?_, ?_⟩
  · rw [Category.assoc, D.ι_π, Limits.comp_zero]
  · have htc : D.toCyc Z ((Ext.addEquiv₀ e) ≫ D.ι 0)
        (by rw [Category.assoc, D.ι_π, Limits.comp_zero]) = Ext.addEquiv₀ e :=
      (D.toCyc_unique Z _ _ _ rfl).symm
    rw [edge, htc, Ext.mk₀_addEquiv₀_apply, chainClass_zero, Ext.comp_mk₀_id]

/-- The edge map as a homomorphism on cocycles.-/
def edgeHom (n : ℕ) : ↥(D.cocycles Z n) →+ Ext Z (D.Cyc 0) n :=
  AddMonoidHom.mk' (fun x => D.edge Z x.1 x.2)
    (fun x y => D.edge_add Z x.1 y.1 x.2 y.2)

/-- Coboundaries lie in the kernel of the edge homomorphism.
@isnad1 id=le.0h5v.s12.9012624aa713 from=translated src=- shape=97d4218e vocab=9dfe65d5
-/
lemma coboundaries_le_ker (n : ℕ) :
    (coboundaries (K := K) Z n).addSubgroupOf (D.cocycles Z (n + 1)) ≤
      (D.edgeHom Z (n + 1)).ker := by
  rintro ⟨x, hx⟩ hmem
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨y, hy⟩ := hmem
  rw [AddMonoidHom.mem_ker]
  have hy' : y ≫ K.d n (n + 1) = x := hy
  subst hy'
  exact D.edge_coboundary Z y hx

/-- **The cohomology-level bijection** in positive degrees: given
`Z`-acyclicity of the terms of `K`, the edge map descends to an additive
equivalence from the `(n+1)`-st cohomology of the hom-complex `Hom(Z, K^•)`
(cocycles mod coboundaries) onto `Ext Z (Cyc 0) (n+1)`.-/
def edgeHomologyEquiv
    (hAc : ∀ i m, Subsingleton (Ext.{w} Z (K.X i) (m + 1))) (n : ℕ) :
    (↥(D.cocycles Z (n + 1)) ⧸
      ((coboundaries (K := K) Z n).addSubgroupOf (D.cocycles Z (n + 1)))) ≃+
      Ext Z (D.Cyc 0) (n + 1) :=
  AddEquiv.ofBijective
    (QuotientAddGroup.lift _ (D.edgeHom Z (n + 1)) (D.coboundaries_le_ker Z n))
    (by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro q hq
        obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
        refine (QuotientAddGroup.eq_zero_iff _).2 ?_
        rw [AddSubgroup.mem_addSubgroupOf]
        obtain ⟨y, hy⟩ := (D.edge_eq_zero_iff Z hAc n x hx).1 hq
        exact ⟨y, hy⟩
      · intro e
        obtain ⟨x, hx, he⟩ := D.edge_surjective Z hAc n e
        exact ⟨QuotientAddGroup.mk ⟨x, hx⟩, he⟩)

/-- Degree zero: the edge map is an additive equivalence from the degree-`0`
cocycles (there are no coboundaries at level `0`) onto `Ext Z (Cyc 0) 0`.
No acyclicity is needed.-/
def edgeZeroEquiv : ↥(D.cocycles Z 0) ≃+ Ext Z (D.Cyc 0) 0 :=
  AddEquiv.ofBijective (D.edgeHom Z 0)
    ⟨fun x y h => Subtype.ext (D.edge_zero_injective Z x.1 y.1 x.2 y.2 h),
     fun e => by
      obtain ⟨x, hx, he⟩ := D.edge_zero_surjective Z e
      exact ⟨⟨x, hx⟩, he⟩⟩

end WithExt

end Decomp

/-! ## Constructing a `Decomp` from an exact augmented complex -/

section Build

variable (K : CochainComplex C ℕ) (F : C) (aug : F ⟶ K.X 0)

/-- One floor of the tower: an object over `K.X i` composing to zero with the
next differential.-/
structure Step (i : ℕ) where
  /-- The floor object.-/
  Cyc : C
  /-- Its structure map to `K.X i`.-/
  ι : Cyc ⟶ K.X i
  /-- The structure map composes to zero with the next differential.-/
  w : ι ≫ K.d i (i + 1) = 0

/-- The recursive tower: `Cyc 0 := F` (augmentation),
`Cyc (i+1) := coker (ι i)`.-/
def step (waug : aug ≫ K.d 0 1 = 0) : ∀ i : ℕ, Step K i :=
  Nat.rec
    ⟨F, aug, waug⟩
    (fun i prev =>
      ⟨cokernel prev.ι,
       cokernel.desc prev.ι (K.d i (i + 1)) prev.w,
       by
         rw [← cancel_epi (cokernel.π prev.ι)]
         simp⟩)

variable {K F aug}

/-- Each floor composes exactly with the differential, given exactness of the
augmented complex.
@isnad1 id=exact.3h5v.s9.e229e3ac841e from=translated src=- shape=6564cdb9 vocab=33c75f88
-/
lemma step_exact (waug : aug ≫ K.d 0 1 = 0)
    (hex0 : (ShortComplex.mk aug (K.d 0 1) waug).Exact)
    (hexS : ∀ i, (ShortComplex.mk (K.d i (i + 1)) (K.d (i + 1) (i + 2))
      (K.d_comp_d _ _ _)).Exact) :
    ∀ i, (ShortComplex.mk (step K F aug waug i).ι (K.d i (i + 1))
      (step K F aug waug i).w).Exact
  | 0 => hex0
  | (i + 1) => by
    exact (@ShortComplex.exact_iff_of_epi_of_isIso_of_mono C _ _
      (ShortComplex.mk (K.d i (i + 1)) (K.d (i + 1) (i + 2)) (K.d_comp_d _ _ _))
      (ShortComplex.mk (step K F aug waug (i + 1)).ι (K.d (i + 1) (i + 2))
        (step K F aug waug (i + 1)).w)
      { τ₁ := cokernel.π (step K F aug waug i).ι
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := (cokernel.π_desc _ _ _).trans (Category.comp_id _).symm
        comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
      (inferInstanceAs (Epi (cokernel.π (step K F aug waug i).ι)))
      (inferInstanceAs (IsIso (𝟙 (K.X (i + 1)))))
      (inferInstanceAs (Mono (𝟙 (K.X (i + 2)))))).1 (hexS i)

/-- Each floor's inclusion is mono, given exactness and mono augmentation.
@isnad1 id=mono.4h5v.s9.a860ee3cd477 from=translated src=- shape=142ae382 vocab=d78472a5
-/
lemma step_mono (waug : aug ≫ K.d 0 1 = 0) (hmono : Mono aug)
    (hex0 : (ShortComplex.mk aug (K.d 0 1) waug).Exact)
    (hexS : ∀ i, (ShortComplex.mk (K.d i (i + 1)) (K.d (i + 1) (i + 2))
      (K.d_comp_d _ _ _)).Exact) :
    ∀ i, Mono (step K F aug waug i).ι
  | 0 => hmono
  | (i + 1) => (step_exact waug hex0 hexS i).mono_cokernelDesc

/-- A `Decomp` from an exact augmented complex, with `Cyc 0 = F` on the nose
(`decompOfExact_cyc_zero` is `rfl`).-/
def decompOfExact (waug : aug ≫ K.d 0 1 = 0) (hmono : Mono aug)
    (hex0 : (ShortComplex.mk aug (K.d 0 1) waug).Exact)
    (hexS : ∀ i, (ShortComplex.mk (K.d i (i + 1)) (K.d (i + 1) (i + 2))
      (K.d_comp_d _ _ _)).Exact) :
    Decomp K where
  Cyc i := (step K F aug waug i).Cyc
  ι i := (step K F aug waug i).ι
  π i := cokernel.π (step K F aug waug i).ι
  ι_π _ := cokernel.condition _
  fac _ := (cokernel.π_desc _ _ _).symm
  shortExact i :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := step_mono waug hmono hex0 hexS i
      epi_g := inferInstanceAs (Epi (cokernel.π (step K F aug waug i).ι)) }

/-- The interface fact: the augmentation object is the zeroth cycle object
*literally*, so every `Ext Z (Cyc 0) n` of the machinery above is an
`Ext Z F n` on the nose.
@isnad1 id=eq.4h4v.s9.16889a6aafeb from=translated src=- shape=f80e614b vocab=256c6bc7
-/
@[simp] lemma decompOfExact_cyc_zero (waug : aug ≫ K.d 0 1 = 0) (hmono : Mono aug)
    (hex0 : (ShortComplex.mk aug (K.d 0 1) waug).Exact)
    (hexS : ∀ i, (ShortComplex.mk (K.d i (i + 1)) (K.d (i + 1) (i + 2))
      (K.d_comp_d _ _ _)).Exact) :
    (decompOfExact waug hmono hex0 hexS).Cyc 0 = F :=
  rfl

end Build

end Generic

/-! ## The global-sections complex of a complex of abelian sheaves -/

section SectionsComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (T : C)
  (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)

/-- The sections over `T` of the differential, as an additive homomorphism
between the section groups.-/
def sectionsD (n m : ℕ) :
    (K.X n).obj.obj (op T) →+ (K.X m).obj.obj (op T) :=
  ((K.d n m).hom.app (op T)).hom

/--
@isnad1 id=eq.0h8v.s13.fd79e84be3bf from=translated src=- shape=bb285efe vocab=7f11d06a
-/
lemma sectionsD_comp_apply (n m k : ℕ) (t : (K.X n).obj.obj (op T)) :
    sectionsD T K m k (sectionsD T K n m t) =
      ((K.d n m ≫ K.d m k).hom.app (op T)).hom t :=
  rfl

/-- Cocycles of the sections-over-`T` complex at level `n`.-/
def sectionsCocycles (n : ℕ) : AddSubgroup ((K.X n).obj.obj (op T)) :=
  (sectionsD T K n (n + 1)).ker

/-- Coboundaries of the sections-over-`T` complex at level `n + 1`.-/
def sectionsCoboundaries (n : ℕ) : AddSubgroup ((K.X (n + 1)).obj.obj (op T)) :=
  (sectionsD T K n (n + 1)).range

/-- Coboundaries are cocycles: the sections of a complex form a complex.
@isnad1 id=le.0h5v.s10.f096bb517e65 from=translated src=- shape=6d40497f vocab=47ad7de7
-/
lemma sectionsCoboundaries_le (n : ℕ) :
    sectionsCoboundaries T K n ≤ sectionsCocycles T K (n + 1) := by
  rintro s ⟨t, rfl⟩
  show sectionsD T K (n + 1) (n + 2) (sectionsD T K n (n + 1) t) = 0
  rw [sectionsD_comp_apply, K.d_comp_d]
  rfl

end SectionsComplex

/-! ## The bridge: hom-groups out of the constant sheaf as global sections -/

section Bridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

variable (J) in
/-- The anchor object of `Sheaf.H`: the constant abelian sheaf at `ULift ℤ`.-/
abbrev constZ : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))

variable {T : C}

/-- The hom-group out of the constant sheaf at `ULift ℤ` is the group of
sections over a terminal object, via `Ext.addEquiv₀` and the pin's
`Sheaf.H.equiv₀`.-/
def homEquivSections (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{w}) :
    (constZ J ⟶ F) ≃+ F.obj.obj (op T) :=
  Ext.addEquiv₀.symm.trans (Sheaf.H.equiv₀ F hT)

/-- Naturality of `homEquivSections` in the sheaf.
@isnad1 id=eq.0h8v.s12.26f28009fd40 from=translated src=- shape=e5cae5eb vocab=8d73c571
-/
lemma homEquivSections_naturality (hT : IsTerminal T)
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (u : constZ J ⟶ F) :
    f.hom.app (op T) (homEquivSections hT F u) = homEquivSections hT G (u ≫ f) := by
  have h : Sheaf.H.map f 0 (Ext.addEquiv₀.symm u) = Ext.addEquiv₀.symm (u ≫ f) :=
    Ext.addEquiv₀.injective (by
      rw [Sheaf.H.addEquiv₀_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply])
  show f.hom.app (op T) (Sheaf.H.equiv₀ F hT (Ext.addEquiv₀.symm u)) =
    Sheaf.H.equiv₀ G hT (Ext.addEquiv₀.symm (u ≫ f))
  rw [← h]
  exact Sheaf.H.equiv₀_naturality hT f _

/-- Naturality of the inverse of `homEquivSections` in the sheaf.
@isnad1 id=eq.0h8v.s12.9cc48178bccc from=translated src=- shape=fe17ce30 vocab=8cf2b858
-/
lemma homEquivSections_symm_naturality (hT : IsTerminal T)
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (s : F.obj.obj (op T)) :
    (homEquivSections hT F).symm s ≫ f =
      (homEquivSections hT G).symm (f.hom.app (op T) s) := by
  apply (homEquivSections hT G).injective
  rw [AddEquiv.apply_symm_apply, ← homEquivSections_naturality hT f,
    AddEquiv.apply_symm_apply]

variable (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ)

/-- `homEquivSections` intertwines post-composition with the differential and
the sections-level differential.
@isnad1 id=eq.0h8v.s13.72823c30fc1f from=translated src=- shape=25a0c4db vocab=08c07a56
-/
lemma sectionsD_homEquivSections (hT : IsTerminal T) (n m : ℕ)
    (u : constZ J ⟶ K.X n) :
    sectionsD T K n m (homEquivSections hT (K.X n) u) =
      homEquivSections hT (K.X m) (u ≫ K.d n m) :=
  homEquivSections_naturality hT (K.d n m) u

variable {K} (D : Decomp K)

/-- The cocycle groups of the hom-complex `Hom(constZ, K^•)` and of the
global-sections complex `Γ(T, K^•)` are identified by `homEquivSections`.-/
def sectionsCocyclesEquiv (hT : IsTerminal T) (n : ℕ) :
    ↥(D.cocycles (constZ J) n) ≃+ ↥(sectionsCocycles T K n) where
  toFun x := ⟨homEquivSections hT (K.X n) x.1, by
    have hd : x.1 ≫ K.d n (n + 1) = 0 := (D.cocycle_iff (constZ J) x.1).2 x.2
    show sectionsD T K n (n + 1) (homEquivSections hT (K.X n) x.1) = 0
    rw [sectionsD_homEquivSections K hT n (n + 1) x.1, hd]
    exact map_zero _⟩
  invFun s := ⟨(homEquivSections hT (K.X n)).symm s.1, by
    have hd : (homEquivSections hT (K.X n)).symm s.1 ≫ K.d n (n + 1) = 0 := by
      rw [homEquivSections_symm_naturality hT (K.d n (n + 1)) s.1]
      have hs : (K.d n (n + 1)).hom.app (op T) s.1 = 0 := s.2
      rw [hs]
      exact map_zero _
    exact (D.cocycle_iff (constZ J) _).1 hd⟩
  left_inv x := Subtype.ext ((homEquivSections hT (K.X n)).symm_apply_apply x.1)
  right_inv s := Subtype.ext ((homEquivSections hT (K.X n)).apply_symm_apply s.1)
  map_add' x y := Subtype.ext (map_add (homEquivSections hT (K.X n)) x.1 y.1)

set_option synthInstance.maxHeartbeats 400000 in
/-- The cocycle identification carries the (relativized) coboundary subgroup of
the hom-complex onto that of the global-sections complex.
@isnad1 id=eq.0h7v.s15.16c3f73643ff from=translated src=- shape=36b9afa0 vocab=d52eeac3
-/
lemma sectionsCoboundaries_map (hT : IsTerminal T) (n : ℕ) :
    (((Decomp.coboundaries (K := K) (constZ J) n).addSubgroupOf
        (D.cocycles (constZ J) (n + 1))).map
      (sectionsCocyclesEquiv D hT (n + 1))) =
      (sectionsCoboundaries T K n).addSubgroupOf (sectionsCocycles T K (n + 1)) := by
  ext s
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
    obtain ⟨u, hu⟩ := hmem
    have hu' : u ≫ K.d n (n + 1) = y := hu
    refine ⟨homEquivSections hT (K.X n) u, ?_⟩
    rw [sectionsD_homEquivSections K hT n (n + 1) u, hu']
    rfl
  · rintro ⟨t, ht⟩
    refine ⟨(sectionsCocyclesEquiv D hT (n + 1)).symm s, ?_,
      (sectionsCocyclesEquiv D hT (n + 1)).apply_symm_apply s⟩
    refine ⟨(homEquivSections hT (K.X n)).symm t, ?_⟩
    show (homEquivSections hT (K.X n)).symm t ≫ K.d n (n + 1) =
      (homEquivSections hT (K.X (n + 1))).symm s.1
    rw [homEquivSections_symm_naturality hT (K.d n (n + 1)) t]
    exact congrArg (homEquivSections hT (K.X (n + 1))).symm ht

/-- **Descent, hom-form to sections-form**, positive degrees: given a kernel
decomposition of `K` whose terms have vanishing higher sheaf cohomology, the
`(n+1)`-st cohomology of the global-sections complex `Γ(T, K^•)` is
additively equivalent to `Sheaf.H (Cyc 0) (n+1)`.-/
def sectionsHomologyEquiv (hT : IsTerminal T)
    (hAc : ∀ i m, Subsingleton (Sheaf.H (K.X i) (m + 1))) (n : ℕ) :
    (↥(sectionsCocycles T K (n + 1)) ⧸
      ((sectionsCoboundaries T K n).addSubgroupOf (sectionsCocycles T K (n + 1)))) ≃+
      Sheaf.H (D.Cyc 0) (n + 1) :=
  (QuotientAddGroup.congr _ _ (sectionsCocyclesEquiv D hT (n + 1))
      (sectionsCoboundaries_map D hT n)).symm.trans
    (D.edgeHomologyEquiv (constZ J) hAc n)

/-- **Descent, hom-form to sections-form**, degree zero: the degree-`0`
cocycles of the global-sections complex are additively equivalent to
`Sheaf.H (Cyc 0) 0`.  No acyclicity is needed.-/
def sectionsZeroEquiv (hT : IsTerminal T) :
    ↥(sectionsCocycles T K 0) ≃+ Sheaf.H (D.Cyc 0) 0 :=
  (sectionsCocyclesEquiv D hT 0).symm.trans (D.edgeZeroEquiv (constZ J))

variable {F : Sheaf J AddCommGrpCat.{w}} {aug : F ⟶ K.X 0}

/-- **The descent equivalence**: for an ℕ-indexed complex `K` of abelian
sheaves whose terms have vanishing higher sheaf cohomology
(`Subsingleton (Sheaf.H (K.X i) (m+1))` — a hypothesis, not proven here),
together with an exact complex `F ⟶ K^0 ⟶ K^1 ⟶ ⋯` with mono augmentation
(exactness likewise a hypothesis), the `(n+1)`-st cohomology of the
global-sections complex `Γ(T, K^•)` over a terminal object `T` is additively
equivalent to `Sheaf.H F (n+1)`.-/
def descentEquiv (hT : IsTerminal T)
    (waug : aug ≫ K.d 0 1 = 0) (hmono : Mono aug)
    (hex0 : (ShortComplex.mk aug (K.d 0 1) waug).Exact)
    (hexS : ∀ i, (ShortComplex.mk (K.d i (i + 1)) (K.d (i + 1) (i + 2))
      (K.d_comp_d _ _ _)).Exact)
    (hAc : ∀ i m, Subsingleton (Sheaf.H (K.X i) (m + 1))) (n : ℕ) :
    (↥(sectionsCocycles T K (n + 1)) ⧸
      ((sectionsCoboundaries T K n).addSubgroupOf (sectionsCocycles T K (n + 1)))) ≃+
      Sheaf.H F (n + 1) :=
  sectionsHomologyEquiv (decompOfExact waug hmono hex0 hexS) hT hAc n

/-- **The degree-zero descent equivalence**: for an exact mono-augmented
complex `F ⟶ K^0 ⟶ ⋯` of abelian sheaves (exactness a hypothesis), the
degree-`0` cocycles of the global-sections complex over a terminal object are
additively equivalent to `Sheaf.H F 0`.  No acyclicity is needed.-/
def descentZeroEquiv (hT : IsTerminal T)
    (waug : aug ≫ K.d 0 1 = 0) (hmono : Mono aug)
    (hex0 : (ShortComplex.mk aug (K.d 0 1) waug).Exact)
    (hexS : ∀ i, (ShortComplex.mk (K.d i (i + 1)) (K.d (i + 1) (i + 2))
      (K.d_comp_d _ _ _)).Exact) :
    ↥(sectionsCocycles T K 0) ≃+ Sheaf.H F 0 :=
  sectionsZeroEquiv (decompOfExact waug hmono hex0 hexS) hT

end Bridge

/-! ## Instantiation at abelian sheaves on a topological space -/

section Space

open TopologicalSpace

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

variable {X : TopCat.{0}} {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  {F : TopCat.Sheaf AddCommGrpCat.{0} X} {aug : F ⟶ K.X 0}

/-- Space-level input conversion: `decompOfExact`'s exactness hypotheses in
**stalkwise** form, discharged by the pin's stalk-detection lemma
`TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`.  The resulting `Decomp` has
`Cyc 0 = F` on the nose.-/
def decompOfStalkExact (waug : aug ≫ K.d 0 1 = 0) (hmono : Mono aug)
    (hex0 : ∀ x : X, ((ShortComplex.mk aug (K.d 0 1) waug).map
      (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)).Exact)
    (hexS : ∀ (i : ℕ) (x : X),
      ((ShortComplex.mk (K.d i (i + 1)) (K.d (i + 1) (i + 2))
        (K.d_comp_d _ _ _)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)).Exact) :
    Decomp K :=
  decompOfExact waug hmono
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2 hex0)
    (fun i => (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2 (hexS i))

end Space

end HodgePilot.AcyclicDescent
