import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.ProductModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Free-particle records and sensor polarity, first half (paper `sec:records`)

Paper labels covered (all in `sec:records`, plus `def:law` and `thm:strict` as used there):
* paragraph "The base and its law data": the base `S` of nonempty observation domains
  `I ⊆ T = {0,1,2}` with one arrow `u_{IJ} : I ⟶ J` iff `J ⊆ I` (`RecDom`), its connectedness
  (`RecDom.isConnected`), a non-invertible arrow (`RecDom.not_isIso_fromFull_single`), the record
  spaces `L(I)` (`recordSpace`), the restrictions `r_{IJ}` (`recRestrict`), the law functor
  `L = L₀ τ`, the description `L(T) = {q₂ - 2q₁ + q₀ = 0}` (`mem_recordSpace_full_iff`, uses
  `0 < τ`), and nontriviality of every `L(I)` (`recordSpace_nontrivial`, `L₀_exists_ne_zero`);
* paragraph "Presentations and their comparisons": `O = S × Pair(G)`, `p = Prod.fst`, with the
  signs represented exactly as `G = ℤˣ` (acting on real vector spaces by `((ε : ℤ) : ℝ) • ·`,
  lemmas `recSign_*`), and the normalized datum `recData := productData RecDom ℤˣ`
  (`recData_act`, `recData_base`, `recData_reind`);
* paragraph "A base symmetry and its implementation": `ρ(j) = 2 - j` (`recρ = Fin.rev`), the strict
  base involution `A(I) = ρ(I)` (`recA`), the selected subgroup `H = {1, A} ≅ C₂` (`recH`,
  `recHMulEquiv`, `recH_card`), the canonical lift `Ã(I,ε) = (ρ(I),ε)` (`recLift_obj`) commuting
  with the polarity change, the selected lift group `Sym_H(p) ≅ C₂ × C₂` (`recSym`), the natural
  linear isomorphism `α : L A ≅ L`, `(α_I x)_j = x_{ρ(j)}` (`recα`) with its involution coherence
  `α_I α_{ρ(I)} = id` (`recα_involution`, `recα_involution_natTrans`, and for labeled spaces
  `recαℓ_involution`), and the strict inequality `L A ≠ L`, both for the unlabeled law
  (`recA_comp_L₀_ne`, uses `τ ≠ 0`) and for explicitly labeled spaces (`recA_comp_Lℓ_ne`), so that
  `H` is not the strict stabilizer (`recA_not_mem_strictLawStabilizer_L₀`,
  `recH_not_le_strictLawStabilizer_L₀`, `recA_not_mem_strictLawStabilizer`).

## Representation of labeled observation spaces

The paper's claim `LA ≠ L` is made "for these explicitly labeled vector spaces". It is formalized
at two levels. Neither argument rests on a failure of `rfl`, or on deciding an equality of carrier
types (such as the carriers of `L(ρ{0})` and `L({0})`, which Lean can neither prove nor refute to
be equal).

**Unlabeled law.** For `L₀ τ : S ⥤ ModuleCat ℝ` (the paper's `L`: `I ↦ L(I) ⊆ ℝ^I`, restrictions
`r_{IJ}`) the inequality `recA.hom ⋙ L₀ τ ≠ L₀ τ` is proved for every `τ ≠ 0`
(`recA_comp_L₀_ne`). An equality of functors yields, via `Functor.congr_hom` on `u : T ⟶ {0}`,
`r_{ρ(T)ρ({0})} = c₁ ≫ r_{T{0}} ≫ c₂` with casts `cᵢ = eqToHom _` between objects of
`ModuleCat ℝ`. These casts are morphisms of `ModuleCat ℝ`, hence linear, and `c₁` is the cast
along `ρ(T) = T`, which acts as the identity on entries. Evaluating on the record `x_j = j` (take
`q₀ = 0`, `v = 1/τ`) gives `2` at index `2 ∈ ρ({0}) = {2}` on the left. On the right, `r_{T{0}}`
returns the entry `x_0 = 0`, so the result is `c₂(0) = 0`. Hence `2 = 0`, a contradiction. This is
the substantive statement about the law: `A ∉ H_L` for `L = L₀ τ`
(`recA_not_mem_strictLawStabilizer_L₀`).

**Labeled law.** For the literal reading "explicitly labeled vector spaces", the observation domain
is also kept as explicit object data. The target is the category `Pair S × ModuleCat ℝ`. Its
objects are pairs (label `⟨I⟩ : Pair S`, real vector space), and its morphisms
`(⟨I⟩, V) ⟶ (⟨J⟩, W)` are exactly the linear maps `V → W` (the `Pair` factor has a unique arrow
between any two labels, so it adds no morphism data). The forgetful functor to real vector spaces
is `Prod.snd`. The labeled law is `Lℓ τ = recLabel.prod' (L₀ τ)`, `I ↦ (⟨I⟩, L(I))`, with
`Lℓ τ ⋙ Prod.snd = L₀ τ` (`Lℓ_comp_snd`, by `rfl`). Here `LA ≠ L` follows from the labels alone:
the label of `(Lℓ τ)(A{0})` is `⟨{2}⟩` and that of `(Lℓ τ){0}` is `⟨{0}⟩` (`recA_comp_Lℓ_ne`).
The argument never looks at the record spaces. The strict stabilizer of `Lℓ τ` is trivial
(`strictLawStabilizer_Lℓ_eq_bot`). Its proof uses only the labels and the thinness of the base, so
it applies verbatim to *any* functor `I ↦ (⟨I⟩, V(I))`, whatever the law (this general form is not
stated as a separate declaration). So
`recA_not_mem_strictLawStabilizer` (for `Lℓ τ`) carries no information about the free-particle law.
The informative statement is the unlabeled one above.

The covariant implementation exists at both levels: `recα : recA.hom ⋙ L₀ τ ≅ L₀ τ` and
`recαℓ : recA.hom ⋙ Lℓ τ ≅ Lℓ τ`. The record component of `recαℓ` is `recα`
(`recαℓ_hom_app_snd`), and both satisfy the involution coherence (`recα_involution`,
`recαℓ_involution`).

## Conventions
* An arrow `I ⟶ J` of `RecDom` is a proof of `J.dom ⊆ I.dom` (wrapped in `PLift`); `RecDom` is
  deliberately a structure (not a subtype of `Finset`) so that mathlib's preorder category on
  `Finset` (with the opposite orientation) is not picked up.
* Elements of `(L₀ τ).obj I` are elements of the submodule `recordSpace τ I`; their entries are
  read with `Subtype.val x j` (`↑x j`).
* Operator order in the paper: `α_I α_{ρ(I)}` is `α_{ρ(I)} ≫ α_I` in Lean.
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

/-! ## The base `S` of observation domains -/

/-- An object of the base `S` of paper `sec:records` ("The base and its law data"): a nonempty
    subset `I ⊆ T = {0,1,2}` of observation times, encoded as a nonempty `Finset (Fin 3)`.-/
@[ext]
structure _root_.Tengoku.ObserverEquivarianceLean.RecDom where
  /-- The set `I ⊆ T` of observation indices.-/
  dom : Finset (Fin 3)
  /-- Observation domains are nonempty.-/
  nonempty : dom.Nonempty

namespace Tengoku.ObserverEquivarianceLean.RecDom

/-- The base category of paper `sec:records`: exactly one arrow `u_{IJ} : I ⟶ J` when `J ⊆ I`
    (restriction of a record to fewer times), none otherwise.-/
instance : SmallCategory RecDom where
  Hom I J := PLift (J.dom ⊆ I.dom)
  id _ := ⟨Finset.Subset.refl _⟩
  comp f g := ⟨g.down.trans f.down⟩

/-- The base of paper `sec:records` is thin: at most one arrow between two domains.-/
instance homSubsingleton (I J : RecDom) : Subsingleton (I ⟶ J) :=
  ⟨fun f g => by
    change PLift (J.dom ⊆ I.dom) at f g
    cases f; cases g; rfl⟩

/-- The arrow `u_{IJ} : I ⟶ J` for `J ⊆ I` (paper `sec:records`).-/
def homOfSubset {I J : RecDom} (h : J.dom ⊆ I.dom) : I ⟶ J := ⟨h⟩

/-- An arrow `I ⟶ J` of the base witnesses `J ⊆ I` (paper `sec:records`).-/
theorem subset_of_hom {I J : RecDom} (u : I ⟶ J) : J.dom ⊆ I.dom := u.down

/-- The full record domain `T = {0,1,2}` (paper `sec:records`).-/
def full : RecDom := ⟨Finset.univ, Finset.univ_nonempty⟩

/-- The singleton domain `{j}` (paper `sec:records`).-/
def single (j : Fin 3) : RecDom := ⟨{j}, Finset.singleton_nonempty j⟩

/-- The restriction arrow `T ⟶ I` from the full domain (paper `sec:records`: "`T` maps to every
    object").-/
def fromFull (I : RecDom) : full ⟶ I := ⟨Finset.subset_univ _⟩

end Tengoku.ObserverEquivarianceLean.RecDom

/-- The base of paper `sec:records` is connected, because `T` maps to every object.-/
instance Tengoku.ObserverEquivarianceLean.RecDom.isConnected : IsConnected RecDom := by
  haveI : Nonempty RecDom := ⟨RecDom.full⟩
  exact zigzag_isConnected fun I J =>
    (Zigzag.of_inv (RecDom.fromFull I)).trans (Zigzag.of_hom (RecDom.fromFull J))

/-! ## The record spaces `L(I)` and the functor `L₀` -/

/-- The record space `L(I) = {(q₀ + v j τ)_{j ∈ I} : q₀, v ∈ ℝ} ⊆ ℝ^I` (paper `sec:records`,
    "The base and its law data").-/
def _root_.Tengoku.ObserverEquivarianceLean.recordSpace (τ : ℝ) (I : RecDom) : Submodule ℝ (↥I.dom → ℝ) where
  carrier := {x | ∃ q₀ v : ℝ, ∀ j : ↥I.dom, x j = q₀ + v * (((j : Fin 3) : ℕ) : ℝ) * τ}
  zero_mem' := ⟨0, 0, fun j => by simp⟩
  add_mem' := by
    rintro x y ⟨a, v, hx⟩ ⟨b, w, hy⟩
    exact ⟨a + b, v + w, fun j => by simp only [Pi.add_apply, hx, hy]; ring⟩
  smul_mem' := by
    rintro c x ⟨a, v, hx⟩
    exact ⟨c * a, c * v, fun j => by simp only [Pi.smul_apply, smul_eq_mul, hx]; ring⟩

/-- Membership in the record space (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.mem_recordSpace {τ : ℝ} {I : RecDom} {x : ↥I.dom → ℝ} :
    x ∈ recordSpace τ I ↔ ∃ q₀ v : ℝ, ∀ j : ↥I.dom, x j = q₀ + v * (((j : Fin 3) : ℕ) : ℝ) * τ :=
  Iff.rfl

/-- On the full domain `T`, the record space is cut out by the second-difference relation
    `q₂ - 2 q₁ + q₀ = 0` (paper `sec:records`, display of `L(T)`; uses `τ > 0`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.mem_recordSpace_full_iff {τ : ℝ} (hτ : 0 < τ) (x : ↥RecDom.full.dom → ℝ) :
    x ∈ recordSpace τ RecDom.full ↔
      x ⟨2, Finset.mem_univ _⟩ - 2 * x ⟨1, Finset.mem_univ _⟩ + x ⟨0, Finset.mem_univ _⟩ = 0 := by
  constructor
  · rintro ⟨q₀, v, hx⟩
    rw [hx, hx, hx]
    simp
    ring
  · intro h
    refine ⟨x ⟨0, Finset.mem_univ _⟩, (x ⟨1, Finset.mem_univ _⟩ - x ⟨0, Finset.mem_univ _⟩) / τ,
      ?_⟩
    rintro ⟨j, hj⟩
    have hτ' : τ ≠ 0 := hτ.ne'
    fin_cases j
    · simp
    · simp
      field_simp
      ring
    · simp
      field_simp
      linarith

/-- The constant record `1` lies in every record space (paper `sec:records`: `q₀ = 1, v = 0`).-/
def _root_.Tengoku.ObserverEquivarianceLean.recordOne (τ : ℝ) (I : RecDom) : recordSpace τ I :=
  ⟨fun _ => 1, 1, 0, fun _ => by simp⟩

/-- The constant record `1` is nonzero, since observation domains are nonempty
    (paper `sec:records`: "each `L(I)` is nonzero").-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recordOne_ne_zero (τ : ℝ) (I : RecDom) : recordOne τ I ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := I.nonempty
  have := congrArg (fun x : recordSpace τ I => (x : ↥I.dom → ℝ) ⟨j, hj⟩) h
  simp [recordOne] at this

/-- The restriction map `r_{IJ} : L(I) → L(J)` for `J ⊆ I` (paper `sec:records`).-/
def _root_.Tengoku.ObserverEquivarianceLean.recRestrict (τ : ℝ) {I J : RecDom} (h : J.dom ⊆ I.dom) :
    recordSpace τ I →ₗ[ℝ] recordSpace τ J where
  toFun x := ⟨fun j => (x : ↥I.dom → ℝ) ⟨j.1, h j.2⟩, by
    obtain ⟨q₀, v, hx⟩ := x.2
    exact ⟨q₀, v, fun j => hx _⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Values of the restriction map (paper `sec:records`): `(r_{IJ} x)_j = x_j`.-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.recRestrict_apply (τ : ℝ) {I J : RecDom} (h : J.dom ⊆ I.dom)
    (x : recordSpace τ I) (j : ↥J.dom) :
    (recRestrict τ h x : ↥J.dom → ℝ) j = (x : ↥I.dom → ℝ) ⟨j.1, h j.2⟩ := rfl

/-- The law functor `L : S ⥤ Vect_ℝ`, `L(I) = recordSpace τ I`, `L(u_{IJ}) = r_{IJ}`
    (paper `sec:records`).-/
def _root_.Tengoku.ObserverEquivarianceLean.L₀ (τ : ℝ) : RecDom ⥤ ModuleCat.{0} ℝ where
  obj I := ModuleCat.of ℝ (recordSpace τ I)
  map u := ModuleCat.ofHom (recRestrict τ (RecDom.subset_of_hom u))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Values of `L₀(u_{IJ}) = r_{IJ}` (paper `sec:records`).-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.L₀_map_hom_apply (τ : ℝ) {I J : RecDom} (u : I ⟶ J) (x : recordSpace τ I)
    (j : ↥J.dom) :
    Subtype.val (((L₀ τ).map u).hom x) j
      = (x : ↥I.dom → ℝ) ⟨j.1, RecDom.subset_of_hom u j.2⟩ :=
  rfl

/-! ## Labeled observation spaces -/

/-- The labeling functor `S ⥤ Pair S`, `I ↦ ⟨I⟩` (paper `sec:records`, "explicitly labeled
    vector spaces": the label of `L(I)` is its observation domain `I`).-/
def _root_.Tengoku.ObserverEquivarianceLean.recLabel : RecDom ⥤ Pair RecDom where
  obj I := ⟨I⟩
  map _ := ⟨⟩

/-- The labeled law functor (paper `sec:records`, "For these explicitly labeled vector spaces"):
    `Lℓ(I) = (⟨I⟩, L(I))` in `Pair S × Vect_ℝ`, `Lℓ(u_{IJ}) = (*, r_{IJ})`.-/
def _root_.Tengoku.ObserverEquivarianceLean.Lℓ (τ : ℝ) : CategoryTheory.Functor.{0, 0} RecDom (Pair RecDom × ModuleCat.{0} ℝ) :=
  recLabel.prod' (L₀ τ)

/-! ## The presentation `O = S × Pair(G)` with `G = ℤˣ` -/

/-- The normalized presentation datum of paper `sec:records` ("Presentations and their
    comparisons"): `O = S × Pair(G)` with `G = ℤˣ = {+1, -1}`, `p(I, ε) = I`.-/
abbrev _root_.Tengoku.ObserverEquivarianceLean.recData : OEData ℤˣ (CategoryTheory.Prod.fst RecDom (Pair ℤˣ)) :=
  productData RecDom ℤˣ

/-! ## Signs acting on real vector spaces -/

/-- The real scalar of a sign `ε ∈ ℤˣ` is multiplicative (paper `sec:records`, signs act on
    records by `((ε : ℤ) : ℝ) • ·`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recSign_mul (ε δ : ℤˣ) :
    (((ε * δ : ℤˣ) : ℤ) : ℝ) = ((ε : ℤ) : ℝ) * ((δ : ℤ) : ℝ) := by
  push_cast; ring

/-- A sign squares to one (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recSign_mul_self (ε : ℤˣ) : ((ε : ℤ) : ℝ) * ((ε : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num

/-- A sign is its own inverse (paper `sec:records`: `ε⁻¹ = ε`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recSign_inv (ε : ℤˣ) : (((ε⁻¹ : ℤˣ) : ℤ) : ℝ) = ((ε : ℤ) : ℝ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num

/-- The scalar of `+1` (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recSign_one : (((1 : ℤˣ) : ℤ) : ℝ) = 1 := by norm_num

/-- The scalar of `-1` (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recSign_neg_one : (((-1 : ℤˣ) : ℤ) : ℝ) = -1 := by norm_num

/-- A sign scalar is nonzero (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recSign_ne_zero (ε : ℤˣ) : ((ε : ℤ) : ℝ) ≠ 0 := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num

/-! ## The reflection `ρ(j) = 2 - j` and the base involution `A` -/

/-- The time reflection `ρ(j) = 2 - j` on `T = {0,1,2}` (paper `sec:records`, "A base symmetry
    and its implementation"), realized as `Fin.rev`.-/
def _root_.Tengoku.ObserverEquivarianceLean.recρ : Fin 3 → Fin 3 := Fin.rev

/-- `ρ(j) = 2 - j` as real numbers (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recρ_cast (j : Fin 3) : (((recρ j : Fin 3) : ℕ) : ℝ) = 2 - (((j : Fin 3) : ℕ) : ℝ) := by
  fin_cases j <;> norm_num [recρ]

/-- `ρ` is an involution (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recρ_recρ (j : Fin 3) : recρ (recρ j) = j := Fin.rev_rev j

/-- The relabeled domain `ρ(I)` (paper `sec:records`: `A(I) = ρ(I)`).-/
def Tengoku.ObserverEquivarianceLean.RecDom.rev (I : RecDom) : RecDom :=
  ⟨I.dom.map Fin.revPerm.toEmbedding, I.nonempty.map⟩

/-- Membership in `ρ(I)` (paper `sec:records`): `j ∈ ρ(I) ↔ ρ(j) ∈ I`.-/
theorem Tengoku.ObserverEquivarianceLean.RecDom.mem_rev {I : RecDom} {j : Fin 3} : j ∈ I.rev.dom ↔ recρ j ∈ I.dom := by
  simp [RecDom.rev, Finset.mem_map_equiv, Fin.revPerm_symm, recρ]

/-- `ρ(ρ(I)) = I` (paper `sec:records`).-/
theorem Tengoku.ObserverEquivarianceLean.RecDom.rev_rev (I : RecDom) : I.rev.rev = I := by
  ext j
  rw [RecDom.mem_rev, RecDom.mem_rev, recρ_recρ]

/-- The functor `A : S ⥤ S`, `I ↦ ρ(I)` (paper `sec:records`).-/
def _root_.Tengoku.ObserverEquivarianceLean.recAFunctor : RecDom ⥤ RecDom where
  obj I := I.rev
  map u := RecDom.homOfSubset fun j hj =>
    RecDom.mem_rev.2 (RecDom.subset_of_hom u (RecDom.mem_rev.1 hj))

/-- `A ⋙ A = 𝟭` on the nose (paper `sec:records`: `A` is an involution).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recAFunctor_comp_self : recAFunctor ⋙ recAFunctor = 𝟭 RecDom :=
  CategoryTheory.Functor.ext (fun I => RecDom.rev_rev I) (fun _ _ _ => Subsingleton.elim _ _)

/-- The strict base automorphism `A(I) = ρ(I)` (paper `sec:records`).-/
def _root_.Tengoku.ObserverEquivarianceLean.recA : StrictAut RecDom :=
  ⟨recAFunctor, recAFunctor, recAFunctor_comp_self, recAFunctor_comp_self⟩

/-- `A(I) = ρ(I)` (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recA_hom_obj (I : RecDom) : recA.hom.obj I = I.rev := rfl

/-- `A² = 1` (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recA_mul_self : recA * recA = 1 :=
  StrictAut.ext recAFunctor_comp_self recAFunctor_comp_self

/-- `ρ({0}) = {2}` (paper `sec:records`: "the singleton domains `{0}` and `{2}` differ").-/
theorem Tengoku.ObserverEquivarianceLean.RecDom.rev_single_zero : (RecDom.single 0).rev = RecDom.single 2 := by
  ext j
  rw [RecDom.mem_rev]
  fin_cases j <;> decide

/-- `A ≠ 1`: it moves `{0}` to `{2}` (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recA_ne_one : recA ≠ 1 := by
  intro h
  have h0 := congrArg (fun B : StrictAut RecDom => B.hom.obj (RecDom.single 0)) h
  simp only [recA_hom_obj, RecDom.rev_single_zero, StrictAut.one_hom, Functor.id_obj] at h0
  have h2 : (2 : Fin 3) ∈ (RecDom.single 2).dom := Finset.mem_singleton_self _
  rw [h0] at h2
  exact absurd h2 (by decide)

/-! ## The selected subgroup `H = {1, A} ≅ C₂` -/

namespace RecordsExample

section C2

variable {A B : Type*} [Group A] [Group B]

/-- A homomorphism out of a group `{1, a}` of order at most two, sending `a` to an involution
    `b` (helper for paper `sec:records`, `H ≅ C₂`).-/
def c2Hom [DecidableEq A] (a : A) (hA : ∀ x : A, x = 1 ∨ x = a) (ha : a ≠ 1) (haa : a * a = 1)
    (b : B) (hbb : b * b = 1) : A →* B where
  toFun x := if x = 1 then 1 else b
  map_one' := ite_eq_left rfl
  map_mul' x y := by
    rcases hA x with rfl | rfl <;> rcases hA y with rfl | rfl <;> simp [ha, haa, hbb]

/-- `c2Hom` sends `1` to `1` (helper for paper `sec:records`).-/
@[simp] theorem c2Hom_one' [DecidableEq A] (a : A) (hA : ∀ x : A, x = 1 ∨ x = a) (ha : a ≠ 1)
    (haa : a * a = 1) (b : B) (hbb : b * b = 1) : c2Hom a hA ha haa b hbb 1 = 1 :=
  ite_eq_left rfl

/-- `c2Hom` sends the generator to `b` (helper for paper `sec:records`).-/
@[simp] theorem c2Hom_gen [DecidableEq A] (a : A) (hA : ∀ x : A, x = 1 ∨ x = a) (ha : a ≠ 1)
    (haa : a * a = 1) (b : B) (hbb : b * b = 1) : c2Hom a hA ha haa b hbb a = b :=
  ite_eq_right ha

/-- Groups `{1, a}`, `{1, b}` of order exactly two are isomorphic via `a ↦ b` (helper for paper
    `sec:records`: `H ≅ C₂` and `G = {±1} ≅ C₂`).-/
def c2MulEquiv [DecidableEq A] [DecidableEq B] (a : A) (hA : ∀ x : A, x = 1 ∨ x = a)
    (ha : a ≠ 1) (haa : a * a = 1) (b : B) (hB : ∀ y : B, y = 1 ∨ y = b) (hb : b ≠ 1)
    (hbb : b * b = 1) : A ≃* B :=
  { c2Hom a hA ha haa b hbb with
    invFun := c2Hom b hB hb hbb a haa
    left_inv := fun x => by
      rcases hA x with rfl | rfl
      · simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, c2Hom_one']
      · simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, c2Hom_gen]
    right_inv := fun y => by
      rcases hB y with rfl | rfl
      · simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, c2Hom_one']
      · simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, c2Hom_gen] }

/-- `c2MulEquiv` sends the generator to the generator (helper for paper `sec:records`).-/
@[simp] theorem c2MulEquiv_gen [DecidableEq A] [DecidableEq B] (a : A)
    (hA : ∀ x : A, x = 1 ∨ x = a) (ha : a ≠ 1) (haa : a * a = 1) (b : B)
    (hB : ∀ y : B, y = 1 ∨ y = b) (hb : b ≠ 1) (hbb : b * b = 1) :
    c2MulEquiv a hA ha haa b hB hb hbb a = b :=
  ite_eq_right ha

end C2

/-- The generator of `C₂ = Multiplicative (ZMod 2)` (paper `sec:records`).-/
def c2Gen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

/-- Every element of `C₂` is `1` or the generator (paper `sec:records`).-/
theorem c2_cases : ∀ k : Multiplicative (ZMod 2), k = 1 ∨ k = c2Gen := by decide

/-- The generator of `C₂` is nontrivial (paper `sec:records`).-/
theorem c2Gen_ne_one : c2Gen ≠ 1 := by decide

/-- The generator of `C₂` is an involution (paper `sec:records`).-/
theorem c2Gen_mul_self : c2Gen * c2Gen = 1 := by decide

end RecordsExample

open RecordsExample

/-- The selected base group `H = {1, A} = ⟨A⟩ ≤ Aut(S)` (paper `sec:records`).-/
def _root_.Tengoku.ObserverEquivarianceLean.recH : Subgroup (StrictAut RecDom) := Subgroup.zpowers recA

/-- The elements of `H` are exactly `1` and `A` (paper `sec:records`: `H = {1, A}`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.mem_recH {B : StrictAut RecDom} : B ∈ recH ↔ B = 1 ∨ B = recA := by
  constructor
  · intro hB
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hB
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, recA_mul_self, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, recA_mul_self, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

/-- `A` as an element of `H` (paper `sec:records`).-/
def _root_.Tengoku.ObserverEquivarianceLean.recHA : recH := ⟨recA, Subgroup.mem_zpowers _⟩

/-- Every element of `H` is `1` or `A` (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recH_cases (B : recH) : B = 1 ∨ B = recHA := by
  rcases mem_recH.1 B.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- `A ≠ 1` in `H` (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recHA_ne_one : recHA ≠ 1 := fun h => recA_ne_one (congrArg Subtype.val h)

/-- `A² = 1` in `H` (paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recHA_mul_self : recHA * recHA = 1 := Subtype.ext recA_mul_self

open Classical in
/-- `H = {1, A} ≅ C₂ = Multiplicative (ZMod 2)`, `A ↦ ofAdd 1` (paper `sec:records`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.recHMulEquiv : recH ≃* Multiplicative (ZMod 2) :=
  c2MulEquiv recHA recH_cases recHA_ne_one recHA_mul_self
    c2Gen c2_cases c2Gen_ne_one c2Gen_mul_self

/-- The sign group `G = ℤˣ = {+1, -1} ≅ C₂`, `-1 ↦ ofAdd 1` (paper `sec:records`).-/
def _root_.Tengoku.ObserverEquivarianceLean.recSignMulEquiv : ℤˣ ≃* Multiplicative (ZMod 2) :=
  c2MulEquiv (-1) (fun u => Int.units_eq_one_or u) (by decide) (by decide)
    c2Gen c2_cases c2Gen_ne_one c2Gen_mul_self

/-! ## The selected lift group `Sym_H(p) ≅ C₂ × C₂` -/

/-- The selected lift group as a direct product, `Sym_H(p) ≅ G × H` (paper `sec:records`, via
    `thm:strict` for the connected base `S`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.recSymProd : AutBoxGOver recData recH ≃* ℤˣ × recH :=
  autBoxGOverMulEquivProd recData recH

/-- The selected lift group `Sym_H(p) ≅ C₂ × C₂` (paper `sec:records`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.recSym :
    AutBoxGOver recData recH ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  recSymProd.trans (MulEquiv.prodCongr recSignMulEquiv recHMulEquiv)

/-! ## Labeled law data: `LA ≠ L` strictly -/

/-! ## Unlabeled law data: `LA ≠ L` strictly -/

/-- The index record `x_j = j` in `L(I)` (`q₀ = 0`, `v = 1/τ`, needs `τ ≠ 0`), used to show
    `L A ≠ L` for the unlabeled law (paper `sec:records`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.recIdxRecord (τ : ℝ) (hτ : τ ≠ 0) (I : RecDom) : recordSpace τ I :=
  ⟨fun j => (((j : Fin 3) : ℕ) : ℝ), 0, 1 / τ, fun j => by field_simp; ring⟩

/-! ## The covariant implementation `α : L A ≅ L` -/

/-- Time reversal of records, `(α_I x)_j = x_{ρ(j)}`, as a linear isomorphism
    `L(ρ(I)) ≃ L(I)` (paper `sec:records`, "A base symmetry and its implementation"). The
    reversed affine record `q₀ + v (2 - j) τ = (q₀ + 2 v τ) - v j τ` is again affine.-/
def _root_.Tengoku.ObserverEquivarianceLean.recRevEquiv (τ : ℝ) (I : RecDom) : recordSpace τ I.rev ≃ₗ[ℝ] recordSpace τ I where
  toFun x := ⟨fun j => (x : ↥I.rev.dom → ℝ) ⟨recρ j.1, by rw [RecDom.mem_rev, recρ_recρ]; exact j.2⟩,
    by
      obtain ⟨q₀, v, hx⟩ := x.2
      refine ⟨q₀ + 2 * v * τ, -v, fun j => ?_⟩
      simp only [hx, recρ_cast]
      ring⟩
  invFun y := ⟨fun k => (y : ↥I.dom → ℝ) ⟨recρ k.1, RecDom.mem_rev.1 k.2⟩,
    by
      obtain ⟨q₀, v, hy⟩ := y.2
      refine ⟨q₀ + 2 * v * τ, -v, fun k => ?_⟩
      simp only [hy, recρ_cast]
      ring⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Subtype.ext (funext fun k => congrArg (x : ↥I.rev.dom → ℝ)
    (Subtype.ext (recρ_recρ k.1)))
  right_inv y := Subtype.ext (funext fun j => congrArg (y : ↥I.dom → ℝ)
    (Subtype.ext (recρ_recρ j.1)))

/-- Values of the time-reversal isomorphism (paper `sec:records`): `(α_I x)_j = x_{ρ(j)}`.-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recRevEquiv_apply (τ : ℝ) (I : RecDom) (x : recordSpace τ I.rev) (j : ↥I.dom) :
    (recRevEquiv τ I x : ↥I.dom → ℝ) j
      = (x : ↥I.rev.dom → ℝ) ⟨recρ j.1, by rw [RecDom.mem_rev, recρ_recρ]; exact j.2⟩ := rfl

/-- The covariant implementation of the base symmetry: the natural linear isomorphism
    `α : L A ≅ L`, `α_I : L(ρ(I)) → L(I)`, `(α_I x)_j = x_{ρ(j)}` (paper `sec:records`).
    Naturality is "the maps `α_I` commute with restrictions".-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.recα (τ : ℝ) : recA.hom ⋙ L₀ τ ≅ L₀ τ :=
  NatIso.ofComponents (fun I => (recRevEquiv τ I).toModuleIso) (fun _ => rfl)

/-- Entries of a record at equal indices agree (helper for paper `sec:records`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.recordSpace_val_congr {τ : ℝ} {I : RecDom} (x : recordSpace τ I) {j k : Fin 3}
    (hj : j ∈ I.dom) (hk : k ∈ I.dom) (h : j = k) :
    (x : ↥I.dom → ℝ) ⟨j, hj⟩ = (x : ↥I.dom → ℝ) ⟨k, hk⟩ := by
  subst h; rfl

/-- The label isomorphism `⟨ρ(I)⟩ ≅ ⟨I⟩` in `Pair S` (paper `sec:records`, labeled spaces).-/
def _root_.Tengoku.ObserverEquivarianceLean.recLabelIso (I J : RecDom) : (⟨I⟩ : Pair RecDom) ≅ ⟨J⟩ where
  hom := ⟨⟩
  inv := ⟨⟩

/-- The covariant implementation on labeled spaces, `αℓ : L A ≅ L` in `Pair S × Vect_ℝ`,
    relabeling `ρ(I)` to `I` and acting by `α_I` on records (paper `sec:records`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.recαℓ (τ : ℝ) : recA.hom ⋙ Lℓ τ ≅ Lℓ τ :=
  NatIso.ofComponents (fun I => Iso.prod (recLabelIso I.rev I) (recRevEquiv τ I).toModuleIso)
    (fun _ => rfl)
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
