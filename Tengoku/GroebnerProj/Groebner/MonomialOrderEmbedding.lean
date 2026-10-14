module

public import Tengoku
public import Tengoku.GroebnerProj.Groebner.ToMathlib.MulEquiv
public import Tengoku.GroebnerProj.Groebner.ToMathlib.Finsupp
public import Tengoku.GroebnerProj.Groebner.ToMathlib.WithBot
public import Tengoku.GroebnerProj.Groebner.MonomialOrder

@[expose] public section
attribute [local simp] and_imp_iff_and imp_and_iff_and


def RelHom.onFun {α : Type*} {β : Type*} (r : β → β → Prop) (f : α → β) :
    RelHom (Function.onFun r f) r where
  toFun := f
  map_rel' := by simp

/--
@isnad1 id=eq.0h4v.s5.9736738f541d from=translated src=- shape=b876d816 vocab=e6e4b7a3
-/
@[simp] lemma RelHom.coe_onFun {α : Type*} {β : Type*} {r : β → β → Prop} (f : α → β) :
    RelHom.onFun r f = f := rfl

instance _root_.IsWellFounded.onFun {α : Type*} {β : Type*} (r : β → β → Prop) (f : α → β)
    [wfl : IsWellFounded β r] :
    IsWellFounded α (Function.onFun r f) := RelHomClass.isWellFounded (RelHom.onFun r f)

namespace MonomialOrder

open MvPolynomial

variable {σ' : Type*} (m' : MonomialOrder σ') {σ : Type*} (m : MonomialOrder σ) (f : σ' → σ)

set_option linter.unusedVariables false in
def ofInjective.Syn (m : MonomialOrder σ) {σ' : Type*} (f : σ' → σ) := σ' →₀ ℕ

noncomputable local instance ofInjective.acm' : AddCommMonoid (Syn m f) :=
  inferInstanceAs <| AddCommMonoid <| σ' →₀ ℕ

noncomputable def ofInjective.toSyn' (m : MonomialOrder σ) {σ' : Type*} (f : σ' → σ) :
    (σ' →₀ ℕ) ≃+ (Syn m f) :=
  AddEquiv.refl (σ' →₀ ℕ)

-- submitted: https://github.com/leanprover-community/mathlib4/pull/32829
/--
@isnad1 id=isordere.0h1v.s5.dbe6bd58c711 from=translated src=- shape=affebb5f vocab=d1d254a9
-/
@[to_additive toIsOrderedCancelAddMonoid']
lemma toIsOrderedCancelMonoid' {α}
    [CancelCommMonoid α] [LinearOrder α] [IsOrderedMonoid α] : IsOrderedCancelMonoid α where
  le_of_mul_le_mul_left _ _ _ h := le_of_mul_le_mul_left' h

open ofInjective in
noncomputable def ofInjective {σ' : Type*} {f : σ' → σ} (hf : f.Injective) :
    MonomialOrder σ' :=
  letI hom := m.toSyn.toAddMonoidHom.comp <| Finsupp.mapDomain.addMonoidHom f
  letI map := m.toSyn ∘ Finsupp.mapDomain f
  haveI map_injective : Function.Injective map := by
    simp [m.toSyn.injective, Finsupp.mapDomain_injective hf, map]
  letI lo : LinearOrder (Syn m f) := LinearOrder.lift' map map_injective
  { syn := Syn m f
    toSyn : (σ' →₀ ℕ) ≃+ (Syn m f) := toSyn' m f
    toSyn_monotone := by
      intro a b h
      apply m.toSyn_monotone
      exact Finsupp.mapDomain_mono h
    isOrderedAddMonoid_syn :=
      {
        add_le_add_left a b hab c := by
          convert_to! map _ ≤ map _ at hab
          convert_to! map (HAdd.hAdd (α := σ' →₀ ℕ) _ _) ≤ map (HAdd.hAdd (α := σ' →₀ ℕ) _ _)
          set_option backward.isDefEq.respectTransparency false in
          simpa [map, Function.comp_def, Finsupp.mapDomain_add, AddEquiv.map_add] using hab

      }
    wellFoundedLT_syn := -- show WellFoundedLT (Syn m f) from
      by set_option backward.isDefEq.respectTransparency false in
        -- why it doesn't work without `show` or `by exact`?
        exact inferInstanceAs <| IsWellFounded (Syn m f) fun x1 x2 ↦ map x1 < map x2
  }

/-- An embedding from a monomial order `m' : MonomialOrder σ'` and `m : MonomialOrder σ` consists:

1. a injective mapping from index `σ'` of `m'` to `σ` of `m`.
2. this mapping "preserves" the order. -/
structure Embedding extends σ' ↪ σ where
  monotone' : Monotone (m.toSyn ∘ Finsupp.mapDomain toFun ∘ m'.toSyn.symm)

namespace Embedding

variable {m' m} (e : Embedding m' m) {R} [CommSemiring R]
variable (p q : MvPolynomial σ' R)

instance instFunLike : FunLike (Embedding m' m) σ' σ where
  coe m := m.toFun
  coe_injective a b h := by
    convert_to (Embedding.mk _ _) = ⟨_, _⟩
    simpa using h

/--
@isnad1 id=eq.1h6v.s6.5d3e18486fa4 from=translated src=- shape=688c951b vocab=6eb3ea1a
-/
@[ext] lemma ext {e₁ e₂ : Embedding m' m} (h : ⇑e₁ = ⇑e₂) : e₁ = e₂ :=
  (instFunLike ..).coe_injective h

/--
@isnad1 id=eq.0h5v.s5.4c57bd82813b from=translated src=- shape=feceea7e vocab=0ad2c7a1
-/
@[simp] lemma coe_toEmbedding_eq_coe : ⇑e.toEmbedding = ⇑e := rfl

/--
@isnad1 id=eq.0h5v.s5.fc31b68be806 from=translated src=- shape=fcbdc512 vocab=7aff311a
-/
@[simp] lemma toFun_eq_coe : e.toFun = ⇑e := rfl

/--
@isnad1 id=monotone.0h5v.s8.1fd295813147 from=translated src=- shape=7f539fd1 vocab=3a87b4ac
-/
lemma monotone : Monotone (m.toSyn ∘ Finsupp.mapDomain e ∘ m'.toSyn.symm) := e.monotone'

/--
@isnad1 id=injectiv.0h5v.s5.0c1327f04c45 from=translated src=- shape=0b5c4c3a vocab=98ffdaa6
-/
@[simp]
lemma coe_injective : Function.Injective e := e.toEmbedding.inj'

/--
@isnad1 id=strictmo.0h5v.s8.6d095a8925b4 from=translated src=- shape=7f539fd1 vocab=0bb6d5ff
-/
lemma toStrictMono : StrictMono (m.toSyn ∘ Finsupp.mapDomain e ∘ m'.toSyn.symm) :=
  e.monotone'.strictMono_of_injective <| by
    simpa using Finsupp.mapDomain_injective <| e.coe_injective

noncomputable def toOrderEmbedding : OrderEmbedding m'.syn m.syn := .ofStrictMono _ e.toStrictMono

/--
@isnad1 id=iff.0h7v.s9.86658b9feee1 from=translated src=- shape=dba7c96a vocab=d648dab0
-/
@[simp]
lemma le_iff_le (a b : m'.syn) :
    Finsupp.mapDomain e (m'.toSyn.symm a) ≼[m] Finsupp.mapDomain e (m'.toSyn.symm b) ↔ a ≤ b :=
  e.toOrderEmbedding.le_iff_le

/--
@isnad1 id=iff.0h7v.s9.3f1a84990d38 from=translated src=- shape=b7f31dee vocab=d5e5950e
-/
@[simp]
lemma le_iff_le' (a b : σ' →₀ ℕ) :
    Finsupp.mapDomain e a ≼[m] Finsupp.mapDomain e b ↔ a ≼[m'] b := by
  nth_rw 1 [← m'.toSyn.symm_apply_apply a, ← m'.toSyn.symm_apply_apply b]
  exact e.le_iff_le ..

/--
@isnad1 id=iff.0h7v.s9.052dadbfb5c6 from=translated src=- shape=dba7c96a vocab=69d3490f
-/
@[simp]
lemma lt_iff_lt (a b : m'.syn) :
    Finsupp.mapDomain e (m'.toSyn.symm a) ≺[m] Finsupp.mapDomain e (m'.toSyn.symm b) ↔ a < b :=
  e.toOrderEmbedding.lt_iff_lt

/--
@isnad1 id=iff.0h7v.s9.b3c81dba0bd3 from=translated src=- shape=b7f31dee vocab=bb304054
-/
@[simp]
lemma lt_iff_lt' (a b : σ' →₀ ℕ) :
    Finsupp.mapDomain e a ≺[m] Finsupp.mapDomain e b ↔ a ≺[m'] b := by
  nth_rw 1 [← m'.toSyn.symm_apply_apply a, ← m'.toSyn.symm_apply_apply b]
  exact e.lt_iff_lt ..

variable (m) in
/-- Given a monomial order `m : MonomialOrder σ` and a injective function `f : σ' → σ`, there exists
an embedding `ofInjective`, from an `m' : MonomialOrder σ'` to `m : MonomialOrder σ` with mapping
`f`. -/
def ofInjective {f : σ' → σ} (hf : f.Injective) : Embedding (m.ofInjective hf) m where
  toEmbedding := ⟨f, hf⟩
  monotone' := by
    intro a b h
    let map := m.toSyn ∘ Finsupp.mapDomain f
    convert_to! map _ ≤ map _ at ⊢ h
    simpa [MonomialOrder.ofInjective, ofInjective.toSyn', map] using h

/-- Renaming with an monomial ordering embedding preserves `degree`.
@isnad1 id=eq.0h7v.s8.1c133eff5e57 from=translated src=- shape=42039eae vocab=21a5c2d5
-/
lemma degree_rename : m.degree (p.rename e) = (m'.degree p).mapDomain e := by
  classical
  simp? [degree, support_rename_of_injective e.coe_injective] says
    simp only [degree, support_rename_of_injective e.coe_injective, Finset.sup_image]
  convert_to
    m.toSyn.symm ((p.support.map m'.toSyn.toEmbedding).sup
      (m.toSyn ∘ Finsupp.mapDomain ⇑e ∘ m'.toSyn.symm)) = _
  · simp [Function.comp_def]
  · simp [← Finset.apply_sup_eq_sup_comp_of_linearOrder _ e.monotone (by simp)]

/--
@isnad1 id=iff.0h8v.s8.1a1362cb7fb2 from=translated src=- shape=1111cb7a vocab=ba7cc77b
-/
@[simp]
lemma degree_eq_degree (p q : MvPolynomial σ' R) :
    m.degree (p.rename e) = m.degree (q.rename e) ↔ m'.degree p = m'.degree q := by
  classical
  simp [e.degree_rename,
    Finsupp.mapDomain_injective e.coe_injective |>.eq_iff]

/--
@isnad1 id=iff.0h8v.s9.14bbd41c762d from=translated src=- shape=1b7d3a68 vocab=2b9efb95
-/
@[simp]
lemma degree_le_degree (p q : MvPolynomial σ' R) :
    m.degree (p.rename e) ≼[m] m.degree (q.rename e) ↔ m'.degree p ≼[m'] m'.degree q := by
  simp [e.degree_rename]

/--
@isnad1 id=iff.0h8v.s8.b2d6dcfd5398 from=translated src=- shape=1111cb7a vocab=b1f9ef34
-/
@[simp]
lemma degree_le_degree' (p q : MvPolynomial σ' R) :
    m.degree (p.rename e) ≤ m.degree (q.rename e) ↔ m'.degree p ≤ m'.degree q := by
  simp [e.degree_rename, Finsupp.mapDomain_le_mapDomain_iff_le e.coe_injective]

/--
@isnad1 id=iff.0h8v.s9.2d759298dac4 from=translated src=- shape=1b7d3a68 vocab=ead4d153
-/
@[simp]
lemma degree_lt_degree (p q : MvPolynomial σ' R) :
    m.degree (p.rename e) ≺[m] m.degree (q.rename e) ↔ m'.degree p ≺[m'] m'.degree q := by
  simp [e.degree_rename]

/-- Renaming with an monomial ordering embedding preserves `degree`.
@isnad1 id=eq.0h7v.s8.9bd2569c536f from=translated src=- shape=5e39d747 vocab=b3b32e3a
-/
lemma withBotDegree_rename :
    m.withBotDegree (p.rename e) = (m'.withBotDegree p).map (·.mapDomain e) := by
  wlog! hp : p ≠ 0
  · simp [hp]
  rw [m.withBotDegree_eq_coe_degree_iff .. |>.mpr, m'.withBotDegree_eq_coe_degree_iff .. |>.mpr hp]
  · simp [e.degree_rename]
  · simp [rename_eq_zero_iff_of_injective _ (R := R) e.coe_injective, hp]

/--
@isnad1 id=eq.0h7v.s9.cfa4041508f3 from=translated src=- shape=cfd08263 vocab=56d90c46
-/
lemma toWithBotSyn_withBotDegree_rename :
    m.toWithBotSyn (m.withBotDegree (p.rename e)) =
      (m'.toWithBotSyn (m'.withBotDegree p)).map
        (m.toSyn ∘ Finsupp.mapDomain e ∘ m'.toSyn.symm) := by
  wlog! hp : p ≠ 0
  · simp [hp]
  rw [m.withBotDegree_eq_coe_degree_iff .. |>.mpr, m'.withBotDegree_eq_coe_degree_iff .. |>.mpr hp]
  · simp [e.degree_rename]
  · simp [rename_eq_zero_iff_of_injective _ (R := R) e.coe_injective, hp]

/--
@isnad1 id=iff.0h8v.s10.f3b610888016 from=translated src=- shape=227e33eb vocab=420aee51
-/
@[simp]
lemma withBotDegree_le_withBotDegree_iff (p q : MvPolynomial σ' R) :
    m.withBotDegree (p.rename e) ≼'[m] m.withBotDegree (q.rename e) ↔
      m'.withBotDegree p ≼'[m'] m'.withBotDegree q := by
  simp [e.toWithBotSyn_withBotDegree_rename]
  rw [WithBot.map_le_iff _]
  exact e.le_iff_le _ _

/--
@isnad1 id=iff.0h9v.s10.03d8744719a2 from=translated src=- shape=9c193ca6 vocab=ecca0cdd
-/
lemma withBotDegree_add_withBotDegree_le_withBotDegree_iff (r p q : MvPolynomial σ' R) :
    m.withBotDegree (r.rename e) +
      m.withBotDegree (p.rename e) ≼'[m] m.withBotDegree (q.rename e) ↔
      m'.withBotDegree r + m'.withBotDegree p ≼'[m'] m'.withBotDegree q := by
  simp only [map_add, e.toWithBotSyn_withBotDegree_rename]
  rw [← WithBot.map_add', WithBot.map_le_iff _]
  · exact e.le_iff_le _ _
  · simp [Finsupp.mapDomain_add]

/--
@isnad1 id=iff.0h9v.s10.a3f88357196f from=translated src=- shape=c1b5576b vocab=ecca0cdd
-/
@[simp]
lemma withBotDegree_add_withBotDegree_le_withBotDegree_iff' (r p q : MvPolynomial σ' R) :
    m.toWithBotSyn (m.withBotDegree (r.rename e)) + m.toWithBotSyn (m.withBotDegree (p.rename e)) ≤
      m.toWithBotSyn (m.withBotDegree (q.rename e)) ↔
    m'.toWithBotSyn (m'.withBotDegree r) + m'.toWithBotSyn (m'.withBotDegree p) ≤
      m'.toWithBotSyn (m'.withBotDegree q) := by
  simpa using e.withBotDegree_add_withBotDegree_le_withBotDegree_iff r p q

/--
@isnad1 id=iff.0h8v.s10.e042e19b028b from=translated src=- shape=227e33eb vocab=a2eda73b
-/
@[simp]
lemma withBotDegree_lt_withBotDegree_iff (p q : MvPolynomial σ' R) :
    m.withBotDegree (p.rename e) ≺'[m] m.withBotDegree (q.rename e) ↔
      m'.withBotDegree p ≺'[m'] m'.withBotDegree q := by
  simp [e.toWithBotSyn_withBotDegree_rename]
  rw [WithBot.map_lt_iff _]
  exact e.lt_iff_lt _ _

/--
@isnad1 id=eq.0h7v.s7.fb7cec6d8be3 from=translated src=- shape=c3ba4190 vocab=93a6d8dc
-/
@[simp]
lemma leadingCoeff_rename : m.leadingCoeff (p.rename e) = m'.leadingCoeff p := by
  simp [leadingCoeff, degree_rename]

/--
@isnad1 id=eq.0h7v.s7.7b48897a9f0b from=translated src=- shape=709646d8 vocab=fb4a89e0
-/
@[simp]
lemma monic_rename : m.Monic (p.rename e) = m'.Monic p := by
  simp [Monic]

/--
@isnad1 id=eq.0h7v.s8.8f0646c32749 from=translated src=- shape=e2667144 vocab=1fa86f44
-/
lemma leadingTerm_rename : m.leadingTerm (p.rename e) = (m'.leadingTerm p).rename e := by
  simp [leadingTerm, degree_rename, rename_monomial]

/--
@isnad1 id=eq.0h8v.s9.ede40d5d4210 from=translated src=- shape=584a18cd vocab=2e57ee3d
-/
lemma sPolynomial_rename {R} [CommRing R] (p q : MvPolynomial σ' R) :
    m.sPolynomial (p.rename e) (q.rename e) = (m'.sPolynomial p q).rename e := by
  simp [sPolynomial, degree_rename, leadingCoeff_rename, rename_monomial,
    Finsupp.mapDomain_tsub e.coe_injective]

end Embedding

end MonomialOrder
-- Tengoku: 1 registration(s) of this module made local so they do not change other libraries (generated)
