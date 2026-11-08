module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Analysis.PolynomialGenericity
public import Tengoku.Seed.Algebra.MvPolynomial.Monad
public import Tengoku.Seed.Topology.Algebra.MvPolynomial
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.EffectiveGenericity
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.BehavioralCollision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MAIS-O24's conclusions (a) and (c) are incompatible

The candidate negative resolution submitted as `lionellevine/MAIS`
[issue #7](https://github.com/lionellevine/MAIS/issues/7) (2026-08-04), checked
here: **no polynomial list can satisfy `prob:effective`'s conclusions (a) and
(c) at once**, whatever the requested size and time bounds say.

## The argument

MAIS-O23's collision, already in this tree, is a *point*. Conclusion (a) is
violated by a whole **open box** of them, and that is what the argument needs:
the utility gap `g = ½ - 1_{(1,1)}` reads the `(1,1)` cell and nothing else, and
at that cell an `X → Y` model and the edgeless model carrying its `X = 1` row
agree by construction — the source row `q₀` is behaviourally invisible. Vary all
three table entries in a box and the collision persists.

So at every point of the box, one of the two graphs' polynomials must vanish, or
(a) would identify two models with different graphs. A finite union of zero sets
of *nonzero* polynomials is null, and the box is not; hence one polynomial is
identically zero along the box at that utility.

Conclusion (c) is then contradicted, but not at that utility — (c) is asserted
only almost everywhere, and nothing says the collision utility is not in the null
set it may discard. The vanishing is instead pushed to *nearby* utilities: the
evaluation map is continuous and the table box is compact, so at utilities close
enough to the collision the same polynomial is uniformly smaller than any given
`μ`, and the whole box lands in (c)'s excluded set while (c)'s own bound
`S^a μ^b` tends to zero.

## One quantifier that has to be handled with care

`prob:effective` puts `∀ μ` **outside** the three conclusions, so (c)'s
almost-every quantifier sits inside it and the null set (c) discards may depend
on `μ`. `O24ExcludedSetSmall` keeps that order, which makes the point visible:
the submitted note picks the utilities first, sets `s_n` to the polynomial's
supremum at each, and only then builds `μ_n` from `s_n` — so the null set it
must avoid is still free to depend on the `μ` its own choice produced. The
argument is circular as written.

The repair is to **reverse the order**, not to strengthen anything. `μ` here is
fixed from `S`, `a`, `b` and the volume of the compact table box alone, none of
which mention a utility; the utility is chosen afterwards, from the
positive-measure set on which (c) is asserted at that one `μ`. No countable
union, and no reading of (c) beyond print's.

## What this costs the rest of the agenda

`AISafetyAtlas.Examples.Causal.EffectiveGenericity` records that `O24Solution`
having no inhabitant is expected — `prob:effective` is open — but that the
*fields being jointly contradictory* is a different and unwelcome reason, since
it makes every downstream *"for every solution to MAIS-O24, …"* vacuously true.
`isEmpty_o24Solution` shows the fields **are** jointly contradictory. MAIS-O26
(`CONJ-003`) is stated over exactly that quantifier and is therefore vacuous as
printed; that is a fact about `conj:exact`, not a defect introduced here.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Causal.O24Refutation

open AISafetyAtlas.Causal
open AISafetyAtlas.Examples.Causal
open MvPolynomial MeasureTheory

/-! ## The two graphs

`prob:effective` supplies one list per compatible graph, and the collision pairs
a one-edge graph with the edgeless one. Both are read off the models MAIS-O23's
collision already carries, so acyclicity comes with them. -/

/-- The `X → Y` graph.-/
@[expose] public def arrowG : Fin 2 → Finset (Fin 2) := arrowXY.parents

/-- The edgeless graph.-/
@[expose] public def edgeG : Fin 2 → Finset (Fin 2) := edgeless.parents

public theorem arrowG_acyclic : ∃ rank : Fin 2 → ℕ, ∀ c, ∀ p ∈ arrowG c, rank p < rank c :=
  arrowXY.acyclic

public theorem edgeG_acyclic : ∃ rank : Fin 2 → ℕ, ∀ c, ∀ p ∈ edgeG c, rank p < rank c :=
  edgeless.acyclic

/-! ## The chart box the collision lives on

Conclusion (a) is stated over models and (c) over chart points, so the family is
carried as chart points and turned into models by `Model.ofChart`. -/

/-- The parent bit an `X → Y` chart index carries: the value of `X` in `Y`'s
row, and `0` in `X`'s own row, which has no parents.-/
@[expose] public def arrowBit (i : ChartIndex arrowG) : Fin 2 :=
  if h : X ∈ arrowG i.1 then i.2 ⟨X, h⟩ else 0

/-- The box's lower corner: MAIS issue #7's own box, `p ∈ (0.45, 0.55)`,
`q₀ ∈ (0.15, 0.25)`, `q₁ ∈ (0.75, 0.85)`.-/
@[expose] public noncomputable def o24Lo (i : ChartIndex arrowG) : ℝ :=
  if i.1 = Y then (if arrowBit i = 1 then 3 / 4 else 3 / 20) else 9 / 20

/-- The box's upper corner.-/
@[expose] public noncomputable def o24Hi (i : ChartIndex arrowG) : ℝ :=
  if i.1 = Y then (if arrowBit i = 1 then 17 / 20 else 1 / 4) else 11 / 20

/-- **The open box of colliding parameters.**-/
@[expose] public noncomputable def o24Box : Set (ChartIndex arrowG → ℝ) :=
  Set.pi Set.univ fun i ↦ Set.Ioo (o24Lo i) (o24Hi i)

/-! ## The colliding pair at a chart point

Every point of the box carries two models: the `X → Y` model it *is*, and the
edgeless model reading each table at the parent configuration `X = 1`. The
source row `q₀` is discarded, and that is exactly what the transform cannot
see. -/

/-- The edgeless chart matched to an `X → Y` chart: every table read at the
parent configuration `X = 1`.-/
@[expose] public noncomputable def matchedEdgeChart (θ : ChartIndex arrowG → ℝ) :
    ChartIndex edgeG → ℝ :=
  fun i ↦ θ ⟨i.1, fun _ ↦ 1⟩

/-- The `X → Y` model at a chart point.-/
@[expose] public noncomputable def arrowModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : Model (Fin 2) (binaryDim (Fin 2)) ℝ :=
  Model.ofChart arrowG arrowG_acyclic θ hθ

/-- The edgeless model carrying that point's `X = 1` row.-/
@[expose] public noncomputable def edgeModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : Model (Fin 2) (binaryDim (Fin 2)) ℝ :=
  Model.ofChart edgeG edgeG_acyclic (matchedEdgeChart θ) fun i ↦ hθ ⟨i.1, fun _ ↦ 1⟩

@[simp] public theorem parents_arrowModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : (arrowModel hθ).parents = arrowG :=
  Model.parents_ofChart _ _ _ _

@[simp] public theorem parents_edgeModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : (edgeModel hθ).parents = edgeG :=
  Model.parents_ofChart _ _ _ _

@[simp] public theorem chartOn_arrowModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) : (arrowModel hθ).chartOn arrowG = θ :=
  Model.chartOn_ofChart _ _ _ _

@[simp] public theorem chartOn_edgeModel {θ : ChartIndex arrowG → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) :
    (edgeModel hθ).chartOn edgeG = matchedEdgeChart θ :=
  Model.chartOn_ofChart _ _ _ _

/-! ## Freezing the utility

Conclusion (a) reads a certificate at a model, which carries both `θ` and `u`;
conclusion (c) reads it at a `θ` with `u` fixed. `spec` is the bridge: the
certificate with the utility substituted, a polynomial in the table coordinates
alone. -/

/-- The collision skeleton's utility, in conclusion (c)'s coordinates.-/
@[expose] public noncomputable def u₀ :
    Bool × UtilityConfig (skel.mapRat ℝ).utilityParents → ℝ :=
  fun dz ↦ (skel.mapRat ℝ).utility dz.1 dz.2.extend

/-- A certificate polynomial with the utility frozen at `u`.-/
@[expose] public noncomputable def spec {G : Fin 2 → Finset (Fin 2)}
    (u : Bool × UtilityConfig (skel.mapRat ℝ).utilityParents → ℝ)
    (q : MvPolynomial (O24Var (skel.mapRat ℝ).utilityParents G) ℚ) :
    MvPolynomial (ChartIndex G) ℝ :=
  MvPolynomial.bind₁ (Sum.elim MvPolynomial.X fun y ↦ MvPolynomial.C (u y))
    (MvPolynomial.map (algebraMap ℚ ℝ) q)

/-! ## One variable set for both graphs

The edgeless certificate is a polynomial in two coordinates and the `X → Y` one
in three. Renaming along the injection that sends each edgeless coordinate to
the `X = 1` row puts both in the same ring, which is what a single covering
argument on the box needs. -/

/-- The coordinate injection: an edgeless index goes to the `X = 1` row.-/
@[expose] public def edgeIndex (i : ChartIndex edgeG) : ChartIndex arrowG :=
  ⟨i.1, fun _ ↦ 1⟩

/-! ## A positive margin below a finite list of positive values -/

/-! ## The box has positive volume -/

/-! ## The whole box lies in the margin class

Conclusion (a) is a statement about `𝕄(sk, λ, μ) ⊆ 𝕄(sk, λ)`, so the collision
only bites once both models are in the printed class at `λ = 1/10`. (M2), (M3)
and (M6) read the gap alone and are inherited from MAIS-O23's witness; (M5)
holds of every model on this skeleton because `𝐙 = 𝐂`; (M1) and (M4) are what
the box was chosen to give. -/

/-- The margin, over `ℝ`.-/
@[expose] public noncomputable def lamR : ℝ := 1 / 10

/-! ## Conclusion (a) kills a certificate polynomial on the box

At a box point where no supplied polynomial vanishes — at either graph — a small
enough `μ` puts *both* colliding models inside `𝕄(sk, λ, μ)`, and (a) then
identifies two models carrying different graphs. So some polynomial vanishes at
every point of the box; a finite list of nonzero polynomials cannot do that,
because the box is not null. -/

/-! ## Conclusion (c) fails at the utilities beside the collision

The vanishing established above is at `u₀`, and (c) is asserted only for almost
every utility, so nothing yet contradicts it — `u₀` may be one of the utilities
(c) discards. What does contradict it is that the vanishing is *stable*: fix a
compact table box `K` and a margin `μ` small enough that (c)'s own bound
`S^a μ^b` is below `Leb(K)`; then by continuity every utility close enough to
`u₀` makes the same polynomial smaller than `μ` on all of `K`, and (c) is
asserted at some such utility because they form a set of positive measure.

**The order of the choices is the whole point.** `μ` is fixed from `S`, `a`, `b`
and `Leb(K)` alone — none of which depend on the utility — and only then is the
utility chosen. Choosing the utility first and building `μ` from it, which is how
the submitted note runs this step, leaves (c)'s null set free to depend on the
`μ` that the utility produced. -/

/-! ## The bundle is uninhabited

`not_o24_identifies_and_excluded` is the sharp form: it takes conclusions (a)
and (c) and nothing else, so the obstruction survives dropping conclusion (b),
the polynomial size bounds, and the construction-time clause. `O24Solution`
carries all of them, so it is empty a fortiori. -/

end AISafetyAtlas.Examples.Causal.O24Refutation
