import Tengoku.Seed.NumberTheory.Padics.MahlerBasis
import Tengoku.Seed.Topology.ContinuousMap.Compact
import Tengoku.Seed.Topology.LocallyConstant.Algebra
import Tengoku.Seed.Topology.MetricSpace.Ultra.ContinuousMaps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# p-adic measures on a compact space

Following Rodrigues Jacinto–Williams, *An introduction to p-adic L-functions*
(arXiv:2309.15692) §3.2, we define the space of `ℤ_[p]`-valued p-adic measures on a
topological space `X` as the space of `ℤ_[p]`-linear functionals on `C(X, ℤ_[p])`.

The source (Def. 3.6, `def:measures`) defines `L`-valued measures as the *continuous*
dual of `C(G, L)` and singles out the `𝒪_L`-valued ones; over `ℤ_[p]`, continuity of an
`ℤ_[p]`-linear functional is automatic (`PadicMeasure.norm_apply_le`,
`PadicMeasure.continuous`), so no continuity hypothesis is needed in the definition.
This file is the `𝒪 = ℤ_[p]` case; the general coefficient case is deferred to the §5
development pass (see `.mathlib-quality/plan.md`, Generality Decisions).

## Main definitions

* `PadicMeasure p X`: `ℤ_[p]`-valued measures on `X`.
* `PadicMeasure.dirac`: the Dirac measure at a point (source Ex. 3.7, `ex:dirac`).
* `PadicMeasure.pushforward`: pushforward along a continuous map; specialises to the
  `σ_a`, `φ` operators and the embedding `Λ(ℤ_p^×) ↪ Λ(ℤ_p)` later.

## Main results

* `PadicMeasure.norm_apply_le` / `PadicMeasure.continuous`: automatic boundedness and
  continuity (source: footnote to Def. 3.6 — boundedness ⟺ continuity).
* `PadicMeasure.exists_locallyConstant_norm_sub_le`: density of locally constant
  functions (source: Rem. 3.8, `rem:locally constant`, lines 782–802).
* `PadicMeasure.ext_locallyConstant`: a measure is determined by its values on locally
  constant functions (source: Eq. (3.1), `eq:restrict measures`).
-/
namespace Tengoku.PadicLFunctions end Tengoku.PadicLFunctions open Tengoku.PadicLFunctions
open scoped fwdDiff

variable (p : ℕ) [hp : Fact p.Prime]

instance (n : ℕ) : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩

noncomputable section

/-- The space of `ℤ_[p]`-valued *p-adic measures* on a topological space `X`: `ℤ_[p]`-linear
functionals on the continuous functions `C(X, ℤ_[p])`. Over `ℤ_[p]` every linear functional
is automatically bounded (norm ≤ 1) and continuous, so this agrees with the continuous
dual used in the source.

Source: RJW Def. 3.6 (`def:measures`, TeX line 760) together with the `𝒪_L`-valued
convention of line 765.-/
abbrev _root_.Tengoku.PadicLFunctions.PadicMeasure (X : Type*) [TopologicalSpace X] :=
  C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]

namespace Tengoku.PadicLFunctions.PadicMeasure

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section basic

/-- The *Dirac measure* at `x : X`: the functional `φ ↦ φ x`.

Source: RJW Ex. 3.7 (`ex:dirac`, TeX lines 774–779).-/
def dirac (x : X) : PadicMeasure p X where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h4v.s8.fbe3a991bd98 from=translated src=- shape=71f16456 vocab=79966173
-/
@[simp]
lemma dirac_apply (x : X) (f : C(X, ℤ_[p])) : dirac p x f = f x := rfl

/-- Precomposition with a continuous map `m : C(X, Y)`, as a linear map
`C(Y, ℤ_[p]) →ₗ[ℤ_[p]] C(X, ℤ_[p])`. Auxiliary for `PadicMeasure.pushforward`.-/
def compRight (m : C(X, Y)) : C(Y, ℤ_[p]) →ₗ[ℤ_[p]] C(X, ℤ_[p]) where
  toFun f := f.comp m
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/--
@isnad1 id=eq.0h5v.s9.45abac3dca2e from=translated src=- shape=164b122d vocab=95b99e8a
-/
@[simp]
lemma compRight_apply (m : C(X, Y)) (f : C(Y, ℤ_[p])) : compRight p m f = f.comp m := rfl

/-- The *pushforward* of a measure along a continuous map `m : C(X, Y)`:
`(pushforward m μ) f = ∫ f ∘ m dμ`. Specialises to `σ_a` and `φ` (RJW §3.5.4) and to
the embedding `Λ(ℤ_p^×) → Λ(ℤ_p)` (RJW Rem. 3.33).-/
def pushforward (m : C(X, Y)) : PadicMeasure p X →ₗ[ℤ_[p]] PadicMeasure p Y where
  toFun μ := μ.comp (compRight p m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h6v.s11.364a296d24df from=translated src=- shape=253b5aa3 vocab=32f073e0
-/
@[simp]
lemma pushforward_apply (m : C(X, Y)) (μ : PadicMeasure p X) (f : C(Y, ℤ_[p])) :
    pushforward p m μ f = μ (f.comp m) := rfl

/--
@isnad1 id=eq.0h5v.s11.5671287fa098 from=translated src=- shape=7be94f94 vocab=5fec0eb3
-/
@[simp]
lemma pushforward_dirac (m : C(X, Y)) (x : X) :
    pushforward p m (dirac p x) = dirac p (m x) := rfl

end basic

section compact

variable [CompactSpace X]

/-- Residue discs mod `p^k` are open in `ℤ_p`: the reduction `toZModPow k` is locally
constant. Workhorse for density and for the `ψ`-operator's digit shift.
@isnad1 id=isopen.0h3v.s8.ac3f215f0a80 from=translated src=- shape=83d15901 vocab=1fa96f47
-/
lemma isOpen_toZModPow_fiber (k : ℕ) (a : ZMod (p ^ k)) :
    IsOpen {z : ℤ_[p] | PadicInt.toZModPow k z = a} := by
  rw [Metric.isOpen_iff]
  intro z hz
  refine ⟨(p : ℝ) ^ (-k : ℤ), zpow_pos (by exact_mod_cast hp.out.pos) _, fun y hy => ?_⟩
  have hmem : PadicInt.toZModPow k (y - z) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow _ k).1
      (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hy))
  rw [map_sub, sub_eq_zero] at hmem
  simpa only [Set.mem_ofPred_eq, hmem] using hz

/-- The canonical-digit lift `x ↦ [x mod p^k] : ℤ_p → ℤ_p` is locally constant
(hence continuous).
@isnad1 id=islocall.0h2v.s8.af49fa6c1c53 from=translated src=- shape=1c312cbe vocab=c6d4b8aa
-/
lemma isLocallyConstant_toZModPow_val (k : ℕ) :
    IsLocallyConstant fun x : ℤ_[p] => (((PadicInt.toZModPow k x).val : ℕ) : ℤ_[p]) :=
  (IsLocallyConstant.comp (fun s => by
      rw [← Set.biUnion_preimage_singleton]
      exact isOpen_biUnion fun a _ => isOpen_toZModPow_fiber p k a)
    fun a : ZMod (p ^ k) => ((a.val : ℕ) : ℤ_[p]))

/-- **Density of locally constant functions**: any continuous `f : X → ℤ_[p]` on a
compact space is uniformly approximated by locally constant functions. The preimages of
the (clopen) balls of radius `ε` form a clopen cover; pass to a finite subcover,
disjointify, and pick values.

Source: RJW Rem. 3.8 (`rem:locally constant`, TeX lines 782–791): "any continuous
function `φ ∈ 𝒞(G, 𝒪_L)` can be p-adically approximated by its locally constant
truncations". Not in mathlib (verified absent); PR candidate.
@isnad1 id=ex.1h4v.s8.6e497f4fd9a4 from=translated src=- shape=3115dfba vocab=ccc07a23
-/
theorem exists_locallyConstant_norm_sub_le (f : C(X, ℤ_[p])) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : LocallyConstant X ℤ_[p], ‖f - (g : C(X, ℤ_[p]))‖ ≤ ε := by
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  have hopen := isOpen_toZModPow_fiber p k
  -- the mod-`p^k` reduction of `f` is locally constant
  set q : X → ZMod (p ^ k) := fun x => PadicInt.toZModPow k (f x) with hq
  have hlc : IsLocallyConstant q := fun s => by
    rw [← Set.biUnion_preimage_singleton]
    exact isOpen_biUnion fun a _ => (hopen a).preimage (map_continuous f)
  -- lift back via the canonical representatives
  refine ⟨⟨fun x => ((q x).val : ℤ_[p]), hlc.comp fun a => ((a.val : ℕ) : ℤ_[p])⟩,
    ((f - _).norm_le hε.le).2 fun x => ?_⟩
  have hgx : PadicInt.toZModPow k (((q x).val : ℤ_[p])) = q x := by
    rw [map_natCast]
    exact ZMod.natCast_rightInverse (q x)
  have hle : ‖f x - ((q x).val : ℤ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
      map_sub, hgx, sub_self]
  calc ‖(f - _) x‖ = ‖f x - ((q x).val : ℤ_[p])‖ := by
        simp [ContinuousMap.sub_apply]
    _ ≤ (p : ℝ) ^ (-k : ℤ) := hle
    _ ≤ ε := hk.le

end compact

end Tengoku.PadicLFunctions.PadicMeasure
-- Tengoku: root names of this library moved to Tengoku.PadicLFunctions so they do not collide with other libraries (generated)
