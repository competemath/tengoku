/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Cslib.Cslib.Computability.Circuit.Composition
public import Tengoku.Cslib.Cslib.Computability.Circuit.Synthesis
public import Tengoku.Seed.Data.ENat.Lattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Circuit complexity

The complexity of a function `f` on a support `S`, written `C^S(f)`, is the least number of gates
in a circuit whose outputs agree with `f` on every input in `S`. The function may have several
values, one for each output of the circuit, and nothing is asked of the circuit outside `S`, so
`C^S(f)` depends only on the restriction of `f` to `S`. The complexity `C(f)` of `f` is its
complexity on all inputs, and the complexity of `f` relative to a function `g`, in
`Cslib.Computability.Circuit.RelativeComplexity`, is a complexity on the graph of `g`.

Over an arbitrary signature and interpretation some functions have no circuit at all. We represent
`C^S(f)` by `ecomplexityOn I S f` and `C(f)` by `ecomplexity I f`, taking values in `ℕ∞` with
`⊤` when no circuit exists. The prefix `e` stands for "extended". Over a complete basis, one over
which every function has a circuit, `complexityOn I S f` and `complexity I f` give the corresponding
natural-number values.

Support complexity obeys a small calculus from which the rules for complexity and relative
complexity follow. It grows with the support and ignores the function outside the support.
Wiring, which only selects, permutes, or duplicates inputs, costs nothing. The composite `g ∘ f`
costs at most the complexity of `f` on `S` plus that of `g` on the image of `S`, and computing two
functions side by side costs at most the sum of their complexities.

See [Jukna, Chapter 1][Jukna2012] for the Boolean case.

## References

* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

universe v u
variable {σ : Signature.{v}} {U : Type u} {n m p : ℕ}

/-- Following [Jukna, Section 1.1][Jukna2012], a basis is complete when every single-valued
function, on every number of inputs, is computed by some circuit over it. Circuits here have no
constant inputs, so this includes the constants, which is why NAND alone is not complete in this
sense. Functions with several values then have circuits too, built by running circuits for their
values side by side.-/
class Interpretation.IsComplete (I : Interpretation σ U) : Prop where
  /-- Every single-valued function has a circuit.-/
  exists_computes_single :
    ∀ {n : ℕ} (f : (Fin n → U) → U), ∃ c : Circuit σ n 1, c.Computes I (single f)

/-- Over a complete basis every function, with any number of values, has a circuit.
@isnad1 id=ex.0h6v.s5.f31021ab297f from=translated src=- shape=76345556 vocab=60447a2a
-/
theorem Interpretation.IsComplete.exists_computes {I : Interpretation σ U} [I.IsComplete] :
    ∀ {n m : ℕ} (f : (Fin n → U) → Fin m → U), ∃ c : Circuit σ n m, c.Computes I f
  | _, 0, _ => ⟨Circuit.wiring σ Fin.elim0, fun _ => funext fun i => i.elim0⟩
  | _, m + 1, f => by
    obtain ⟨c, hc⟩ := exists_computes (I := I) fun x => f x ∘ Fin.castSucc
    obtain ⟨d, hd⟩ := exists_computes_single (I := I) fun x => f x (Fin.last m)
    refine ⟨c.append d, fun x => ?_⟩
    rw [Circuit.eval_append, hc x, hd x, Fin.append_right_eq_snoc]
    exact Fin.snoc_init_self (f x)

/-- The complexity `C^S(f)` of `f` on the support `S`: the least size of a circuit computing `f`
on `S` under `I`, or `⊤` if there is none.-/
noncomputable def ecomplexityOn (I : Interpretation σ U) (S : Set (Fin n → U))
    (f : (Fin n → U) → Fin m → U) : ℕ∞ :=
  ⨅ c : {c : Circuit σ n m // c.ComputesOn I S f}, (c.1.size : ℕ∞)

/-- The complexity `C(f)` of `f`: its complexity on all inputs.-/
noncomputable def ecomplexity (I : Interpretation σ U) (f : (Fin n → U) → Fin m → U) : ℕ∞ :=
  ecomplexityOn I Set.univ f

variable {I : Interpretation σ U} {S T : Set (Fin n → U)} {f f' : (Fin n → U) → Fin m → U}
  {k : ℕ}

/-! ### Complexity on a support -/

/--
@isnad1 id=le.1h8v.s5.03fc4fa908f7 from=translated src=- shape=be6f197b vocab=8811b647
-/
theorem ecomplexityOn_le_of_computesOn (c : Circuit σ n m) (hc : c.ComputesOn I S f) :
    ecomplexityOn I S f ≤ c.size :=
  iInf_le (fun c : {c // c.ComputesOn I S f} => (c.1.size : ℕ∞)) ⟨c, hc⟩

/--
@isnad1 id=iff.0h7v.s5.7b8af1697570 from=translated src=- shape=600e67dc vocab=61f35088
-/
theorem ecomplexityOn_ne_top_iff :
    ecomplexityOn I S f ≠ ⊤ ↔ ∃ c : Circuit σ n m, c.ComputesOn I S f := by
  rw [ecomplexityOn, ENat.iInf_natCast_ne_top, nonempty_subtype]

/-- When some circuit computes `f` on `S`, the least size is attained by some
(potentially different) circuit.
@isnad1 id=ex.1h7v.s6.8a9b51905e26 from=translated src=- shape=1d11e20a vocab=5ee952ae
-/
theorem exists_computesOn_size_eq_ecomplexityOn (h : ∃ c : Circuit σ n m, c.ComputesOn I S f) :
    ∃ c : Circuit σ n m, c.ComputesOn I S f ∧ (c.size : ℕ∞) = ecomplexityOn I S f := by
  have : Nonempty {c : Circuit σ n m // c.ComputesOn I S f} := nonempty_subtype.mpr h
  obtain ⟨⟨c, hc⟩, hmin⟩ := ENat.exists_eq_iInf
    (fun c : {c : Circuit σ n m // c.ComputesOn I S f} => (c.1.size : ℕ∞))
  exact ⟨c, hc, hmin⟩

/--
@isnad1 id=iff.0h8v.s6.116874b37ee9 from=translated src=- shape=dc4a86fa vocab=8811b647
-/
theorem ecomplexityOn_le_iff :
    ecomplexityOn I S f ≤ k ↔ ∃ c : Circuit σ n m, c.ComputesOn I S f ∧ c.size ≤ k := by
  constructor
  · intro h
    have hne : ecomplexityOn I S f ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
    obtain ⟨c, hc, hsize⟩ :=
      exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hne)
    exact ⟨c, hc, by exact_mod_cast hsize.trans_le h⟩
  · rintro ⟨c, hc, hk⟩
    exact (ecomplexityOn_le_of_computesOn c hc).trans (by exact_mod_cast hk)

/-- Lower bounds on support complexity are exactly lower bounds on the size of every circuit
computing the function on the support, including when no such circuit exists.
@isnad1 id=iff.0h8v.s6.5ab462c0177c from=translated src=- shape=6a82851d vocab=8811b647
-/
theorem le_ecomplexityOn_iff {k : ℕ∞} :
    k ≤ ecomplexityOn I S f ↔
      ∀ c : Circuit σ n m, c.ComputesOn I S f → k ≤ c.size := by
  simp only [ecomplexityOn, le_iInf_iff, Subtype.forall]

/-- A larger support is harder to compute on.
@isnad1 id=le.1h8v.s6.aaac2761d794 from=translated src=- shape=e24d3576 vocab=7d72ebbb
-/
theorem ecomplexityOn_mono (h : S ⊆ T) : ecomplexityOn I S f ≤ ecomplexityOn I T f :=
  le_iInf fun c => iInf_le_of_le ⟨c.1, c.2.mono h⟩ le_rfl

/-- Complexity on a support depends only on the values of the function on the support.
@isnad1 id=eq.1h8v.s6.ec687de9cdec from=translated src=- shape=684635d3 vocab=40731aa9
-/
theorem ecomplexityOn_congr (h : Set.EqOn f f' S) : ecomplexityOn I S f = ecomplexityOn I S f' :=
  le_antisymm (le_iInf fun c => iInf_le_of_le ⟨c.1, c.2.trans h.symm⟩ le_rfl)
    (le_iInf fun c => iInf_le_of_le ⟨c.1, c.2.trans h⟩ le_rfl)

/--
@isnad1 id=le.0h7v.s5.15b3829e1e86 from=translated src=- shape=578d7aec vocab=7d37999c
-/
theorem ecomplexityOn_le_ecomplexity : ecomplexityOn I S f ≤ ecomplexity I f :=
  ecomplexityOn_mono (Set.subset_univ S)

/-- Selecting, permuting, or duplicating inputs costs nothing.
@isnad1 id=eq.0h7v.s5.3930fa879c55 from=translated src=- shape=023cc536 vocab=a32052f6
-/
@[simp] theorem ecomplexityOn_wiring (select : Fin m → Fin n) :
    ecomplexityOn I S (fun x => x ∘ select) = 0 :=
  nonpos_iff_eq_zero.mp <| (ecomplexityOn_le_of_computesOn _
    ((Circuit.wiring_computes select I).computesOn S)).trans (by simp)

/-- The composition rule: computing `g ∘ f` on `S` costs at most computing `f` on `S` and then
`g` on the values `f` takes there.
@isnad1 id=le.0h9v.s6.26c4fc38bac9 from=translated src=- shape=ce9b02d3 vocab=c18b4fd0
-/
theorem ecomplexityOn_comp_le (f : (Fin n → U) → Fin m → U) (g : (Fin m → U) → Fin p → U) :
    ecomplexityOn I S (g ∘ f) ≤ ecomplexityOn I S f + ecomplexityOn I (f '' S) g := by
  by_cases hF : ecomplexityOn I S f = ⊤
  · simp [hF]
  by_cases hH : ecomplexityOn I (f '' S) g = ⊤
  · simp [hH]
  obtain ⟨c, hc, hcs⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hF)
  obtain ⟨d, hd, hds⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hH)
  refine (ecomplexityOn_le_of_computesOn _ (hc.comp hd)).trans_eq ?_
  rw [← hcs, ← hds, Circuit.size_comp, Nat.cast_add]

/-- The pairing rule: computing `f` and `g` side by side on `S` costs at most the sum of their
complexities on `S`.
@isnad1 id=le.0h9v.s6.f913dc47a879 from=translated src=- shape=991110b5 vocab=f0f025f5
-/
theorem ecomplexityOn_append_le (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin p → U) :
    ecomplexityOn I S (fun x => Fin.append (f x) (g x)) ≤
      ecomplexityOn I S f + ecomplexityOn I S g := by
  by_cases hF : ecomplexityOn I S f = ⊤
  · simp [hF]
  by_cases hG : ecomplexityOn I S g = ⊤
  · simp [hG]
  obtain ⟨c, hc, hcs⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hF)
  obtain ⟨d, hd, hds⟩ := exists_computesOn_size_eq_ecomplexityOn (ecomplexityOn_ne_top_iff.mp hG)
  refine (ecomplexityOn_le_of_computesOn _ (hc.append hd)).trans_eq ?_
  rw [← hcs, ← hds, Circuit.size_append, Nat.cast_add]

/-- Reading the inputs through a wiring costs nothing beyond computing `f` on the rewired
support.
@isnad1 id=le.0h9v.s6.c86e5e6c9b0f from=translated src=- shape=cce99ea0 vocab=47239d17
-/
theorem ecomplexityOn_comp_wiring_le {S : Set (Fin p → U)} (select : Fin n → Fin p)
    (f : (Fin n → U) → Fin m → U) :
    ecomplexityOn I S (fun x => f (x ∘ select)) ≤ ecomplexityOn I ((· ∘ select) '' S) f := by
  have h := ecomplexityOn_comp_le (I := I) (S := S) (fun x => x ∘ select) f
  rw [ecomplexityOn_wiring, zero_add] at h
  exact h

/-- Selecting, permuting, or duplicating the values of `f` costs nothing.
@isnad1 id=le.0h9v.s6.29d882fe3ea8 from=translated src=- shape=416cc93e vocab=c90d598b
-/
theorem ecomplexityOn_wiring_comp_le (select : Fin p → Fin m) (f : (Fin n → U) → Fin m → U) :
    ecomplexityOn I S (fun x => f x ∘ select) ≤ ecomplexityOn I S f := by
  have h := ecomplexityOn_comp_le (I := I) (S := S) f (fun y => y ∘ select)
  rw [ecomplexityOn_wiring, add_zero] at h
  exact h

/-- Computing `f` alongside `g` on `S` is at least as hard as computing `f` on `S`.
@isnad1 id=le.0h9v.s6.575748c384e1 from=translated src=- shape=ed4ec50b vocab=f0f025f5
-/
theorem ecomplexityOn_le_ecomplexityOn_append_left (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin p → U) :
    ecomplexityOn I S f ≤ ecomplexityOn I S (fun x => Fin.append (f x) (g x)) := by
  simpa only [Fin.append_comp_castAdd] using
    ecomplexityOn_wiring_comp_le (I := I) (S := S) (Fin.castAdd p)
      (fun x => Fin.append (f x) (g x))

/-- Computing `g` alongside `f` on `S` is at least as hard as computing `g` on `S`.
@isnad1 id=le.0h9v.s6.a2ac1e2aeeaa from=translated src=- shape=256937e9 vocab=f0f025f5
-/
theorem ecomplexityOn_le_ecomplexityOn_append_right (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin p → U) :
    ecomplexityOn I S g ≤ ecomplexityOn I S (fun x => Fin.append (f x) (g x)) := by
  simpa only [Fin.append_comp_natAdd] using
    ecomplexityOn_wiring_comp_le (I := I) (S := S) (Fin.natAdd m)
      (fun x => Fin.append (f x) (g x))

/-! ### Complexity on all inputs -/

/--
@isnad1 id=le.1h7v.s5.c4d17ad520d5 from=translated src=- shape=b5e6d447 vocab=7b8a0092
-/
theorem ecomplexity_le_of_computes (c : Circuit σ n m) (hc : c.Computes I f) :
    ecomplexity I f ≤ c.size :=
  ecomplexityOn_le_of_computesOn c (hc.computesOn _)

/--
@isnad1 id=iff.0h6v.s5.e5a818f6f04e from=translated src=- shape=d6509775 vocab=69a3f5b6
-/
theorem ecomplexity_ne_top_iff : ecomplexity I f ≠ ⊤ ↔ ∃ c : Circuit σ n m, c.Computes I f := by
  simp [ecomplexity, ecomplexityOn_ne_top_iff]

/-- When some circuit computes `f`, the least size is attained by some (potentially different)
circuit.
@isnad1 id=ex.1h6v.s6.4ab55dfd70a2 from=translated src=- shape=357da4ac vocab=d8d048f1
-/
theorem exists_computes_size_eq_ecomplexity (h : ∃ c : Circuit σ n m, c.Computes I f) :
    ∃ c : Circuit σ n m, c.Computes I f ∧ (c.size : ℕ∞) = ecomplexity I f := by
  have hOn : ∃ c : Circuit σ n m, c.ComputesOn I Set.univ f := by
    simpa using h
  simpa [ecomplexity] using exists_computesOn_size_eq_ecomplexityOn hOn

/--
@isnad1 id=iff.0h7v.s6.9cc4fb9c0aa3 from=translated src=- shape=1d154047 vocab=7b8a0092
-/
theorem ecomplexity_le_iff :
    ecomplexity I f ≤ k ↔ ∃ c : Circuit σ n m, c.Computes I f ∧ c.size ≤ k := by
  simp [ecomplexity, ecomplexityOn_le_iff]

/-- Lower bounds on complexity are exactly lower bounds on the size of every circuit computing
the function, including when no such circuit exists.
@isnad1 id=iff.0h7v.s5.b236234683bf from=translated src=- shape=b97f2931 vocab=7b8a0092
-/
theorem le_ecomplexity_iff {k : ℕ∞} :
    k ≤ ecomplexity I f ↔ ∀ c : Circuit σ n m, c.Computes I f → k ≤ c.size := by
  simp [ecomplexity, le_ecomplexityOn_iff]

/-- Selecting, permuting, or duplicating inputs costs nothing.
@isnad1 id=eq.0h6v.s5.999e6e27e188 from=translated src=- shape=8ed27126 vocab=0a27ca8a
-/
@[simp] theorem ecomplexity_wiring (select : Fin m → Fin n) :
    ecomplexity I (fun x => x ∘ select) = 0 :=
  ecomplexityOn_wiring select

/--
@isnad1 id=le.0h8v.s6.0766a4975ede from=translated src=- shape=d14a8e47 vocab=15bd9a92
-/
theorem ecomplexity_comp_le (f : (Fin n → U) → Fin m → U) (g : (Fin m → U) → Fin p → U) :
    ecomplexity I (g ∘ f) ≤ ecomplexity I f + ecomplexity I g :=
  (ecomplexityOn_comp_le f g).trans (add_le_add le_rfl ecomplexityOn_le_ecomplexity)

/--
@isnad1 id=le.0h8v.s6.133d96df3760 from=translated src=- shape=85bd188a vocab=80338b21
-/
theorem ecomplexity_append_le (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin p → U) :
    ecomplexity I (fun x => Fin.append (f x) (g x)) ≤ ecomplexity I f + ecomplexity I g :=
  ecomplexityOn_append_le f g

/-- Computing `f` alongside `g` is at least as hard as computing `f`.
@isnad1 id=le.0h8v.s6.985a991a4e60 from=translated src=- shape=daba8491 vocab=80338b21
-/
theorem ecomplexity_le_ecomplexity_append_left (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin p → U) :
    ecomplexity I f ≤ ecomplexity I (fun x => Fin.append (f x) (g x)) :=
  ecomplexityOn_le_ecomplexityOn_append_left f g

/-- Computing `g` alongside `f` is at least as hard as computing `g`.
@isnad1 id=le.0h8v.s6.10f551ea8443 from=translated src=- shape=531057b5 vocab=80338b21
-/
theorem ecomplexity_le_ecomplexity_append_right (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin p → U) :
    ecomplexity I g ≤ ecomplexity I (fun x => Fin.append (f x) (g x)) :=
  ecomplexityOn_le_ecomplexityOn_append_right f g

/-- A synthesis bound on the input projections bounds the extended complexity.
@isnad1 id=le.1h6v.s6.967417cb4ecb from=translated src=- shape=8de56785 vocab=03985ae1
-/
theorem Synthesis.ecomplexity_le {f : (Fin n → U) → U} {cost : ℕ}
    (h : Synthesis I (inputs n) {f} cost) : ecomplexity I (single f) ≤ cost :=
  ecomplexity_le_iff.mpr h.exists_circuit

/-! ### Over a complete basis -/

section Complete

/--
@isnad1 id=ne.0h7v.s5.05c268a614a8 from=translated src=- shape=cbb145ed vocab=7b05b1e3
-/
theorem ecomplexityOn_ne_top [I.IsComplete] : ecomplexityOn I S f ≠ ⊤ :=
  ecomplexityOn_ne_top_iff.mpr <|
    (Interpretation.IsComplete.exists_computes f).imp fun _ hc => hc.computesOn S

/--
@isnad1 id=ne.0h6v.s5.1132093255eb from=translated src=- shape=fa4d2de6 vocab=43f47e17
-/
theorem ecomplexity_ne_top [I.IsComplete] : ecomplexity I f ≠ ⊤ :=
  ecomplexityOn_ne_top

/-- The complexity `C^S(f)` of `f` on the support `S` over a complete basis, as a natural
number.-/
noncomputable def complexityOn (I : Interpretation σ U) [I.IsComplete] (S : Set (Fin n → U))
    (f : (Fin n → U) → Fin m → U) : ℕ :=
  (ecomplexityOn I S f).untop ecomplexityOn_ne_top

/-- The complexity `C(f)` of `f` over a complete basis, as a natural number.-/
noncomputable def complexity (I : Interpretation σ U) [I.IsComplete]
    (f : (Fin n → U) → Fin m → U) : ℕ :=
  complexityOn I Set.univ f

variable [I.IsComplete]

/--
@isnad1 id=eq.0h7v.s5.3ece5ddf7960 from=translated src=- shape=c4927f1e vocab=377bb48b
-/
@[simp] theorem natCast_complexityOn : (complexityOn I S f : ℕ∞) = ecomplexityOn I S f :=
  WithTop.coe_untop _ _

/--
@isnad1 id=eq.0h6v.s5.a11113c9eba5 from=translated src=- shape=51b2c958 vocab=b9d9bd91
-/
@[simp] theorem natCast_complexity : (complexity I f : ℕ∞) = ecomplexity I f :=
  natCast_complexityOn

/-- A circuit computing `f` on `S` bounds its support complexity.
@isnad1 id=le.1h8v.s6.cd313f2a7819 from=translated src=- shape=99b2eb74 vocab=2dcb5cdf
-/
theorem complexityOn_le_of_computesOn (c : Circuit σ n m) (hc : c.ComputesOn I S f) :
    complexityOn I S f ≤ c.size := by
  have := ecomplexityOn_le_of_computesOn c hc
  rw [← natCast_complexityOn] at this
  exact_mod_cast this

/-- Over a complete basis the least size on a support is attained.
@isnad1 id=ex.0h7v.s6.ca206a8e688c from=translated src=- shape=67bc47a1 vocab=b20c2dc0
-/
theorem exists_computesOn_size_eq_complexityOn :
    ∃ c : Circuit σ n m, c.ComputesOn I S f ∧ c.size = complexityOn I S f := by
  obtain ⟨c, hc, hsize⟩ := exists_computesOn_size_eq_ecomplexityOn
    (ecomplexityOn_ne_top_iff.mp (ecomplexityOn_ne_top (I := I)))
  exact ⟨c, hc, by exact_mod_cast hsize.trans (natCast_complexityOn (I := I)).symm⟩

/-- Support complexity is at most `k` exactly when some circuit of size at most `k` computes
the function on the support.
@isnad1 id=iff.0h8v.s6.6d9f45607797 from=translated src=- shape=acd88048 vocab=2dcb5cdf
-/
theorem complexityOn_le_iff :
    complexityOn I S f ≤ k ↔ ∃ c : Circuit σ n m, c.ComputesOn I S f ∧ c.size ≤ k := by
  rw [← ecomplexityOn_le_iff, ← natCast_complexityOn (I := I) (S := S) (f := f)]
  exact_mod_cast Iff.rfl

/-- Over a complete basis, lower bounds on support complexity are exactly lower bounds on the
size of every circuit computing the function on the support.
@isnad1 id=iff.0h8v.s6.3672824ccf43 from=translated src=- shape=566dbd68 vocab=2dcb5cdf
-/
theorem le_complexityOn_iff :
    k ≤ complexityOn I S f ↔ ∀ c : Circuit σ n m, c.ComputesOn I S f → k ≤ c.size := by
  have h := le_ecomplexityOn_iff (I := I) (S := S) (f := f) (k := k)
  rw [← natCast_complexityOn] at h
  exact_mod_cast h

/--
@isnad1 id=le.1h7v.s5.52a289e497fe from=translated src=- shape=bb397a24 vocab=551b6bf8
-/
theorem complexity_le_of_computes (c : Circuit σ n m) (hc : c.Computes I f) :
    complexity I f ≤ c.size :=
  complexityOn_le_of_computesOn c (hc.computesOn _)

/-- A lower bound on the complexity is a lower bound on the size of every circuit.
@isnad1 id=le.2h8v.s6.84284e5e2f44 from=translated src=- shape=caaf68a7 vocab=551b6bf8
-/
theorem le_size_of_le_complexity (h : k ≤ complexity I f) {c : Circuit σ n m}
    (hc : c.Computes I f) : k ≤ c.size :=
  h.trans (complexity_le_of_computes c hc)

/-- Over a complete basis the least size is attained.
@isnad1 id=ex.0h6v.s5.c3861e5eac5c from=translated src=- shape=291b0cca vocab=0daf8333
-/
theorem exists_computes_size_eq_complexity :
    ∃ c : Circuit σ n m, c.Computes I f ∧ c.size = complexity I f := by
  simpa [complexity] using
    exists_computesOn_size_eq_complexityOn (I := I) (S := Set.univ) (f := f)

/--
@isnad1 id=iff.0h7v.s6.f141ad180138 from=translated src=- shape=db168e12 vocab=551b6bf8
-/
theorem complexity_le_iff :
    complexity I f ≤ k ↔ ∃ c : Circuit σ n m, c.Computes I f ∧ c.size ≤ k := by
  simpa [complexity] using complexityOn_le_iff (I := I) (S := Set.univ) (f := f) (k := k)

/-- Over a complete basis, lower bounds on complexity are exactly lower bounds on the size
of every circuit.
@isnad1 id=iff.0h7v.s6.07c21cf262fd from=translated src=- shape=6dade4e6 vocab=551b6bf8
-/
theorem le_complexity_iff :
    k ≤ complexity I f ↔ ∀ c : Circuit σ n m, c.Computes I f → k ≤ c.size := by
  simpa [complexity] using le_complexityOn_iff (I := I) (S := Set.univ) (f := f) (k := k)

/--
@isnad1 id=le.1h8v.s6.ee38556f3992 from=translated src=- shape=4af0a5a4 vocab=ea6a9e11
-/
theorem complexityOn_mono (h : S ⊆ T) : complexityOn I S f ≤ complexityOn I T f := by
  have := ecomplexityOn_mono (I := I) (f := f) h
  rw [← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

/-- Complexity on a support depends only on the values of the function on the support.
@isnad1 id=eq.1h8v.s6.120adcc77b34 from=translated src=- shape=206f7ae4 vocab=d5797d59
-/
theorem complexityOn_congr (h : Set.EqOn f f' S) : complexityOn I S f = complexityOn I S f' := by
  have := ecomplexityOn_congr (I := I) h
  rw [← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

/-- Restricting the inputs to a support cannot increase complexity.
@isnad1 id=le.0h7v.s5.61a6c3b2f626 from=translated src=- shape=29663051 vocab=e8526c96
-/
theorem complexityOn_le_complexity : complexityOn I S f ≤ complexity I f :=
  complexityOn_mono (Set.subset_univ S)

/-- Selecting, permuting, or duplicating inputs costs nothing.
@isnad1 id=eq.0h7v.s5.580fec285d97 from=translated src=- shape=da6d32f3 vocab=011cb3a5
-/
@[simp] theorem complexityOn_wiring (select : Fin m → Fin n) :
    complexityOn I S (fun x => x ∘ select) = 0 := by
  have := ecomplexityOn_wiring (I := I) (S := S) select
  rw [← natCast_complexityOn] at this
  exact_mod_cast this

/--
@isnad1 id=le.0h9v.s6.94543084ef4d from=translated src=- shape=21a8bc7e vocab=03280894
-/
theorem complexityOn_comp_le (f : (Fin n → U) → Fin m → U) (g : (Fin m → U) → Fin p → U) :
    complexityOn I S (g ∘ f) ≤ complexityOn I S f + complexityOn I (f '' S) g := by
  have := ecomplexityOn_comp_le (I := I) (S := S) f g
  rw [← natCast_complexityOn, ← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

/--
@isnad1 id=le.0h9v.s6.35aa6d80e7cf from=translated src=- shape=ab06f7ef vocab=6724f316
-/
theorem complexityOn_append_le (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin p → U) :
    complexityOn I S (fun x => Fin.append (f x) (g x)) ≤
      complexityOn I S f + complexityOn I S g := by
  have := ecomplexityOn_append_le (I := I) (S := S) f g
  rw [← natCast_complexityOn, ← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

/-- Computing `f` alongside `g` on `S` is at least as hard as computing `f` on `S`.
@isnad1 id=le.0h9v.s6.b3ca823df918 from=translated src=- shape=ba387d15 vocab=6724f316
-/
theorem complexityOn_le_complexityOn_append_left (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin p → U) :
    complexityOn I S f ≤ complexityOn I S (fun x => Fin.append (f x) (g x)) := by
  have := ecomplexityOn_le_ecomplexityOn_append_left (I := I) (S := S) f g
  rw [← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

/-- Computing `g` alongside `f` on `S` is at least as hard as computing `g` on `S`.
@isnad1 id=le.0h9v.s6.08289c290a3a from=translated src=- shape=8746211d vocab=6724f316
-/
theorem complexityOn_le_complexityOn_append_right (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin p → U) :
    complexityOn I S g ≤ complexityOn I S (fun x => Fin.append (f x) (g x)) := by
  have := ecomplexityOn_le_ecomplexityOn_append_right (I := I) (S := S) f g
  rw [← natCast_complexityOn, ← natCast_complexityOn] at this
  exact_mod_cast this

/-- Selecting, permuting, or duplicating inputs costs nothing.
@isnad1 id=eq.0h6v.s5.cab970cfb682 from=translated src=- shape=72e47233 vocab=2251230b
-/
@[simp] theorem complexity_wiring (select : Fin m → Fin n) :
    complexity I (fun x => x ∘ select) = 0 :=
  complexityOn_wiring select

/-- Computing a composite costs at most the sum of the complexities of its two functions.
@isnad1 id=le.0h8v.s6.5c72143dc242 from=translated src=- shape=c21e224e vocab=8af409e5
-/
theorem complexity_comp_le (f : (Fin n → U) → Fin m → U) (g : (Fin m → U) → Fin p → U) :
    complexity I (g ∘ f) ≤ complexity I f + complexity I g :=
  (complexityOn_comp_le f g).trans (add_le_add le_rfl complexityOn_le_complexity)

/-- Computing two functions side by side costs at most the sum of their complexities.
@isnad1 id=le.0h8v.s6.8ce2bd95027a from=translated src=- shape=bbcad8b7 vocab=a9c59e2e
-/
theorem complexity_append_le (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin p → U) :
    complexity I (fun x => Fin.append (f x) (g x)) ≤ complexity I f + complexity I g :=
  complexityOn_append_le f g

/-- Computing `f` alongside `g` is at least as hard as computing `f`.
@isnad1 id=le.0h8v.s6.a766a3e87a56 from=translated src=- shape=3c77913c vocab=a9c59e2e
-/
theorem complexity_le_complexity_append_left (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin p → U) :
    complexity I f ≤ complexity I (fun x => Fin.append (f x) (g x)) :=
  complexityOn_le_complexityOn_append_left f g

/-- Computing `g` alongside `f` is at least as hard as computing `g`.
@isnad1 id=le.0h8v.s6.25efd1c3d047 from=translated src=- shape=b77c8581 vocab=a9c59e2e
-/
theorem complexity_le_complexity_append_right (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin p → U) :
    complexity I g ≤ complexity I (fun x => Fin.append (f x) (g x)) :=
  complexityOn_le_complexityOn_append_right f g

/-- A synthesis bound on the input projections bounds the complexity.
@isnad1 id=le.1h6v.s6.9f55f3485d8d from=translated src=- shape=039d32b1 vocab=47ceacb8
-/
theorem Synthesis.complexity_le {f : (Fin n → U) → U} {cost : ℕ}
    (h : Synthesis I (inputs n) {f} cost) : complexity I (single f) ≤ cost :=
  complexity_le_iff.mpr h.exists_circuit

end Complete

end Cslib.Circuits
