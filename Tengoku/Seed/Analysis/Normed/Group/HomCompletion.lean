/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Group.Hom
public import Tengoku.Seed.Analysis.Normed.Group.Completion

/-!
# Completion of normed group homs

Given two (semi) normed groups `G` and `H` and a normed group hom `f : NormedAddGroupHom G H`,
we build and study a normed group hom
`f.completion : NormedAddGroupHom (completion G) (completion H)` such that the diagram

```
                   f
     G       ----------->     H

     |                        |
     |                        |
     |                        |
     V                        V

completion G -----------> completion H
            f.completion
```

commutes. The map itself comes from the general theory of completion of uniform spaces, but here
we want a normed group hom, study its operator norm and kernel.

The vertical maps in the above diagrams are also normed group homs constructed in this file.

## Main definitions and results:

* `NormedAddGroupHom.completion`: see the discussion above.
* `NormedAddCommGroup.toCompl : NormedAddGroupHom G (completion G)`: the canonical map from
  `G` to its completion, as a normed group hom
* `NormedAddGroupHom.completion_toCompl`: the above diagram indeed commutes.
* `NormedAddGroupHom.norm_completion`: `‖f.completion‖ = ‖f‖`
* `NormedAddGroupHom.ker_le_ker_completion`: the kernel of `f.completion` contains the image of
  the kernel of `f`.
* `NormedAddGroupHom.ker_completion`: the kernel of `f.completion` is the closure of the image of
  the kernel of `f` under an assumption that `f` is quantitatively surjective onto its image.
* `NormedAddGroupHom.extension` : if `H` is complete, the extension of
  `f : NormedAddGroupHom G H` to a `NormedAddGroupHom (completion G) H`.
-/

@[expose] public section


noncomputable section

open Set NormedAddGroupHom UniformSpace

section Completion

variable {G : Type*} [SeminormedAddCommGroup G] {H : Type*} [SeminormedAddCommGroup H]
  {K : Type*} [SeminormedAddCommGroup K]

/-- The normed group hom induced between completions. -/
def NormedAddGroupHom.completion (f : NormedAddGroupHom G H) :
    NormedAddGroupHom (Completion G) (Completion H) :=
  .ofLipschitz (f.toAddMonoidHom.completion f.continuous) f.lipschitz.completion_map

/--
@isnad1 id=eq.0h4v.s7.a8588a309b3f from=seed src=0 shape=e2fecbf4 vocab=6c07a401
-/
theorem NormedAddGroupHom.completion_def (f : NormedAddGroupHom G H) (x : Completion G) :
    f.completion x = Completion.map f x :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.858468d3cf24 from=seed src=0 shape=2d5ac4d7 vocab=6c07a401
-/
@[simp]
theorem NormedAddGroupHom.completion_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.completion : Completion G → Completion H) = Completion.map f := rfl

/--
@isnad1 id=eq.0h4v.s7.78e546f0ce1c from=seed src=0 shape=02edadf6 vocab=5c267e13
-/
theorem NormedAddGroupHom.completion_coe (f : NormedAddGroupHom G H) (g : G) :
    f.completion g = f g :=
  Completion.map_coe f.uniformContinuous _

/--
@isnad1 id=eq.0h4v.s6.488d59222b43 from=seed src=0 shape=63719b30 vocab=1626c6c7
-/
@[simp]
theorem NormedAddGroupHom.completion_coe' (f : NormedAddGroupHom G H) (g : G) :
    Completion.map f g = f g :=
  f.completion_coe g

/-- Completion of normed group homs as a normed group hom. -/
@[simps]
def normedAddGroupHomCompletionHom :
    NormedAddGroupHom G H →+ NormedAddGroupHom (Completion G) (Completion H) where
  toFun := NormedAddGroupHom.completion
  map_zero' := toAddMonoidHom_injective AddMonoidHom.completion_zero
  map_add' f g := toAddMonoidHom_injective <|
    f.toAddMonoidHom.completion_add g.toAddMonoidHom f.continuous g.continuous

/--
@isnad1 id=eq.0h1v.s6.de82e861ecf1 from=seed src=0 shape=a9843297 vocab=fa3df476
-/
@[simp]
theorem NormedAddGroupHom.completion_id :
    (NormedAddGroupHom.id G).completion = NormedAddGroupHom.id (Completion G) := by
  ext x
  rw [NormedAddGroupHom.completion_def, NormedAddGroupHom.coe_id, Completion.map_id]
  rfl

/--
@isnad1 id=eq.0h5v.s7.37fe437fc7b2 from=seed src=0 shape=2ce16a60 vocab=aa462235
-/
theorem NormedAddGroupHom.completion_comp (f : NormedAddGroupHom G H) (g : NormedAddGroupHom H K) :
    g.completion.comp f.completion = (g.comp f).completion := by
  ext x
  rw [NormedAddGroupHom.coe_comp, NormedAddGroupHom.completion_def,
    NormedAddGroupHom.completion_coe_to_fun, NormedAddGroupHom.completion_coe_to_fun,
    Completion.map_comp g.uniformContinuous f.uniformContinuous]
  rfl

/--
@isnad1 id=eq.0h3v.s7.53038724ad13 from=seed src=0 shape=4eaa263a vocab=f8526cae
-/
theorem NormedAddGroupHom.completion_neg (f : NormedAddGroupHom G H) :
    (-f).completion = -f.completion :=
  map_neg (normedAddGroupHomCompletionHom : NormedAddGroupHom G H →+ _) f

/--
@isnad1 id=eq.0h4v.s8.3f8927d8dfac from=seed src=0 shape=4e8c402f vocab=79f16c5d
-/
theorem NormedAddGroupHom.completion_add (f g : NormedAddGroupHom G H) :
    (f + g).completion = f.completion + g.completion :=
  normedAddGroupHomCompletionHom.map_add f g

/--
@isnad1 id=eq.0h4v.s8.f659f3f1e0fa from=seed src=0 shape=4e8c402f vocab=69a5c8c6
-/
theorem NormedAddGroupHom.completion_sub (f g : NormedAddGroupHom G H) :
    (f - g).completion = f.completion - g.completion :=
  map_sub (normedAddGroupHomCompletionHom : NormedAddGroupHom G H →+ _) f g

/--
@isnad1 id=eq.0h2v.s7.d92cc2b95802 from=seed src=0 shape=b50532d6 vocab=2fc92d42
-/
@[simp]
theorem NormedAddGroupHom.zero_completion : (0 : NormedAddGroupHom G H).completion = 0 :=
  normedAddGroupHomCompletionHom.map_zero

/-- The map from a normed group to its completion, as a normed group hom. -/
@[simps]
def NormedAddCommGroup.toCompl : NormedAddGroupHom G (Completion G) where
  toFun := (↑)
  map_add' := Completion.toCompl.map_add
  bound' := ⟨1, by simp⟩

open NormedAddCommGroup

/--
@isnad1 id=eq.0h2v.s6.9fe5d8ffa287 from=seed src=0 shape=1921f2dd vocab=d178b330
-/
theorem NormedAddCommGroup.norm_toCompl (x : G) : ‖toCompl x‖ = ‖x‖ :=
  Completion.norm_coe x

/--
@isnad1 id=denseran.0h1v.s6.517abff3b3ab from=seed src=0 shape=94491be1 vocab=662ce186
-/
theorem NormedAddCommGroup.denseRange_toCompl : DenseRange (toCompl : G → Completion G) :=
  Completion.isDenseInducing_coe.dense

/--
@isnad1 id=eq.0h3v.s6.269aadd3bcce from=seed src=0 shape=b9372095 vocab=ba8a77de
-/
@[simp]
theorem NormedAddGroupHom.completion_toCompl (f : NormedAddGroupHom G H) :
    f.completion.comp toCompl = toCompl.comp f := by ext x; simp

/--
@isnad1 id=eq.0h3v.s6.3bafbd4752b3 from=seed src=0 shape=841ad90f vocab=5b47dc7d
-/
@[simp]
theorem NormedAddGroupHom.norm_completion (f : NormedAddGroupHom G H) : ‖f.completion‖ = ‖f‖ :=
  le_antisymm (ofLipschitz_norm_le _ _) <| opNorm_le_bound _ (norm_nonneg _) fun x => by
    simpa using f.completion.le_opNorm x

/--
@isnad1 id=le.0h3v.s8.cdb13e2c40e9 from=seed src=0 shape=ec6bb5dc vocab=70a729db
-/
theorem NormedAddGroupHom.ker_le_ker_completion (f : NormedAddGroupHom G H) :
    (toCompl.comp <| incl f.ker).range ≤ f.completion.ker := by
  rintro _ ⟨⟨g, h₀ : f g = 0⟩, rfl⟩
  simp [h₀, mem_ker, Completion.coe_zero]

/--
@isnad1 id=eq.1h4v.s8.3410c57a5572 from=seed src=0 shape=a48c995a vocab=195c22c9
-/
theorem NormedAddGroupHom.ker_completion {f : NormedAddGroupHom G H} {C : ℝ}
    (h : f.SurjectiveOnWith f.range C) :
    (f.completion.ker : Set <| Completion G) = closure (toCompl.comp <| incl f.ker).range := by
  refine le_antisymm ?_ (closure_minimal f.ker_le_ker_completion f.completion.isClosed_ker)
  rintro hatg (hatg_in : f.completion hatg = 0)
  rw [SeminormedAddCommGroup.mem_closure_iff]
  intro ε ε_pos
  rcases h.exists_pos with ⟨C', C'_pos, hC'⟩
  rcases exists_pos_mul_lt ε_pos (1 + C' * ‖f‖) with ⟨δ, δ_pos, hδ⟩
  obtain ⟨_, ⟨g : G, rfl⟩, hg : ‖hatg - g‖ < δ⟩ :=
    SeminormedAddCommGroup.mem_closure_iff.mp (Completion.isDenseInducing_coe.dense hatg) δ δ_pos
  obtain ⟨g' : G, hgg' : f g' = f g, hfg : ‖g'‖ ≤ C' * ‖f g‖⟩ := hC' (f g) (mem_range_self _ g)
  have mem_ker : g - g' ∈ f.ker := by rw [f.mem_ker, map_sub, sub_eq_zero.mpr hgg'.symm]
  refine ⟨_, ⟨⟨g - g', mem_ker⟩, rfl⟩, ?_⟩
  have : ‖f g‖ ≤ ‖f‖ * δ := calc
    ‖f g‖ ≤ ‖f‖ * ‖hatg - g‖ := by
      simpa [map_sub, hatg_in] using f.completion.le_opNorm (hatg - g)
    _ ≤ ‖f‖ * δ := by gcongr
  calc ‖hatg - ↑(g - g')‖ = ‖hatg - g + g'‖ := by rw [Completion.coe_sub, sub_add]
    _ ≤ ‖hatg - g‖ + ‖(g' : Completion G)‖ := norm_add_le _ _
    _ = ‖hatg - g‖ + ‖g'‖ := by rw [Completion.norm_coe]
    _ < δ + C' * ‖f g‖ := add_lt_add_of_lt_of_le hg hfg
    _ ≤ δ + C' * (‖f‖ * δ) := by gcongr
    _ < ε := by simpa only [add_mul, one_mul, mul_assoc] using hδ

end Completion

section Extension

variable {G : Type*} [SeminormedAddCommGroup G]
variable {H : Type*} [SeminormedAddCommGroup H] [T0Space H] [CompleteSpace H]

/-- If `H` is complete, the extension of `f : NormedAddGroupHom G H` to a
`NormedAddGroupHom (completion G) H`. -/
def NormedAddGroupHom.extension (f : NormedAddGroupHom G H) : NormedAddGroupHom (Completion G) H :=
  .ofLipschitz (f.toAddMonoidHom.extension f.continuous) <|
    let _ := MetricSpace.ofT0PseudoMetricSpace H
    f.lipschitz.completion_extension

/--
@isnad1 id=eq.0h4v.s7.23ac80f684ec from=seed src=0 shape=c5944a0e vocab=4e9a047e
-/
theorem NormedAddGroupHom.extension_def (f : NormedAddGroupHom G H) (v : G) :
    f.extension v = Completion.extension f v :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.173ce2071e73 from=seed src=0 shape=4d54d6aa vocab=e70c6772
-/
@[simp]
theorem NormedAddGroupHom.extension_coe (f : NormedAddGroupHom G H) (v : G) : f.extension v = f v :=
  AddMonoidHom.extension_coe _ f.continuous _

/--
@isnad1 id=eq.0h3v.s7.f7cc7a418a6c from=seed src=0 shape=641d57b8 vocab=3903acd1
-/
theorem NormedAddGroupHom.extension_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.extension : Completion G → H) = Completion.extension f :=
  rfl

/--
@isnad1 id=eq.1h4v.s7.0688176a2623 from=seed src=0 shape=0cc637fb vocab=e70c6772
-/
theorem NormedAddGroupHom.extension_unique (f : NormedAddGroupHom G H)
    {g : NormedAddGroupHom (Completion G) H} (hg : ∀ v, f v = g v) : f.extension = g := by
  ext v
  rw [NormedAddGroupHom.extension_coe_to_fun,
    Completion.extension_unique f.uniformContinuous g.uniformContinuous fun a => hg a]

end Extension
