/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.Seed.ModelTheory.Complexity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Model companions and existentially closed models

This file implements the first four parts of Definition 2.2 of the paper. Model completeness
uses the paper's definition: every formula is equivalent over the theory to an existential
formula. `AllEmbeddingsElementary` records the semantic formulation separately. The implication
from the paper's definition to that formulation is proved here; the converse requires further
compactness machinery and is not asserted in this file.

Companions are encoded by embeddings of bundled nonempty models, as in mathlib's canonical
semantic universe. Replacing an embedding by an isomorphic inclusion gives the inclusions in the
paper. Existential formulas use mathlib's finite existential prefixes over quantifier-free
formulas. The theory's Pi-two condition and the finite-diagram assertions of Definition 2.2 are
separate later developments.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.2, items 1–4, lines 274–277; no label.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w'

namespace FirstOrder.Language.Theory

variable {L : Language.{u, v}} {T T' T'' : L.Theory}

/-- Every bundled nonempty model of `T` embeds into a bundled nonempty model of `T'`.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.2, item 1, line 274; no label.-/
def ModelsEmbedInto (T T' : L.Theory) : Prop :=
  ∀ M : T.ModelType.{u, v, max u v},
    ∃ N : T'.ModelType.{u, v, max u v}, Nonempty (M ↪[L] N)

/-- Composition of the model-embedding property.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 1; no label.
@isnad1 id=modelsem.2h4v.s4.38b054b4ab1b from=translated src=- shape=de5dbc67 vocab=3b119500
-/
theorem ModelsEmbedInto.trans (hTT' : T.ModelsEmbedInto T')
    (hT'T'' : T'.ModelsEmbedInto T'') : T.ModelsEmbedInto T'' := by
  intro M
  obtain ⟨N, ⟨f⟩⟩ := hTT' M
  obtain ⟨P, ⟨g⟩⟩ := hT'T'' N
  exact ⟨P, ⟨g.comp f⟩⟩

/-- Two theories are companions when every model of either embeds into a model of the other.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.2, item 1, line 274; no label.-/
def IsCompanion (T T' : L.Theory) : Prop :=
  T.ModelsEmbedInto T' ∧ T'.ModelsEmbedInto T

/-- Every theory is a companion of itself.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 1; no label.
@isnad1 id=iscompan.0h2v.s3.01526fd91681 from=translated src=- shape=f3577ae2 vocab=6f74518f
-/
theorem IsCompanion.refl (T : L.Theory) : T.IsCompanion T := by
  constructor <;> intro M <;> exact ⟨M, ⟨Embedding.refl L M⟩⟩

/-- The companion relation is symmetric.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 1; no label.
@isnad1 id=iscompan.1h3v.s4.05dc7460f406 from=translated src=- shape=26022270 vocab=6f74518f
-/
theorem IsCompanion.symm (h : T.IsCompanion T') : T'.IsCompanion T :=
  ⟨h.2, h.1⟩

/-- The companion relation is transitive.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 1; no label.
@isnad1 id=iscompan.2h4v.s4.19ee79f70b6f from=translated src=- shape=de5dbc67 vocab=6f74518f
-/
theorem IsCompanion.trans (hTT' : T.IsCompanion T') (hT'T'' : T'.IsCompanion T'') :
    T.IsCompanion T'' :=
  ⟨hTT'.1.trans hT'T''.1, hT'T''.2.trans hTT'.2⟩

/-- Model completeness as defined in the paper: each formula is equivalent over the theory to
an existential formula. Mathlib's theory equivalence universally quantifies the free variables.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.2, item 2, line 275; no label.-/
def IsModelComplete (T : L.Theory) : Prop :=
  ∀ {n : ℕ} (φ : L.Formula (Fin n)),
    ∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧ (φ ⇔[T] ψ)

/-- The semantic formulation of model completeness, kept separate from the paper's definition.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, semantic comparison for Definition 2.2, item 2; no label.-/
def AllEmbeddingsElementary (T : L.Theory) : Prop :=
  ∀ (M N : T.ModelType.{u, v, max u v}) (f : M ↪[L] N),
    ∃ f' : M ↪ₑ[L] N, f'.toEmbedding = f

/-- Existential rewriting makes every formula persist along an embedding between models.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 2; no label.
@isnad1 id=realize.2h8v.s6.f3e39db38b81 from=translated src=- shape=c1676845 vocab=9a9dd221
-/
theorem IsModelComplete.realize_embedding (h : T.IsModelComplete)
    {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
    [M ⊨ T] [N ⊨ T] (f : M ↪[L] N) {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → M)
    (hφ : φ.Realize x) : φ.Realize (f ∘ x) := by
  obtain ⟨ψ, hψ, heq⟩ := h φ
  apply heq.realize_iff.mpr
  have hM : ψ.Realize x := heq.realize_iff.mp hφ
  simpa only [Formula.Realize, Unique.eq_default (f ∘ default)] using hψ.realize_embedding f hM

/-- In a model-complete theory, embeddings preserve and reflect all formulas.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 2; no label.
@isnad1 id=iff.1h8v.s6.dd05d6e6e7ea from=translated src=- shape=9417c6a2 vocab=9a9dd221
-/
theorem IsModelComplete.realize_embedding_iff (h : T.IsModelComplete)
    {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
    [M ⊨ T] [N ⊨ T] (f : M ↪[L] N) {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → M) :
    φ.Realize (f ∘ x) ↔ φ.Realize x := by
  constructor
  · intro hN
    by_contra hM
    have hnot : φ.not.Realize x := hM
    exact (h.realize_embedding f φ.not x hnot) hN
  · exact h.realize_embedding f φ x

/-- The paper's syntactic definition implies the semantic elementary-embedding condition.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, semantic comparison for Definition 2.2, item 2; no label.
@isnad1 id=allembed.1h2v.s3.58952e96c4c5 from=translated src=- shape=b28a8773 vocab=427e5598
-/
theorem IsModelComplete.allEmbeddingsElementary (h : T.IsModelComplete) :
    T.AllEmbeddingsElementary := by
  intro M N f
  exact ⟨⟨f, fun _ φ x => h.realize_embedding_iff f φ x⟩, Embedding.ext fun _ => rfl⟩

/-- A model companion is a model-complete companion, using the paper's model completeness.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.2, item 3, line 276; no label.-/
def IsModelCompanionOf (Tstar T : L.Theory) : Prop :=
  Tstar.IsCompanion T ∧ Tstar.IsModelComplete

/-- A model companion is a companion.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 3; no label.
@isnad1 id=iscompan.1h3v.s4.cdaedfeb0999 from=translated src=- shape=d90a4985 vocab=a6f414f9
-/
theorem IsModelCompanionOf.isCompanion {Tstar : L.Theory}
    (h : Tstar.IsModelCompanionOf T) : Tstar.IsCompanion T :=
  h.1

/-- A model companion is model complete in the paper's sense.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 3; no label.
@isnad1 id=ismodelc.1h3v.s4.77d871a4ca4d from=translated src=- shape=9bd4f843 vocab=60d538bf
-/
theorem IsModelCompanionOf.isModelComplete {Tstar : L.Theory}
    (h : Tstar.IsModelCompanionOf T) : Tstar.IsModelComplete :=
  h.2

/-- A theory has a model companion if it has some model-complete companion.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 3; no label.-/
def HasModelCompanion (T : L.Theory) : Prop :=
  ∃ Tstar : L.Theory, Tstar.IsModelCompanionOf T

/-- A nonempty model is existentially closed when every existential formula with parameters
that holds in an extension model already holds in the original model.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.2, item 4, line 277; no label.-/
def IsExistentiallyClosed (T : L.Theory) (M : Type (max u v)) [L.Structure M] : Prop :=
  Nonempty M ∧ M ⊨ T ∧
    ∀ (N : T.ModelType.{u, v, max u v}) (f : M ↪[L] N)
      {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → M),
      φ.IsExistential → φ.Realize (f ∘ x) → φ.Realize x

/-- Every model of a model-complete theory is existentially closed among that theory's models.
This does not assert the Pi-two model-companion criterion of Fact 2.3.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, items 2 and 4; no label.
@isnad1 id=isexiste.1h3v.s4.5aed16452765 from=translated src=- shape=5619c4bb vocab=2578ff57
-/
theorem IsModelComplete.isExistentiallyClosed (h : T.IsModelComplete)
    (M : T.ModelType.{u, v, max u v}) : T.IsExistentiallyClosed M := by
  refine ⟨inferInstance, M.is_model, ?_⟩
  intro N f n φ x _ hN
  exact (h.realize_embedding_iff f φ x).mp hN

/-- A model of a model companion that is also a model of the original theory is existentially
closed among models of the original theory. The second model assumption is explicit; this lemma
does not supply the Pi-two implication that appears in Fact 2.3.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, items 3 and 4; no label.
@isnad1 id=isexiste.1h4v.s5.a0914e1555db from=translated src=- shape=b047cd67 vocab=e32dd124
-/
theorem IsModelCompanionOf.isExistentiallyClosed_of_models {Tstar : L.Theory}
    (h : Tstar.IsModelCompanionOf T) (M : Tstar.ModelType.{u, v, max u v}) [M ⊨ T] :
    T.IsExistentiallyClosed M := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro N f n φ x hφ hN
  obtain ⟨N', ⟨g⟩⟩ := h.isCompanion.2 N
  apply (IsModelComplete.realize_embedding_iff h.isModelComplete (g.comp f) φ x).mp
  simpa only [Formula.Realize, Unique.eq_default (g ∘ default), Function.comp_def,
    Embedding.comp_apply] using
    hφ.realize_embedding g hN

/-- If a universal theory has a companion, every model of the companion satisfies the theory.
The universal hypothesis is used only in this auxiliary result, not as a replacement for the
paper's Pi-two hypothesis.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 1; no label.
@isnad1 id=model.1h4v.s5.7e6a97a611b7 from=translated src=- shape=7eef4379 vocab=363867e0
-/
theorem IsCompanion.models_of_isUniversal [T.IsUniversal] (h : T.IsCompanion T')
    (M : T'.ModelType.{u, v, max u v}) : M ⊨ T := by
  obtain ⟨N, ⟨f⟩⟩ := h.2 M
  exact IsUniversal.models_of_embedding f

/-- Every model of a model companion of a universal theory satisfies the original theory.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 3; no label.
@isnad1 id=model.1h4v.s5.df61451de2bf from=translated src=- shape=3fc53087 vocab=770a9573
-/
theorem IsModelCompanionOf.models_of_isUniversal [T.IsUniversal]
    (h : T'.IsModelCompanionOf T) (M : T'.ModelType.{u, v, max u v}) : M ⊨ T :=
  h.isCompanion.symm.models_of_isUniversal M

/-- Every model of a model companion of a universal theory is existentially closed among models
of the original theory. This auxiliary special case does not prove Fact 2.3 for Pi-two theories.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, items 3 and 4; no label.
@isnad1 id=isexiste.1h4v.s5.9220733725c5 from=translated src=- shape=2784de81 vocab=c208d67c
-/
theorem IsModelCompanionOf.isExistentiallyClosed_of_isUniversal [T.IsUniversal]
    (h : T'.IsModelCompanionOf T) (M : T'.ModelType.{u, v, max u v}) :
    T.IsExistentiallyClosed M := by
  let : M ⊨ T := h.models_of_isUniversal M
  exact h.isExistentiallyClosed_of_models M

end FirstOrder.Language.Theory
