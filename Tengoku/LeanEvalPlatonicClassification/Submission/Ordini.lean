import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.ScalaBandiere
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.Equivarianza
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.LibertaGenerica
import Tengoku.LeanEvalPlatonicClassification.Submission.RelazioniCoxeter
import Tengoku.LeanEvalPlatonicClassification.Submission.GruppoFinito

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 15 — IL SOTTOGRUPPO E GLI ORDINI (19 lug 2026).

Le simmetrie formano un sottogruppo di `Isom n`, finito per il passo
precedente. In un gruppo finito ogni elemento ha ordine finito: nasce
così la MATRICE DI COXETER `mᵢⱼ = ord(rᵢ rⱼ)`, con `mᵢᵢ = 1` (le
riflessioni sono involuzioni non banali) e `mᵢⱼ = 2` per i ranghi
lontani (commutano).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- L'essere simmetria dipende solo dalla funzione sottostante.
@isnad1 id=issymmet.2h4v.s9.a88560b8f60d from=translated src=- shape=b13a97d9 vocab=befcffc9
-/
theorem isSymmetry_congr (P : ConvexPolytope n) {φ ψ : Isom n}
    (h : ∀ x, φ x = ψ x) (hφ : P.isSymmetry φ) : P.isSymmetry ψ := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑ψ) '' P.toSet = (⇑φ) '' P.toSet :=
      Set.image_congr (fun x _ => (h x).symm)
    _ = P.toSet := hφ

/-- **Il gruppo di simmetria** come sottogruppo di `Isom n`.-/
def symGroup (P : ConvexPolytope n) : Subgroup (Isom n) where
  carrier := {φ : Isom n | P.isSymmetry φ}
  one_mem' := symmetry_reflN P
  mul_mem' {a b} ha hb := by
    refine isSymmetry_congr P (φ := b.trans a) (fun x => rfl)
      (symmetry_transN hb ha)
  inv_mem' {a} ha := by
    refine isSymmetry_congr P (φ := a.symm) (fun x => rfl)
      (symmetry_symmN ha)

/--
@isnad1 id=iff.0h3v.s8.9609d02d3b18 from=translated src=- shape=783f8f72 vocab=aad6aa5d
-/
@[simp] theorem mem_symGroup (P : ConvexPolytope n) {φ : Isom n} :
    φ ∈ symGroup P ↔ P.isSymmetry φ := Iff.rfl

/-- La riflessione semplice, come elemento del gruppo.-/
noncomputable def simpleGen (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : symGroup P :=
  ⟨simpleReflection P hreg F i, simpleReflection_isSymmetry P hreg F i⟩

/-- **rᵢ ≠ 1**: i generatori non sono banali.
@isnad1 id=ne.1h4v.s10.043235d738c9 from=translated src=- shape=295c840e vocab=f1d7ec02
-/
theorem simpleGen_ne_one (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) : simpleGen P hreg F i ≠ 1 := by
  intro h
  refine simpleReflection_ne_id P hreg F i (fun x => ?_)
  have hv : ((simpleGen P hreg F i : symGroup P) : Isom n) x = x := by
    rw [h]
    simp
  exact hv

/-- La matrice di Coxeter del politopo, relativa a una bandiera base.-/
noncomputable def coxeterMatrix (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i j : Fin n) : ℕ :=
  orderOf (simpleGen P hreg F i * simpleGen P hreg F j)

end LeanEval.Geometry.PlatonicClassification
