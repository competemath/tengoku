import Tengoku.StringDiagramsLean.StringDiagrams.Monoidal
import Tengoku.Seed.Algebra.Algebra.Subalgebra.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport along equalities of objects

Objects of the free 2-category are words, and equalities between them (for instance
`strands (i + 2 + j) = strands n`) are frequent when diagrams are placed at symbolic positions.
This file provides one family of lemmas for moving morphisms of a presented category, and
equalities between them, along such equalities.

* `Presentation.castHom ha hb f = eqToHom ≫ f ≫ eqToHom`: a morphism
  `P.obj a ⟶ P.obj b` retyped along `a = a'` and `b = b'`. It sends classes of diagrams to
  classes of retyped diagrams (`castHom_diag`), is compatible with composition and identities
  (`castHom_comp`, `castHom_id`), and is an `R`-linear equivalence (`castLinearEquiv`); on
  endomorphisms it is an isomorphism of `R`-algebras (`endCast`).
* `Presentation.diag_eq_castHom_of_layers_eq`: diagrams with the same list of layers have the
  same class up to retyping; hence an equality (or any linear relation) between classes of
  diagrams transfers to diagrams with the same layers between equal objects
  (`Presentation.diag_transfer`, `Presentation.diag_eq_diag_iff_of_layers_eq`).
* `Presentation.lin_cast`: retyping linear combinations of diagrams.
* `Presentation.mem_subalgebra_of_layers`: if every layer with source `a` has target `a`, then
  `End (P.obj a)` is generated as an `R`-algebra by the classes of the single layers.

The basic retyping lemma `Presentation.diag_cast` is in `StringDiagrams.Monoidal`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

variable {a b c a' b' c' a'' b'' : Obj S}

/-- Retyping of linear combinations of diagrams.
@isnad1 id=eq.2h8v.s8.84bbbfb6fa63 from=translated src=- shape=fa877589 vocab=9800f798
-/
theorem lin_cast (f : LinDiagram R a b) (ha : a = a') (hb : b = b') :
    P.lin (LinDiagram.cast f ha hb) =
      eqToHom (congrArg P.obj ha.symm) ≫ P.lin f ≫ eqToHom (congrArg P.obj hb) := by
  subst ha hb; simp

/-- A morphism of the presented category retyped along equalities of its boundary objects.-/
def castHom (ha : a = a') (hb : b = b') (f : P.obj a ⟶ P.obj b) : P.obj a' ⟶ P.obj b' :=
  eqToHom (congrArg P.obj ha.symm) ≫ f ≫ eqToHom (congrArg P.obj hb)

/--
@isnad1 id=eq.0h6v.s6.a2dd6697f328 from=translated src=- shape=910bb215 vocab=58d63284
-/
@[simp] theorem castHom_rfl (f : P.obj a ⟶ P.obj b) : P.castHom rfl rfl f = f := by
  simp [castHom]

/--
@isnad1 id=eq.2h8v.s7.6581e4c88028 from=translated src=- shape=ff2e3835 vocab=370c5b74
-/
@[simp] theorem castHom_diag (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    P.castHom ha hb (P.diag f) = P.diag (Diagram.cast f ha hb) :=
  (P.diag_cast f ha hb).symm

/--
@isnad1 id=eq.2h8v.s7.52c61949cd57 from=translated src=- shape=abaa2ddd vocab=e1f24e6e
-/
@[simp] theorem castHom_lin (f : LinDiagram R a b) (ha : a = a') (hb : b = b') :
    P.castHom ha hb (P.lin f) = P.lin (LinDiagram.cast f ha hb) :=
  (P.lin_cast f ha hb).symm

/--
@isnad1 id=eq.4h10v.s7.211640367695 from=translated src=- shape=19a415f1 vocab=73e3f30d
-/
@[simp] theorem castHom_castHom (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'')
    (f : P.obj a ⟶ P.obj b) :
    P.castHom ha' hb' (P.castHom ha hb f) = P.castHom (ha.trans ha') (hb.trans hb') f := by
  subst ha hb ha' hb'; simp

/--
@isnad1 id=eq.3h11v.s8.b64607bcbd16 from=translated src=- shape=616539e8 vocab=2e34a869
-/
theorem castHom_comp (ha : a = a') (hb : b = b') (hc : c = c') (f : P.obj a ⟶ P.obj b)
    (g : P.obj b ⟶ P.obj c) :
    P.castHom ha hc (f ≫ g) = P.castHom ha hb f ≫ P.castHom hb hc g := by
  subst ha hb hc; simp

/--
@isnad1 id=eq.1h5v.s7.195a986e4139 from=translated src=- shape=7a4ffee8 vocab=cb3e0332
-/
@[simp] theorem castHom_id (ha : a = a') : P.castHom ha ha (𝟙 (P.obj a)) = 𝟙 _ := by
  subst ha; simp

/--
@isnad1 id=eq.3h7v.s7.73f2f1da3673 from=translated src=- shape=6006595e vocab=dd4063b1
-/
theorem castHom_eqToHom (ha : a = a') (hb : b = b') (h : P.obj a = P.obj b) :
    P.castHom ha hb (eqToHom h) = eqToHom (by rw [← ha, ← hb, h]) := by
  subst ha hb; simp

/--
@isnad1 id=iff.2h9v.s7.14697c75ff11 from=translated src=- shape=97e02aa9 vocab=972ec1dd
-/
theorem castHom_eq_iff (ha : a = a') (hb : b = b') (f : P.obj a ⟶ P.obj b)
    (g : P.obj a' ⟶ P.obj b') : P.castHom ha hb f = g ↔ f = P.castHom ha.symm hb.symm g := by
  subst ha hb; simp

/--
@isnad1 id=injectiv.2h7v.s7.d10bc2426b38 from=translated src=- shape=de6b0d60 vocab=559a0d87
-/
theorem castHom_injective (ha : a = a') (hb : b = b') : Function.Injective (P.castHom ha hb) := by
  intro f g h
  subst ha hb
  simpa using h

/--
@isnad1 id=iff.2h9v.s7.35c1381fccc3 from=translated src=- shape=0077f1f6 vocab=6be9767f
-/
@[simp] theorem castHom_inj (ha : a = a') (hb : b = b') {f g : P.obj a ⟶ P.obj b} :
    P.castHom ha hb f = P.castHom ha hb g ↔ f = g :=
  (P.castHom_injective ha hb).eq_iff

/-- Whiskering commutes with retyping.
@isnad1 id=eq.2h10v.s7.76530466ba0c from=translated src=- shape=db47057c vocab=377175bc
-/
theorem whisk_castHom (ha : a = a') (hb : b = b') (f : P.obj a ⟶ P.obj b) (u : Obj S)
    (v : List S.Colour) :
    P.whisk (P.castHom ha hb f) u v =
      P.castHom (congrArg (Obj.whisker · u v) ha) (congrArg (Obj.whisker · u v) hb)
        (P.whisk f u v) := by
  subst ha hb; simp

/-- Retyping as an `R`-linear equivalence of Hom modules.-/
def castLinearEquiv (ha : a = a') (hb : b = b') :
    (P.obj a ⟶ P.obj b) ≃ₗ[R] (P.obj a' ⟶ P.obj b') where
  toFun := P.castHom ha hb
  invFun := P.castHom ha.symm hb.symm
  map_add' f g := by simp [castHom]
  map_smul' r f := by simp [castHom]
  left_inv f := by simp
  right_inv f := by simp

/--
@isnad1 id=eq.2h8v.s10.0147ad239af1 from=translated src=- shape=86afc3a1 vocab=bb014eb9
-/
@[simp] theorem castLinearEquiv_apply (ha : a = a') (hb : b = b') (f : P.obj a ⟶ P.obj b) :
    P.castLinearEquiv ha hb f = P.castHom ha hb f := rfl

/--
@isnad1 id=eq.2h8v.s10.4510a4323cce from=translated src=- shape=ec3b1f8c vocab=9baa5740
-/
@[simp] theorem castLinearEquiv_symm_apply (ha : a = a') (hb : b = b')
    (f : P.obj a' ⟶ P.obj b') :
    (P.castLinearEquiv ha hb).symm f = P.castHom ha.symm hb.symm f := rfl

/--
@isnad1 id=eq.2h9v.s10.dee08ffbe9c2 from=translated src=- shape=87aef3e1 vocab=fbf62e7c
-/
theorem castHom_add (ha : a = a') (hb : b = b') (f g : P.obj a ⟶ P.obj b) :
    P.castHom ha hb (f + g) = P.castHom ha hb f + P.castHom ha hb g :=
  (P.castLinearEquiv ha hb).map_add f g

/--
@isnad1 id=eq.2h9v.s9.a7c7ac03e9a8 from=translated src=- shape=87aef3e1 vocab=d4e6c47d
-/
theorem castHom_sub (ha : a = a') (hb : b = b') (f g : P.obj a ⟶ P.obj b) :
    P.castHom ha hb (f - g) = P.castHom ha hb f - P.castHom ha hb g :=
  (P.castLinearEquiv ha hb).map_sub f g

/--
@isnad1 id=eq.2h8v.s9.007cb8fc67a4 from=translated src=- shape=3a0c259d vocab=02ee83bd
-/
theorem castHom_neg (ha : a = a') (hb : b = b') (f : P.obj a ⟶ P.obj b) :
    P.castHom ha hb (-f) = -P.castHom ha hb f :=
  (P.castLinearEquiv ha hb).map_neg f

/--
@isnad1 id=eq.2h7v.s8.4a1d9406e542 from=translated src=- shape=f7e84503 vocab=6be9767f
-/
@[simp] theorem castHom_zero (ha : a = a') (hb : b = b') :
    P.castHom ha hb (0 : P.obj a ⟶ P.obj b) = 0 :=
  (P.castLinearEquiv ha hb).map_zero

/--
@isnad1 id=eq.2h9v.s11.a6c702df9c19 from=translated src=- shape=a36d02a5 vocab=b64dc73d
-/
theorem castHom_smul (ha : a = a') (hb : b = b') (r : R) (f : P.obj a ⟶ P.obj b) :
    P.castHom ha hb (r • f) = r • P.castHom ha hb f :=
  (P.castLinearEquiv ha hb).map_smul r f

/-- Retyping of endomorphisms as an isomorphism of `R`-algebras.-/
def endCast (h : a = a') : End (P.obj a) ≃ₐ[R] End (P.obj a') where
  toFun := P.castHom h h
  invFun := P.castHom h.symm h.symm
  left_inv f := by simp
  right_inv f := by simp
  map_mul' f g := by
    rw [End.mul_def, End.mul_def, P.castHom_comp h h h]
  map_add' f g := P.castHom_add h h f g
  commutes' r := by
    subst h
    simp

/--
@isnad1 id=eq.1h6v.s8.bb18bf650e12 from=translated src=- shape=c09bc403 vocab=724b22af
-/
@[simp] theorem endCast_apply (h : a = a') (f : End (P.obj a)) : P.endCast h f = P.castHom h h f :=
  rfl

/--
@isnad1 id=eq.1h6v.s9.70dc266664dc from=translated src=- shape=26fd833f vocab=94721357
-/
@[simp] theorem endCast_symm_apply (h : a = a') (f : End (P.obj a')) :
    (P.endCast h).symm f = P.castHom h.symm h.symm f := rfl

/-! ## Diagrams with the same layers -/

/-- Diagrams with the same layers have the same class, up to retyping.
@isnad1 id=eq.3h9v.s7.1a7300ac83fc from=translated src=- shape=25e60e62 vocab=6801723b
-/
theorem diag_eq_castHom_of_layers_eq (f : a ⟶ b) (g : a' ⟶ b') (ha : a' = a) (hb : b' = b)
    (h : Diagram.layers f = Diagram.layers g) : P.diag f = P.castHom ha hb (P.diag g) := by
  rw [castHom_diag]
  exact P.diag_eq_of_layers_eq h

/-- Transfer of an equality of classes of diagrams to diagrams with the same layers between
equal objects.
@isnad1 id=eq.5h11v.s7.cc4276e2cd3c from=translated src=- shape=f15f5b36 vocab=c38a1ddd
-/
theorem diag_transfer (A B : a ⟶ b) (A' B' : a' ⟶ b') (ha : a = a') (hb : b = b')
    (hA : Diagram.layers A = Diagram.layers A') (hB : Diagram.layers B = Diagram.layers B')
    (h : P.diag A' = P.diag B') : P.diag A = P.diag B := by
  rw [P.diag_eq_castHom_of_layers_eq A A' ha.symm hb.symm hA,
    P.diag_eq_castHom_of_layers_eq B B' ha.symm hb.symm hB, h]

/--
@isnad1 id=iff.4h11v.s7.fef003e3fb45 from=translated src=- shape=79092533 vocab=c38a1ddd
-/
theorem diag_eq_diag_iff_of_layers_eq (A B : a ⟶ b) (A' B' : a' ⟶ b') (ha : a = a')
    (hb : b = b') (hA : Diagram.layers A = Diagram.layers A')
    (hB : Diagram.layers B = Diagram.layers B') : P.diag A = P.diag B ↔ P.diag A' = P.diag B' :=
  ⟨P.diag_transfer A' B' A B ha.symm hb.symm hA.symm hB.symm,
    P.diag_transfer A B A' B' ha hb hA hB⟩

/-! ## Generation of endomorphism algebras by layers -/

/-- **Generation of an endomorphism algebra by layers.** If every layer with source `a` has
target `a` (for instance, `a` is the object of `n` strands in a one-colour signature whose
generators preserve the number of strands), then every endomorphism of `a` lies in any
subalgebra containing the classes of all single layers with source `a`.
@isnad1 id=mem.2h6v.s9.0fa68db04d0f from=translated src=- shape=ab985b27 vocab=3d2e298b
-/
theorem mem_subalgebra_of_layers {a : Obj S}
    (ha : ∀ (L : Layer S), L.Valid → L.dom = a → L.cod = a) (A : Subalgebra R (End (P.obj a)))
    (hA : ∀ (L : Layer S) (hv : L.Valid) (hd : L.dom = a), P.layer L hv hd (ha L hv hd) ∈ A)
    (f : End (P.obj a)) : f ∈ A := by
  let M : ∀ x y : Obj S, Submodule R (P.obj x ⟶ P.obj y) := fun x y =>
    { carrier := {g | ∀ (hx : x = a) (hy : y = a), P.castHom hx hy g ∈ A}
      add_mem' := fun hf hg hx hy => by
        rw [castHom_add]; exact A.add_mem (hf hx hy) (hg hx hy)
      zero_mem' := fun hx hy => by rw [castHom_zero]; exact A.zero_mem
      smul_mem' := fun r g hg hx hy => by rw [castHom_smul]; exact A.smul_mem (hg hx hy) r }
  have key := P.mem_of_layers {x | x = a} (fun L hv hL => ha L hv hL) M
    (fun x hx hx' _ => by rw [castHom_id]; exact A.one_mem)
    (fun {x y z} _ hy _ g g' hg hg' hx hz => by
      rw [P.castHom_comp hx hy hz]; exact A.mul_mem (hg' hy hz) (hg hx hy))
    (fun L hv hL hx hy => by
      rw [castHom_diag]
      exact hA L hv hx) rfl rfl f
  simpa using key rfl rfl

end Presentation

end StringDiagrams

end
