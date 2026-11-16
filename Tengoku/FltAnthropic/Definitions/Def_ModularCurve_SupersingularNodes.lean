import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SpecializeModuli

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable {K : Type*} [Field K]

def frobNodePair (q : ℕ) (a : K) :
    Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1) :=
  (charLGeomPlaceOfPoint K a, charLGeomPlaceOfPoint K (a ^ q))

/--
@isnad1 id=eq.0h3v.s10.e3192ebbdcd3 from=translated src=- shape=ad32cf21 vocab=5d25de2b
-/
@[simp] theorem frobNodePair_fst (q : ℕ) (a : K) :
    (frobNodePair q a).1 = charLGeomPlaceOfPoint K a := rfl

/--
@isnad1 id=eq.0h3v.s10.b9c15c20780a from=translated src=- shape=7d9be2ea vocab=6d7ef705
-/
@[simp] theorem frobNodePair_snd (q : ℕ) (a : K) :
    (frobNodePair q a).2 = charLGeomPlaceOfPoint K (a ^ q) := rfl

/--
@isnad1 id=injectiv.0h2v.s10.ed2a86d77670 from=translated src=- shape=05c7006c vocab=bb697283
-/
theorem frobNodePair_injective (q : ℕ) : Function.Injective (frobNodePair (K := K) q) :=
  fun _ _ h => charLGeomPlaceOfPoint_injective K (congrArg Prod.fst h)

def frobNodePairEmb (q : ℕ) :
    K ↪ Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1) :=
  ⟨frobNodePair q, frobNodePair_injective q⟩

/--
@isnad1 id=eq.0h3v.s12.05894bdefc96 from=translated src=- shape=2cd84c89 vocab=7f809c65
-/
@[simp] theorem frobNodePairEmb_apply (q : ℕ) (a : K) :
    frobNodePairEmb q a = frobNodePair q a := rfl

def nodePairsOf (q : ℕ) (S : Finset K) :
    Finset (Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1)) :=
  S.map (frobNodePairEmb q)

/--
@isnad1 id=iff.0h4v.s12.bdb13b6db63e from=translated src=- shape=c8077e13 vocab=97e4a9d8
-/
theorem mem_nodePairsOf_iff (q : ℕ) (S : Finset K)
    (s : Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1)) :
    s ∈ nodePairsOf q S ↔ ∃ a ∈ S, frobNodePair q a = s := by
  simp only [nodePairsOf, Finset.mem_map, frobNodePairEmb_apply]

/--
@isnad1 id=mem.1h4v.s12.330afbef7c4c from=translated src=- shape=4b2a50eb vocab=97e4a9d8
-/
theorem frobNodePair_mem_nodePairsOf (q : ℕ) {S : Finset K} {a : K} (ha : a ∈ S) :
    frobNodePair q a ∈ nodePairsOf q S :=
  Finset.mem_map_of_mem (frobNodePairEmb q) ha

/--
@isnad1 id=eq.0h3v.s10.bdf06e9bd814 from=translated src=- shape=fe10da97 vocab=9968368f
-/
@[simp] theorem card_nodePairsOf (q : ℕ) (S : Finset K) : (nodePairsOf q S).card = S.card :=
  Finset.card_map _

def jOfNode (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) : K :=
  Classical.choose ((mem_nodePairsOf_iff q S s).mp s.2)

/--
@isnad1 id=mem.0h4v.s12.b533f17a91c5 from=translated src=- shape=8e6202c6 vocab=0de86f6d
-/
theorem jOfNode_mem (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) : jOfNode q S s ∈ S :=
  (Classical.choose_spec ((mem_nodePairsOf_iff q S s).mp s.2)).1

/--
@isnad1 id=eq.0h4v.s14.50ad2b30466e from=translated src=- shape=39643e30 vocab=3e953fc6
-/
@[simp] theorem frobNodePair_jOfNode (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) :
    frobNodePair q (jOfNode q S s) = s :=
  (Classical.choose_spec ((mem_nodePairsOf_iff q S s).mp s.2)).2

/--
@isnad1 id=eq.1h4v.s12.ee8ea67b7e49 from=translated src=- shape=5f099f1f vocab=171f4613
-/
@[simp] theorem jOfNode_mk (q : ℕ) {S : Finset K} {a : K} (ha : a ∈ S) :
    jOfNode q S ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q ha⟩ = a :=
  frobNodePair_injective q (frobNodePair_jOfNode q S _)

/--
@isnad1 id=injectiv.0h3v.s12.8914e9abb8a6 from=translated src=- shape=8c293911 vocab=ca05c5c3
-/
theorem jOfNode_injective (q : ℕ) (S : Finset K) : Function.Injective (jOfNode q S) :=
  fun s t h => Subtype.ext (by rw [← frobNodePair_jOfNode q S s, ← frobNodePair_jOfNode q S t, h])

def nodeEquiv (q : ℕ) (S : Finset K) : ↥S ≃ ↥(nodePairsOf q S) where
  toFun a := ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q a.2⟩
  invFun s := ⟨jOfNode q S s, jOfNode_mem q S s⟩
  left_inv a := Subtype.ext (jOfNode_mk q a.2)
  right_inv s := Subtype.ext (frobNodePair_jOfNode q S s)

/--
@isnad1 id=eq.0h4v.s15.afd737dfa178 from=translated src=- shape=db3529b9 vocab=d57a48df
-/
@[simp] theorem coe_nodeEquiv_apply (q : ℕ) (S : Finset K) (a : ↥S) :
    ((nodeEquiv q S a : ↥(nodePairsOf q S)) :
      Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1))
      = frobNodePair q (a : K) := rfl

/--
@isnad1 id=eq.0h4v.s15.7ea7bbdee2c7 from=translated src=- shape=9244864a vocab=b255c045
-/
@[simp] theorem coe_nodeEquiv_symm_apply (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) :
    ((nodeEquiv q S).symm s : K) = jOfNode q S s := rfl

def widthOf (q : ℕ) (S : Finset K) (e : K → ℕ) : ↥(nodePairsOf q S) → ℕ :=
  fun s => e (jOfNode q S s)

/--
@isnad1 id=eq.0h5v.s12.044e45427655 from=translated src=- shape=b63d2c02 vocab=c932c136
-/
theorem widthOf_apply (q : ℕ) (S : Finset K) (e : K → ℕ) (s : ↥(nodePairsOf q S)) :
    widthOf q S e s = e (jOfNode q S s) := rfl

/--
@isnad1 id=eq.1h5v.s12.3d87b6c4781b from=translated src=- shape=8e16ff77 vocab=f19f7665
-/
@[simp] theorem widthOf_mk (q : ℕ) {S : Finset K} (e : K → ℕ) {a : K} (ha : a ∈ S) :
    widthOf q S e ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q ha⟩ = e a := by
  rw [widthOf_apply, jOfNode_mk q ha]

/--
@isnad1 id=eq.0h5v.s15.890df1e17e28 from=translated src=- shape=8afc369e vocab=f22bc732
-/
theorem widthOf_nodeEquiv (q : ℕ) (S : Finset K) (e : K → ℕ) (a : ↥S) :
    widthOf q S e (nodeEquiv q S a) = e a :=
  widthOf_mk q e a.2

end ModularCurve

end
