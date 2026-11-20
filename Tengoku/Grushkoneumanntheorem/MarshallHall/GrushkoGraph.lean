import Tengoku.Grushkoneumanntheorem.MarshallHall.GrushkoFold
import Tengoku.Seed.Combinatorics.Quiver.Cast
import Tengoku.Seed.Combinatorics.Quiver.Symmetric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
## Labelled paths for the Grushko fold argument

The fold proof is carried by a finite graph whose oriented edges are labelled
by elements of the two factors.  This file isolates the path-level semantics:
composition reads as multiplication, reversal reads as inversion, and every
path has an explicit list of factor labels.  The graph-fold construction can
therefore use these operations without introducing a second, informal notion
of path evaluation.
-/

open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u v

variable {G H : Type u} {V : Type v} [Group G] [Group H] [Quiver V]
  [HasInvolutiveReverse V]

/--
@isnad1 id=eq.2h6v.s5.563f50985789 from=translated src=- shape=631d8527 vocab=50eaaa53
-/
theorem path_length_cast {a b a' b' : V} (ha : a = a') (hb : b = b')
    (p : Path a b) : (p.cast ha hb).length = p.length := by
  subst_vars
  rfl

/-- An oriented-edge labelling by the two factors, compatible with reversal.-/
structure BinaryLabelling where
  label : ∀ {a b : V}, (a ⟶ b) → Sum G H
  reverse_label : ∀ {a b : V} (e : a ⟶ b),
    label (Quiver.reverse e) = factorWordInv (G := G) (H := H) (label e)

namespace BinaryLabelling

variable (L : BinaryLabelling (G := G) (H := H) (V := V))

/-- The factor-label list read along a directed path.-/
def pathLabels {a : V} : ∀ {b : V}, Path a b → List (Sum G H)
  | _, Path.nil => []
  | _, Path.cons p e => pathLabels p ++ [L.label e]

/-- The element of the free product read along a directed path.-/
def pathRead {a : V} {b : V} (p : Path a b) : G ∗ H :=
  factorWordProd (G := G) (H := H) (pathLabels L p)

/-- A path is monochromatic when all of its edge labels come from one factor.-/
def IsMonochromatic {a b : V} (p : Path a b) (color : Bool) : Prop :=
  ∀ z ∈ L.pathLabels p,
    binarySumIndex (G := G) (H := H) z = color

/--
@isnad1 id=eq.0h5v.s5.a81b80f803c3 from=translated src=- shape=b5071b1b vocab=0d4997ac
-/
@[simp] theorem pathLabels_nil {a : V} :
    L.pathLabels (Path.nil : Path a a) = [] :=
  rfl

/--
@isnad1 id=eq.0h7v.s6.cfc38cc6af70 from=translated src=- shape=154f04dd vocab=d0badb58
-/
@[simp] theorem pathLabels_toPath {a b : V} (e : a ⟶ b) :
    L.pathLabels e.toPath = [L.label e] := by
  rfl

/--
@isnad1 id=eq.1h8v.s6.c9227b50da46 from=translated src=- shape=3730a492 vocab=174790cc
-/
theorem pathLabels_eq_of_endpoint_eq {a b c : V} (h : b = c)
    (p : Path a b) :
    L.pathLabels (h ▸ p) = L.pathLabels p := by
  cases h
  rfl

/--
@isnad1 id=eq.2h9v.s6.f785ec123626 from=translated src=- shape=01099727 vocab=00e1774a
-/
theorem pathLabels_cast {a b a' b' : V} (ha : a = a') (hb : b = b')
    (p : Path a b) :
    L.pathLabels (p.cast ha hb) = L.pathLabels p := by
  subst_vars
  rfl

/--
@isnad1 id=eq.2h9v.s6.55ca3ff2b62c from=translated src=- shape=84676b9b vocab=ded487f3
-/
theorem pathRead_cast {a b a' b' : V} (ha : a = a') (hb : b = b')
    (p : Path a b) :
    L.pathRead (p.cast ha hb) = L.pathRead p := by
  simp only [pathRead, pathLabels_cast]

/--
@isnad1 id=eq.0h5v.s7.d68cc2fe48dc from=translated src=- shape=49add644 vocab=13714931
-/
@[simp] theorem pathRead_nil {a : V} :
    L.pathRead (Path.nil : Path a a) = 1 := by
  simp [pathRead, pathLabels, factorWordProd]

/--
@isnad1 id=eq.0h7v.s6.8089e47860f4 from=translated src=- shape=60a9db2d vocab=d15de98b
-/
@[simp] theorem pathRead_toPath {a b : V} (e : a ⟶ b) :
    L.pathRead e.toPath = separatedMap (L.label e) := by
  simp [pathRead, pathLabels, factorWordProd, separatedMap]

/--
@isnad1 id=eq.0h9v.s6.8c09a0b320d1 from=translated src=- shape=70ae6474 vocab=19a7d29c
-/
theorem pathLabels_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), L.pathLabels (p.comp q) =
      L.pathLabels p ++ L.pathLabels q
  | _, Path.nil => by simp
  | _, Path.cons q e => by
      simp only [Path.comp_cons, pathLabels]
      rw [pathLabels_comp p q, List.append_assoc]

/--
@isnad1 id=eq.0h9v.s7.11bfb9d0a1d7 from=translated src=- shape=3e00c7c1 vocab=83c13750
-/
theorem pathRead_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), L.pathRead (p.comp q) =
      L.pathRead p * L.pathRead q
  | _, q => by
      simp only [pathRead, pathLabels_comp, factorWordProd_append]

/-! ### Reading paths in the symmetrized graph -/

def symmLabel {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    Sum G H :=
  match e with
  | Sum.inl f => L.label f
  | Sum.inr f => factorWordInv (L.label f)

def symmPathLabels {a : Symmetrify V} :
    ∀ {b : Symmetrify V},
      @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b →
        List (Sum G H)
  | _, Path.nil => []
  | _, Path.cons p e => symmPathLabels p ++ [L.symmLabel e]

def symmPathRead {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
  G ∗ H :=
  factorWordProd (G := G) (H := H) (L.symmPathLabels p)

/--
@isnad1 id=eq.2h9v.s6.dba9889932c3 from=translated src=- shape=90d0067d vocab=1392e0bf
-/
theorem symmPathLabels_cast {a b a' b' : Symmetrify V}
    (ha : a = a') (hb : b = b')
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmPathLabels (p.cast ha hb) = L.symmPathLabels p := by
  subst_vars
  rfl

/--
@isnad1 id=eq.2h9v.s6.5914f2efa314 from=translated src=- shape=4a828dac vocab=ed82f378
-/
theorem symmPathRead_cast {a b a' b' : Symmetrify V}
    (ha : a = a') (hb : b = b')
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmPathRead (p.cast ha hb) = L.symmPathRead p := by
  simp only [symmPathRead, symmPathLabels_cast]

/--
@isnad1 id=eq.0h5v.s5.0a917dee9301 from=translated src=- shape=a55cecab vocab=16d168b9
-/
@[simp] theorem symmPathLabels_nil {a : Symmetrify V} :
    L.symmPathLabels
      (@Quiver.Path.nil (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a) = [] :=
  rfl

/--
@isnad1 id=eq.0h7v.s6.cf14e0a12485 from=translated src=- shape=b0db6ef0 vocab=0bc74c8f
-/
@[simp] theorem symmPathLabels_toPath {a b : Symmetrify V}
  (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmPathLabels e.toPath = [L.symmLabel e] := by
  rfl

/--
@isnad1 id=eq.0h5v.s7.de58e4ed3790 from=translated src=- shape=8212aedf vocab=03d81d29
-/
@[simp] theorem symmPathRead_nil {a : Symmetrify V} :
    L.symmPathRead
      (@Quiver.Path.nil (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a) = 1 := by
  simp [symmPathRead, symmPathLabels, factorWordProd]

/--
@isnad1 id=eq.0h7v.s6.67cd43760fff from=translated src=- shape=86288970 vocab=67bbf0aa
-/
@[simp] theorem symmPathRead_toPath {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmPathRead e.toPath = separatedMap (L.symmLabel e) := by
  change factorWordProd [L.symmLabel e] = separatedMap (L.symmLabel e)
  simp [factorWordProd]

/--
@isnad1 id=eq.0h9v.s7.9db9219d4269 from=translated src=- shape=b6e402c1 vocab=b40cbf7b
-/
theorem symmPathLabels_comp {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    ∀ {c : Symmetrify V}
      (q : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) b c),
      L.symmPathLabels (p.comp q) =
        L.symmPathLabels p ++ L.symmPathLabels q
  | _, Path.nil => by
      change L.symmPathLabels p = L.symmPathLabels p ++ []
      simp
  | _, Path.cons q e => by
      simp only [Path.comp_cons, symmPathLabels]
      rw [symmPathLabels_comp p q, List.append_assoc]

/--
@isnad1 id=eq.0h9v.s7.c1a5ebbe40b4 from=translated src=- shape=188684d9 vocab=fc1d3322
-/
theorem symmPathRead_comp {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    ∀ {c : Symmetrify V}
      (q : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) b c),
      L.symmPathRead (p.comp q) = L.symmPathRead p * L.symmPathRead q
  | _, q => by
      simp only [symmPathRead, symmPathLabels_comp, factorWordProd_append]

/--
@isnad1 id=eq.0h7v.s6.845888184f0b from=translated src=- shape=7ef4d34d vocab=269d26d1
-/
theorem symmLabel_reverse {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmLabel (Quiver.reverse e) = factorWordInv (L.symmLabel e) := by
  cases e with
  | inl f =>
      rfl
  | inr f =>
      simp [symmLabel]

/--
@isnad1 id=eq.0h7v.s6.590f66f6f912 from=translated src=- shape=bad07e47 vocab=98f56235
-/
theorem symmPathRead_reverse {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmPathRead p.reverse = (L.symmPathRead p)⁻¹ := by
  induction p with
  | nil => simp
  | cons p e ih =>
      change L.symmPathRead ((Quiver.reverse e).toPath.comp p.reverse) =
        (L.symmPathRead (p.comp e.toPath))⁻¹
      rw [symmPathRead_comp, symmPathRead_toPath, symmLabel_reverse, ih,
        symmPathRead_comp, symmPathRead_toPath]
      simp [separatedMap_factorWordInv, mul_inv_rev]

/--
@isnad1 id=eq.0h7v.s6.592c55ea3504 from=translated src=- shape=b43f4c24 vocab=dcc774ac
-/
theorem symmPathRead_map_of {a b : V}
    (p : @Quiver.Path V _ a b) :
    L.symmPathRead
        ((@Quiver.Symmetrify.of V _).mapPath p) = L.pathRead p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change L.symmPathRead
          (((@Quiver.Symmetrify.of V _).mapPath p).comp
            ((@Quiver.Symmetrify.of V _).map e).toPath) =
        L.pathRead (p.comp e.toPath)
      rw [symmPathRead_comp, ih, symmPathRead_toPath, L.pathRead_comp,
        L.pathRead_toPath]
      simp [symmLabel]
      rfl

def symmIsMonochromatic {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b)
    (color : Bool) : Prop :=
  ∀ z ∈ L.symmPathLabels p,
    binarySumIndex (G := G) (H := H) z = color

/--
@isnad1 id=symmismo.0h6v.s5.22b99e51450e from=translated src=- shape=5a5253b6 vocab=ff5ff1db
-/
@[simp] theorem symmIsMonochromatic_nil {a : Symmetrify V} (color : Bool) :
    L.symmIsMonochromatic
      (@Quiver.Path.nil (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a) color := by
  simp [symmIsMonochromatic]

/--
@isnad1 id=symmismo.0h7v.s6.2fae198a0e31 from=translated src=- shape=fb959887 vocab=efd349e6
-/
theorem symmIsMonochromatic_toPath {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmIsMonochromatic e.toPath
      (binarySumIndex (G := G) (H := H) (L.symmLabel e)) := by
  intro z hz
  have hz' : z = L.symmLabel e := by
    simpa only [symmPathLabels_toPath, List.mem_singleton] using hz
  exact congrArg (binarySumIndex (G := G) (H := H)) hz'

/--
@isnad1 id=symmismo.2h10v.s6.c58bfaf095ec from=translated src=- shape=ce8b3f5e vocab=b4dc22cb
-/
theorem symmIsMonochromatic_comp {a b c : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b)
    (q : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) b c)
    {color : Bool} (hp : L.symmIsMonochromatic p color)
    (hq : L.symmIsMonochromatic q color) :
    L.symmIsMonochromatic (p.comp q) color := by
  intro z hz
  rw [symmPathLabels_comp] at hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hp z hz
  · exact hq z hz

/--
@isnad1 id=ex.1h7v.s8.c9ae54a616e5 from=translated src=- shape=d1c89a7b vocab=bd18797b
-/
theorem symmPathRead_mono_false {a b : Symmetrify V}
    {p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b}
    (hp : L.symmIsMonochromatic p false) :
    ∃ g : G, L.symmPathRead p = Monoid.Coprod.inl g := by
  obtain ⟨l, hl⟩ := exists_map_inl_of_idx_false (G := G) (H := H) (by
    simpa [symmIsMonochromatic] using hp)
  refine ⟨l.prod, ?_⟩
  rw [symmPathRead, hl, factorWordProd_map_inl]

/--
@isnad1 id=ex.1h7v.s8.e3b1697c4b5f from=translated src=- shape=1c6aea07 vocab=57171ee8
-/
theorem symmPathRead_mono_true {a b : Symmetrify V}
    {p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b}
    (hp : L.symmIsMonochromatic p true) :
    ∃ h : H, L.symmPathRead p = Monoid.Coprod.inr h := by
  obtain ⟨l, hl⟩ := exists_map_inr_of_idx_true (G := G) (H := H) (by
    simpa [symmIsMonochromatic] using hp)
  refine ⟨l.prod, ?_⟩
  rw [symmPathRead, hl, factorWordProd_map_inr]

structure SymmRunPiece where
  source : Symmetrify V
  target : Symmetrify V
  path : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) source target
  color : Bool
  monochromatic : L.symmIsMonochromatic path color
  nonempty : path.length ≠ 0

namespace SymmRunPiece

@[reducible] def single {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    SymmRunPiece L :=
  { source := a
    target := b
    path := e.toPath
    color := binarySumIndex (G := G) (H := H) (L.symmLabel e)
    monochromatic := L.symmIsMonochromatic_toPath e
    nonempty := by simp }

@[reducible] def extend {c : Symmetrify V} (r : SymmRunPiece L)
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _)
      r.target c)
    (hcolor : binarySumIndex (G := G) (H := H) (L.symmLabel e) = r.color) :
    SymmRunPiece L :=
  { source := r.source
    target := c
    path := r.path.comp e.toPath
    color := r.color
    monochromatic := by
      apply L.symmIsMonochromatic_comp r.path e.toPath
        r.monochromatic
      intro z hz
      have hz' : z = L.symmLabel e := by
        simpa only [symmPathLabels_toPath, List.mem_singleton] using hz
      rw [hz', hcolor]
    nonempty := by
      rw [Quiver.Path.length_comp]
      simp }

end SymmRunPiece

def symmRunTag (r : SymmRunPiece L) : Sum G H :=
  match r.color with
  | false => Sum.inl (Monoid.Coprod.fst (L.symmPathRead r.path))
  | true => Sum.inr (Monoid.Coprod.snd (L.symmPathRead r.path))

/--
@isnad1 id=eq.0h5v.s6.9af3aed2423b from=translated src=- shape=014639cc vocab=a572fa9d
-/
theorem separatedMap_symmRunTag (r : SymmRunPiece L) :
    separatedMap (L.symmRunTag r) = L.symmPathRead r.path := by
  cases hc : r.color with
  | false =>
      have hmono : L.symmIsMonochromatic r.path false := by
        simpa [hc] using r.monochromatic
      obtain ⟨g, hg⟩ := L.symmPathRead_mono_false hmono
      simp only [symmRunTag, hc, hg, separatedMap]
      rfl
  | true =>
      have hmono : L.symmIsMonochromatic r.path true := by
        simpa [hc] using r.monochromatic
      obtain ⟨h, hh⟩ := L.symmPathRead_mono_true hmono
      simp only [symmRunTag, hc, hh, separatedMap]
      rfl

inductive SymmRunChain (L : BinaryLabelling (G := G) (H := H) (V := V)) :
    Symmetrify V → Symmetrify V → Type (max v 1)
  | nil (a : Symmetrify V) : SymmRunChain L a a
  | cons {a : Symmetrify V} (r : SymmRunPiece L)
      (rest : SymmRunChain L a r.source) : SymmRunChain L a r.target

def SymmRunChain.path : ∀ {a b : Symmetrify V},
    SymmRunChain L a b →
      @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b
  | _, _, .nil _ => Path.nil
  | _, _, .cons r rest => (SymmRunChain.path rest).comp r.path

def SymmRunChain.colors : ∀ {a b : Symmetrify V},
    SymmRunChain L a b → List Bool
  | _, _, .nil _ => []
  | _, _, .cons r rest => r.color :: SymmRunChain.colors rest

def SymmRunChain.pieces : ∀ {a b : Symmetrify V},
    SymmRunChain L a b → List (SymmRunPiece L)
  | _, _, .nil _ => []
  | _, _, .cons r rest => SymmRunChain.pieces rest ++ [r]

def SymmRunChain.pieceColors : ∀ {a b : Symmetrify V},
    SymmRunChain L a b → List Bool
  | _, _, .nil _ => []
  | _, _, .cons r rest =>
      SymmRunChain.pieceColors rest ++ [r.color]

/--
@isnad1 id=eq.0h7v.s6.219d208e9b58 from=translated src=- shape=c5a9b0e2 vocab=6f5e5ad0
-/
theorem SymmRunChain.pieceColors_eq_colors_reverse
    {a b : Symmetrify V} (c : SymmRunChain L a b) :
    (c.pieces.map (fun r => r.color)) = c.colors.reverse := by
  induction c with
  | nil => simp [SymmRunChain.pieces, SymmRunChain.colors]
  | cons r rest ih =>
      simp [SymmRunChain.pieces, SymmRunChain.colors, ih]

/--
@isnad1 id=eq.0h7v.s6.81e2d06ef79a from=translated src=- shape=73e8b271 vocab=35b10e7d
-/
theorem SymmRunChain.pieceColors_eq_defined
    {a b : Symmetrify V} (c : SymmRunChain L a b) :
    c.pieceColors = c.pieces.map (fun r => r.color) := by
  induction c with
  | nil => simp [SymmRunChain.pieceColors, SymmRunChain.pieces]
  | cons r rest ih =>
      simp [SymmRunChain.pieceColors, SymmRunChain.pieces, ih]

/--
@isnad1 id=ischain.1h7v.s6.ae3c4ea790f5 from=translated src=- shape=05eab417 vocab=94195e3e
-/
theorem SymmRunChain.pieceColors_isChain
    {a b : Symmetrify V} (c : SymmRunChain L a b)
      (h : c.colors.IsChain (fun x y : Bool => x ≠ y)) :
    (c.pieces.map (fun r => r.color)).IsChain
      (fun x y : Bool => x ≠ y) := by
  rw [SymmRunChain.pieceColors_eq_colors_reverse L c]
  apply List.isChain_reverse.mpr
  simpa [eq_comm] using h

/--
@isnad1 id=eq.0h5v.s5.448faac88a45 from=translated src=- shape=13b289b3 vocab=f33d4761
-/
theorem symmRunTag_index (r : SymmRunPiece L) :
    binarySumIndex (G := G) (H := H) (L.symmRunTag r) = r.color := by
  cases hc : r.color <;> simp [symmRunTag, hc]

/--
@isnad1 id=ischain.1h7v.s6.4aaea5cf00aa from=translated src=- shape=578fb9e2 vocab=2a92c237
-/
theorem SymmRunChain.tags_isChain
    {a b : Symmetrify V} (c : SymmRunChain L a b)
    (h : c.colors.IsChain (fun x y : Bool => x ≠ y)) :
    (c.pieces.map L.symmRunTag).IsChain
      (fun x y => binarySumIndex (G := G) (H := H) x ≠
        binarySumIndex (G := G) (H := H) y) := by
  rw [List.isChain_map]
  have hp := SymmRunChain.pieceColors_isChain L c h
  rw [List.isChain_map] at hp
  apply hp.imp
  intro r s hrs
  simpa only [symmRunTag_index] using hrs

/--
@isnad1 id=eq.0h7v.s6.56dea22a79c4 from=translated src=- shape=a9c17ba8 vocab=c54b1e58
-/
theorem SymmRunChain.pathRead_eq_factorWordProd_tags
    {a b : Symmetrify V} (c : SymmRunChain L a b) :
    L.symmPathRead (c.path) =
      factorWordProd (G := G) (H := H)
        (c.pieces.map L.symmRunTag) := by
  induction c with
  | nil => simp [SymmRunChain.path, SymmRunChain.pieces, factorWordProd]
  | cons r rest ih =>
      simp [SymmRunChain.path, SymmRunChain.pieces,
        L.symmPathRead_comp, factorWordProd_append,
        factorWordProd, separatedMap_symmRunTag, ih]

/--
@isnad1 id=ne.1h7v.s6.eaf83e41d655 from=translated src=- shape=8bc15c14 vocab=ea028b0f
-/
theorem SymmRunChain.pieces_ne_nil_of_path_ne_nil
    {a b : Symmetrify V} (c : SymmRunChain L a b)
    (hpath : c.path.length ≠ 0) :
    c.pieces ≠ [] := by
  cases c with
  | nil => simp [SymmRunChain.path] at hpath
  | cons r rest => simp [SymmRunChain.pieces]

/--
@isnad1 id=ex.1h8v.s7.c8cb1522c616 from=translated src=- shape=70379fcc vocab=b8f91d7f
-/
theorem SymmRunChain.exists_path_split_at_run
    {a b : Symmetrify V} (c : SymmRunChain L a b)
    {r : SymmRunPiece L} (hr : r ∈ c.pieces) :
    ∃ p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a r.source,
      ∃ q : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _)
        r.target b,
        c.path = p.comp (r.path.comp q) := by
  induction c with
  | nil => simp [SymmRunChain.pieces] at hr
  | cons r₀ rest ih =>
      have hr' : r ∈ rest.pieces ∨ r = r₀ := by
        simpa [SymmRunChain.pieces] using hr
      rcases hr' with hr' | rfl
      · obtain ⟨p, q, hsplit⟩ := ih hr'
        refine ⟨p, q.comp r₀.path, ?_⟩
        simp [SymmRunChain.path, hsplit, Path.comp_assoc]
      · refine ⟨SymmRunChain.path L rest, Path.nil, ?_⟩
        simp [SymmRunChain.path, Path.comp_assoc]

/--
@isnad1 id=ex.4h8v.s9.8dd35d3bf33c from=translated src=- shape=be0081f0 vocab=7c7de7bf
-/
theorem exists_shorter_null_path_of_null_loop_run
    {a b : Symmetrify V} (c : SymmRunChain L a b)
    {r : SymmRunPiece L} (hr : r ∈ c.pieces)
    (hloop : r.source = r.target)
    (hread_r : L.symmPathRead r.path = 1)
    (hread_c : L.symmPathRead c.path = 1) :
    ∃ p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b,
      L.symmPathRead p = 1 ∧ p.length < c.path.length := by
  obtain ⟨p, q, hsplit⟩ :=
    SymmRunChain.exists_path_split_at_run L c hr
  let q' := q.cast hloop.symm rfl
  refine ⟨p.comp q', ?_, ?_⟩
  · calc
      L.symmPathRead (p.comp q') =
          L.symmPathRead p * L.symmPathRead q' :=
        L.symmPathRead_comp p q'
      _ = L.symmPathRead p * L.symmPathRead q := by
        rw [show L.symmPathRead q' = L.symmPathRead q by
          simpa [q'] using L.symmPathRead_cast hloop.symm rfl q]
      _ = L.symmPathRead p *
          (L.symmPathRead r.path * L.symmPathRead q) := by
        rw [hread_r]
        simp
      _ = L.symmPathRead c.path := by
        rw [hsplit, L.symmPathRead_comp, L.symmPathRead_comp]
      _ = 1 := hread_c
  · have hpos : 0 < r.path.length := Nat.pos_of_ne_zero r.nonempty
    have hqlength : q'.length = q.length := by
      simpa [q'] using path_length_cast hloop.symm rfl q
    rw [Quiver.Path.length_comp, hqlength, hsplit,
      Quiver.Path.length_comp, Quiver.Path.length_comp]
    omega

/--
@isnad1 id=ex.3h7v.s8.1135abd61ff2 from=translated src=- shape=14a9ad26 vocab=35ca70ed
-/
theorem exists_null_piece_of_null_chain
    {a b : Symmetrify V} (c : SymmRunChain L a b)
    (hcolors : c.colors.IsChain (fun x y : Bool => x ≠ y))
    (hpieces : c.pieces ≠ [])
    (hread : L.symmPathRead c.path = 1) :
    ∃ r ∈ c.pieces, L.symmPathRead r.path = 1 := by
  by_contra h
  have hpiece_ne : ∀ r ∈ c.pieces, L.symmPathRead r.path ≠ 1 := by
    intro r hr hzero
    exact h ⟨r, hr, hzero⟩
  have htag_ne : ∀ z ∈ c.pieces.map L.symmRunTag,
      z ≠ Sum.inl 1 ∧ z ≠ Sum.inr 1 := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    constructor
    · intro htag
      apply hpiece_ne r hr
      rw [← separatedMap_symmRunTag, htag]
      simp [separatedMap]
    · intro htag
      apply hpiece_ne r hr
      rw [← separatedMap_symmRunTag, htag]
      simp [separatedMap]
  have htags : c.pieces.map L.symmRunTag ≠ [] := by
    simpa using hpieces
  have hprod_ne :
    factorWordProd (G := G) (H := H)
        (c.pieces.map L.symmRunTag) ≠ 1 :=
    factorWordProd_ne_one_of_reduced htag_ne
      (SymmRunChain.tags_isChain L c hcolors) htags
  apply hprod_ne
  rw [← SymmRunChain.pathRead_eq_factorWordProd_tags L c]
  exact hread

structure SymmRunDecomposition {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) where
  chain : SymmRunChain L a b
  path_eq : chain.path = p
  alternating : (chain.colors).IsChain (fun x y => x ≠ y)

def symmRunDecomposition {a b : Symmetrify V} :
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) →
      SymmRunDecomposition (L := L) p
  | Path.nil =>
      { chain := SymmRunChain.nil a
        path_eq := by simp [SymmRunChain.path]
        alternating := by simp [SymmRunChain.colors] }
  | Path.cons p e => by
      let d : SymmRunDecomposition (L := L) p := symmRunDecomposition p
      obtain ⟨chain, hpath, halt⟩ := d
      cases chain with
      | nil =>
          let r := SymmRunPiece.single (L := L) e
          have hp : p = Path.nil := by
            simpa [SymmRunChain.path] using hpath.symm
          subst p
          exact
            { chain := SymmRunChain.cons r (SymmRunChain.nil a)
              path_eq := by
                simp [SymmRunChain.path, r, SymmRunPiece.single]
              alternating := by
                simpa only [SymmRunChain.colors] using
                  (List.isChain_singleton (R := fun x y : Bool => x ≠ y)
                    r.color) }
      | cons r rest =>
          by_cases hcolor :
              binarySumIndex (G := G) (H := H) (L.symmLabel e) = r.color
          · let r' := SymmRunPiece.extend L r e hcolor
            exact
              { chain := SymmRunChain.cons r' rest
                path_eq := by
                  simpa [SymmRunChain.path, r', SymmRunPiece.extend] using
                    congrArg (fun q => q.cons e) hpath
                alternating := by
                  simpa [SymmRunChain.colors, r', SymmRunPiece.extend]
                    using halt }
          · let s := SymmRunPiece.single L e
            exact
              { chain := SymmRunChain.cons s (SymmRunChain.cons r rest)
                path_eq := by
                  simpa [SymmRunChain.path, s, SymmRunPiece.single] using
                    congrArg (fun q => q.cons e) hpath
                alternating := by
                  simp only [SymmRunChain.colors]
                  exact List.isChain_cons_cons.mpr
                    ⟨hcolor, by simpa only [SymmRunChain.colors] using halt⟩ }
  termination_by p => p.length
  decreasing_by
    simp_wf

/--
@isnad1 id=ex.2h7v.s8.db3bf12fc3fe from=translated src=- shape=488e044e vocab=5b1116ec
-/
theorem exists_null_monochromatic_run_of_null_path
    {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b)
    (hp : p.length ≠ 0)
    (hread : L.symmPathRead p = 1) :
    ∃ r ∈ (symmRunDecomposition (L := L) p).chain.pieces,
      L.symmPathRead r.path = 1 := by
  let d := symmRunDecomposition (L := L) p
  have hpieces : d.chain.pieces ≠ [] := by
    apply SymmRunChain.pieces_ne_nil_of_path_ne_nil L d.chain
    rw [d.path_eq]
    exact hp
  have hchainread : L.symmPathRead d.chain.path = 1 := by
    rw [d.path_eq]
    exact hread
  obtain ⟨r, hr, hrread⟩ :=
    exists_null_piece_of_null_chain L d.chain d.alternating hpieces hchainread
  exact ⟨r, hr, hrread⟩

/--
@isnad1 id=ex.1h4v.s6.7f29c28487f8 from=translated src=- shape=374d8cb0 vocab=dfd80b94
-/
theorem exists_first_edge_comp
    {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b)
    (hp : p.length ≠ 0) :
    ∃ c : Symmetrify V,
      ∃ e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a c,
        ∃ q : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) c b,
          p = e.toPath.comp q := by
  induction p with
  | nil => simp at hp
  | cons p e ih =>
      by_cases hzero : p.length = 0
      · have hend := Path.eq_of_length_zero p hzero
        cases hend
        have hnil : p = Path.nil := Path.eq_nil_of_length_zero p hzero
        subst p
        refine ⟨_, e, Path.nil, ?_⟩
        rfl
      · obtain ⟨c, f, q, hpq⟩ := ih hzero
        refine ⟨c, f, q.comp e.toPath, ?_⟩
        rw [← Path.comp_toPath_eq_cons, ← Path.comp_assoc, hpq]

/--
@isnad1 id=ex.3h7v.s9.25971c214ad6 from=translated src=- shape=78f3c45a vocab=5a5d3531
-/
theorem exists_null_nonloop_run_of_minimal_null_path
    {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b)
    (hp : p.length ≠ 0)
    (hread : L.symmPathRead p = 1)
    (hminimal : ∀ q : @Quiver.Path (Symmetrify V)
        (@Quiver.symmetrifyQuiver V _) a b,
        L.symmPathRead q = 1 → ¬ q.length < p.length) :
    ∃ r ∈ (symmRunDecomposition (L := L) p).chain.pieces,
      L.symmPathRead r.path = 1 ∧ r.source ≠ r.target := by
  let d := symmRunDecomposition (L := L) p
  have hpieces : d.chain.pieces ≠ [] := by
    apply SymmRunChain.pieces_ne_nil_of_path_ne_nil L d.chain
    rw [d.path_eq]
    exact hp
  have hchainread : L.symmPathRead d.chain.path = 1 := by
    rw [d.path_eq]
    exact hread
  obtain ⟨r, hr, hrread⟩ :=
    exists_null_piece_of_null_chain L d.chain d.alternating hpieces hchainread
  refine ⟨r, ?_, hrread, ?_⟩
  · simpa [d] using hr
  · intro hloop
    obtain ⟨q, hqread, hqlength⟩ :=
      exists_shorter_null_path_of_null_loop_run L d.chain hr hloop
        hrread hchainread
    apply hminimal q hqread
    rw [← d.path_eq]
    exact hqlength

/--
@isnad1 id=eq.0h7v.s6.d99690fce703 from=translated src=- shape=bf931a0a vocab=d855bb4a
-/
theorem pathLabels_reverse {a b : V} (p : Path a b) :
    L.pathLabels p.reverse =
      (L.pathLabels p).reverse.map (factorWordInv (G := G) (H := H)) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [Path.reverse, pathLabels_comp]
      rw [pathLabels_toPath, L.reverse_label]
      simp [pathLabels, ih]

/--
@isnad1 id=eq.0h7v.s6.43e16d870ff7 from=translated src=- shape=8a0aa5cc vocab=e681249f
-/
theorem pathRead_reverse {a b : V} (p : Path a b) :
    L.pathRead p.reverse = (L.pathRead p)⁻¹ := by
  simp only [pathRead, pathLabels_reverse, factorWordProd_reverse_inv]

/--
@isnad1 id=ismonoch.1h8v.s6.3b1ad39ebfde from=translated src=- shape=d9f384ff vocab=6b6edc40
-/
theorem isMonochromatic_reverse {a b : V} {p : Path a b} {color : Bool}
    (hp : L.IsMonochromatic p color) :
    L.IsMonochromatic p.reverse color := by
  intro z hz
  rw [pathLabels_reverse] at hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  simp only [binarySumIndex_factorWordInv]
  exact hp y (by simpa using hy)

/--
@isnad1 id=ex.1h7v.s7.5b261343308e from=translated src=- shape=a728b25b vocab=e13fc6cb
-/
theorem pathRead_mono_false {a b : V} {p : Path a b}
    (hp : L.IsMonochromatic p false) :
    ∃ g : G, L.pathRead p = Monoid.Coprod.inl g := by
  obtain ⟨l, hl⟩ := exists_map_inl_of_idx_false (G := G) (H := H)
    (by simpa [IsMonochromatic] using hp)
  refine ⟨l.prod, ?_⟩
  rw [pathRead, hl, factorWordProd_map_inl]

/--
@isnad1 id=ex.1h7v.s7.de9c4b3d582a from=translated src=- shape=9ef768b2 vocab=addf3ea8
-/
theorem pathRead_mono_true {a b : V} {p : Path a b}
    (hp : L.IsMonochromatic p true) :
    ∃ h : H, L.pathRead p = Monoid.Coprod.inr h := by
  obtain ⟨l, hl⟩ := exists_map_inr_of_idx_true (G := G) (H := H)
    (by simpa [IsMonochromatic] using hp)
  refine ⟨l.prod, ?_⟩
  rw [pathRead, hl, factorWordProd_map_inr]

/-! ### Marked loop moves

The fundamental-group part of a fold changes a marked family of based loops by
permuting loops, reversing a loop, or concatenating two loops.  These are the
path-level counterparts of the algebraic Nielsen generators. -/

inductive LoopNielsenStep {b : V} {n : ℕ}
    (x y : Fin n → Path b b) : Prop
  | perm (e : Fin n ≃ Fin n) (h : y = x ∘ e) : LoopNielsenStep x y
  | invert (i : Fin n) (h : y = Function.update x i (x i).reverse) :
      LoopNielsenStep x y
  | mulRight (i j : Fin n) (hij : i ≠ j)
      (h : y = Function.update x i ((x i).comp (x j))) :
      LoopNielsenStep x y

def LoopNielsenEquivalent {b : V} {n : ℕ}
    (x y : Fin n → Path b b) : Prop :=
  Relation.ReflTransGen (fun u v : Fin n → Path b b => LoopNielsenStep u v) x y

def loopRead {b : V} {n : ℕ} (x : Fin n → Path b b) : Fin n → G ∗ H :=
  fun i => L.pathRead (x i)

/--
@isnad1 id=nielsens.1h8v.s6.7ebd4e402b8e from=translated src=- shape=93757e8e vocab=fde51d45
-/
theorem loopNielsenStep_read {b : V} {n : ℕ}
    {x y : Fin n → Path b b} (h : LoopNielsenStep x y) :
    NielsenStep (L.loopRead x) (L.loopRead y) := by
  cases h with
  | perm e hEq =>
      apply NielsenStep.perm e
      rw [hEq]
      rfl
  | invert i hEq =>
      apply NielsenStep.invert i
      funext k
      by_cases hki : k = i
      · subst k
        simp [hEq, loopRead, pathRead_reverse]
      · simp [hEq, loopRead, hki]
  | mulRight i j hij hEq =>
      apply NielsenStep.mulRight i j hij
      funext k
      by_cases hki : k = i
      · subst k
        simp [hEq, loopRead, pathRead_comp]
      · simp [hEq, loopRead, hki]

/--
@isnad1 id=nielsene.1h8v.s6.76ee446f22ad from=translated src=- shape=93757e8e vocab=d72a083a
-/
theorem loopNielsenEquivalent_read {b : V} {n : ℕ}
    {x y : Fin n → Path b b} (h : LoopNielsenEquivalent x y) :
    NielsenEquivalent (L.loopRead x) (L.loopRead y) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | single hstep => exact Relation.ReflTransGen.single (loopNielsenStep_read L hstep)
  | trans h₁ h₂ ih₁ ih₂ => exact Relation.ReflTransGen.trans ih₁ ih₂

/--
@isnad1 id=eq.1h8v.s7.18c6858b5041 from=translated src=- shape=a0fff738 vocab=c69654b4
-/
theorem loopNielsenStep_read_closure_eq {b : V} {n : ℕ}
    {x y : Fin n → Path b b} (h : LoopNielsenStep x y) :
    Subgroup.closure (Set.range (L.loopRead x)) =
      Subgroup.closure (Set.range (L.loopRead y)) := by
  exact nielsenStep_closure_eq (loopNielsenStep_read L h)

/--
@isnad1 id=eq.1h8v.s7.2c53f29232ab from=translated src=- shape=a0fff738 vocab=26231cb3
-/
theorem loopNielsenEquivalent_read_closure_eq {b : V} {n : ℕ}
    {x y : Fin n → Path b b} (h : LoopNielsenEquivalent x y) :
    Subgroup.closure (Set.range (L.loopRead x)) =
      Subgroup.closure (Set.range (L.loopRead y)) := by
  exact nielsenEquivalent_closure_eq (loopNielsenEquivalent_read L h)

end BinaryLabelling

/-! ### A marked finite graph interface

The eventual fold induction acts on a connected finite graph together with a
finite marked family of based loops.  The definition below keeps the marking
separate from the fold operation: it records exactly the data needed to state
that the labelled loops generate the free product, while the path lemmas above
prove how that data behaves under a graph-level Nielsen move. -/

structure MarkedBinaryGraph (n : ℕ) where
  base : V
  labeling : BinaryLabelling (G := G) (H := H) (V := V)
  loops : Fin n → Path base base

namespace MarkedBinaryGraph

variable (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)

def read : Fin n → G ∗ H :=
  M.labeling.loopRead M.loops

def IsGenerating : Prop :=
  Subgroup.closure (Set.range M.read) = ⊤

def WeaklyConnected : Prop :=
  ∀ v : V, Nonempty (@Path (Symmetrify V) _ M.base v)

/--
@isnad1 id=nielsene.1h7v.s7.8117e37de229 from=translated src=- shape=4c20db9d vocab=da4f2e6b
-/
theorem read_nielsenEquivalent {x y : Fin n → Path M.base M.base}
    (h : BinaryLabelling.LoopNielsenEquivalent x y) :
    NielsenEquivalent (M.labeling.loopRead x) (M.labeling.loopRead y) := by
  exact M.labeling.loopNielsenEquivalent_read h

/--
@isnad1 id=eq.2h7v.s8.3db3b9105caa from=translated src=- shape=1750ec78 vocab=3f8732a4
-/
theorem generating_of_loopNielsenEquivalent
    {x y : Fin n → Path M.base M.base}
    (hx : Subgroup.closure (Set.range (M.labeling.loopRead x)) = ⊤)
    (h : BinaryLabelling.LoopNielsenEquivalent x y) :
    Subgroup.closure (Set.range (M.labeling.loopRead y)) = ⊤ := by
  rw [← M.labeling.loopNielsenEquivalent_read_closure_eq h]
  exact hx

/--
@isnad1 id=iff.0h5v.s7.d56db1213f8d from=translated src=- shape=c2d7c3d0 vocab=e570bb82
-/
theorem isGenerating_iff :
    M.IsGenerating ↔ Subgroup.closure (Set.range
      (M.labeling.loopRead M.loops)) = ⊤ :=
  Iff.rfl

/-! ### Paths representing the generated subgroup

The marked loops generate the target group, so every target element is read by
some based loop.  This is the small algebraic bridge needed to append a loop to
a path whose endpoints are different. -/

def loopReadSubgroup : Subgroup (G ∗ H) where
  carrier := {g | ∃ p : Path M.base M.base, M.labeling.pathRead p = g}
  one_mem' := by
    exact ⟨Path.nil, by simp⟩
  mul_mem' := by
    rintro g h ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨p.comp q, ?_⟩
    rw [M.labeling.pathRead_comp, hp, hq]
  inv_mem' := by
    rintro g ⟨p, hp⟩
    refine ⟨p.reverse, ?_⟩
    rw [M.labeling.pathRead_reverse, hp]

/--
@isnad1 id=mem.0h6v.s7.08539f4d3888 from=translated src=- shape=5b6cfb5a vocab=048f71f9
-/
theorem mem_loopReadSubgroup_of_marked (i : Fin n) :
    M.read i ∈ M.loopReadSubgroup := by
  exact ⟨M.loops i, rfl⟩

/--
@isnad1 id=ex.1h6v.s7.d9d206ef3a2f from=translated src=- shape=dff167ed vocab=6e2340ed
-/
theorem exists_loop_read (hM : M.IsGenerating) (g : G ∗ H) :
    ∃ p : Path M.base M.base, M.labeling.pathRead p = g := by
  have hsub : Subgroup.closure (Set.range M.read) ≤ M.loopReadSubgroup := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, rfl⟩
    exact M.mem_loopReadSubgroup_of_marked i
  have hg : g ∈ Subgroup.closure (Set.range M.read) := by
    rw [hM]
    trivial
  exact hsub hg

/--
@isnad1 id=ex.2h6v.s8.648f1174de5e from=translated src=- shape=88aa4b5a vocab=46f19569
-/
theorem exists_null_path (hM : M.IsGenerating) {v : V}
    (hv : Nonempty (@Path (Symmetrify V) _ M.base v)) :
    ∃ p : @Path (Symmetrify V) _ M.base v,
      M.labeling.symmPathRead p = 1 := by
  obtain ⟨p⟩ := hv
  obtain ⟨q, hq⟩ := M.exists_loop_read hM (M.labeling.symmPathRead p)⁻¹
  refine ⟨(@Quiver.Symmetrify.of V _).mapPath q |>.comp p, ?_⟩
  calc
    M.labeling.symmPathRead
        ((@Quiver.Symmetrify.of V _).mapPath q |>.comp p) =
      M.labeling.symmPathRead ((@Quiver.Symmetrify.of V _).mapPath q) *
        M.labeling.symmPathRead p :=
      M.labeling.symmPathRead_comp
        ((@Quiver.Symmetrify.of V _).mapPath q) p
    _ = M.labeling.pathRead q * M.labeling.symmPathRead p := by
      rw [M.labeling.symmPathRead_map_of]
    _ = 1 := by rw [hq]; simp

/--
@isnad1 id=ex.3h5v.s8.2a027b398536 from=translated src=- shape=2d64692f vocab=b586953b
-/
theorem exists_null_nonloop_path [Fintype V] (hgen : M.IsGenerating)
    (hconn : M.WeaklyConnected) (hcard : 1 < Fintype.card V) :
    ∃ v : V, v ≠ M.base ∧
      ∃ p : @Path (Symmetrify V) _ M.base v,
        M.labeling.symmPathRead p = 1 := by
  have hex : ∃ v : V, v ≠ M.base := by
    by_contra h
    have hall : ∀ v : V, v = M.base := by
      intro v
      by_contra hv
      exact h ⟨v, hv⟩
    letI : Subsingleton V := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have hle : Fintype.card V ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  obtain ⟨v, hv⟩ := hex
  obtain ⟨p⟩ := hconn v
  exact ⟨v, hv, exists_null_path M hgen ⟨p⟩ |>.choose,
    (exists_null_path M hgen ⟨p⟩).choose_spec⟩

/--
@isnad1 id=ex.3h5v.s8.9d9cfd6265de from=translated src=- shape=f13608ba vocab=ddebd83b
-/
theorem exists_minimal_null_nonloop_path [Fintype V]
    (hgen : M.IsGenerating) (hconn : M.WeaklyConnected)
    (hcard : 1 < Fintype.card V) :
    ∃ v : V, v ≠ M.base ∧
      ∃ p : @Path (Symmetrify V) _ M.base v,
        M.labeling.symmPathRead p = 1 ∧
        ∀ q : @Path (Symmetrify V) _ M.base v,
          M.labeling.symmPathRead q = 1 → ¬ q.length < p.length := by
  classical
  let good : ℕ → Prop := fun n =>
    ∃ v : V, v ≠ M.base ∧
      ∃ p : @Path (Symmetrify V) _ M.base v,
        p.length = n ∧ M.labeling.symmPathRead p = 1
  obtain ⟨v₀, hv₀, p₀, hp₀⟩ :=
    M.exists_null_nonloop_path hgen hconn hcard
  have hgood : ∃ n, good n := by
    refine ⟨p₀.length, v₀, hv₀, p₀, rfl, hp₀⟩
  obtain ⟨v, hv, p, hplen, hpread⟩ := by
    simpa [good] using Nat.find_spec hgood
  refine ⟨v, hv, p, hpread, ?_⟩
  intro q hq hlt
  have hlt' : q.length < Nat.find hgood := by
    rw [← hplen]
    exact hlt
  have hnot : ¬ good q.length := Nat.find_min hgood hlt'
  apply hnot
  exact ⟨v, hv, q, rfl, hq⟩

end MarkedBinaryGraph

end GeneralGrushko
end MarshallHall
