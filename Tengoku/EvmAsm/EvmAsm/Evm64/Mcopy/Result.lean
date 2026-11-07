/-
  EvmAsm.Evm64.Mcopy.Result

  Pure list model of the EVM `MCOPY` opcode (0x5e, EIP-5656) — the `memmove`
  reference semantics and the two per-direction loop-content abstractions.

  The reference (execution-specs `cancun/vm/instructions/memory.py::mcopy`) reads
  the ORIGINAL source bytes then writes them at the destination:
  `mcopyResult mem destOff srcOff len` is `mem` with the window
  `[destOff, destOff+len)` overwritten by `mem[srcOff, srcOff+len)`. The result
  is direction-independent; the runtime just picks a copy order that preserves
  the source while copying.

  The forward (low→high) and backward (high→low) loops each maintain their own
  evolving content:

    * `mcopyFwdContent mem copied destOff i` — `mem` with `[destOff, destOff+i)`
      overwritten by the first `i` bytes of `copied` (the source slice).
    * `mcopyBwdContent mem copied destOff len k` — `mem` with the suffix window
      `[destOff+len-k, destOff+len)` overwritten by the last `k` bytes of
      `copied`.

  Each direction has an element characterization (`_getElem`), the `_zero` /
  `_set` / `_full` window-progress lemmas, and a *read-sees-original* lemma
  (`_getElem_src`): in the direction the runtime chose, the next byte read still
  holds the original source value. These are the pure ingredients the loop specs
  (`ForwardLoopSpec` / `BackwardLoopSpec`) consume.
-/

module

public import Tengoku.Seed.Data.List.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.Evm64
namespace Mcopy

variable {α : Type _}

/-- The `memmove` result: `mem` with `[destOff, destOff+len)` overwritten by the
    original source slice `mem[srcOff, srcOff+len)`.-/
def mcopyResult (mem : List α) (destOff srcOff len : Nat) : List α :=
  mem.take destOff ++ (mem.drop srcOff).take len ++ mem.drop (destOff + len)

/-- Forward-loop content after `i` bytes copied low→high.-/
def mcopyFwdContent (mem copied : List α) (destOff i : Nat) : List α :=
  mem.take destOff ++ copied.take i ++ mem.drop (destOff + i)

/-- Backward-loop content after `k` bytes copied high→low.-/
def mcopyBwdContent (mem copied : List α) (destOff len k : Nat) : List α :=
  mem.take (destOff + len - k) ++ copied.drop (len - k) ++ mem.drop (destOff + len)

/-- Element `i` of the source slice `(mem.drop srcOff).take len` is the original
    byte `mem[srcOff+i]`.
@isnad1 id=eq.2h5v.s6.8b36ac3b745f from=translated src=- shape=0269f81e vocab=6b5e11af
-/
theorem sourceSlice_getElem (mem : List α) (srcOff len i : Nat)
    (h_i : i < len) (h_fits : srcOff + len ≤ mem.length) :
    ((mem.drop srcOff).take len)[i]'(by rw [List.length_take, List.length_drop]; omega)
      = mem[srcOff + i]'(by omega) := by
  rw [List.getElem_take, List.getElem_drop]

/-! ## Forward content -/

/--
@isnad1 id=eq.2h5v.s5.c7d7d0210e2d from=translated src=- shape=f269647e vocab=24f28581
-/
theorem mcopyFwdContent_length (mem copied : List α) (destOff i : Nat)
    (h_i : i ≤ copied.length) (h_win : destOff + copied.length ≤ mem.length) :
    (mcopyFwdContent mem copied destOff i).length = mem.length := by
  simp only [mcopyFwdContent, List.length_append, List.length_take,
    List.length_drop]
  omega

/-- Element characterization of the forward content: index `j` reads the copied
    slice inside the written window `[destOff, destOff+i)` (at `copied[j-destOff]`)
    and the original `mem` elsewhere.
@isnad1 id=eq.3h6v.s7.3e768bd43649 from=translated src=- shape=0abb7aab vocab=8bca48fa
-/
theorem mcopyFwdContent_getElem (mem copied : List α) (destOff i j : Nat)
    (h_i : i ≤ copied.length) (h_win : destOff + copied.length ≤ mem.length)
    (hj : j < mem.length) :
    (mcopyFwdContent mem copied destOff i)[j]'(by
        rw [mcopyFwdContent_length mem copied destOff i h_i h_win]; exact hj)
      = if h : destOff ≤ j ∧ j < destOff + i
        then copied[j - destOff]'(by omega) else mem[j] := by
  have htk : (mem.take destOff).length = destOff := by rw [List.length_take]; omega
  have hcp : (copied.take i).length = i := by rw [List.length_take]; omega
  simp only [mcopyFwdContent, List.append_assoc]
  by_cases h : destOff ≤ j ∧ j < destOff + i
  · rw [dite_eq_left h]
    obtain ⟨h1, h2⟩ := h
    rw [List.getElem_append_right (by rw [htk]; omega),
        List.getElem_append_left (by rw [hcp]; omega),
        List.getElem_take]
    congr 1
    omega
  · rw [dite_eq_right h]
    by_cases h1 : j < destOff
    · rw [List.getElem_append_left (by rw [htk]; omega), List.getElem_take]
    · have h2 : destOff + i ≤ j := by omega
      rw [List.getElem_append_right (by rw [htk]; omega),
          List.getElem_append_right (by rw [hcp]; omega),
          List.getElem_drop]
      congr 1
      omega

/-- At `i = 0` the forward content is untouched.
@isnad1 id=eq.1h4v.s5.d37e32d53022 from=translated src=- shape=f08b921c vocab=24f28581
-/
theorem mcopyFwdContent_zero (mem copied : List α) (destOff : Nat)
    (h_win : destOff + copied.length ≤ mem.length) :
    mcopyFwdContent mem copied destOff 0 = mem := by
  apply List.ext_getElem
  · rw [mcopyFwdContent_length mem copied destOff 0 (by omega) h_win]
  · intro j hj _
    have hjm : j < mem.length := by
      rw [mcopyFwdContent_length mem copied destOff 0 (by omega) h_win] at hj; exact hj
    rw [mcopyFwdContent_getElem mem copied destOff 0 j (by omega) h_win hjm, dite_eq_right (by omega)]

/-- At `i = copied.length` the forward window holds all of `copied`.
@isnad1 id=eq.0h4v.s6.b594081c3276 from=translated src=- shape=4e319d52 vocab=3a267bce
-/
theorem mcopyFwdContent_full (mem copied : List α) (destOff : Nat) :
    mcopyFwdContent mem copied destOff copied.length
      = mem.take destOff ++ copied ++ mem.drop (destOff + copied.length) := by
  simp only [mcopyFwdContent, List.take_length]

/-- Writing `copied[i]` at index `destOff+i` advances the forward window from the
    `i`-prefix to the `(i+1)`-prefix.
@isnad1 id=eq.3h6v.s6.efe4f7647afa from=translated src=- shape=d5bff8fd vocab=773bb3e5
-/
theorem mcopyFwdContent_set (mem copied : List α) (destOff i : Nat) (v : α)
    (h_i : i < copied.length) (h_win : destOff + copied.length ≤ mem.length)
    (h_v : v = copied[i]) :
    (mcopyFwdContent mem copied destOff i).set (destOff + i) v
      = mcopyFwdContent mem copied destOff (i + 1) := by
  apply List.ext_getElem
  · rw [List.length_set, mcopyFwdContent_length mem copied destOff i (by omega) h_win,
        mcopyFwdContent_length mem copied destOff (i + 1) (by omega) h_win]
  · intro j hj _
    have hjm : j < mem.length := by
      rw [List.length_set,
          mcopyFwdContent_length mem copied destOff i (by omega) h_win] at hj
      exact hj
    rw [mcopyFwdContent_getElem mem copied destOff (i + 1) j (by omega) h_win hjm]
    by_cases h_eq : destOff + i = j
    · subst h_eq
      rw [List.getElem_set_self, dite_eq_left (by omega), h_v]
      congr 1
      omega
    · rw [List.getElem_set_ne h_eq,
          mcopyFwdContent_getElem mem copied destOff i j (by omega) h_win hjm]
      by_cases hin : destOff ≤ j ∧ j < destOff + i
      · rw [dite_eq_left hin, dite_eq_left (by omega)]
      · rw [dite_eq_right hin]
        by_cases hin1 : destOff ≤ j ∧ j < destOff + (i + 1)
        · exfalso; exact h_eq (by omega)
        · rw [dite_eq_right hin1]

/-- **Forward read-sees-original.** When the runtime chose the forward loop —
    `destOff ≤ srcOff` (dest at/before src) or `srcOff + len ≤ destOff`
    (disjoint) — the byte at source index `srcOff+i` in the `i`-step forward
    content is still the original `mem[srcOff+i]`.
@isnad1 id=eq.5h7v.s7.35abf164aee2 from=translated src=- shape=1644b760 vocab=9787fb37
-/
theorem mcopyFwdContent_getElem_src (mem copied : List α) (destOff srcOff len i : Nat)
    (h_i : i < len) (h_clen : copied.length = len)
    (h_win : destOff + len ≤ mem.length) (h_sfits : srcOff + len ≤ mem.length)
    (h_fwd : destOff ≤ srcOff ∨ srcOff + len ≤ destOff) :
    (mcopyFwdContent mem copied destOff i)[srcOff + i]'(by
        rw [mcopyFwdContent_length mem copied destOff i (by omega) (by omega)]; omega)
      = mem[srcOff + i]'(by omega) := by
  rw [mcopyFwdContent_getElem mem copied destOff i (srcOff + i) (by omega) (by omega) (by omega)]
  rcases h_fwd with h | h
  · rw [dite_eq_right (by omega)]
  · rw [dite_eq_right (by omega)]

/-! ## Backward content -/

/--
@isnad1 id=eq.3h6v.s5.da29b6984095 from=translated src=- shape=d5b4fdbc vocab=9ddeea61
-/
theorem mcopyBwdContent_length (mem copied : List α) (destOff len k : Nat)
    (h_k : k ≤ len) (h_clen : copied.length = len)
    (h_win : destOff + len ≤ mem.length) :
    (mcopyBwdContent mem copied destOff len k).length = mem.length := by
  simp only [mcopyBwdContent, List.length_append, List.length_take,
    List.length_drop, h_clen]
  omega

/-- Element characterization of the backward content: index `j` reads the copied
    slice inside the written suffix window `[destOff+len-k, destOff+len)` (at
    `copied[j-destOff]`) and the original `mem` elsewhere.
@isnad1 id=eq.4h7v.s8.f2a7fef4e54f from=translated src=- shape=9f1a30f8 vocab=2f043344
-/
theorem mcopyBwdContent_getElem (mem copied : List α) (destOff len k j : Nat)
    (h_k : k ≤ len) (h_clen : copied.length = len)
    (h_win : destOff + len ≤ mem.length) (hj : j < mem.length) :
    (mcopyBwdContent mem copied destOff len k)[j]'(by
        rw [mcopyBwdContent_length mem copied destOff len k h_k h_clen h_win]; exact hj)
      = if h : destOff + len - k ≤ j ∧ j < destOff + len
        then copied[j - destOff]'(by omega) else mem[j] := by
  have htk : (mem.take (destOff + len - k)).length = destOff + len - k := by
    rw [List.length_take]; omega
  have hdr : (copied.drop (len - k)).length = k := by rw [List.length_drop]; omega
  simp only [mcopyBwdContent, List.append_assoc]
  by_cases h : destOff + len - k ≤ j ∧ j < destOff + len
  · rw [dite_eq_left h]
    obtain ⟨h1, h2⟩ := h
    rw [List.getElem_append_right (by rw [htk]; omega),
        List.getElem_append_left (by rw [hdr]; omega),
        List.getElem_drop]
    congr 1
    omega
  · rw [dite_eq_right h]
    by_cases h1 : j < destOff + len - k
    · rw [List.getElem_append_left (by rw [htk]; omega), List.getElem_take]
    · have h2 : destOff + len ≤ j := by omega
      rw [List.getElem_append_right (by rw [htk]; omega),
          List.getElem_append_right (by rw [hdr]; omega),
          List.getElem_drop]
      congr 1
      omega

/-- At `k = 0` the backward content is untouched.
@isnad1 id=eq.2h5v.s5.b5f65974722b from=translated src=- shape=adbeb012 vocab=9ddeea61
-/
theorem mcopyBwdContent_zero (mem copied : List α) (destOff len : Nat)
    (h_clen : copied.length = len) (h_win : destOff + len ≤ mem.length) :
    mcopyBwdContent mem copied destOff len 0 = mem := by
  apply List.ext_getElem
  · rw [mcopyBwdContent_length mem copied destOff len 0 (by omega) h_clen h_win]
  · intro j hj _
    have hjm : j < mem.length := by
      rw [mcopyBwdContent_length mem copied destOff len 0 (by omega) h_clen h_win] at hj
      exact hj
    rw [mcopyBwdContent_getElem mem copied destOff len 0 j (by omega) h_clen h_win hjm,
        dite_eq_right (by omega)]

/-- At `k = len` the backward window holds all of `copied`.
@isnad1 id=eq.0h5v.s5.cb8270712650 from=translated src=- shape=c6321ee5 vocab=fe4d4049
-/
theorem mcopyBwdContent_full (mem copied : List α) (destOff len : Nat) :
    mcopyBwdContent mem copied destOff len len
      = mem.take destOff ++ copied ++ mem.drop (destOff + len) := by
  simp only [mcopyBwdContent, Nat.sub_self, List.drop_zero, Nat.add_sub_cancel]

/-- Writing `copied[len-1-k]` at index `destOff+len-1-k` advances the backward
    window from the `k`-suffix to the `(k+1)`-suffix.
@isnad1 id=eq.4h7v.s7.5b7003c291ce from=translated src=- shape=c140a5a6 vocab=9953fcfe
-/
theorem mcopyBwdContent_set (mem copied : List α) (destOff len k : Nat) (v : α)
    (h_k : k < len) (h_clen : copied.length = len)
    (h_win : destOff + len ≤ mem.length) (h_v : v = copied[len - 1 - k]'(by omega)) :
    (mcopyBwdContent mem copied destOff len k).set (destOff + len - 1 - k) v
      = mcopyBwdContent mem copied destOff len (k + 1) := by
  apply List.ext_getElem
  · rw [List.length_set,
        mcopyBwdContent_length mem copied destOff len k (by omega) h_clen h_win,
        mcopyBwdContent_length mem copied destOff len (k + 1) (by omega) h_clen h_win]
  · intro j hj _
    have hjm : j < mem.length := by
      rw [List.length_set,
          mcopyBwdContent_length mem copied destOff len k (by omega) h_clen h_win] at hj
      exact hj
    rw [mcopyBwdContent_getElem mem copied destOff len (k + 1) j (by omega) h_clen h_win hjm]
    by_cases h_eq : destOff + len - 1 - k = j
    · subst h_eq
      rw [List.getElem_set_self, dite_eq_left (by omega), h_v]
      congr 1
      omega
    · rw [List.getElem_set_ne h_eq,
          mcopyBwdContent_getElem mem copied destOff len k j (by omega) h_clen h_win hjm]
      by_cases hk : destOff + len - k ≤ j ∧ j < destOff + len
      · rw [dite_eq_left hk, dite_eq_left (by omega)]
      · rw [dite_eq_right hk]
        by_cases hk1 : destOff + len - (k + 1) ≤ j ∧ j < destOff + len
        · exfalso; exact h_eq (by omega)
        · rw [dite_eq_right hk1]

/-- **Backward read-sees-original.** When the runtime chose the backward loop —
    `srcOff < destOff` (dest strictly after src, the genuine forward-overlap
    case; here `srcOff ≤ destOff` suffices) — the byte at source index
    `srcOff+len-1-k` in the `k`-step backward content is still the original
    `mem[srcOff+len-1-k]`.
@isnad1 id=eq.5h7v.s7.2ad3722a3a0b from=translated src=- shape=8e76f601 vocab=88176877
-/
theorem mcopyBwdContent_getElem_src (mem copied : List α) (destOff srcOff len k : Nat)
    (h_k : k < len) (h_clen : copied.length = len)
    (h_win : destOff + len ≤ mem.length) (h_sfits : srcOff + len ≤ mem.length)
    (h_bwd : srcOff ≤ destOff) :
    (mcopyBwdContent mem copied destOff len k)[srcOff + len - 1 - k]'(by
        rw [mcopyBwdContent_length mem copied destOff len k (by omega) h_clen h_win]; omega)
      = mem[srcOff + len - 1 - k]'(by omega) := by
  rw [mcopyBwdContent_getElem mem copied destOff len k (srcOff + len - 1 - k)
        (by omega) h_clen h_win (by omega),
      dite_eq_right (by omega)]

/-! ## Reference result -/

/--
@isnad1 id=eq.0h5v.s6.72cb80a2826c from=translated src=- shape=6c3b45e7 vocab=d72319b6
-/
theorem mcopyResult_eq (mem : List α) (destOff srcOff len : Nat) :
    mcopyResult mem destOff srcOff len
      = mem.take destOff ++ (mem.drop srcOff).take len ++ mem.drop (destOff + len) :=
  rfl

/-- The memmove result preserves the buffer length.
@isnad1 id=eq.2h5v.s5.84a4ebdf64f3 from=translated src=- shape=c70eac89 vocab=ed18da35
-/
theorem mcopyResult_length (mem : List α) (destOff srcOff len : Nat)
    (h_win : destOff + len ≤ mem.length) (h_sfits : srcOff + len ≤ mem.length) :
    (mcopyResult mem destOff srcOff len).length = mem.length := by
  simp only [mcopyResult, List.length_append, List.length_take, List.length_drop]
  omega

/-- Both directions land on `mcopyResult` once `copied` is the source slice:
    the shared full-window shape equals `mcopyResult`.
@isnad1 id=eq.1h6v.s6.f31853bb0f6e from=translated src=- shape=de7802f5 vocab=d72319b6
-/
theorem full_eq_mcopyResult (mem copied : List α) (destOff srcOff len : Nat)
    (h_copied : copied = (mem.drop srcOff).take len) :
    mem.take destOff ++ copied ++ mem.drop (destOff + len)
      = mcopyResult mem destOff srcOff len := by
  rw [h_copied, mcopyResult]

/-- Forward loop endpoint (`i = len`) is `mcopyResult`.
@isnad1 id=eq.2h6v.s5.569f47bebd88 from=translated src=- shape=05386836 vocab=94b37656
-/
theorem mcopyFwdContent_result (mem copied : List α) (destOff srcOff len : Nat)
    (hclen : copied.length = len) (h_copied : copied = (mem.drop srcOff).take len) :
    mcopyFwdContent mem copied destOff len = mcopyResult mem destOff srcOff len := by
  have htk : copied.take len = copied := by rw [← hclen]; exact List.take_length
  rw [mcopyFwdContent, htk]
  exact full_eq_mcopyResult mem copied destOff srcOff len h_copied

/-- Backward loop endpoint (`k = len`) is `mcopyResult`.
@isnad1 id=eq.1h6v.s5.cd9b22ddb538 from=translated src=- shape=d578cdc9 vocab=c201d290
-/
theorem mcopyBwdContent_result (mem copied : List α) (destOff srcOff len : Nat)
    (h_copied : copied = (mem.drop srcOff).take len) :
    mcopyBwdContent mem copied destOff len len = mcopyResult mem destOff srcOff len := by
  rw [mcopyBwdContent_full]
  exact full_eq_mcopyResult mem copied destOff srcOff len h_copied

end Mcopy
end EvmAsm.Evm64
