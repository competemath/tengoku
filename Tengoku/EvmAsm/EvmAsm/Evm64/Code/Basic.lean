/-
  EvmAsm.Evm64.Code.Basic

  Pure byte helpers for CODECOPY executable-spec bridges
  (GH #107 / GH #118).
-/

module

@[expose] public section
namespace EvmAsm.Evm64
namespace Code

/-- Byte offset of the M33 `codeSize` cell within the dispatcher env block.
    Both dispatcher prologues seed this with the exact running-bytecode length;
    CODESIZE, CODECOPY, and JUMP/JUMPI bounds checks read it.-/
def codeSizeOff : Nat := 496

/-- Read one byte from executable code, returning zero past the end.-/
def byte (code : List (BitVec 8)) (idx : Nat) : BitVec 8 :=
  if h : idx < code.length then code[idx] else 0

/-- Bytes written by CODECOPY:
    `size` bytes from `code` starting at `codeOffset`, with out-of-bounds
    reads producing zero. Distinctive token: Code.copyBytes #107 #118.-/
def copyBytes
    (code : List (BitVec 8)) (codeOffset size : Nat) : List (BitVec 8) :=
  (List.range size).map (fun i => byte code (codeOffset + i))

/--
@isnad1 id=eq.1h2v.s6.fb774a6ae72c from=translated src=- shape=537e03bc vocab=8728b714
-/
theorem byte_of_lt {code : List (BitVec 8)} {idx : Nat}
    (h : idx < code.length) :
    byte code idx = code[idx] := by
  simp [byte, h]

/--
@isnad1 id=eq.1h2v.s5.dadaa96fa4da from=translated src=- shape=e6661f4e vocab=4d946326
-/
theorem byte_of_ge {code : List (BitVec 8)} {idx : Nat}
    (h : code.length ≤ idx) :
    byte code idx = 0 := by
  simp [byte, show ¬idx < code.length from by omega]

/--
@isnad1 id=eq.0h1v.s5.e389c4dccb38 from=translated src=- shape=bb7fe741 vocab=92ee73e2
-/
@[simp] theorem byte_nil (idx : Nat) :
    byte [] idx = 0 := by
  exact byte_of_ge (code := []) (idx := idx) (by simp)

/--
@isnad1 id=eq.0h3v.s4.560a8dbbf4ac from=translated src=- shape=f4dcf33e vocab=94425aa8
-/
@[simp] theorem copyBytes_length
    (code : List (BitVec 8)) (codeOffset size : Nat) :
    (copyBytes code codeOffset size).length = size := by
  simp [copyBytes]

/--
@isnad1 id=eq.0h2v.s5.7efc24229d4e from=translated src=- shape=7d8017ca vocab=8c1ab9f5
-/
@[simp] theorem copyBytes_zero
    (code : List (BitVec 8)) (codeOffset : Nat) :
    copyBytes code codeOffset 0 = [] := by
  simp [copyBytes]

/--
@isnad1 id=eq.1h4v.s6.6032d12c8f19 from=translated src=- shape=32b007db vocab=7f7ddcea
-/
theorem copyBytes_get
    {code : List (BitVec 8)} {codeOffset size i : Nat}
    (h : i < size) :
    (copyBytes code codeOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = byte code (codeOffset + i) := by
  simp [copyBytes]

/--
@isnad1 id=eq.2h4v.s7.e048dbf95abe from=translated src=- shape=0b567736 vocab=de5b39a2
-/
theorem copyBytes_get_of_in_bounds
    {code : List (BitVec 8)} {codeOffset size i : Nat}
    (h : i < size)
    (hsrc : codeOffset + i < code.length) :
    (copyBytes code codeOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = code[codeOffset + i] := by
  rw [copyBytes_get h, byte_of_lt hsrc]

/--
@isnad1 id=eq.2h4v.s6.9a8c1ee6ef89 from=translated src=- shape=ed77eae0 vocab=3094278d
-/
theorem copyBytes_get_of_out_of_bounds
    {code : List (BitVec 8)} {codeOffset size i : Nat}
    (h : i < size)
    (hsrc : code.length ≤ codeOffset + i) :
    (copyBytes code codeOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = 0 := by
  rw [copyBytes_get h, byte_of_ge hsrc]

/--
@isnad1 id=eq.0h2v.s5.3c73aa5fa7ac from=translated src=- shape=a3ffc0a1 vocab=bcbc4ddd
-/
@[simp] theorem copyBytes_nil (codeOffset size : Nat) :
    copyBytes [] codeOffset size = List.replicate size 0 := by
  simp [copyBytes, List.map_const']

end Code
end EvmAsm.Evm64
