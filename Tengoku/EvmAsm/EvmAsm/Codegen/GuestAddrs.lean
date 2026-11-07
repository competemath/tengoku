/-
  EvmAsm.Codegen.GuestAddrs

  GENERATED — do not edit by hand.
  `python3 scripts/asm_to_program.py guest-addrs` regenerates this from
  `scripts/asm-fixtures/symbol-addresses.tsv` (the linker-facts table of
  bead evm-asm-4ch8f.6). One `Nat` constant per guest symbol that a
  converted `_prog` references — function entries (the `pc` base for a
  `la`/`jal` immediate) and `la`/cross-`jal` targets (data arenas, tables,
  callee entries).

  This is the SINGLE file that churns on guest layout drift: the per-
  function `_prog` defs reference these constants by name via
  `AsmReloc.{laHi,laLo,jalOff}`, so a `.text`/`.data` size change only
  requires regenerating the TSV + this file, never the 100s of `_prog`s.
  Guarded by `scripts/check-asm-to-program.sh` (regenerate + diff).

  Addresses are LINK_DEPENDENT (move on any layout change); the trusted
  arbiter that they are correct is the whole-guest byte-identity gate.
-/

module

@[expose] public section
namespace EvmAsm.Codegen.GuestAddrs

def bal_account_has_state_change : Nat := 0x8000e01c
def bal_account_nonstorage_finals : Nat := 0x800265b0
def bav_hash : Nat := 0xa9e8655c
def bloom_add_value : Nat := 0x80014d58
def blsg_lt_p : Nat := 0x80033d5c
def call_frame_arena : Nat := 0xabf6dc00
def frame_base : Nat := 0x8003c6ec
def mpt_delete_walk_db : Nat := 0x800073fc
def mpt_set_record_walk_db : Nat := 0x80006e10
def priority_fee_per_gas_eip1559 : Nat := 0x80027140
def rlp_content_to_u256_be : Nat := 0x80005368
def rlp_content_to_u64 : Nat := 0x80005320
def rlp_walk_init : Nat := 0x80004c18
def rlp_walk_next : Nat := 0x80004cec
def sha256_w_input : Nat := 0xa3a0a938
def sha256_w_iv : Nat := 0xa0b00000
def sha256_w_params : Nat := 0xa0b00020
def sha256_w_state : Nat := 0xa3a0a918
def u256_div_u64_be : Nat := 0x80005904
def u256_min : Nat := 0x800270e0
def u256_mul_u64_be : Nat := 0x800057a4
def u256_sub_be : Nat := 0x800059e8
def u256m_acc : Nat := 0xa4386860
def zk3_state : Nat := 0xa3a4c0e0
def zkvm_keccak256 : Nat := 0x80003460
def zkvm_keccak256_segments : Nat := 0x80003574
def zkvm_sha256 : Nat := 0x800018c0

end EvmAsm.Codegen.GuestAddrs
