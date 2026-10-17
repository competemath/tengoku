#!/usr/bin/env python3
"""lint_banked.py <base> <head> | --text FILE — banked Lean must not run code.
Records paste `context` and `proof` verbatim into modules; modules are compiled
by CI and imported by every Leak service, where `initialize` runs. A staging or
trusted record (the tiers the tree compiles) must pass the allow-list
(scripts/ci/allowlist.py): only known-inert commands, attributes and options.
Tentative records (never compiled) and module lines keep the list of known
dangers below. Existing records are not re-judged: only lines a PR adds."""

from __future__ import annotations

import json
import os
import re
import sys
import tempfile
from pathlib import Path

from _git import added_lines, blob, changed_files, fail, load_schema, match, pascal, removed_lines
from allowlist import violations
from lean_lex import code_only
from restructure_check import is_restructure

IMPORT_START = r"^\s*import\b"
# three rules, because three readings of TENGOKU_INTAKE_LINT allow them differently (docs/bundle-lint.md): notation commands in `proposed` and `wide`, the macro
# family in `wide`, the elaborator commands in no mode
NOTATION = "notation declarations"
MACRO = "syntax/macro declarations"
ELAB = "elab declarations"
NOTATION_COMMANDS = ["notation3?", "infixl?", "infixr", "prefix", "postfix"]
MACRO_COMMANDS = ["macro", "macro_rules", "syntax", "declare_syntax_cat"]
ELAB_COMMANDS = ["elab", "elab_rules"]


def declaration_rule(commands: list[str]) -> re.Pattern:
    return re.compile(r"^\s*(@\[[^\]]*\]\s*)*(scoped\s+|local\s+)?(" + "|".join(commands) + r")\b", re.M)


FORBIDDEN = [
    (re.compile(IMPORT_START, re.M), "import (the generator supplies imports)"),
    (re.compile(r"#eval\b"), "#eval"),
    (re.compile(r"#print\s+axioms"), "#print axioms (CI runs its own)"),
    (re.compile(r"\brun_cmd\b"), "run_cmd"),
    (re.compile(r"\brun_tac\b"), "run_tac"),
    (re.compile(r"\brun_elab\b"), "run_elab"),
    (re.compile(r"^\s*(builtin_)?initialize\b", re.M), "initialize (runs on import in every Leak service)"),
    (
        re.compile(r"@\[\s*(init|builtin_init|extern|implemented_by|export|never_extract)\b"),
        "@[init]/@[extern]/@[implemented_by]/@[export]",
    ),
    (re.compile(r"^\s*(unsafe|partial)\s+(def|theorem|abbrev|instance|opaque)", re.M), "unsafe/partial definitions"),
    (declaration_rule(NOTATION_COMMANDS), NOTATION),
    (declaration_rule(MACRO_COMMANDS), MACRO),
    (declaration_rule(ELAB_COMMANDS), ELAB),
    (re.compile(r"\bnative_decide\b"), "native_decide (trusts the compiler)"),
    (re.compile(r"^\s*opaque\b", re.M), "opaque"),
    (re.compile(r"^\s*axiom\b", re.M), "axiom"),
    (re.compile(r"\bIO\.(Process|FS)\b|\bSystem\.(FilePath|Platform)\b"), "IO.Process / IO.FS"),
]
SET_OPTION = re.compile(r"set_option\s+([A-Za-z_][\w.]*)")

# A PR of the scope-fix class (scripts/ci/scope_fix_check.py judges every line of it) makes a library's global notation `scoped` or `local`: the line of the command is
# edited, so the PR "adds" a notation command, and the importers get a `local` copy of a command that was made local. Neither is a new declaration: the text is the
# one the tree already has, in a narrower scope. 2026-10-17: tengoku#601 was ejected from the queue by "notation declarations" on 64 such modules.
COMMAND_WORDS = "prefix|infixl|infixr|infix|postfix|notation3|notation|syntax|macro|elab"
COMMAND = re.compile(
    rf"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|public|noncomputable)[ \t]+)*(?:(?:local|scoped)[ \t]+)?(?P<kw>{COMMAND_WORDS})(?![\w'.])"
)
NARROWED = re.compile(rf"^(?P<pre>[ \t]*(?:@\[[^\]]*\][ \t]*)*)(?P<mod>local|scoped)[ \t]+(?P<cmd>(?:{COMMAND_WORDS})(?![\w'.]).*)$")


def code_end(text: str) -> int:
    """the column where the code of this line ends: before a `--` comment that is not inside a string literal"""
    inside, i = False, 0
    while i < len(text):
        c = text[i]
        if inside:
            if c == "\\":
                i += 2
                continue
            inside = c != '"'
        elif c == '"':
            inside = True
        elif text.startswith("--", i):
            return len(text[:i].rstrip())
        i += 1
    return len(text.rstrip())


def removed_sources(base: str, head: str) -> tuple[set[str], set[str]]:
    """what the PR takes out of the Lean modules it changes: the lines (stripped), and the commands among them (from the command word to the end of the code)"""
    lines: set[str] = set()
    cmds: set[str] = set()
    for st, p in changed_files(base, head):
        if st == "M" and p.endswith(".lean") and p.startswith("Tengoku/"):
            for _, text in removed_lines(base, head, p):
                lines.add(text.strip())
                if m := COMMAND.match(text):
                    cmds.add(text[m.start("kw") : code_end(text)].strip())
    return lines, cmds


def narrows(line: str, removed: tuple[set[str], set[str]]) -> bool:
    """An added line that is a line the PR removes with `scoped` or `local` put in front of its command, or `local <command>` for a command the PR removes (the copy an importer
    declares again when the command was made local). Anything else that starts with a command word is a new declaration."""
    m = NARROWED.match(line)
    if not m:
        return False
    lines, cmds = removed
    if (line[: m.start("mod")] + line[m.start("cmd") :]).strip() in lines:
        return True
    return m.group("mod") == "local" and not m.group("pre").strip() and line[m.start("cmd") : code_end(line)].strip() in cmds


def intake_modules(base: str, head: str) -> tuple[str, ...]:
    """The module paths of an intake bundle in this diff, when the repository's intake lint is `proposed` or `wide` (variable TENGOKU_INTAKE_LINT):
    notation commands are allowed there, as in scripts/ci/intake_check.py (the allow-list lint of the bundle). Nowhere else."""
    if os.environ.get("TENGOKU_INTAKE_LINT") not in ("proposed", "wide"):
        return ()
    libs = {m.group(1) for _, p in changed_files(base, head) if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))}
    return tuple(x for lib in libs for x in (f"Tengoku/{pascal(lib)}/", f"Tengoku/{pascal(lib)}.lean"))


def in_intake(p: str, intake: tuple[str, ...]) -> bool:
    """Is `p` one of the bundle's own modules: its root file exactly, or a file under its directory (never a sibling that merely starts the same)."""
    return p in intake or any(x.endswith("/") and p.startswith(x) for x in intake)


def check_text(label: str, text: str, allowed: set[str], notation_ok: bool = False, macro_ok: bool = False) -> list[str]:
    out = []
    for re_, why in FORBIDDEN:
        if (why == NOTATION and notation_ok) or (why == MACRO and macro_ok):
            continue
        if re_.search(text):
            out.append(f"{label}: {why}")
    for opt in SET_OPTION.findall(text):
        if opt not in allowed:
            out.append(f"{label}: set_option {opt} is not on the allowlist")
    return out


RECORD_FILES = [
    "data/tentative/*.jsonl",
    "data/staging/*.jsonl",
    "data/trusted/*.jsonl",
    "data/tentative/*/*.jsonl",
    "data/staging/*/*.jsonl",
]


def lint_record_file(base: str, head: str, p: str, allowed: set[str]) -> list[str]:
    """The lines a PR adds to a records file, judged by the allow-list (compiled tiers) or the list of known dangers."""
    errors = []
    for no, text in added_lines(base, head, p):
        try:
            r = json.loads(text)
        except Exception:
            continue
        if not isinstance(r, dict) or "tombstone" in r:  # not an object: validate_records.py refuses it
            continue
        body = "\n".join(str(r.get(k, "")) for k in ("context", "statement", "proof"))
        label = f"{p}:{no} ({r.get('name')})"
        if p.startswith(("data/staging/", "data/trusted/")):  # compiled: only what is known to be inert
            errors += [f"{label}: {v}" for v in violations(body, allowed)]
        else:
            errors += check_text(label, body, allowed)
    return errors


def lint_module(
    base: str,
    head: str,
    p: str,
    allowed: set[str],
    notation_ok: bool,
    added: bool = False,
    macro_ok: bool = False,
    removed: tuple[set[str], set[str]] = (set(), set()),
) -> list[str]:
    """The lines a PR adds to a module. `import` lines in a module are the generator's own (a promotion regenerates them); records may not contain one.
    A module the PR adds is read whole and without its comments and string literals (lean_lex.code_only): the words this list refuses are
    refused where they run, not where a docstring mentions them (`#print axioms` in a doc comment is prose). A module the PR changes is read whole
    the same way, and only the lines it adds are judged: a line alone cannot tell code from the middle of a comment, the whole file can."""
    raw = blob(head, p) if added else None
    if added and raw is None:  # fail closed: the line-by-line path below cannot see a block comment that an `import X -/` line closes
        return [f"{p}: could not read the module at {head}"]
    if raw is not None:
        # comments and strings first, THEN the import lines: a line `import X -/` inside a block comment closes it, and dropping it first would
        # turn the rest of the file into comment text (a `#eval` after it would go unread)
        code = code_only(raw.decode("utf-8", "replace"))
        return check_text(
            p,
            "\n".join(ln for ln in code.split("\n") if not re.match(IMPORT_START, ln)),
            allowed,
            notation_ok=notation_ok,
            macro_ok=macro_ok,
        )
    added_here = [
        (no, t) for no, t in added_lines(base, head, p) if not narrows(t, removed)
    ]  # the narrowed ones declare nothing the tree does not have
    raw_head = blob(head, p)
    if raw_head is not None:
        # The module is read whole and lexed like an added one, and only the lines the PR adds are judged, as code: an isnad tag moves the `-/` of a docstring to its own line, which makes the
        # docstring's last line an added line, and prose that starts with `prefix` or `notation` was refused as a notation command (isnad tag PR #438, 2026-10-11: "prefix length](hyp:Z,p,k) …").
        code = code_only(raw_head.decode("utf-8", "replace")).split("\n")
        if len(code) == len(
            raw_head.decode("utf-8", "replace").split("\n")
        ):  # the lexer keeps every line break; if it ever did not, the lines would not line up and the old reading stands
            text = "\n".join(code[no - 1] for no, _ in added_here if no - 1 < len(code) and not re.match(IMPORT_START, code[no - 1]))
            return check_text(p, text, allowed, notation_ok=notation_ok, macro_ok=macro_ok)
    text = "\n".join(t for _, t in added_here if not re.match(IMPORT_START, t))
    return check_text(p, text, allowed, notation_ok=notation_ok, macro_ok=macro_ok)


def checked_path(arg: str) -> Path:
    """A file given on the command line: it must lie in the working directory or the temporary directory."""
    p = Path(arg).resolve()
    if not any(p.is_relative_to(root.resolve()) for root in (Path.cwd(), Path(tempfile.gettempdir()))):
        fail(f"{arg} is outside the working directory and the temporary directory")
    return p


def main() -> None:
    allowed = set(load_schema("allowed-options.json")["allowed"])
    errors = []
    if sys.argv[1] == "--text":
        errors = check_text(sys.argv[2], checked_path(sys.argv[2]).read_text(), allowed)
    else:
        base, head = sys.argv[1], sys.argv[2]
        intake = intake_modules(base, head)
        removed = removed_sources(base, head)
        moved_seed = is_restructure(
            base, head
        )  # the seed's move is recomputed by restructure_check.py; it is upstream code, never banked content
        for st, p in changed_files(base, head):
            if moved_seed and p.startswith("Tengoku/Seed/"):
                continue
            if match(p, RECORD_FILES):
                errors += lint_record_file(base, head, p, allowed)
            elif p.endswith(".lean") and p.startswith(
                "Tengoku/"
            ):  # modules only; root tool programs (TengokuExtract/TengokuAxioms) run in CI, not in the library
                own = in_intake(p, intake)
                errors += lint_module(
                    base,
                    head,
                    p,
                    allowed,
                    notation_ok=own,
                    added=st == "A",
                    macro_ok=own and os.environ.get("TENGOKU_INTAKE_LINT") == "wide",
                    removed=removed,
                )
    if errors:
        fail("banked content lint:\n  " + "\n  ".join(errors[:20]))
    print("content lint OK")


main()
