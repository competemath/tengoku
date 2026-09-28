#!/usr/bin/env python3
"""Turn verified records into tree modules.

    python3 scripts/generate.py --corpus <path to equational_theories checkout> [--libraries equational-theories]

For each non-seed library with `source_path` records (data/staging + data/trusted):

  Tengoku/<Library>/Deps/<Module>.lean   the corpus modules the records' contexts
                                         pasted (verbatim source, imports mapped),
                                         and Deps/Equations.lean regenerated from
                                         every `equation N := law` in the corpus —
                                         all under `namespace <Library>`
  Tengoku/<Library>/<source path>.lean   one module per original source file:
                                         the file's own earlier declarations (from
                                         the records' `context`, after the prelude)
                                         + every verified theorem of that file
  Tengoku/<Library>.lean                 imports all of the above

Everything from a corpus lives under its own namespace (`EquationalTheories.*`),
so a corpus type that shares a name with a seeded one (`FreeMagma`) can coexist.
Records are the source of truth for theorems; the corpus checkout is only read
for definition modules, exactly as the translation harness reads it.

That is the "legacy" generator, kept for equational-theories (schemas/sources.json corpora.<lib>.generator).
Every other library uses the "verified" generator: the tree is built from exactly the text Emissary-Archangel
verified, never from the corpus files. A record's context is

    set_option ...
    -- [Emissary prelude] <Module> — verbatim|expanded (imports stripped)     one block per corpus module it needs,
    <that module's text as it compiled in the tree>                           in dependency order
    -- [Emissary] <source file>, everything before line N (...)             the record's own file, up to the theorem
    <that prefix>

so Deps/<Module> is the prelude block's text (the most common version across the library's records), importing
Tengoku and the Deps before it; a file module is the own-file prefixes plus the records, importing Tengoku and
the Deps its records need. Nothing is wrapped or renamed, and no corpus import survives: tooling a corpus used
(blueprint packages such as Architect) never reaches the tree.
"""

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from seed import IMPORT_RE, PACKAGES, module_map  # noqa: E402

# Only TRUSTED records become modules of the tree. A staging record (both
# gates passed, module not yet proven to build) is promoted by
# scripts/promote.py, which builds its module before moving it here; nothing
# staging or tentative is ever importable through Tengoku.All.
DATA_TIERS = ("trusted",)
FILE_MARKER_RE = re.compile(r"^-- \[Emissary\] (\S+), everything before line \d+[^\n]*\n", re.M)
PRELUDE_MODULE_RE = re.compile(r"^-- \[Emissary prelude\] (\S+) — verbatim", re.M)
PRELUDE_ANY_RE = re.compile(r"^-- \[Emissary prelude\] (\S+) — [^\n]*\n", re.M)
EQUATION_LINE_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*equation\s+(\d+)\s*:=\s*(.+?)\s*$", re.M)
UNSAFE_MODULE_RE = re.compile(
    r"^\s*(?:scoped\s+)?(initialize|builtin_initialize|register_simp_attr|register_option|register_label_attr|register_tag_attr|register_parametric_attr)\b",
    re.M,
)


# Namespacing a corpus module (`namespace EquationalTheories … end`) keeps its
# own names (Magma, EquationN, FreeMagma) from clashing with seeded ones — but
# a corpus file also EXTENDS outside namespaces (`def Lean.MVarId.congrWith`,
# `theorem Eq.comm'`), and inside the wrapper those would silently become
# `EquationalTheories.Lean.MVarId.congrWith`, breaking every `m.congrWith`.
# A dotted declaration whose head is an outside namespace gets `_root_.`;
# a module that opens an outside namespace block is left unwrapped.
TOOLCHAIN_ROOTS = set(
    """
Lean Init Std Eq Ne HEq Nat Int List Array String Char Option Prod Sum Fin Function Sigma PSigma Subtype Quot Quotient
Decidable Bool Iff And Or Not Exists True False Unit PUnit IO Task Id StateT ReaderT ExceptT Except Monad Functor
Applicative HashMap HashSet RBMap ByteArray Float UInt8 UInt16 UInt32 UInt64 USize Empty PEmpty Classical WellFounded Acc
Setoid Equivalence Inhabited Nonempty Subsingleton DecidableEq BEq Hashable Ord LT LE Add Mul Sub Div Neg HAdd HMul HSub HDiv
Membership Singleton Insert EmptyCollection Union Inter SDiff HasSubset Coe CoeFun CoeSort Zero One Dvd Mod Pow HPow Append
GetElem Bind Pure Seq SeqLeft SeqRight ToString Repr Format Syntax Name Expr Level MVarId FVarId Meta Elab Tactic Term Command
""".split()
)


def seed_heads(out: Path) -> set[str]:
    """First segments of every declaration/namespace in the seeded tree."""
    heads = set(TOOLCHAIN_ROOTS)
    rx = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public)\s+)*(?:namespace|def|theorem|lemma|abbrev|instance|opaque|axiom|inductive|structure|class)\s+([A-Za-z_][\w']*)",
        re.M,
    )
    for f in (out / "Tengoku").rglob("*.lean"):
        if "EquationalTheories" in f.parts or "CompeteMath" in f.parts:
            continue
        try:
            heads.update(rx.findall(f.read_text(encoding="utf-8", errors="ignore")))
        except OSError:
            pass
    return heads


DECL_HEAD_RE = re.compile(
    r"^(\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*(?:def|theorem|lemma|abbrev|instance|opaque|axiom|inductive|structure|class)\s+)([A-Za-z_][\w']*)\.",
    re.M,
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w']*)", re.M)


def rootify(body: str, external: set[str]) -> str:
    """`def Lean.MVarId.congrWith` at the top level of a file extends an outside
    namespace and must stay there (`_root_.`) once the file is wrapped. The
    same spelling INSIDE the file's own `namespace Asterix` block names
    `Asterix.Denumerable.notMemFinset`, and its callers rely on that — so the
    rewrite applies only at namespace depth zero."""
    out, stack = [], []
    for line in body.splitlines():
        m = re.match(r"^(?:noncomputable\s+)?(namespace|section)\b", line)
        if m:
            stack.append(m.group(1))
        elif re.match(r"^end\b", line) and stack:
            stack.pop()
        if "namespace" not in stack:
            line = DECL_HEAD_RE.sub(lambda mm: f"{mm.group(1)}{'_root_.' if mm.group(2) in external else ''}{mm.group(2)}.", line)
        out.append(line)
    return "\n".join(out)


def opens_external_namespace(body: str, external: set[str]) -> bool:
    return any(h in external for h in NAMESPACE_RE.findall(body))


def wrap(body: str, lib_ns: str, external: set[str]) -> str:
    if opens_external_namespace(body, external):
        # Its declarations extend an outside namespace and must land there; the
        # library's own names (Magma, EquationN, the Deps) are reached by opening it.
        return f"-- left unwrapped: this module opens an outside namespace block\nopen {lib_ns}\n\n{body.strip()}\n"
    return f"namespace {lib_ns}\n\n{rootify(body, external).strip()}\n\nend {lib_ns}\n"


def unclosed_scopes(text: str) -> list[str]:
    """`end` lines closing every namespace/section `text` opens and never
    closes, innermost first. A file prefix ends before the file's own
    `end <ns>`, so the wrapper must close what it left open."""
    stack: list[str] = []
    for line in text.splitlines():
        m = re.match(r"^(?:noncomputable\s+)?(namespace|section)\b[ \t]*([^\s]*)", line)  # `section run'` too
        if m:
            stack.append(m.group(2))
            continue
        m = re.match(r"^end\b[ \t]*([^\s]*)", line)
        if m and stack:
            stack.pop()
    return [f"end {n}".rstrip() for n in reversed(stack)]


def strip_trailing_ends(proof: str) -> str:
    """A record's proof runs from its `:=` to the end of the script, so an
    agent-written script leaves `end <Namespace>` (closing what the context
    opened) at its tail. The module shares one prefix, so those must go."""
    lines = proof.rstrip().splitlines()
    while lines and (not lines[-1].strip() or re.match(r"^end\b", lines[-1])):
        lines.pop()
    return "\n".join(lines)


def pascal(library: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_ ]+", library) if p)


def strip_corpus_attrs(text: str) -> str:
    def attrs(m):
        kept = [s.strip() for s in m.group(1).split(",") if s.strip() and not s.strip().startswith("equational_result")]
        return f"@[{', '.join(kept)}]" if kept else ""

    return re.sub(r"@\[([^\]]*)\]", attrs, text)


def corpus_roots(out: Path, library: str) -> list[str]:
    """The corpus's lean_lib module roots (schemas/sources.json corpora[<library>].roots); the
    library name with `-` -> `_` when it has none, which is how equational-theories is laid out."""
    try:
        spec = json.loads((out / "schemas" / "sources.json").read_text(encoding="utf-8")).get("corpora", {}).get(library, {})
    except (OSError, ValueError):
        spec = {}
    return list(spec.get("roots") or [library.replace("-", "_")])


def generator_of(out: Path, library: str) -> str:
    """schemas/sources.json corpora.<library>.generator: "legacy" (equational-theories) or "verified" (the default)."""
    try:
        spec = json.loads((out / "schemas" / "sources.json").read_text(encoding="utf-8")).get("corpora", {}).get(library, {})
    except (OSError, ValueError):
        spec = {}
    return spec.get("generator", "verified")


def is_corpus_module(mod: str, roots: list[str]) -> bool:
    return any(mod == r or mod.startswith(r + ".") for r in roots)


def deps_key(mod: str) -> str:
    """A corpus module's name inside Deps: its path below the root (`Classical.Basic`), so two
    `Basic`s under different directories are two Deps modules. A flat corpus keeps bare leaves."""
    parts = mod.split(".")
    return ".".join(parts[1:]) if len(parts) > 1 else parts[0]


def deps_file(deps_dir: Path, key: str) -> Path:
    p = deps_dir / Path(*key.split(".")).with_suffix(".lean")
    p.parent.mkdir(parents=True, exist_ok=True)
    return p


def deps_modules(deps_dir: Path) -> list[str]:
    return sorted(".".join(p.relative_to(deps_dir).with_suffix("").parts) for p in deps_dir.rglob("*.lean"))


def map_imports(
    text: str, corpus_roots: list[str], lib_ns: str, deps_available: set[str], corpus: Path | None = None, _seen: set[str] | None = None
) -> str:
    """Seed imports -> Tengoku.*; corpus imports -> this library's Deps modules.
    A corpus module the tree does not reproduce is replaced by what IT imported
    (recursively), so a module keeps the seed-library surface its file had —
    the standalone script compiled with the whole tree in scope; the module
    must not silently lose `Mathlib.ModelTheory` because it arrived through a
    corpus import."""
    roots = [(v[1], v[2]) for v in PACKAGES.values()]
    seen = _seen if _seen is not None else set()

    def sub(m):
        mod = m.group(2)
        if is_corpus_module(mod, corpus_roots):
            leaf = deps_key(mod)
            if leaf in deps_available:
                return f"{m.group(1)}Tengoku.{lib_ns}.Deps.{leaf}{m.group(3)}"
            if corpus is not None and mod not in seen:
                seen.add(mod)
                f = corpus / Path(*mod.split(".")).with_suffix(".lean")
                if f.exists():
                    inner = map_imports(f.read_text(encoding="utf-8"), corpus_roots, lib_ns, deps_available, corpus, seen)
                    return "\n".join(l.strip() for l in inner.splitlines() if re.match(r"\s*(public |private |meta )*import ", l))
            return ""  # a corpus module we don't reproduce and cannot read: nothing to import
        for root_mod, mapped in roots:
            new = module_map(root_mod, mapped, mod)
            if new:
                return f"{m.group(1)}{new}{m.group(3)}"
        return m.group(0)

    return IMPORT_RE.sub(sub, text)


DECL_NAME_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public)\s+)*(?:def|theorem|lemma|abbrev|instance|opaque|axiom|inductive|structure|class)\s+([A-Za-z_][\w'.]*)",
    re.M,
)
IMPORT_LINE_RE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s")


NOTATION_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:scoped\s+|local\s+)?(?:infixl?|infixr|prefix|postfix|notation)\b[^\"]*\"([^\"]+)\"")


def deps_declared(deps_dir: Path) -> tuple[set[str], set[str]]:
    """Names and (whitespace-normalised) lines every Deps module already
    provides. A notation counts by its token: `" ◇ "` declared by Deps/Magma
    is the same notation however a script spells the declaration, and a
    second copy makes every `x ◇ y` ambiguous."""
    names, lines = set(), set()
    for f in deps_dir.rglob("*.lean"):
        text = f.read_text(encoding="utf-8")
        names.update(n.removeprefix("_root_.") for n in DECL_NAME_RE.findall(text))
        for l in text.splitlines():
            if l.strip() and not l.lstrip().startswith("--"):
                lines.add(" ".join(l.split()))
                m = NOTATION_RE.match(l)
                if m:
                    names.add("notation:" + m.group(1).strip())
    return names, lines


def only_lead_in(text: str) -> bool:
    """Nothing but doc/block/line comments, attributes, modifiers or `… in` lines (a multi-line doc comment's middle
    lines included): it belongs to the declaration that follows it."""
    s = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    s = re.sub(r"--[^\n]*", " ", s)
    s = re.sub(r"@\[[^\]]*\]", " ", s)
    s = re.sub(r"^.*\bin\s*$", " ", s, flags=re.M)
    s = re.sub(r"\b(private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public)\b", " ", s)
    return not s.strip()


MODIFIER_LINE_RE = re.compile(r"^(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public)\s*)+$")
CONTINUATION_RE = re.compile(r"^(\||deriving\b|with\b|where\b|termination_by\b|decreasing_by\b|\)|\]|\})")


def top_level_chunks(text: str, continuations: bool = False) -> list[list[str]]:
    """Split a file prefix at column-0 lines; attribute/doc-comment lead-ins and
    the inside of block comments stay with the declaration they belong to. With
    `continuations` (the verified generator), a column-0 `| constructor`,
    `deriving …`, `termination_by …` (and the like) stays with its declaration too."""
    out: list[list[str]] = []
    cur: list[str] = []
    depth = 0

    def lead_in_only(lines: list[str]) -> bool:
        # attributes, doc comments, and `set_option … in` / `omit … in` /
        # `open … in` modifiers all belong to the declaration that follows
        # (and, for the verified generator, a modifier alone on its line: `noncomputable`, `private`, …; a line that
        # only STARTS with an attribute, `@[simp] lemma …` or `@[expose] public section`, is a command of its own)
        if continuations:
            return only_lead_in("\n".join(lines))
        return all(
            not l.strip()
            or l.startswith(("@[", "/--", "/-", "--"))
            or l.strip().endswith("-/")
            or l.rstrip().endswith(" in")
            or (continuations and MODIFIER_LINE_RE.match(l))
            for l in lines
        ) or (continuations and only_lead_in("\n".join(lines)))

    for line in text.splitlines():
        if (
            line
            and not line[0].isspace()
            and depth == 0
            and cur
            and not lead_in_only(cur)
            and not (continuations and CONTINUATION_RE.match(line))
            # a comment written at column 0 inside a proof is not the end of the declaration
            and not (continuations and (line.startswith("--") or (line.startswith("/-") and not line.startswith(("/--", "/-!")))))
        ):
            out.append(cur)
            cur = []
        cur.append(line)
        depth += line.count("/-") - line.count("-/")
    if cur:
        out.append(cur)
    return out


def dedupe_prefix(prefix: str, deps_names: set[str], deps_lines: set[str]) -> str:
    """A context written by an agent (no prelude marker) is a self-contained
    script: `import Mathlib`, its own `class Magma`, `abbrev EquationN`, the
    `◇` notation. Inside the tree those come from the library's Deps modules,
    so imports go and any top-level declaration Deps already provides is
    dropped — an `import` after line 1 or a second `class Magma` in the same
    namespace fails the build. Universe declarations are per-file and kept."""
    kept = []
    for chunk in top_level_chunks(prefix):
        body = "\n".join(chunk)
        code = [l for l in chunk if l.strip() and not l.lstrip().startswith(("--", "/-", "@[")) and not l.strip().endswith("-/")]
        if not code:
            continue
        if any(IMPORT_LINE_RE.match(l) for l in code):
            continue
        if code[0].startswith("universe"):
            kept.append(body)
            continue
        m = DECL_NAME_RE.search(body)
        if m and m.group(1).removeprefix("_root_.") in deps_names:
            continue
        n = NOTATION_RE.match(code[0])
        if n and ("notation:" + n.group(1).strip()) in deps_names:
            continue
        kept.append(body)
    return "\n".join(kept)


def prelude_blocks(context: str) -> list[tuple[str, str]]:
    """(module, text) for every `-- [Emissary prelude] <Module> — …` block of a context, in order: the text runs to
    the next prelude marker or the record's own-file marker."""
    marks = list(PRELUDE_ANY_RE.finditer(context))
    own = FILE_MARKER_RE.search(context)
    out = []
    for i, m in enumerate(marks):
        end = marks[i + 1].start() if i + 1 < len(marks) else (own.start() if own and own.start() > m.end() else len(context))
        out.append((m.group(1), context[m.end() : end].strip("\n") + "\n"))
    return out


def topo_order(sequences: list[list[str]]) -> list[str]:
    """One order of all modules consistent with the order they appear in each context (a cycle, which the
    contexts should never form, is broken by first appearance)."""
    first: dict[str, int] = {}
    after: dict[str, set[str]] = {}
    for seq in sequences:
        for i, m in enumerate(seq):
            first.setdefault(m, len(first))
            after.setdefault(m, set()).update(seq[:i])
    done: list[str] = []
    placed: set[str] = set()
    for m in sorted(first, key=first.get):
        stack = [m]
        while stack:
            cur = stack[-1]
            if cur in placed:
                stack.pop()
                continue
            pending = sorted((d for d in after.get(cur, ()) if d not in placed and d not in stack), key=first.get)
            if pending:
                stack.append(pending[0])
            else:
                placed.add(cur)
                done.append(cur)
                stack.pop()
    return done


def corpus_edges(modules: set[str], corpus: Path | None, roots: list[str]) -> dict[str, set[str]]:
    """For each prelude module, the prelude modules its ORIGINAL file imports — directly, or through corpus modules
    no context carries (followed transitively). Only import lines are read; the file's text never reaches the tree.
    A module whose file is not in the corpus checkout is left out (its edges come from the contexts)."""
    edges: dict[str, set[str]] = {}
    memo: dict[str, set[str]] = {}

    def imports_of(mod: str) -> set[str] | None:
        if corpus is None:
            return None
        f = corpus / Path(*mod.split(".")).with_suffix(".lean")
        if not f.exists():
            return None
        return {m.group(2) for m in IMPORT_RE.finditer(f.read_text(encoding="utf-8", errors="ignore"))}

    def reach(mod: str, seen: set[str]) -> set[str]:
        if mod in memo:
            return memo[mod]
        out: set[str] = set()
        for im in imports_of(mod) or ():
            if im in modules:
                out.add(im)
            elif is_corpus_module(im, roots) and im not in seen:
                seen.add(im)
                out |= reach(im, seen)
        memo[mod] = out
        return out

    for m in modules:
        if imports_of(m) is not None:
            edges[m] = reach(m, {m})
    return edges


def verified_deps(
    records: list[dict], deps_dir: Path, lib_ns: str, corpus: Path | None = None, roots: list[str] | None = None
) -> tuple[list[str], dict[str, str]]:
    """Deps/<key> for every corpus module a record's context carries as a prelude block: that block's text (the most
    common version; the build decides if a rarer one was needed), importing Tengoku and the Deps modules its original
    file imports (from the corpus's import lines; without a corpus file, every Deps module that came before it in a
    context). Returns (topological order, module -> key)."""
    from collections import Counter

    versions: dict[str, Counter] = {}
    sequences = []
    for r in records:
        blocks = prelude_blocks(r["context"])
        sequences.append([m for m, _ in blocks])
        for m, text in blocks:
            versions.setdefault(m, Counter())[text] += 1
    edges = corpus_edges(set(versions), corpus, roots or [])
    # the corpus's import graph orders the modules; context order fills in modules the corpus does not have
    # context order only constrains modules the corpus says nothing about (a context may list independent modules
    # in any order, and must not override a real import)
    # one pair per import: a longer sequence would also order the imports among themselves, which nothing says
    order = topo_order(
        [[d, m] for m, deps in edges.items() for d in deps]
        + [[m] for m in edges]
        + [[m for m in seq if m not in edges] for seq in sequences]
    )
    rank = {m: i for i, m in enumerate(order)}
    before: dict[str, set[str]] = {}
    for m, deps in edges.items():
        before[m] = {d for d in deps if rank[d] < rank[m]}
    for seq in sequences:
        for i, m in enumerate(seq):
            if m not in edges:
                before.setdefault(m, set()).update(d for d in seq[:i] if rank[d] < rank[m])
    keys = {m: deps_key(m) for m in order}
    for m in order:
        text = max(versions[m].items(), key=lambda kv: (kv[1], len(kv[0])))[0]
        imports = "\n".join(f"import Tengoku.{lib_ns}.Deps.{keys[d]}" for d in sorted(before.get(m, ()), key=rank.get))
        variants = f" ({len(versions[m])} versions across records; the most common is used)" if len(versions[m]) > 1 else ""
        deps_file(deps_dir, keys[m]).write_text(
            f"-- {lib_ns}/Deps/{keys[m]}: {m} as it was verified in the tree (a record's prelude block){variants}\n"
            f"import Tengoku\n{imports}\n\nset_option linter.all false\n\n{text}",
            encoding="utf-8",
        )
    return order, keys


SCOPE_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|public|private)\s+)*(namespace|section)\b[ \t]*([^\s]*)")
END_RE = re.compile(r"^end\b[ \t]*([^\s]*)")


def scoped_chunks(text: str) -> tuple[list[tuple[str, str]], list[tuple[str, str]]]:
    """A file text as (key, chunk) pairs in order, and the scope stack at its end. A declaration's key is its FULL
    name — the enclosing `namespace`s joined to the name as written (`_root_.` escapes them), exactly as Lean names
    it — so `foo` in two namespaces are two declarations; anything else is keyed by its text. Import lines go."""
    stack: list[tuple[str, str]] = []  # (kind, name)
    out: list[tuple[str, str]] = []
    seen: dict[str, int] = {}  # a structural line that recurs (a second `namespace Heap` with its own `variable`) is
    # keyed by its occurrence, so the n-th copy lines up with the n-th copy of another prefix of the same file
    for ch in top_level_chunks(text, continuations=True):
        body = "\n".join(ch).strip()
        if not body:
            continue
        code = [l for l in ch if l.strip() and not l.lstrip().startswith(("--", "/-")) and not l.strip().endswith("-/") and not only_lead_in(l)]
        if code and IMPORT_LINE_RE.match(code[0]):
            continue
        m = DECL_NAME_RE.search(body)
        first = code[0] if code else ""
        s = SCOPE_RE.match(first)
        e = END_RE.match(first)
        if m and not s:
            name = m.group(1)
            ns = [n for k, n in stack if k == "namespace" and n]
            full = name[len("_root_.") :] if name.startswith("_root_.") else ".".join(ns + [name])
            out.append(("name:" + full, body))
        else:
            norm = " ".join(body.split())
            seen[norm] = seen.get(norm, 0) + 1
            out.append((f"text:{norm}#{seen[norm]}", body))
        if s:
            stack.append((s.group(1), s.group(2)))
        elif e and stack:
            stack.pop()
    return out, stack


def qualified_names(text: str) -> set[str]:
    return {k[5:] for k, _ in scoped_chunks(text)[0] if k.startswith("name:")}


IDENT_RUN_RE = re.compile(r"(?<![\w'!?.])\.?[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*")


def clash_suffix(library: str) -> str:
    return "__" + re.sub(r"[^A-Za-z0-9]", "_", library)  # bank-flush renames records the same way


def library_declarations(lib_dir: Path, candidates: bool = False, where: dict[str, set[Path]] | None = None) -> dict[str, str]:
    """Every public declaration a library's modules make: full name -> its text (whitespace-normalised); `where`, when
    given, collects the files declaring each."""
    out: dict[str, str] = {}
    for f in sorted(lib_dir.rglob("*.lean")):
        if f.name.startswith("_candidate_") and not candidates:
            continue
        for k, chunk in scoped_chunks(f.read_text(encoding="utf-8"))[0]:
            if k.startswith("name:"):
                out.setdefault(k[5:], " ".join(chunk.split()))
                if where is not None:
                    where.setdefault(k[5:], set()).add(f)
    return out


def importers(lib_dir: Path) -> dict[Path, set[Path]]:
    """Each file of a library -> itself and every file of the library importing it, directly or not."""
    root = lib_dir.parent.parent  # <out>/Tengoku/<Lib> -> <out>
    files = sorted(lib_dir.rglob("*.lean"))
    by_mod = {".".join(f.relative_to(root).with_suffix("").parts): f for f in files}
    direct: dict[Path, set[Path]] = {f: set() for f in files}
    for f in files:
        for m in re.findall(r"^import (\S+)", f.read_text(encoding="utf-8"), re.M):
            if m in by_mod:
                direct[by_mod[m]].add(f)
    out: dict[Path, set[Path]] = {}
    for f in files:
        seen, todo = {f}, [f]
        while todo:
            for g in direct[todo.pop()]:
                if g not in seen:
                    seen.add(g)
                    todo.append(g)
        out[f] = seen
    return out


def rename_tokens(text: str, targets: dict[str, str]) -> str:
    """Give each target declaration (full name -> new last component) its new name wherever the text refers to it:
    written in full, under a suffix of its namespace, bare, or by dot notation (`h.foo`)."""
    by_short: dict[str, list[tuple[list[str], str]]] = {}
    for full, new in targets.items():
        *ns, short = full.split(".")
        by_short.setdefault(short, []).append((ns, new))

    def fix(m: re.Match) -> str:
        run = m.group(0)
        before, after = m.string[: m.start()].rstrip()[-1:], m.string[m.end() :].lstrip()[:2]
        if after == ":=" and before in ("(", "{", ","):  # a named argument or a structure field: a parameter's name
            return run
        lead = "." if run.startswith(".") else ""
        comps = run[len(lead) :].split(".")
        for i, c in enumerate(comps):
            for ns, new in by_short.get(c, []):
                prefix = comps[:i]
                if prefix[:1] == ["_root_"]:
                    ok = prefix[1:] == ns
                else:
                    ok = not prefix or ns[len(ns) - len(prefix) :] == prefix or (len(prefix) == 1 and prefix[0][:1].islower() and i == len(comps) - 1)
                if ok:
                    comps[i] = new
                    break
        return lead + ".".join(comps)

    return IDENT_RUN_RE.sub(fix, text)


def library_imports(out: Path, start: Path, lib_dirs: set[str]) -> set[Path]:
    """The library files `start` imports, directly or not (the seeded tree's own modules are not followed)."""
    seen: set[Path] = set()
    todo = [start]
    while todo:
        for m in re.findall(r"^import (\S+)", todo.pop().read_text(encoding="utf-8"), re.M):
            parts = m.split(".")
            if len(parts) > 2 and parts[0] == "Tengoku" and parts[1] in lib_dirs:
                f = out.joinpath(*parts).with_suffix(".lean")
                if f.is_file() and f not in seen:
                    seen.add(f)
                    todo.append(f)
    return seen


def rename_clashes(out: Path, lib_dir: Path, library: str, libraries: list[str]) -> str:
    """A declaration this library makes that another library's modules already make would stop the tree importing
    both; the library already in the tree keeps it. An identical copy (same full name, same text: a fork, a vendored
    file) is kept once — this library's module imports the other's and drops its own. A different one is renamed
    `<name>__<library>` wherever it is in scope here (the outermost clashing name only: renaming a structure renames
    its fields and lemmas with it)."""
    where: dict[str, set[Path]] = {}
    mine = library_declarations(lib_dir, candidates=True, where=where)  # a candidate module is treated as its module
    theirs: dict[str, tuple[str, Path]] = {}
    lib_dirs = {pascal(k) for k in libraries} | {lib_dir.name}
    for other in libraries:
        d = out / "Tengoku" / pascal(other)
        if other != library and d.is_dir() and d != lib_dir:
            w: dict[str, set[Path]] = {}
            for name, text in library_declarations(d, where=w).items():
                theirs.setdefault(name, (text, sorted(w[name])[0]))
    clashes = sorted(n for n in mine if n in theirs)
    if not clashes:
        return ""
    identical = {n for n in clashes if mine[n] == theirs[n][0]}
    differing = set(clashes) - identical

    def prefixes(n: str) -> list[str]:
        return [".".join(n.split(".")[:i]) for i in range(1, n.count(".") + 1)]

    outer = [n for n in sorted(differing) if not any(p in differing for p in prefixes(n))]
    covered = {n for n in clashes if any(p in outer for p in prefixes(n))}  # renamed along with a parent
    # keeping one copy means importing the other library's module: never when that module imports this library
    back: dict[Path, bool] = {}
    kept_once: dict[str, Path] = {}
    for n in sorted(identical - covered):
        src = theirs[n][1]
        if src not in back:
            back[src] = any(lib_dir in f.parents for f in library_imports(out, src, lib_dirs))
        if back[src]:
            outer.append(n)
        else:
            kept_once[n] = src
    suffix = clash_suffix(library)
    targets = {n: n.rsplit(".", 1)[-1] + suffix for n in outer if not n.rsplit(".", 1)[-1].startswith("«")}
    # only where the declaration is in scope: the file making it and the files importing that one (a file module is
    # imported by none, so a clash there is renamed in that file alone — a binder `f` elsewhere keeps its name)
    reach = importers(lib_dir)
    seen_in: dict[Path, dict[str, str]] = {}
    for n, new_short in targets.items():
        for decl_file in where.get(n, ()):
            for f in reach.get(decl_file, {decl_file}):
                seen_in.setdefault(f, {})[n] = new_short
    drop_in: dict[Path, dict[str, Path]] = {}
    for n, src in kept_once.items():
        for decl_file in where.get(n, ()):
            drop_in.setdefault(decl_file, {})[n] = src
    for f in set(seen_in) | set(drop_in):
        text = f.read_text(encoding="utf-8")
        new = text
        if f in drop_in:
            chunks = dict(scoped_chunks(new)[0])
            for n in drop_in[f]:
                if "name:" + n in chunks:
                    new = new.replace(chunks["name:" + n], "", 1)
            imports = sorted({".".join(src.relative_to(out).with_suffix("").parts) for src in drop_in[f].values()})
            lines = new.split("\n")
            last_import = max((i for i, l in enumerate(lines) if l.startswith("import ")), default=0)
            have = set(lines)
            lines[last_import + 1 : last_import + 1] = [f"import {m}" for m in imports if f"import {m}" not in have]
            new = "\n".join(lines)
        if f in seen_in:
            new = rename_tokens(new, seen_in[f])
        if new != text:
            f.write_text(new, encoding="utf-8")
    return (
        f"{len(clashes)} clashes with other libraries ({len(identical)} identical, {len(differing)} differing): "
        f"{len(kept_once)} kept once (imported), {len(targets)} renamed *{suffix}"
    )


def is_lead_in(text: str) -> bool:
    """Only doc comments, attributes, comments, modifiers or `… in` lines: it belongs to the declaration after it."""
    return bool(text.strip()) and only_lead_in(text) and not DECL_NAME_RE.search(text)


def theorem_text(statement: str, proof: str) -> str:
    """A record's declaration as it stood: the split was at the first `:=` after its keyword, which for a definition
    by pattern matching is inside a `have` of one arm — `… have h : P` + `:= by omega` must stay on one line."""
    statement, proof = strip_corpus_attrs(statement), strip_trailing_ends(proof)
    last = statement.rstrip().splitlines()[-1] if statement.strip() else ""
    return f"{statement} {proof}" if proof.startswith(":=") and "--" not in last else f"{statement}\n{proof}"


def verified_file_body(recs: list[dict], own_text, deps_names: set[str], orig_line=None) -> list[str]:
    """One file's module body from its records (in file order): each record's own-file block is aligned with what
    the earlier ones built (a keyed sequence merge, so a second `section`/`end` is not mistaken for the first; a
    declaration, keyed by its full name, appears once), and its theorem goes right after its own block, under the
    namespaces open there. A declaration a Deps module already has (by full name) is not declared again; a doc comment,
    attribute or modifier left without its declaration is dropped."""
    from difflib import SequenceMatcher

    marked = [r for r in recs if FILE_MARKER_RE.search(r["context"])]
    agent = [r for r in recs if not FILE_MARKER_RE.search(r["context"])]
    merged: list[tuple[str, str]] = []
    placed: list[tuple[int, str]] = []  # (line of a marked record's theorem, its key)
    # an agent record is placed by its line in the corpus file, so the marked ones are compared by theirs (a marker's
    # line is the self-contained text's, which need not be the corpus file's)
    raw: list[tuple[int, str]] = []
    alias: dict[str, str] = {}  # a record the flush renamed (a clash) -> its original name, which a sibling's prefix may carry
    for r in marked:
        block, stack = scoped_chunks(own_text(r))
        block = [(k, c) for k, c in block if not (k.startswith("name:") and k[5:] in deps_names)]
        # an attribute or doc comment ending the block is the record's own (a prefix omits a sibling together with its
        # attributes): it goes with the theorem as one piece — left in the block, every record's `@[simp]` would look
        # alike to the alignment and pull the next record's block in front of the earlier theorems
        own_lead: list[str] = []
        while block and block[-1][0].startswith("text:") and is_lead_in(block[-1][1]):
            own_lead.insert(0, block.pop()[1])
        mm = re.search(r"everything before line (\d+)", r["context"])
        sm = SequenceMatcher(a=[k for k, _ in merged], b=[k for k, _ in block], autojunk=False)
        new: list[tuple[str, str]] = []
        last_of_block = -1
        declared = {k for k, _ in merged if k.startswith("name:")}
        declared |= {alias[k] for k in declared if k in alias}

        def fresh(items: list[tuple[str, str]]) -> list[tuple[str, str]]:
            out = []
            for k, text in items:
                if k.startswith("name:"):
                    if k in declared:
                        continue
                    declared.add(k)
                out.append((k, text))
            return out

        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == "equal":
                new += merged[i1:i2]
                last_of_block = len(new) - 1
            elif tag == "delete":
                new += merged[i1:i2]
            elif tag == "insert":
                new += fresh(block[j1:j2])
                last_of_block = len(new) - 1
            else:  # replace: keep what is there, add what is new
                new += merged[i1:i2]
                have = {k for k, _ in merged[i1:i2]}
                new += fresh([b for b in block[j1:j2] if b[0] not in have])
                last_of_block = len(new) - 1
        m = DECL_NAME_RE.search(r["statement"])
        written = m.group(1) if m else r["name"]
        ns = [n for k, n in stack if k == "namespace" and n]
        full = written[len("_root_.") :] if written.startswith("_root_.") else ".".join(ns + [written])
        key = "name:" + full
        if r.get("original_name"):
            alias[key] = "name:" + r["original_name"]
        present = {k for k, _ in new}
        if full not in deps_names and key not in present and alias.get(key) not in present:
            # after its own block, and after the theorems above it in the file (its prefix omits them)
            at = last_of_block + 1
            line = int(mm.group(1)) if mm else 0
            keys = [k for k, _ in new]
            for n, k in placed:
                if n <= line and k in keys:
                    at = max(at, keys.index(k) + 1)
            new.insert(at, (key, "\n".join(own_lead + [theorem_text(r["statement"], r["proof"])])))
        placed.append((int(mm.group(1)) if mm else 0, key))
        at_line = orig_line(r) if orig_line else None
        if at_line is not None:
            raw.append((at_line, key))
        merged = new
    # An agent's script restates what it needs (the prelude modules and the file's earlier declarations, inlined as
    # plain text), so its context is not merged: the file module already has those declarations. Its theorem goes
    # where the original stood — right after the nearest marked theorem above it in the source file, where the same
    # namespaces and variables are open; at the end when that is unknown. A helper the agent changed would fail the
    # build: such a module is refused, never trusted.
    for r in agent:
        line = orig_line(r) if orig_line else None
        at = len(merged)
        if line is not None:
            keys = [k for k, _ in merged]
            before = [k for n, k in sorted(raw) if n <= line and k in keys]
            if before:
                at = keys.index(before[-1]) + 1
        stack: list[tuple[str, str]] = []
        for k, text in merged[:at]:
            first = text.lstrip().splitlines()[0] if text.strip() else ""
            s, e = SCOPE_RE.match(first), END_RE.match(first)
            if k.startswith("text:") and s:
                stack.append((s.group(1), s.group(2)))
            elif k.startswith("text:") and e and stack:
                stack.pop()
        statement = r["statement"]
        m = DECL_NAME_RE.search(statement)
        written = m.group(1) if m else r["name"]
        ns = [n for kind, n in stack if kind == "namespace" and n]
        full = written[len("_root_.") :] if written.startswith("_root_.") else ".".join(ns + [written])
        if m and full != r["name"]:  # the namespaces open here are not the original's: name it in full
            statement = statement[: m.start(1)] + "_root_." + r["name"] + statement[m.end(1) :]
            full = r["name"]
        present = {k for k, _ in merged}
        if full in deps_names or ("name:" + full) in present or (r.get("original_name") and "name:" + r["original_name"] in present):
            continue
        merged.insert(at, ("name:" + full, theorem_text(statement, r["proof"])))
        if line is not None:
            raw.append((line, "name:" + full))
    parts = [text for _, text in merged]
    # a lead-in whose declaration went (deduplicated, or in Deps) would attach to whatever follows it
    kept: list[str] = []
    for i, text in enumerate(parts):
        nxt = parts[i + 1] if i + 1 < len(parts) else ""
        if is_lead_in(text) and not (DECL_NAME_RE.search(nxt) and not is_lead_in(nxt)):
            continue
        kept.append(text)
    return kept


def regenerate_equations(corpus: Path, corpus_roots: list[str]) -> list[str]:
    out = []
    for f in sorted(f for root in corpus_roots for f in (corpus / root / "Equations").glob("*.lean")):
        for m in EQUATION_LINE_RE.finditer(f.read_text(encoding="utf-8")):
            law = m.group(2)
            vars_ = []
            for t in re.finditer(r"[A-Za-z_][A-Za-z0-9_']*", law):
                if t.group(0) not in vars_:
                    vars_.append(t.group(0))
            out.append(f"abbrev Equation{m.group(1)} (G : Type uEq) [Magma G] : Prop := ∀ {' '.join(vars_)} : G, {law}")
    return out


def data_files(out: Path, tier: str, library: str) -> list[Path]:
    """data/<tier>/<library>.jsonl plus data/<tier>/<library>/*.jsonl — contributors add one file per PR so appends never conflict."""
    flat = out / "data" / tier / f"{library}.jsonl"
    nested = sorted((out / "data" / tier / library).glob("*.jsonl")) if (out / "data" / tier / library).is_dir() else []
    return ([flat] if flat.exists() else []) + nested


def tombstoned_names(out: Path, library: str) -> list[str]:
    """Names retracted by tombstone lines in the library's trusted files."""
    names = []
    for p in data_files(out, "trusted", library):
        for line in p.read_text(encoding="utf-8").splitlines():
            if line.strip():
                r = json.loads(line)
                if "tombstone" in r:
                    names.append(str(r["tombstone"]))
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True, help="checkout of the corpus (dir containing e.g. equational_theories/)")
    ap.add_argument("--libraries", nargs="*", default=["equational-theories"])
    ap.add_argument("--out", default=".")
    ap.add_argument("--only", default=None, help="regenerate just this source_path's module (Deps and the aggregator are still refreshed)")
    ap.add_argument(
        "--candidate",
        default=None,
        help="generate this source_path's module from its trusted AND staging records into a `_candidate_` sibling file (the real module and aggregator are untouched); promote.py builds it before trusting the records",
    )
    ap.add_argument(
        "--candidate-names",
        default="",
        help="with --candidate: only these staging records (comma-separated names) join the trusted ones; the merge queue passes the group's own records so an older broken staging record of the same file cannot fail someone else's PR",
    )
    args = ap.parse_args()
    if args.candidate:
        args.only = args.candidate
    out = Path(args.out).resolve()
    corpus = Path(args.corpus).expanduser().resolve()

    for library in args.libraries:
        lib_ns = pascal(library)
        roots = corpus_roots(out, library)
        records = []
        # A tombstone line {"tombstone": "<name>", ...} in a trusted file retracts every record of that name
        # (history stays in the file). The campaign found the schema accepted tombstones that changed nothing.
        retracted = set(tombstoned_names(out, library))
        for tier in DATA_TIERS:
            for p in data_files(out, tier, library):
                for line in p.read_text(encoding="utf-8").splitlines():
                    if line.strip():
                        r = json.loads(line)
                        if "tombstone" in r or r.get("name") in retracted:
                            continue
                        if r.get("source_path") and r.get("context") is not None:
                            records.append(r)
        if args.candidate:
            only_names = set(args.candidate_names.split(",")) if args.candidate_names else None
            for p in data_files(out, "staging", library):
                for line in p.read_text(encoding="utf-8").splitlines():
                    if line.strip():
                        r = json.loads(line)
                        if "tombstone" in r or r.get("name") in retracted:
                            continue
                        if r.get("source_path") == args.candidate and r.get("context") is not None:
                            if only_names is None or r.get("name") in only_names:
                                records.append(r)
        if not records:
            print(f"{library}: no trusted records with source_path/context — modules on disk are removed, Deps kept")

        lib_dir = out / "Tengoku" / lib_ns
        deps_dir = lib_dir / "Deps"
        deps_dir.mkdir(parents=True, exist_ok=True)
        external = seed_heads(out)

        mode = generator_of(out, library)
        order: list[str] = []
        keys: dict[str, str] = {}
        eqs: list[str] = []
        if mode == "verified":
            # ---- Deps: every prelude block the records' contexts carry, as verified; the corpus is never read
            written_before = set(deps_dir.rglob("*.lean"))
            order, keys = verified_deps(records, deps_dir, lib_ns, corpus if corpus.is_dir() else None, roots)
            for f in written_before - {deps_file(deps_dir, k) for k in keys.values()}:
                f.unlink()  # a module no record's context carries any more
            deps_available = set(keys.values())
            pasted = set()
        else:
            # ---- Deps: the corpus modules any context pasted verbatim, plus all equations
            pasted = set()
            for r in records:
                pasted.update(PRELUDE_MODULE_RE.findall(r["context"]))
            deps_available = {deps_key(m) for m in pasted}
        for mod in sorted(pasted):
            src = corpus / Path(*mod.split(".")).with_suffix(".lean")
            text = src.read_text(encoding="utf-8")
            if UNSAFE_MODULE_RE.search(text):
                print(f"  skip {mod}: needs load-time initialisation")
                continue
            body = strip_corpus_attrs(map_imports(text, roots, lib_ns, deps_available, corpus))
            imports = "\n".join(l for l in body.splitlines() if re.match(r"\s*(public |private |meta )*import ", l))
            rest = "\n".join(l for l in body.splitlines() if not re.match(r"\s*(public |private |meta )*import ", l))
            leaf = deps_key(mod)
            deps_file(deps_dir, leaf).write_text(
                f"-- {lib_ns}/Deps/{leaf}: verbatim from {mod} (imports mapped, corpus bookkeeping attributes stripped)\n"
                f"{imports}\nimport Tengoku.Init\n\nset_option linter.all false\n\n{wrap(rest, lib_ns, external)}",
                encoding="utf-8",
            )
        if mode != "verified":
            eqs = regenerate_equations(corpus, roots)
        if eqs and (deps_dir / "Magma.lean").exists():  # the abbrevs need Magma; without it the file would not build
            (deps_dir / "Equations.lean").write_text(
                f"-- {lib_ns}/Deps/Equations: every `equation N := law` of the corpus, in the exact shape its `equation` command produces\n"
                f"import Tengoku.{lib_ns}.Deps.Magma\n\nset_option linter.all false\n\n"
                + wrap("universe uEq\n\n" + "\n".join(eqs), lib_ns, external),
                encoding="utf-8",
            )
        deps_mods = deps_modules(deps_dir)
        (lib_dir / "Deps.lean").write_text("\n".join(f"import Tengoku.{lib_ns}.Deps.{m}" for m in deps_mods) + "\n", encoding="utf-8")
        deps_names, deps_lines = deps_declared(deps_dir)
        deps_full = set()
        if mode == "verified":
            for f in deps_dir.rglob("*.lean"):
                deps_full |= qualified_names(f.read_text(encoding="utf-8"))

        # ---- One module per original source file
        by_file: dict[str, list[dict]] = {}
        for r in records:
            by_file.setdefault(r["source_path"], []).append(r)
        warnings = 0
        for source_path, recs in sorted(by_file.items()):
            if args.only and source_path != args.only:
                continue
            rel = Path(source_path)
            if rel.parts and rel.parts[0] in roots:
                rel = Path(*rel.parts[1:])
            mod_path = lib_dir / rel
            mod_name = f"Tengoku.{lib_ns}." + ".".join(rel.with_suffix("").parts)
            if args.candidate:
                mod_path = mod_path.with_name("_candidate_" + mod_path.name)
                head, leaf = mod_name.rsplit(".", 1)
                mod_name = f"{head}._candidate_{leaf}"

            def line_of(r):
                m = re.search(r"#L(\d+)", r.get("source_url") or "")
                return int(m.group(1)) if m else 0

            if mode == "verified":
                # the own-file marker says where the theorem is ("everything before line N"); a record without one (an
                # agent's self-contained script) goes last. source_url carries no #L for these libraries.
                def marker_line(r):
                    mm = re.search(r"^-- \[Emissary\] \S+, everything before line (\d+)", r["context"], re.M)
                    return int(mm.group(1)) if mm else (line_of(r) or 10**9)

                recs.sort(key=marker_line)
            else:
                recs.sort(key=line_of)

            # The file's own declarations: everything after the prelude marker in
            # a record's context (a marker-bearing record is preferred: its prefix
            # is the original file's, not an agent's self-contained rewrite).
            # Contexts that differ (an agent's fix) are noted; the build decides.
            def own_prefix(r):
                mm = FILE_MARKER_RE.search(r["context"])
                text = r["context"][mm.end() :] if mm else r["context"]
                text = "\n".join(l for l in text.splitlines() if not l.startswith("set_option linter.all false"))
                return dedupe_prefix(text, deps_names, deps_lines)

            # Walk the records in file order; before each theorem emit whatever
            # its context declares that the module does not have yet (a
            # definition sitting between two theorems is in the later one's
            # context, not the earlier one's), then the theorem itself. A
            # declaration is identified by its name, a structural line
            # (namespace/section/end/open/variable/…) by its text.
            emitted: set[str] = set()
            parts: list[str] = []

            def emit(text: str) -> None:
                text = text.strip()
                if not text:
                    return
                if text.rstrip().endswith(" in"):  # a modifier for the next declaration: never deduplicated
                    parts.append(text)
                    return
                m = DECL_NAME_RE.search(text)
                key = ("name:" + m.group(1).removeprefix("_root_.")) if m else ("text:" + " ".join(text.split()))
                if key in emitted:
                    return
                emitted.add(key)
                parts.append(text)

            if mode == "verified":

                def own_text(r):
                    mm = FILE_MARKER_RE.search(r["context"])
                    if mm:
                        text = r["context"][mm.end() :]
                    else:  # an agent's script: its prelude blocks are Deps already
                        text = r["context"]
                        for _, block in prelude_blocks(text):
                            text = text.replace(block.rstrip("\n"), "")
                        text = PRELUDE_ANY_RE.sub("", text)
                    return "\n".join(l for l in text.splitlines() if not l.startswith("set_option linter.all false"))

                src_text = (corpus / source_path).read_text(encoding="utf-8", errors="ignore") if (corpus / source_path).is_file() else ""

                def orig_line(r):
                    bare = r["name"].rsplit(".", 1)[-1]
                    mm = re.search(
                        r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|nonrec)[ \t]+)*(?:theorem|lemma)[ \t]+(?:[\w'.«»]*\.)?"
                        + re.escape(bare)
                        + r"(?![\w'])",
                        src_text,
                        re.M,
                    )
                    return src_text.count("\n", 0, mm.start()) + 1 if mm else None

                parts = verified_file_body(recs, own_text, deps_full, orig_line)
            for r in [] if mode == "verified" else recs:
                for chunk in top_level_chunks(own_prefix(r)):
                    emit("\n".join(chunk))
                emit(f"{strip_corpus_attrs(r['statement'])}\n{strip_trailing_ends(r['proof'])}")
            body = "\n\n".join(parts)
            if mode == "verified":
                # Tengoku (the whole seed: the records were verified with the tree in scope) and the Deps this file's
                # records carry, plus its own Deps module when the file is itself another record's prelude
                rank = {m: i for i, m in enumerate(order)}
                own_mod = ".".join(Path(source_path).with_suffix("").parts)
                mods = {m for r in recs for m, _ in prelude_blocks(r["context"])} | ({own_mod} if own_mod in keys else set())
                imports = "\n".join(["import Tengoku"] + [f"import Tengoku.{lib_ns}.Deps.{keys[m]}" for m in sorted(mods, key=rank.get)])
                closers = unclosed_scopes(body)
                if closers:
                    body += "\n\n" + "\n".join(closers)
                mod_path.parent.mkdir(parents=True, exist_ok=True)
                mod_path.write_text(
                    f"-- {mod_name}: verified translations of {source_path} ({len(recs)} theorem{'s' if len(recs) != 1 else ''})\n"
                    f"{imports}\n\nset_option linter.all false\n\n{body}\n",
                    encoding="utf-8",
                )
                continue
            # Import what the ORIGINAL file imported, mapped into the tree —
            # not the whole tree: builds stay proportional to the file, and a
            # module is testable against a partial build.
            orig = corpus / source_path
            orig_imports = []
            if orig.exists():
                mapped = map_imports(orig.read_text(encoding="utf-8"), roots, lib_ns, deps_available, corpus)
                orig_imports = [l.strip() for l in mapped.splitlines() if re.match(r"\s*(public |private |meta )*import ", l)]
                orig_imports = [re.sub(r"^(public |private |meta )+", "", l) for l in orig_imports]
            # The Deps this file's records pasted (plus Magma/Equations, which
            # every equation abbrev needs) — not the Deps aggregator, so a corpus
            # module first pasted by some OTHER file does not rebuild this one.
            needed = {deps_key(m) for r in recs for m in PRELUDE_MODULE_RE.findall(r["context"])} & deps_available
            needed |= {d for d in ("Magma", "Equations") if d in deps_mods}
            dep_imports = [f"import Tengoku.{lib_ns}.Deps.{d}" for d in sorted(needed)]
            # A mechanical record is the original text, which compiled with its
            # file's own imports. An agent-written one (no prelude marker) was
            # verified with the whole tree in scope and may lean on any seeded
            # lemma, so such a file imports the seeded root as well.
            if any(not FILE_MARKER_RE.search(r["context"]) for r in recs):
                orig_imports = ["import Tengoku"] + orig_imports
            imports = "\n".join(dict.fromkeys(orig_imports + dep_imports))
            closers = unclosed_scopes(body)
            if closers:
                body += "\n\n" + "\n".join(closers)
            mod_path.parent.mkdir(parents=True, exist_ok=True)
            mod_path.write_text(
                f"-- {mod_name}: verified translations of {source_path} ({len(recs)} theorem{'s' if len(recs) != 1 else ''})\n"
                f"{imports}\n\nset_option linter.all false\n\n{wrap(body, lib_ns, external - deps_names)}",
                encoding="utf-8",
            )

        # A module on disk that no trusted record backs any more is removed —
        # a file whose records went back to staging must not stay importable.
        def mod_path_of(source_path: str) -> Path:
            rel = Path(source_path)
            if rel.parts and rel.parts[0] in roots:
                rel = Path(*rel.parts[1:])
            return lib_dir / rel

        backed = {mod_path_of(sp) for sp in by_file}
        stale = (
            []
            if args.candidate
            else [mod_path_of(args.only)]
            if args.only
            else [
                p
                for p in lib_dir.rglob("*.lean")
                if "Deps" not in p.relative_to(lib_dir).parts and p.name != "Deps.lean" and not p.name.startswith("_candidate_")
            ]
        )
        for p in stale:
            if p not in backed and p.exists():
                p.unlink()
                print(f"  removed {p.relative_to(out)}: no trusted record backs it")
        # The aggregator lists every file module on disk (not just this run's),
        # so a `--only` regeneration keeps the whole library importable.
        modules = sorted(
            f"Tengoku.{lib_ns}." + ".".join(p.relative_to(lib_dir).with_suffix("").parts)
            for p in lib_dir.rglob("*.lean")
            if "Deps" not in p.relative_to(lib_dir).parts and p.name != "Deps.lean" and not p.name.startswith("_candidate_")
        )
        (out / "Tengoku" / f"{lib_ns}.lean").write_text(
            f"import Tengoku.{lib_ns}.Deps\n" + "\n".join(f"import {m}" for m in modules) + "\n", encoding="utf-8"
        )
        clash_note = ""
        if mode == "verified":
            try:
                all_libraries = list(json.loads((out / "schemas" / "sources.json").read_text(encoding="utf-8")).get("corpora", {}))
            except (OSError, ValueError):
                all_libraries = []
            clash_note = rename_clashes(out, lib_dir, library, all_libraries)
        print(
            f"{library}: {len(records)} records -> {len(modules)} file modules on disk, {len(deps_mods)} Deps modules ({len(eqs)} equations); {warnings} context notes"
            + (f"; {clash_note}" if clash_note else "")
        )

    # Tengoku/All.lean: everything, for tools that index or import "the whole
    # tree" (loogle, the verifier's injected import). A legacy-style file can
    # import both the module-system root and the legacy translation modules;
    # the root itself cannot.
    libs = sorted(
        p.stem
        for p in (out / "Tengoku").glob("*.lean")
        if p.stem not in {"All", "Init", "Tactic", "Std", "Widgets"}
        and (out / "Tengoku" / p.stem).is_dir()
        and (out / "Tengoku" / p.stem / "Deps.lean").exists()
    )
    (out / "Tengoku" / "All.lean").write_text(
        "-- Everything in the tree: the seeded root plus every library of verified additions.\nimport Tengoku\n"
        + "\n".join(f"import Tengoku.{l}" for l in libs)
        + "\n",
        encoding="utf-8",
    )
    print(f"Tengoku/All.lean: root + {', '.join(libs) or 'no additions yet'}")


if __name__ == "__main__":
    main()
