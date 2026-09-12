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
"""
import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from seed import PACKAGES, IMPORT_RE, module_map  # noqa: E402

DATA_TIERS = ("staging", "trusted")
FILE_MARKER_RE = re.compile(r"^-- \[Emissary\] (\S+), everything before line \d+[^\n]*\n", re.M)
PRELUDE_MODULE_RE = re.compile(r"^-- \[Emissary prelude\] (\S+) — verbatim", re.M)
EQUATION_LINE_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*equation\s+(\d+)\s*:=\s*(.+?)\s*$", re.M)
UNSAFE_MODULE_RE = re.compile(r"^\s*(?:scoped\s+)?(initialize|builtin_initialize|register_simp_attr|register_option|register_label_attr|register_tag_attr|register_parametric_attr)\b", re.M)


# Namespacing a corpus module (`namespace EquationalTheories … end`) keeps its
# own names (Magma, EquationN, FreeMagma) from clashing with seeded ones — but
# a corpus file also EXTENDS outside namespaces (`def Lean.MVarId.congrWith`,
# `theorem Eq.comm'`), and inside the wrapper those would silently become
# `EquationalTheories.Lean.MVarId.congrWith`, breaking every `m.congrWith`.
# A dotted declaration whose head is an outside namespace gets `_root_.`;
# a module that opens an outside namespace block is left unwrapped.
TOOLCHAIN_ROOTS = set("""
Lean Init Std Eq Ne HEq Nat Int List Array String Char Option Prod Sum Fin Function Sigma PSigma Subtype Quot Quotient
Decidable Bool Iff And Or Not Exists True False Unit PUnit IO Task Id StateT ReaderT ExceptT Except Monad Functor
Applicative HashMap HashSet RBMap ByteArray Float UInt8 UInt16 UInt32 UInt64 USize Empty PEmpty Classical WellFounded Acc
Setoid Equivalence Inhabited Nonempty Subsingleton DecidableEq BEq Hashable Ord LT LE Add Mul Sub Div Neg HAdd HMul HSub HDiv
Membership Singleton Insert EmptyCollection Union Inter SDiff HasSubset Coe CoeFun CoeSort Zero One Dvd Mod Pow HPow Append
GetElem Bind Pure Seq SeqLeft SeqRight ToString Repr Format Syntax Name Expr Level MVarId FVarId Meta Elab Tactic Term Command
""".split())


def seed_heads(out: Path) -> set[str]:
    """First segments of every declaration/namespace in the seeded tree."""
    heads = set(TOOLCHAIN_ROOTS)
    rx = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public)\s+)*(?:namespace|def|theorem|lemma|abbrev|instance|opaque|axiom|inductive|structure|class)\s+([A-Za-z_][\w']*)", re.M)
    for f in (out / "Tengoku").rglob("*.lean"):
        if "EquationalTheories" in f.parts or "CompeteMath" in f.parts:
            continue
        try:
            heads.update(rx.findall(f.read_text(encoding="utf-8", errors="ignore")))
        except OSError:
            pass
    return heads


DECL_HEAD_RE = re.compile(r"^(\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*(?:def|theorem|lemma|abbrev|instance|opaque|axiom|inductive|structure|class)\s+)([A-Za-z_][\w']*)\.", re.M)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w']*)", re.M)


def rootify(body: str, external: set[str]) -> str:
    return DECL_HEAD_RE.sub(lambda m: f"{m.group(1)}{'_root_.' if m.group(2) in external else ''}{m.group(2)}.", body)


def opens_external_namespace(body: str, external: set[str]) -> bool:
    return any(h in external for h in NAMESPACE_RE.findall(body))


def wrap(body: str, lib_ns: str, external: set[str]) -> str:
    if opens_external_namespace(body, external):
        return f"-- left unwrapped: this module opens an outside namespace block\n{body.strip()}\n"
    return f"namespace {lib_ns}\n\n{rootify(body, external).strip()}\n\nend {lib_ns}\n"


def pascal(library: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_ ]+", library) if p)


def strip_corpus_attrs(text: str) -> str:
    def attrs(m):
        kept = [s.strip() for s in m.group(1).split(",") if s.strip() and not s.strip().startswith("equational_result")]
        return f"@[{', '.join(kept)}]" if kept else ""
    return re.sub(r"@\[([^\]]*)\]", attrs, text)


def map_imports(text: str, corpus_prefix: str, lib_ns: str, deps_available: set[str]) -> str:
    """Seed imports -> Tengoku.*; corpus imports -> this library's Deps modules (or dropped)."""
    roots = [(v[1], v[2]) for v in PACKAGES.values()]

    def sub(m):
        mod = m.group(2)
        if mod == corpus_prefix or mod.startswith(corpus_prefix + "."):
            leaf = mod.split(".")[-1]
            if leaf in deps_available:
                return f"{m.group(1)}Tengoku.{lib_ns}.Deps.{leaf}{m.group(3)}"
            return ""  # a corpus module we don't reproduce: nothing to import
        for root_mod, mapped in roots:
            new = module_map(root_mod, mapped, mod)
            if new:
                return f"{m.group(1)}{new}{m.group(3)}"
        return m.group(0)
    return IMPORT_RE.sub(sub, text)


def regenerate_equations(corpus: Path, corpus_prefix: str) -> list[str]:
    out = []
    for f in sorted((corpus / corpus_prefix / "Equations").glob("*.lean")):
        for m in EQUATION_LINE_RE.finditer(f.read_text(encoding="utf-8")):
            law = m.group(2)
            vars_ = []
            for t in re.finditer(r"[A-Za-z_][A-Za-z0-9_']*", law):
                if t.group(0) not in vars_:
                    vars_.append(t.group(0))
            out.append(f"abbrev Equation{m.group(1)} (G : Type uEq) [Magma G] : Prop := ∀ {' '.join(vars_)} : G, {law}")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True, help="checkout of the corpus (dir containing e.g. equational_theories/)")
    ap.add_argument("--libraries", nargs="*", default=["equational-theories"])
    ap.add_argument("--out", default=".")
    ap.add_argument("--only", default=None, help="regenerate just this source_path's module (Deps and the aggregator are still refreshed)")
    args = ap.parse_args()
    out = Path(args.out).resolve()
    corpus = Path(args.corpus).expanduser().resolve()

    for library in args.libraries:
        lib_ns = pascal(library)
        corpus_prefix = library.replace("-", "_")  # equational-theories -> equational_theories
        records = []
        for tier in DATA_TIERS:
            p = out / "data" / tier / f"{library}.jsonl"
            if not p.exists():
                continue
            for line in p.read_text(encoding="utf-8").splitlines():
                if line.strip():
                    r = json.loads(line)
                    if r.get("source_path") and r.get("context") is not None:
                        records.append(r)
        if not records:
            print(f"{library}: no records with source_path/context — nothing to generate")
            continue

        lib_dir = out / "Tengoku" / lib_ns
        deps_dir = lib_dir / "Deps"
        deps_dir.mkdir(parents=True, exist_ok=True)
        external = seed_heads(out)

        # ---- Deps: the corpus modules any context pasted verbatim, plus all equations
        pasted = set()
        for r in records:
            pasted.update(PRELUDE_MODULE_RE.findall(r["context"]))
        deps_available = {m.split(".")[-1] for m in pasted}
        for mod in sorted(pasted):
            src = corpus / Path(*mod.split(".")).with_suffix(".lean")
            text = src.read_text(encoding="utf-8")
            if UNSAFE_MODULE_RE.search(text):
                print(f"  skip {mod}: needs load-time initialisation")
                continue
            body = strip_corpus_attrs(map_imports(text, corpus_prefix, lib_ns, deps_available))
            imports = "\n".join(l for l in body.splitlines() if re.match(r"\s*(public |private |meta )*import ", l))
            rest = "\n".join(l for l in body.splitlines() if not re.match(r"\s*(public |private |meta )*import ", l))
            leaf = mod.split(".")[-1]
            (deps_dir / f"{leaf}.lean").write_text(
                f"-- {lib_ns}/Deps/{leaf}: verbatim from {mod} (imports mapped, corpus bookkeeping attributes stripped)\n"
                f"{imports}\nimport Tengoku.Init\n\nset_option linter.all false\n\n{wrap(rest, lib_ns, external)}",
                encoding="utf-8",
            )
        eqs = regenerate_equations(corpus, corpus_prefix)
        (deps_dir / "Equations.lean").write_text(
            f"-- {lib_ns}/Deps/Equations: every `equation N := law` of the corpus, in the exact shape its `equation` command produces\n"
            f"import Tengoku.{lib_ns}.Deps.Magma\n\nset_option linter.all false\n\n" + wrap("universe uEq\n\n" + "\n".join(eqs), lib_ns, external),
            encoding="utf-8",
        )
        deps_mods = sorted(p.stem for p in deps_dir.glob("*.lean"))
        (lib_dir / "Deps.lean").write_text("\n".join(f"import Tengoku.{lib_ns}.Deps.{m}" for m in deps_mods) + "\n", encoding="utf-8")

        # ---- One module per original source file
        by_file: dict[str, list[dict]] = {}
        for r in records:
            by_file.setdefault(r["source_path"], []).append(r)
        warnings = 0
        for source_path, recs in sorted(by_file.items()):
            if args.only and source_path != args.only:
                continue
            rel = Path(source_path)
            if rel.parts and rel.parts[0] == corpus_prefix:
                rel = Path(*rel.parts[1:])
            mod_path = lib_dir / rel
            mod_name = f"Tengoku.{lib_ns}." + ".".join(rel.with_suffix("").parts)

            def line_of(r):
                m = re.search(r"#L(\d+)", r.get("source_url") or "")
                return int(m.group(1)) if m else 0
            recs.sort(key=line_of)
            # The file's own declarations: everything after the prelude marker in the
            # first record's context. Contexts that differ (an agent's fix) are noted;
            # the build decides.
            first = recs[0]["context"]
            m = FILE_MARKER_RE.search(first)
            file_prefix = first[m.end():] if m else first
            file_prefix = "\n".join(l for l in file_prefix.splitlines() if not l.startswith("set_option linter.all false"))
            for r in recs[1:]:
                mm = FILE_MARKER_RE.search(r["context"])
                other = r["context"][mm.end():] if mm else r["context"]
                if other.strip() != file_prefix.strip():
                    warnings += 1
                    print(f"  note: {r['name']}: context differs from {recs[0]['name']}'s in {source_path} — using the first; the build decides")
            theorems = "\n\n".join(f"{strip_corpus_attrs(r['statement'])}\n{r['proof']}" for r in recs)
            # Import what the ORIGINAL file imported, mapped into the tree —
            # not the whole tree: builds stay proportional to the file, and a
            # module is testable against a partial build.
            orig = corpus / source_path
            orig_imports = []
            if orig.exists():
                mapped = map_imports(orig.read_text(encoding="utf-8"), corpus_prefix, lib_ns, deps_available)
                orig_imports = [l.strip() for l in mapped.splitlines() if re.match(r"\s*(public |private |meta )*import ", l)]
                orig_imports = [re.sub(r"^(public |private |meta )+", "", l) for l in orig_imports]
            imports = "\n".join(dict.fromkeys(orig_imports + [f"import Tengoku.{lib_ns}.Deps"]))
            mod_path.parent.mkdir(parents=True, exist_ok=True)
            mod_path.write_text(
                f"-- {mod_name}: verified translations of {source_path} ({len(recs)} theorem{'s' if len(recs) != 1 else ''})\n"
                f"{imports}\n\nset_option linter.all false\n\n{wrap(f'{file_prefix.strip()}\n\n{theorems}', lib_ns, external)}",
                encoding="utf-8",
            )
        # The aggregator lists every file module on disk (not just this run's),
        # so a `--only` regeneration keeps the whole library importable.
        modules = sorted(
            f"Tengoku.{lib_ns}." + ".".join(p.relative_to(lib_dir).with_suffix("").parts)
            for p in lib_dir.rglob("*.lean")
            if "Deps" not in p.relative_to(lib_dir).parts and p.name != "Deps.lean"
        )
        (out / "Tengoku" / f"{lib_ns}.lean").write_text(
            f"import Tengoku.{lib_ns}.Deps\n" + "\n".join(f"import {m}" for m in modules) + "\n", encoding="utf-8"
        )
        print(f"{library}: {len(records)} records -> {len(modules)} file modules on disk, {len(deps_mods)} Deps modules ({len(eqs)} equations); {warnings} context notes")


if __name__ == "__main__":
    main()
