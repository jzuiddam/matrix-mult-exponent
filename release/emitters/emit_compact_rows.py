#!/usr/bin/env python3
"""Emit a compact row-bridge cohort.

    emit_compact_rows.py REPO --cohort R0Y0 [--ref COMMIT | --triples DIR] [--check]
                         [--corrupt-parent P] [--out-name NAME]

Input: the generated triple `ADVXXZGeneralRowsBridge<C>{Source30,Leaves30,Final30}` of cohort C,
read from git at REF (so the tool keeps working after the triple is retired), or, with
`--triples DIR`, from `DIR/OmegaBound/ADVXXZGeneralRowsBridge<C>*.lean` (a directory holding those
three modules; no git history needed).  REF defaults to the
development-repository commit that last carried the triples: `375cd738…`, the intermediate tree
of this release (earlier candidates used `6d22de9e…` for cohort R0Y0 and `7c79479a…` for the other
95; `--ref` still accepts them, and they emit the same modules).

Output, under REPO/OmegaBound/:

  ReleaseCompactRowsBase.lean   (shared, cohort-independent; emitted once)
      the generic kernel theorem `value_eq_of_sameCoefs130f`: two rows with equal constants and
      equal per-atom coefficient totals have equal real values.

  ReleaseCompactRows<C>Check.lean
      * every `def` of the triple, byte-identical, in source order (the released row data:
        occurrence/left/node/level tables, child and beta profiles, the literal rows);
      * ONE `native_decide` theorem `rowsCompact<C>_check`: the conjunction, per parent, of every
        theorem statement of the triple (function equalities pointwise; the one real-valued
        statement `_raw_value_compact30` replaced by its decidable certificate `SameCoefs130f`);
      * every theorem of the triple re-declared with its statement text unchanged, proved by a
        kernel projection of that conjunction (+ `funext`, or + the generic theorem above);
      * the `Final30` theorems `rowsCell…_raw`, byte-identical (they are kernel terms).

The consumer `ADVXXZGeneralRowsCells<C>` then imports `ReleaseCompactRows<C>Check` instead of
`ADVXXZGeneralRowsBridge<C>Final30`; nothing else changes.

--corrupt-parent P writes a teeth variant (module name from --out-name) in which one numerator
of parent P's literal row `rowsCell…Raw30` is incremented by one.
--check compares the emitted text with the files on disk instead of writing.
--rewire replaces, in `ADVXXZGeneralRowsCells<C>`, the import of the retired `…Final30` by the
compact module, and refuses to write unless the import-stripped body is byte-identical before and
after (its SHA-256 is printed).
"""

from __future__ import annotations

import argparse
import hashlib
import pathlib
import re
import subprocess
import sys

TRIPLE = ("Source30", "Leaves30", "Final30")
DECL_RE = re.compile(r"^(theorem|def|noncomputable def) (\S+)")

BASE = '''import OmegaBound.ADVXXZT6Round130fEvaluator

/-!
# Release compaction: generic soundness shared by the compact row cohorts

Emitted by `release/emitters/emit_compact_rows.py`.  One kernel theorem, independent of every
released row: a `LinearQ130f` row's real value depends only on its constant and on the total
coefficient of each formal atom.  Cohort checks certify `SameCoefs130f` natively and obtain the
real-valued equality between a literal row and its compact (merged, zero-free) form from here.
-/

namespace OmegaBound.ReleaseCompactRows

open OmegaBound.ADVXXZT6Round130f

/-- Total coefficient of the formal atom `a` in a term list. -/
def coefSum130f : List (AtomQ130f × ℚ) → AtomQ130f → ℚ
  | [], _ => 0
  | x :: xs, a => (if x.1 = a then x.2 else 0) + coefSum130f xs a

/-- Equal constants and equal coefficient totals at every atom occurring in either row. -/
def SameCoefs130f (e f : LinearQ130f) : Prop :=
  e.constant = f.constant ∧
    ∀ x ∈ e.terms ++ f.terms, coefSum130f e.terms x.1 = coefSum130f f.terms x.1

instance (e f : LinearQ130f) : Decidable (SameCoefs130f e f) := by
  unfold SameCoefs130f
  infer_instance

theorem termsValue130f_eq_sum (xs : List (AtomQ130f × ℚ)) (S : Finset AtomQ130f)
    (hS : ∀ x ∈ xs, x.1 ∈ S) :
    termsValue130f xs = ∑ a ∈ S, (coefSum130f xs a : ℝ) * a.value := by
  induction xs with
  | nil => simp [termsValue130f, coefSum130f]
  | cons x xs ih =>
    have hx : x.1 ∈ S := hS x (by simp)
    have hrest := ih (fun y hy => hS y (by simp [hy]))
    have hcons : termsValue130f (x :: xs) = (x.2 : ℝ) * x.1.value + termsValue130f xs := by
      simp [termsValue130f]
    rw [hcons, hrest]
    simp only [coefSum130f, Rat.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single_of_mem x.1 hx]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]

theorem value_eq_of_sameCoefs130f (e f : LinearQ130f) (h : SameCoefs130f e f) :
    e.value = f.value := by
  classical
  obtain ⟨hc, hall⟩ := h
  let S : Finset AtomQ130f := ((e.terms ++ f.terms).map Prod.fst).toFinset
  have hS : ∀ x ∈ e.terms ++ f.terms, x.1 ∈ S := fun x hx =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
  unfold LinearQ130f.value
  rw [hc, termsValue130f_eq_sum e.terms S (fun x hx => hS x (List.mem_append_left _ hx)),
    termsValue130f_eq_sum f.terms S (fun x hx => hS x (List.mem_append_right _ hx))]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ha)
  rw [hall x hx]

end OmegaBound.ReleaseCompactRows
'''


# The commit that last carried the retired triples (see the module docstring).
REF_TRIPLES = "375cd7387547d005214ca9c25e4c92523977d4e2"   # intermediate tree of release-candidate-8
REF_PILOT = "6d22de9ec40989807e6269246dcd66fd760e0561"      # earlier: release-candidate-5, R0Y0
REF_REST = "7c79479a37d0a34f5270991dbf2e554d254e7753"       # earlier: release-candidate-6, the rest


def default_ref(cohort: str) -> str:
    return REF_TRIPLES


def git_show(repo: pathlib.Path, ref: str, rel: str) -> str:
    if ref.startswith("dir:"):
        return (pathlib.Path(ref[4:]) / rel).read_text()
    return subprocess.run(["git", "-C", str(repo), "show", f"{ref}:{rel}"], check=True,
                          capture_output=True, text=True).stdout


def blocks(text: str) -> tuple[list[str], list[str], list[tuple[str, str, str]]]:
    """(imports, opens/options header lines, [(kind, name, block text)]) of a generated module.
    A block is a column-0 `def`/`theorem` line with every following line up to the next
    non-empty column-0 line; `set_option … in` lines directly above a def are kept with it."""
    lines = text.split("\n")
    imports = [l for l in lines if l.startswith("import ")]
    header = [l for l in lines if l.startswith("open ") or l.startswith("set_option linter")]
    out: list[tuple[str, str, str]] = []
    i = 0
    while i < len(lines):
        m = DECL_RE.match(lines[i])
        if not m:
            i += 1
            continue
        j = i
        while j > 0 and lines[j - 1].startswith("set_option ") and lines[j - 1].endswith(" in"):
            j -= 1
        k = i + 1
        while k < len(lines) and (lines[k] == "" or lines[k][0] in " \t|"):
            k += 1
        body = "\n".join(lines[i:k]).rstrip("\n")
        prefix = "\n".join(lines[j:i])
        kind = "def" if "def" in m.group(1) else "theorem"
        out.append((kind, m.group(2), (prefix + "\n" + body) if (prefix and kind == "def") else body))
        i = k
    return imports, header, out


def split_theorem(block: str, name: str) -> tuple[str, str, str]:
    """(binders, statement, proof) of `theorem name binders : statement := proof`."""
    rest = block[len("theorem ") + len(name):]
    depth, colon = 0, None
    for idx, ch in enumerate(rest):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and rest[idx + 1] != "=":
            colon = idx
            break
    assert colon is not None, name
    binders = rest[:colon].strip()
    tail = rest[colon + 1:]
    depth = 0
    for idx, ch in enumerate(tail):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif tail.startswith(":=", idx) and depth == 0:
            return binders, tail[:idx].strip(), tail[idx + 2:].strip()
    raise AssertionError(name)


FUN_EQ = ("_betaChild30", "_betaRegion_literal30", "_selectedBeta_literal30")
FUN_EQ_VAR = {"_betaChild30": "i", "_betaRegion_literal30": "i", "_selectedBeta_literal30": "i"}
FUN_EQ_DOM = {"_betaChild30": "Fin 9", "_betaRegion_literal30": "Fin 81",
              "_selectedBeta_literal30": "Fin 9"}


def binder_vars(binders: str) -> list[str]:
    names = []
    for grp in re.findall(r"\(([^():]+):", binders):
        names += grp.split()
    return names


def conjunct(name: str, binders: str, stmt: str) -> tuple[str, str]:
    """(decidable conjunct text, proof of the original statement from `h`)."""
    vars_ = binder_vars(binders)
    app = " ".join(["h"] + vars_)
    suffix = next((s for s in FUN_EQ if name.endswith(s)), None)
    if suffix:
        lhs, rhs = [s.strip() for s in stmt.split(" =\n", 1)] if " =\n" in stmt else \
            [s.strip() for s in stmt.split(" = ", 1)]
        v = FUN_EQ_VAR[suffix]
        body = f"∀ {v} : {FUN_EQ_DOM[suffix]}, ({lhs}) {v} = ({rhs}) {v}"
        proof = f"funext ({app})"
    elif name.endswith("_raw_value_compact30"):
        m = re.fullmatch(r"(\S+)\.value = (\S+)\.value", " ".join(stmt.split()))
        assert m, stmt
        body = f"OmegaBound.ReleaseCompactRows.SameCoefs130f {m.group(1)} {m.group(2)}"
        proof = f"OmegaBound.ReleaseCompactRows.value_eq_of_sameCoefs130f _ _ {app}"
    else:
        body = " ".join(stmt.split())
        proof = app
    if binders:
        body = f"∀ {binders}, {body}"
    return "(" + " ".join(body.split()) + ")", proof


def emit_cohort(repo: pathlib.Path, ref: str, cohort: str, module: str,
                corrupt_parent: int | None) -> str:
    srcs = {t: git_show(repo, ref, f"OmegaBound/ADVXXZGeneralRowsBridge{cohort}{t}.lean") for t in TRIPLE}
    imports: list[str] = []
    header: list[str] = []
    decls: list[tuple[str, str, str, str]] = []
    for t in TRIPLE:
        imp, hdr, bl = blocks(srcs[t])
        imports += [i for i in imp if "ADVXXZGeneralRowsBridge" + cohort not in i and i not in imports]
        header += [h for h in hdr if h not in header]
        decls += [(t, *b) for b in bl]
    imports.append("import OmegaBound.ReleaseCompactRowsBase")
    defs = [(n, b) for t, k, n, b in decls if k == "def"]
    thms = [(t, n, b) for t, k, n, b in decls if k == "theorem"]
    if corrupt_parent is not None:
        tag = f"P{corrupt_parent:03d}Raw30"
        for idx, (n, b) in enumerate(defs):
            if n.endswith(tag) and n.startswith("rowsCell"):
                m = re.search(r"\(\(([0-9]+) : ℚ\)", b)
                assert m
                b = b[:m.start(1)] + str(int(m.group(1)) + 1) + b[m.end(1):]
                defs[idx] = (n, b)
                break
        else:
            raise SystemExit(f"no literal row {tag}")
    parent_of = lambda n: re.search(r"P([0-9]{3})", n).group(1)
    parents: list[str] = []
    per: dict[str, list[tuple[str, str, str]]] = {}
    finals: list[str] = []
    for t, n, b in thms:
        if t == "Final30":
            finals.append(b)
            continue
        binders, stmt, _ = split_theorem(b, n)
        c, proof = conjunct(n, binders, stmt)
        p = parent_of(n)
        if p not in per:
            parents.append(p)
            per[p] = []
        per[p].append((n, binders, stmt, c, proof))
    ns = f"rowsCompact{cohort}"
    out = [f"-- GENERATED by release/emitters/emit_compact_rows.py.  Do not edit by hand.\n"]
    out += [i + "\n" for i in imports]
    out.append("\n")
    out += [h + "\n" for h in header]
    out.append("namespace OmegaBound.ADVXXZGeneral\n\n")
    out.append(f"/-! ## Released row data of cohort {cohort}: every definition of the retired triple\n"
               f"`ADVXXZGeneralRowsBridge{cohort}{{Source30,Leaves30,Final30}}`, byte-identical. -/\n\n")
    for _, b in defs:
        out.append(b + "\n\n")
    out.append(f"/-! ## One native check: every theorem statement of the retired triple, per parent. -/\n\n")
    conj_parents = []
    for p in parents:
        conj_parents.append("(" + " ∧\n    ".join(c for _, _, _, c, _ in per[p]) + ")")
    out.append(f"set_option maxRecDepth 1000000 in\n")
    out.append(f"set_option synthInstance.maxSize 1000000 in\n")
    out.append(f"set_option synthInstance.maxHeartbeats 4000000 in\n")
    out.append(f"theorem {ns}_check :\n    " + " ∧\n  ".join(conj_parents) + " := by\n  native_decide\n\n")
    out.append(f"/-! ## Kernel projections onto the retired names, statements unchanged. -/\n\n")
    for pi, p in enumerate(parents):
        base = f"{ns}_check" + ".2" * pi + (".1" if pi < len(parents) - 1 else "")
        k = len(per[p])
        for ti, (n, binders, stmt, _, proof) in enumerate(per[p]):
            proj = base + ".2" * ti + (".1" if ti < k - 1 else "")
            head = f"theorem {n}" + (f" {binders}" if binders else "") + " :\n    " + stmt
            out.append(f"{head} :=\n  have h := {proj}\n  {proof}\n\n")
    out.append("/-! ## The cohort's exports to `ADVXXZGeneralRowsCells`, byte-identical. -/\n\n")
    for b in finals:
        out.append(b + "\n\n")
    out.append("end OmegaBound.ADVXXZGeneral\n")
    return "".join(out)


def stripped_sha(text: str) -> str:
    body = "\n".join(l for l in text.split("\n") if not l.startswith("import "))
    return hashlib.sha256(body.encode()).hexdigest()


def rewire(repo: pathlib.Path, cohort: str, module: str) -> int:
    p = repo / "OmegaBound" / f"ADVXXZGeneralRowsCells{cohort}.lean"
    old = p.read_text()
    line = f"import OmegaBound.ADVXXZGeneralRowsBridge{cohort}Final30\n"
    assert old.count(line) == 1, "consumer does not import the retired Final30 exactly once"
    new = old.replace(line, f"import OmegaBound.{module}\n")
    before, after = stripped_sha(old), stripped_sha(new)
    if before != after:
        print("REFUSED: import-stripped body changed", file=sys.stderr)
        return 1
    p.write_text(new)
    print(f"rewired {p.name}: import-stripped SHA-256 {after} (unchanged)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo")
    ap.add_argument("--cohort", required=True)
    ap.add_argument("--ref", default=None,
                    help="commit holding the triple (default: the pinned commit id of the cohort)")
    ap.add_argument("--triples", type=pathlib.Path, default=None,
                    help="read the triple from DIR/OmegaBound/ instead of git")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--corrupt-parent", type=int)
    ap.add_argument("--out-name")
    ap.add_argument("--rewire", action="store_true")
    args = ap.parse_args()
    repo = pathlib.Path(args.repo).resolve()
    if args.triples is not None and args.ref is not None:
        ap.error("--ref and --triples are exclusive")
    ref = f"dir:{args.triples.resolve()}" if args.triples is not None else (args.ref or default_ref(args.cohort))
    module = args.out_name or f"ReleaseCompactRows{args.cohort}Check"
    if args.rewire:
        return rewire(repo, args.cohort, module)
    files = {"ReleaseCompactRowsBase.lean": BASE,
             f"{module}.lean": emit_cohort(repo, ref, args.cohort, module, args.corrupt_parent)}
    if args.corrupt_parent is not None:
        files.pop("ReleaseCompactRowsBase.lean")
    bad = 0
    for name, text in files.items():
        p = repo / "OmegaBound" / name
        if args.check:
            if not p.exists() or p.read_text() != text:
                print(f"DIFFERS {name}", file=sys.stderr)
                bad += 1
        else:
            p.write_text(text)
            print(f"wrote {p} ({len(text.encode())} B)")
    if args.check:
        print(f"check: {len(files) - bad}/{len(files)} identical")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
