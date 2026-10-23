"""Generate the concrete procedure table of the fixed-parameter program.

Adapted from the generator of the registered XP development's final program
table. The script reads every `structure ... (p : ℕ) where` record of procedure
ids and every `Matches` predicate in `MWIS/` and `MWIS/Fun/`, instantiates the
three root records

* `fptTop : RegisterTopLevel.Procedures P` (XP's top level),
* `fptHardIds : FPTRegister.Procedures P` (the fixed-parameter hard procedure),
* `fptInterp : Fun.Interp.Procedures P` (the `Fun` interpreter),

adds the two builder procedures `fptBuild1`, `fptBuild2` (bodies
`FPTBuild.buildBody t₁` and `FPTBuild.buildBody t₂`) and the two stage wrappers
(`fptHardIds.consts` = `FPTRunFun.wrap2Body fptBuild1 fptInterp.eval`,
`fptHardIds.funStage` = `FPTRunFun.wrap5Body fptBuild2 fptInterp.eval`), and
emits ordinary Lean:

* `MWIS/FPTProgramBodies*.lean`: for every equation `code X = body` of a
  `Matches` predicate, a definition of `body` as a function of the ids record
  (and the other parameters of the predicate), stated in the namespace and under
  the `open` lines of the source file;
* `MWIS/FPTProgramIds.lean`: the size `P` and the id records (numerals);
* `MWIS/FPTProgramTable*.lean`: the table `fptProgram (t₁ t₂ : Fun.Tree)`;
* `MWIS/FPTProgram.lean`: the `Matches` proofs (all by `rfl`, for all `t₁ t₂`).

Id fields that the predicates force to coincide (`code a = code b`, `a = b`,
and the hard procedure shared by the top level and the hard record) get one
number. Ids that no predicate constrains share a single `.fail` entry.

Usage: python3 scripts/gen_fpt_program.py
"""

from pathlib import Path
import re
import textwrap
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "MWIS"
PREFIX = "FPTProgram"
NS = "MWIS.FPTProgram"
BODY_SPLIT = 450
BLOCK = 32  # entries per block of the two-level table
BLOCKS_PER_FILE = 7  # approximate maximal lines per bodies file


# ---------------------------------------------------------------- parsing

def split_top(text, sep):
    """Split `text` at occurrences of `sep` outside brackets."""
    parts, depth, cur, i = [], 0, "", 0
    while i < len(text):
        c = text[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        if depth == 0 and text.startswith(sep, i):
            parts.append(cur)
            cur = ""
            i += len(sep)
            continue
        cur += c
        i += 1
    parts.append(cur)
    return [p.strip() for p in parts]


def binder_groups(header):
    """Explicit binder groups `(a b : T)` of a declaration header."""
    groups, depth, start = [], 0, None
    for i, c in enumerate(header):
        if c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0 and start is not None:
                inner = header[start + 1:i]
                if " : " in inner:
                    names, ty = inner.split(" : ", 1)
                    groups.append((names.split(), ty.strip()))
                start = None
    return groups


class FileInfo:
    def __init__(self, path):
        self.path = path
        self.module = "MWIS." + path.stem


STRUCTS = {}   # full type name -> list of (field, type string, namespace, opens)
MATCHES = {}   # key -> dict
STRUCT_CTX = {}


def parse_file(path):
    lines = path.read_text().splitlines()
    ns_stack = []
    opens = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^namespace (\S+)", line)
        if m:
            ns_stack.append(m.group(1))
            i += 1
            continue
        m = re.match(r"^end (\S+)\s*$", line)
        if m and ns_stack and ns_stack[-1] == m.group(1):
            ns_stack.pop()
            i += 1
            continue
        if line.startswith("open ") and not line.rstrip().endswith(" in"):
            text = line.rstrip()
            while (text.count("(") > text.count(")") and i + 1 < len(lines)
                   and lines[i + 1].startswith("  ")):
                i += 1
                text += "\n" + lines[i].rstrip()
            opens.append(text)
            i += 1
            continue
        ns = ns_stack[-1] if ns_stack else ""
        m = re.match(r"^structure (\w+) \(p : ℕ\) where\s*$", line)
        if m:
            fields = []
            j = i + 1
            while j < len(lines) and re.match(r"^  \w+ : ", lines[j]):
                f, ty = lines[j].strip().split(" : ", 1)
                fields.append((f, ty.strip()))
                j += 1
            full = ns + "." + m.group(1)
            STRUCTS[full] = fields
            STRUCT_CTX[full] = (ns, list(opens))
            i = j
            continue
        m = re.match(r"^(def|structure) (?:(\w+)\.)?(\w*Matches)\b(.*)$", line)
        if m:
            kind, owner, mname = m.group(1), m.group(2), m.group(3)
            header = m.group(4)
            j = i
            if kind == "def":
                while ":=" not in header:
                    j += 1
                    header += " " + lines[j].strip()
                header, rest = header.split(":=", 1)
                body = rest.strip()
                j += 1
                while j < len(lines) and lines[j].startswith("  ") and lines[j].strip():
                    body += " " + lines[j].strip()
                    j += 1
                clauses = [(None, c) for c in split_top(body, "∧")]
            else:
                while not header.rstrip().endswith("where"):
                    j += 1
                    header += " " + lines[j].strip()
                header = header.rstrip()[:-len("where")]
                j += 1
                clauses = []
                while j < len(lines) and lines[j].startswith("  ") and lines[j].strip():
                    fm = re.match(r"^  (\w+) : (.*)$", lines[j])
                    if fm:
                        clauses.append([fm.group(1), fm.group(2).strip()])
                    else:
                        clauses[-1][1] += " " + lines[j].strip()
                    j += 1
                clauses = [tuple(c) for c in clauses]
            groups = binder_groups(header)
            if owner:
                key = ("dot", ns + "." + owner, mname)
            else:
                key = ("fn", ns + "." + mname)
            MATCHES[key] = dict(ns=ns, opens=list(opens), groups=groups, clauses=clauses,
                                owner=owner, mname=mname, kind=kind,
                                module=".".join(("MWIS",) + path.relative_to(SRC).with_suffix("").parts))
            i = j
            continue
        i += 1


SOURCES = sorted(SRC.glob("*.lean")) + sorted((SRC / "Fun").glob("*.lean"))
for f in SOURCES:
    if f.stem.startswith("FinalProgram") or f.stem.startswith(PREFIX):
        continue
    parse_file(f)


def resolve_type(ty, ns, opens):
    ty = ty.strip()
    if not ty.endswith(" p"):
        return None
    base = ty[:-2].strip()
    if base == "Fin":
        return "Fin"
    cands = []
    parts = ns.split(".")
    for k in range(len(parts), -1, -1):
        cands.append(".".join(parts[:k] + [base]) if k else base)
    for o in opens:
        for name in re.findall(r"MWIS[\w.]*", o):
            cands.append(name + "." + base)
    for c in cands:
        if c in STRUCTS:
            return c
    raise SystemExit(f"cannot resolve type {ty} in {ns}")


# ---------------------------------------------------------------- tree

LEAVES = []          # list of paths (tuples)
NODE_TYPE = {}       # path -> full type ("Fin" for leaves)


def build(path, ty):
    NODE_TYPE[path] = ty
    if ty == "Fin":
        LEAVES.append(path)
        return
    ns, opens = STRUCT_CTX[ty]
    for f, fty in STRUCTS[ty]:
        build(path + (f,), resolve_type(fty, ns, opens))


ROOTS = [("fptTop", "MWIS.RegisterTopLevel.Procedures"),
         ("fptHardIds", "MWIS.FPTRegister.Procedures"),
         ("fptInterp", "MWIS.Fun.Interp.Procedures")]
for r, t in ROOTS:
    build((r,), t)
# the two builder procedures, numbered last
BUILDERS = [("fptBuild1", "t₁"), ("fptBuild2", "t₂")]
for b, _ in BUILDERS:
    NODE_TYPE[(b,)] = "Fin"
    LEAVES.append((b,))

parent = {l: l for l in LEAVES}


def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


def union(a, b):
    a, b = find(a), find(b)
    if a != b:
        parent[b] = a


EQS = {}          # leaf -> list of (defname, args)
BODY_DEFS = {}    # (key, clause index) -> (defname, used binder names, rhs)
PROOFS = {}


def path_of(expr, env):
    parts = expr.split(".")
    if parts[0] not in env:
        return None
    p = env[parts[0]] + tuple(parts[1:])
    if p not in NODE_TYPE:
        raise SystemExit(f"unknown path {p}")
    return p


def binder_list(info):
    out = []
    for names, ty in info["groups"]:
        for n in names:
            out.append((n, ty))
    return out


def find_matches(fn_expr, mname, first_node, env, ns):
    """Locate the Matches key for a sub-call."""
    if first_node is not None:
        ty = NODE_TYPE[first_node]
        key = ("dot", ty, mname)
        if key in MATCHES:
            return key
        raise SystemExit(f"no matches {key}")
    parts = ns.split(".")
    for k in range(len(parts), -1, -1):
        cand = ".".join(parts[:k] + [fn_expr + "." + mname]) if k else fn_expr + "." + mname
        if ("fn", cand) in MATCHES:
            return ("fn", cand)
    raise SystemExit(f"no fn matches {fn_expr}.{mname} from {ns}")


def body_name(key, idx, label):
    info = MATCHES[key]
    owner = info["owner"] or "fn"
    return f"{PREFIX}Bodies.{owner}_{info['mname']}_{idx}_{label}"


def process(key, env, depth=0):
    """Instantiate a Matches predicate; return the proof term."""
    info = MATCHES[key]
    ns = info["ns"]
    terms = []
    names = [n for n, _ in binder_list(info)]
    for idx, (label, clause) in enumerate(info["clauses"]):
        c = " ".join(clause.split())
        m = re.match(r"^code (\S+) = code (\S+)$", c)
        if m:
            union(path_of(m.group(1), env), path_of(m.group(2), env))
            terms.append("rfl")
            continue
        m = re.match(r"^code (\S+) =\s*(.+)$", c)
        if m:
            lhs = path_of(m.group(1), env)
            rhs = m.group(2)
            used = [n for n in names if n != "code" and re.search(r"(?<![\w.])" + re.escape(n) + r"\b", rhs)]
            lab = label or m.group(1).split(".")[-1]
            dn = body_name(key, idx, lab)
            BODY_DEFS[(key, idx)] = (dn, used, rhs)
            EQS.setdefault(lhs, []).append((ns + "." + dn, tuple(env[u] for u in used)))
            terms.append("rfl")
            continue
        m = re.match(r"^(\S+) = (\S+)$", c)
        if m:
            union(path_of(m.group(1), env), path_of(m.group(2), env))
            terms.append("rfl")
            continue
        m = re.match(r"^(\S+)\.(\w*Matches) code\s*(.*)$", c)
        if m:
            fexpr, mname, rest = m.group(1), m.group(2), m.group(3).split()
            first = path_of(fexpr, env)
            sub = find_matches(fexpr, mname, first, env, ns)
            args = ([first] if first is not None else []) + [path_of(a, env) for a in rest]
            sb = [n for n, _ in binder_list(MATCHES[sub]) if n != "code"]
            if len(sb) != len(args):
                raise SystemExit(f"arity mismatch {c} in {key}")
            terms.append(process(sub, dict(zip(sb, args)), depth + 1))
            continue
        raise SystemExit(f"unparsed clause {c!r} in {key}")
    if info["kind"] == "def" and len(terms) == 1:
        return terms[0]
    return "⟨" + ", ".join(terms) + "⟩"


def first_binder(key):
    return binder_list(MATCHES[key])[0][0]


PROOFS = {}
for r, t in ROOTS:
    key = ("dot", t, "Matches")
    PROOFS[r] = process(key, {first_binder(key): (r,)})
union(("fptHardIds", "hard"), ("fptTop", "assembly", "allHalf", "component", "hard"))

# The stage wrappers and the builders (not part of a `Matches` predicate).
EXTRA = {
    ("fptHardIds", "consts"): ("MWIS.FPTRunFun.wrap2Body", (("fptBuild1",), ("fptInterp", "eval"))),
    ("fptHardIds", "funStage"): ("MWIS.FPTRunFun.wrap5Body", (("fptBuild2",), ("fptInterp", "eval"))),
}
for b, t in BUILDERS:
    EXTRA[(b,)] = ("MWIS.FPTBuild.buildBody", ((t,),))
for leaf, eq in EXTRA.items():
    if EQS.get(leaf):
        raise SystemExit(f"extra equation for constrained leaf {leaf}")
    EQS[leaf] = [eq]

# ---------------------------------------------------------------- numbering

classes = {}
for l in LEAVES:
    classes.setdefault(find(l), []).append(l)

entries = []      # (rep, body expr)
index = {}
unconstrained = []


def argexpr(p):
    return ".".join(p)


warnings = []
for l in LEAVES:
    rep = find(l)
    if rep in index or rep in unconstrained:
        continue
    eqs = []
    for m in classes[rep]:
        eqs += EQS.get(m, [])
    if not eqs:
        unconstrained.append(rep)
        continue
    distinct = sorted(set(eqs))
    if len(distinct) > 1:
        warnings.append((rep, distinct))
    dn, args = eqs[0]
    index[rep] = len(entries)
    entries.append((rep, " ".join([dn] + [argexpr(a) for a in args])))

fail_index = None
if unconstrained:
    fail_index = len(entries)
    entries.append((None, ".fail"))
    for r in unconstrained:
        index[r] = fail_index

P = len(entries)
for rep, d in warnings:
    print("WARNING multiple bodies for", rep, d, file=sys.stderr)

# ---------------------------------------------------------------- emission

HEADER_DOC = "/-!\n# {title}\n\n{text}\n-/\n"


def emit_bodies():
    """Group body definitions by (module, namespace) and write files."""
    groups = {}
    order = []
    for (key, idx), (dn, used, rhs) in BODY_DEFS.items():
        info = MATCHES[key]
        g = (info["module"], info["ns"])
        if g not in groups:
            groups[g] = []
            order.append(g)
        groups[g].append((key, idx, dn, used, rhs))
    files = []
    cur, cur_lines = [], 0
    for g in order:
        n = 6 + 3 * len(groups[g]) + sum(len(o) for o in [MATCHES[groups[g][0][0]]["opens"]])
        if cur and cur_lines + n > BODY_SPLIT:
            files.append(cur)
            cur, cur_lines = [], 0
        cur.append(g)
        cur_lines += n
    if cur:
        files.append(cur)
    names = []
    for fi, gs in enumerate(files):
        name = f"{PREFIX}Bodies{fi + 1}"
        names.append(name)
        imports = sorted({MATCHES[groups[g][0][0]]["module"] for g in gs} |
                         {g[0] for g in gs})
        out = ["module", ""]
        out += [f"public import {m}" for m in imports]
        out += ["", HEADER_DOC.format(
            title=f"Procedure bodies of the fixed-parameter program, part {fi + 1}",
            text=("Every equation `code id = body` of a `Matches` predicate gives a definition\n"
                  "of `body` as a function of the ids record and the other parameters of the\n"
                  "predicate, stated in the namespace and under the `open` lines of the source\n"
                  "module. The concrete table `FPTProgram.fptProgram` lists these bodies.\n"
                  "This file is generated by `scripts/gen_fpt_program.py`.")),
                "@[expose] public section", ""]
        for g in gs:
            mod, ns = g
            items = groups[g]
            info0 = MATCHES[items[0][0]]
            out.append(f"namespace {ns}")
            out.append("")
            out += info0["opens"]
            out.append("")
            out.append("variable {p : ℕ}")
            out.append("")
            for key, idx, dn, used, rhs in items:
                info = MATCHES[key]
                tys = dict(binder_list(info))
                binders = " ".join(f"({u} : {tys[u]})" for u in used)
                out.append(f"def {dn} {binders} : Command p :=".replace("  ", " "))
                out.append("\n".join(textwrap.wrap(rhs, 100, initial_indent="  ",
                                                   subsequent_indent="    ",
                                                   break_long_words=False,
                                                   break_on_hyphens=False)))
            out.append("")
            out.append(f"end {ns}")
            out.append("")
        (SRC / f"{name}.lean").write_text("\n".join(out))
    return names


def record_inline(path):
    ty = NODE_TYPE[path]
    if ty == "Fin":
        return str(index[find(path)])
    return "{ " + ", ".join(f"{f} := {record_inline(path + (f,))}" for f, _ in STRUCTS[ty]) + " }"


def record_lines(path, col, width=100):
    """Lines of a structure instance whose `{` is at column `col`; the fields
    of a structure instance are laid out at one column."""
    ty = NODE_TYPE[path]
    items = []
    for f, _ in STRUCTS[ty]:
        inline = f"{f} := {record_inline(path + (f,))}"
        if col + 2 + len(inline) + 2 <= width:
            items.append([inline])
        else:
            sub = record_lines(path + (f,), col + 4, width)
            items.append([f"{f} :="] + sub)
    lines, cur = [], None
    fcol = " " * (col + 2)
    for k, it in enumerate(items):
        last = k == len(items) - 1
        if len(it) == 1:
            piece = it[0] + ("" if last else ",")
            if cur is not None and len(cur) + 1 + len(piece) <= width:
                cur += " " + piece
            else:
                if cur is not None:
                    lines.append(cur)
                cur = fcol + piece
        else:
            if cur is not None:
                lines.append(cur)
                cur = None
            lines.append(fcol + it[0])
            body = it[1:]
            if not last:
                body[-1] += ","
            lines += body
    if cur is not None:
        lines.append(cur)
    lines[-1] += " }"
    lines[0] = " " * col + "{ " + lines[0][col + 2:]
    return lines


TREE_PARAMS = [t for _, t in BUILDERS]


def params_of(text):
    return [t for t in TREE_PARAMS if re.search(re.escape(t) + r"(?![\w₀-₉])", text)]


ROOT_TYPES = {"fptTop": "RegisterTopLevel.Procedures", "fptHardIds": "FPTRegister.Procedures",
              "fptInterp": "Fun.Interp.Procedures"}
ROOT_DOCS = {"fptTop": "Procedure numbers of XP's top-level procedures.",
             "fptHardIds": "Procedure numbers of the fixed-parameter hard-component procedures.",
             "fptInterp": "Procedure numbers of the `Fun` interpreter."}


def emit_ids(body_files):
    out = ["module", "",
           "public import MWIS.RegisterTopLevel", "public import MWIS.FPTRegister",
           "public import MWIS.Fun.Interp",
           "", HEADER_DOC.format(
               title="Procedure numbers of the fixed-parameter program",
               text=(f"The fixed-parameter program has `P = {P}` procedures. The id records\n"
                     "`fptTop`, `fptHardIds`, `fptInterp` and the builder ids `fptBuild1`,\n"
                     "`fptBuild2` number them; ids that the `Matches` predicates force to\n"
                     "coincide get one number. This file is generated by\n"
                     "`scripts/gen_fpt_program.py`.")),
           "@[expose] public section", "",
           f"namespace {NS}", "",
           "/-- The number of procedures. -/",
           f"abbrev P : ℕ := {P}", ""]
    for r, _ in ROOTS:
        out += [f"/-- {ROOT_DOCS[r]} -/", f"def {r} : {ROOT_TYPES[r]} P :=",
                "\n".join(record_lines((r,), 2)), ""]
    for b, t in BUILDERS:
        out += [f"/-- The procedure building the stored program tree `{t}`. -/",
                f"def {b} : Fin P := {index[find((b,))]}", ""]
    out += [f"end {NS}", ""]
    (SRC / f"{PREFIX}Ids.lean").write_text("\n".join(out))
    nblocks = (len(entries) + BLOCK - 1) // BLOCK
    parts = [list(range(k, min(k + BLOCKS_PER_FILE, nblocks)))
             for k in range(0, nblocks, BLOCKS_PER_FILE)]
    prev = [f"{PREFIX}Ids"] + body_files
    block_params = {}
    for fi, part in enumerate(parts):
        name = f"{PREFIX}Table{fi + 1}"
        last = fi == len(parts) - 1
        out = ["module", ""] + [f"public import MWIS.{m}" for m in prev]
        if fi == 0:
            out.append("public import MWIS.FPTBuild")
            out.append("public import MWIS.FPTRunFun")
        out += ["", HEADER_DOC.format(
                    title=f"The concrete procedure table of the fixed-parameter program, part {fi + 1}",
                    text=(f"Block `j` lists the bodies of procedures `{BLOCK} j` to `{BLOCK} j + {BLOCK - 1}`"
                          f" (of `P = {P}`),\n"
                          "built from the generic bodies of `FPTProgramBodies*` applied to the id\n"
                          "records."
                          + ("\nThe program looks up procedure `k` as entry `k % B` of block `k / B`."
                             if last else "")
                          + "\nThis file is generated by `scripts/gen_fpt_program.py`.")),
                "@[expose] public section", "",
                f"namespace {NS}", "",
                "open MWIS.RegisterMachine", ""]
        for j in part:
            lo, hi = j * BLOCK, min((j + 1) * BLOCK, len(entries))
            body = ",\n".join(
                "\n".join(textwrap.wrap(e, 100, initial_indent="    ", subsequent_indent="      ",
                                        break_long_words=False, break_on_hyphens=False))
                for _, e in entries[lo:hi])
            ps = params_of(body)
            block_params[j] = ps
            binders = "".join(f" ({t} : MWIS.Fun.Tree)" for t in ps)
            out.append(f"/-- The bodies of procedures {lo} to {hi - 1}. -/")
            out.append(f"def block{j}{binders} : List (Command P) := [")
            out.append(body + "]")
            out.append("")
        if last:
            allp = " ".join(TREE_PARAMS)
            blocks = ", ".join(("(" + " ".join([f"block{j}"] + block_params[j]) + ")")
                               if block_params[j] else f"block{j}" for j in range(nblocks))
            out += ["/-- The blocks of the table, for the stored program trees `t₁` and `t₂`. -/",
                    f"def table ({allp} : MWIS.Fun.Tree) : List (List (Command P)) :=",
                    "\n".join(textwrap.wrap(blocks, 96,
                                            initial_indent="  [", subsequent_indent="   ")) + "]",
                    "", "/-- The block size of `table`. -/", f"abbrev B : ℕ := {BLOCK}", "",
                    "/-- The fixed-parameter program, with the stored program trees `t₁` (the",
                    "constants stage) and `t₂` (the numerical stage): procedure `k` is entry",
                    "`k % B` of block `k / B`. -/",
                    f"def fptProgram ({allp} : MWIS.Fun.Tree) : Code P := fun i =>",
                    f"  ((table {allp}).getD (i.val / B) []).getD (i.val % B) .fail", ""]
        out += [f"end {NS}", ""]
        (SRC / f"{name}.lean").write_text("\n".join(out))
        prev = [name]
    global TABLE_LAST
    TABLE_LAST = f"{PREFIX}Table{len(parts)}"


def wrap(term, width=96, indent="  "):
    term = term.replace(" := ", "\u00a0:=\u00a0")
    return "\n".join(textwrap.wrap(term, width, initial_indent=indent,
                                    subsequent_indent=indent + "  ",
                                    break_long_words=False, break_on_hyphens=False)).replace("\u00a0", " ")


def emit_proofs():
    out = ["module", "", f"public import MWIS.{TABLE_LAST}", "",
           HEADER_DOC.format(
               title="The fixed-parameter program",
               text=("For all stored program trees `t₁ t₂`, the concrete table `fptProgram t₁ t₂`\n"
                     "satisfies the `Matches` predicates of XP's top-level procedures, of the\n"
                     "fixed-parameter hard-component procedures and of the `Fun` interpreter;\n"
                     "the constants and numerical stages are the wrappers running the interpreter\n"
                     "on the trees built by `fptBuild1` and `fptBuild2`; and the hard procedure\n"
                     "called by the top level is the hard-component entry. Every equation holds by\n"
                     "`rfl`. This file is generated by `scripts/gen_fpt_program.py`.")),
           "@[expose] public section", "",
           f"namespace {NS}", "",
           "open MWIS.RegisterMachine", "",
           "variable (t₁ t₂ : MWIS.Fun.Tree)", "",
           "theorem fptTop_matches : fptTop.Matches (fptProgram t₁ t₂) :=",
           wrap(PROOFS["fptTop"]), "",
           "theorem fptHardIds_matches : fptHardIds.Matches (fptProgram t₁ t₂) :=",
           wrap(PROOFS["fptHardIds"]), "",
           "theorem fptInterp_matches : fptInterp.Matches (fptProgram t₁ t₂) :=",
           wrap(PROOFS["fptInterp"]), "",
           "theorem fptProgram_consts :",
           "    fptProgram t₁ t₂ fptHardIds.consts = FPTRunFun.wrap2Body fptBuild1 fptInterp.eval :=",
           "  rfl", "",
           "theorem fptProgram_funStage :",
           "    fptProgram t₁ t₂ fptHardIds.funStage = FPTRunFun.wrap5Body fptBuild2 fptInterp.eval :=",
           "  rfl", "",
           "theorem fptProgram_build1 : fptProgram t₁ t₂ fptBuild1 = FPTBuild.buildBody t₁ := rfl", "",
           "theorem fptProgram_build2 : fptProgram t₁ t₂ fptBuild2 = FPTBuild.buildBody t₂ := rfl", "",
           "theorem fptTop_hard : fptTop.hard = fptHardIds.hard := rfl", "",
           f"end {NS}", ""]
    (SRC / f"{PREFIX}.lean").write_text("\n".join(out))


bf = emit_bodies()
emit_ids(bf)
emit_proofs()
print("P =", P, "leaves =", len(LEAVES), "bodies =", len(BODY_DEFS), "files =", bf,
      "unconstrained =", len(unconstrained))
for u in unconstrained:
    print("  unconstrained:", ".".join(u))
