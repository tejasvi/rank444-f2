#!/usr/bin/env python3
"""s26_leafmatch.py IN_DIR OUT_DIR [--procs N]   (standard library only; reads IN_DIR, the traces and IPs it lists, and the T2 modules)
IN_DIR holds e1_inventory.tsv (one row per class with leaves: c, ip_path, leaves), e1_traces.tsv (one row per trace file: c,
path, bytes, leaves, err), seeded334.tsv, and T2/ (the modules lean/B334/T2/*.lean of the release).

leaf_match.tsv: every E1 leaf of the 49 classes whose traces have L records, matched to a T2 record.
E1 side (as convert/conv_e1g.py and B334/E1x/G/Bridge2.lean see a leaf): the leaf is an L node at depth R; its packed prefix
pl holds the R labels (label indices of the class's IP) of the block prefix plus the path, label s at bits [7 s, 7 s + 7) for E1G
(IP with N <= 127 labels) and [8 s, 8 s + 8) for E1P (N = 255, the points); the terms are termsOf R VT pl: term s = the 9-bit entry
VT[label s] (VT = vecs of IP line 2, entry l at bit 9 l); n = R (IP header); dom = DOM = sum of 2^X over X in 1..511 with X & e of even
parity for every e of the class basis (seeded334.tsv).
T2 side (B334/T2/Index.lean, K_<c>_*.lean, N_0.lean): leaves_c = the concatenation, in the order of Index.lean, of the lists kl_<c>_k and
nl_<c>, each a list of leaf records `def L_<c>_leaf<m> : Nat := 0x..` with leafN R = rd 6 R, leafT R = rd (9 n) (sk 6 R), leafDom R =
rd 512 (sk 2 (sk (6 + 9 n) R)) (B334/BCP/Leaf.lean).  A match is the first record of leaves_c with the same n, the same dom and the
same multiset of 9-bit terms; p is the permutation with E1 term s = term p[s] of the record (for equal terms the smallest unused
index of the record, in the order of s).  Every row is re-checked by a mirror of B334/BCP/PermL.lean t2match (leafN R == n, leafDom R
== dom, permL p n, aT T' s == aT (leafT R) (p.getD s 0) for all s < n), and a negative control per row (two entries of p with different
terms swapped) must be rejected.  Columns: class file block node pl n i t2_leaf p; then e1kind, t2_list (the kl/nl list and position),
dups (number of leaves of the class with this pl; one row is kept per distinct (class, pl)).
"""
import collections, glob, hashlib, multiprocessing, os, re, sys

CLS = {}


def die(msg):
    print("FATAL: " + msg)
    sys.exit(2)


def read_tsv(path):
    with open(path) as f:
        lines = f.read().split("\n")
    hdr = lines[0].split("\t")
    return [dict(zip(hdr, ln.split("\t"))) for ln in lines[1:] if ln.strip()]


# ------------------------------------------------------------------------------------------------ E1 side: the L nodes of a trace
def walk(p, i, plabels):
    """(node index, label tuple) of every L node of a block payload p whose node records start at i; plabels = the prefix labels"""
    def u8():
        nonlocal i
        x = p[i]
        i += 1
        return x

    def var():
        nonlocal i
        x = 0
        s = 0
        while True:
            c = p[i]
            i += 1
            x |= (c & 127) << s
            s += 7
            if c < 128:
                return x

    def dual():
        k = var()
        for _ in range(k):
            var()
            var()

    out = []
    sel = []
    ni = 0
    expect_node = True
    while True:
        if expect_node:
            t = chr(u8())
            if t == "L":
                out.append((ni, tuple(plabels) + tuple(sel)))
            elif t == "K":
                dual()
            elif t == "O":
                u8()
                kind = u8()
                if kind == 1:
                    var()
                if u8():
                    dual()
                sel.append(None)
            elif t != "F":
                raise ValueError("node tag %r" % t)
            ni += 1
            expect_node = False
            continue
        if not sel:
            break
        c = chr(u8())
        if c == "E":
            sel.pop()
            continue
        if c != "C":
            raise ValueError("expected C or E, got %r" % c)
        sel[-1] = u8()
        if i < len(p) and p[i] == ord("P"):
            i += 1
            if u8() == 1:
                var()
            continue
        expect_node = True
    if chr(u8()) != "Z":
        raise ValueError("expected Z")
    var()
    return out


MAGIC = 0x3942454C


def scan_file(task):
    c, path = task
    info = CLS[c]
    with open(path, "rb") as f:
        data = f.read()
    n = len(data)
    q = 0
    bi = 0
    leaves = []
    err = ""
    while q < n:
        if q + 12 > n:
            err = "truncated header"
            break
        mg = int.from_bytes(data[q:q + 4], "little")
        ln = int.from_bytes(data[q + 4:q + 12], "little")
        if mg != MAGIC or q + 12 + ln > n:
            err = "bad block at %d" % q
            break
        base = q + 12
        kind = chr(data[base])
        k = data[base + 1]
        vec = [int.from_bytes(data[base + 2 + 2 * j:base + 4 + 2 * j], "little") for j in range(k)]
        try:
            plabels = [info["lab"][v] for v in vec]
            off = 1 + 1 + 2 * k + (1 if kind == "T" else 0)
            for ni, labs in walk(data[base:base + ln], off, plabels):
                leaves.append((bi, ni, labs))
        except (KeyError, ValueError, IndexError) as e:
            err = "block %d: %r" % (bi, e)
            break
        bi += 1
        q += 12 + ln
    return c, path, dict(bytes=n, blocks=bi, leaves=leaves, err=err)


# ------------------------------------------------------------------------------------------------ the mirror of BCP/PermL.lean
def rd(k, S):
    return S & ((1 << k) - 1)


def sk(k, S):
    return S >> k


def leafN(R):
    return rd(6, R)


def leafT(R):
    return rd(9 * rd(6, R), sk(6, R))


def leafDom(R):
    return rd(512, sk(2, sk(6 + 9 * rd(6, R), R)))


def aT(T, t):
    return (T >> (9 * t)) & 511


def permL(p, n):
    return len(p) == n and all(0 <= x < n for x in p) and len(set(p)) == len(p)


def t2match(R, Tp, n, dom, p):
    if leafN(R) != n or leafDom(R) != dom or not permL(p, n):
        return False
    LT = leafT(R)
    return all(aT(Tp, s) == aT(LT, p[s] if s < len(p) else 0) for s in range(n))


def main():
    if len(sys.argv) < 3:
        die("usage: s26_leafmatch.py IN_DIR OUT_DIR [--procs N]")
    inp, out = sys.argv[1], sys.argv[2]
    procs = int(sys.argv[sys.argv.index("--procs") + 1]) if "--procs" in sys.argv else 64
    os.makedirs(out)
    S = []

    def say(s=""):
        S.append(s)

    def P(name):
        return os.path.join(inp, name)

    # ---- the classes and their files (e1_inventory.tsv / e1_traces.tsv, re-checked against the files)
    inv = dict((int(r["c"]), r) for r in read_tsv(P("e1_inventory.tsv")))
    classes = sorted(c for c in inv if int(inv[c]["leaves"]) > 0)
    files = collections.defaultdict(list)
    tleaves = {}
    for r in read_tsv(P("e1_traces.tsv")):
        c = int(r["c"])
        if c in classes and int(r["bytes"]) > 0:
            if os.path.getsize(r["path"]) != int(r["bytes"]):
                die("size of %s changed" % r["path"])
            files[c].append(r["path"])
            tleaves[(c, r["path"])] = int(r["leaves"])
    basis = {}
    for r in read_tsv(P("seeded334.tsv")):
        basis[int(r["idx"])] = [int(x) for x in r["basis"].split(",") if x]
    exp_leaves = sum(int(inv[c]["leaves"]) for c in classes)
    say("classes with E1 leaves: %d, %d L records expected from e1_inventory.tsv, %d trace files" % (len(classes), exp_leaves, sum(len(v) for v in files.values())))
    for c in classes:
        ipf = inv[c]["ip_path"]
        with open(ipf) as f:
            h = f.readline().split()
            vecs = [int(x) for x in f.readline().split()]
        R, N = int(h[1]), int(h[3])
        if len(vecs) != N or R != int(inv[c]["L"]):
            die("class %d: IP header differs from the inventory" % c)
        kind = "E1P" if N == 255 else "E1G"
        if kind != inv[c]["e1kind"] or (kind == "E1G" and N > 127):
            die("class %d: e1kind mismatch" % c)
        dom = 0
        for X in range(1, 512):
            if all(bin(X & e).count("1") % 2 == 0 for e in basis[c]):
                dom |= 1 << X
        CLS[c] = dict(R=R, N=N, vecs=vecs, lab=dict((v, l) for l, v in enumerate(vecs)), kind=kind, bits=8 if kind == "E1P" else 7, dom=dom,
                      VT=sum(v << (9 * l) for l, v in enumerate(vecs)))

    # ---- T2 records in Index.lean order
    t2 = P("T2")
    leafdef, lists = {}, {}
    for fn in sorted(os.listdir(t2)):
        if not (fn.startswith("K_") or fn == "N_0.lean"):
            continue
        with open(os.path.join(t2, fn)) as f:
            for ln in f:
                m = re.match(r"^def (L_\d+_leaf\d+) : Nat := 0x([0-9a-f]+)\s*$", ln)
                if m:
                    leafdef[m.group(1)] = int(m.group(2), 16)
                    continue
                m = re.match(r"^def ((?:kl|nl)_\d+(?:_\d+)?) : List Nat := \[(.*)\]\s*$", ln)
                if m:
                    lists[m.group(1)] = re.findall(r"L_\d+_leaf\d+", m.group(2))
    order = {}
    with open(os.path.join(t2, "Index.lean")) as f:
        for ln in f:
            m = re.match(r"^def leaves_(\d+) : List Nat := (.*)$", ln)
            if m:
                order[int(m.group(1))] = re.findall(r"\b((?:kl|nl)_\d+(?:_\d+)?)\b", m.group(2))
    say("T2: %d leaf records, %d lists, %d classes in Index.lean; classes of the E1 side missing in Index.lean: %s; Index classes without E1 leaves: %s" % (
        len(leafdef), len(lists), len(order), [c for c in classes if c not in order], [c for c in sorted(order) if c not in classes]))
    t2recs, t2key = {}, {}
    badrec = 0
    for c in sorted(order):
        recs = []
        for ln_ in order[c]:
            for pos, nm in enumerate(lists[ln_]):
                recs.append((nm, ln_, pos, leafdef[nm]))
        t2recs[c] = recs
        key = {}
        for i, (nm, ln_, pos, R) in enumerate(recs):
            n = leafN(R)
            if rd(2, sk(6 + 9 * n, R)) != 1 or n > 31:
                badrec += 1
            terms = tuple(sorted(aT(leafT(R), t) for t in range(n)))
            key.setdefault((n, leafDom(R), terms), i)
        t2key[c] = key
    say("T2 records with dom mode != 01 or n > 31: %d" % badrec)

    # ---- the L nodes of the traces
    tasks = sorted((c, p) for c in classes for p in files[c])
    sys.stdout.flush()
    with multiprocessing.get_context("fork").Pool(procs) as pool:
        res = dict(((c, p), r) for c, p, r in pool.imap_unordered(scan_file, sorted(tasks, key=lambda t: -os.path.getsize(t[1])), 1))
    errs = [(k, r["err"]) for k, r in res.items() if r["err"]]
    nL = sum(len(r["leaves"]) for r in res.values())
    perfile_bad = [k for k, r in res.items() if len(r["leaves"]) != tleaves[k]]
    say("trace files read: %d, %d bytes; L records found: %d (inventory %d); parse errors: %d %s; files whose L count differs from e1_traces.tsv: %d %s"
        % (len(res), sum(r["bytes"] for r in res.values()), nL, exp_leaves, len(errs), errs[:3], len(perfile_bad), perfile_bad[:3]))

    # ---- the match
    hdr = ["class", "file", "block", "node", "pl", "n", "i", "t2_leaf", "p", "e1kind", "t2_list", "dups"]
    lines = ["\t".join(hdr)]
    percls = {}
    nmir = nneg = nnegrej = 0
    unmatched = []
    for c in classes:
        info = CLS[c]
        R, bits, VT, dom = info["R"], info["bits"], info["VT"], info["dom"]
        seen = collections.OrderedDict()
        for (cc, path) in sorted(k for k in res if k[0] == c):
            for (bi, ni, labs) in res[(cc, path)]["leaves"]:
                if len(labs) != R or any(labs[j] > labs[j + 1] for j in range(R - 1)) or any(l >= info["N"] for l in labs):
                    die("class %d: a leaf in %s block %d node %d has %d labels, not sorted or out of range" % (c, path, bi, ni, len(labs)))
                pl = 0
                for s, l in enumerate(labs):
                    pl |= l << (bits * s)
                if pl in seen:
                    seen[pl][1] += 1
                else:
                    seen[pl] = [(path, bi, ni, labs), 1]
        nm = 0
        usedkeys = set()
        for pl, ((path, bi, ni, labs), dups) in seen.items():
            terms = [info["vecs"][l] for l in labs]
            Tp = sum(t << (9 * s) for s, t in enumerate(terms))
            kk = (R, dom, tuple(sorted(terms)))
            i = t2key[c].get(kk) if c in t2key else None
            if i is not None:
                usedkeys.add(kk)
            if i is None:
                unmatched.append((c, path, bi, ni))
                lines.append("\t".join([str(c), path, str(bi), str(ni), "0x%x" % pl, str(R), "-1", "UNMATCHED", "-", info["kind"], "-", str(dups)]))
                continue
            name, ln_, pos, R2 = t2recs[c][i]
            avail = collections.defaultdict(list)
            for j in range(R):
                avail[aT(leafT(R2), j)].append(j)
            p = []
            for s in range(R):
                p.append(avail[terms[s]].pop(0))
            ok = t2match(R2, Tp, R, dom, p)
            nmir += 1
            if not ok:
                die("class %d: mirror t2match rejects the permutation of leaf %s" % (c, name))
            # negative control: swap two entries of p whose E1 terms differ
            pair = [(a, b) for a in range(R) for b in range(a + 1, R) if terms[a] != terms[b]][:1]
            if pair:
                a, b = pair[0]
                q = list(p)
                q[a], q[b] = q[b], q[a]
                nneg += 1
                if not t2match(R2, Tp, R, dom, q):
                    nnegrej += 1
                else:
                    die("class %d: the negative control (swapped p) is accepted for %s" % (c, name))
            nm += 1
            lines.append("\t".join([str(c), path, str(bi), str(ni), "0x%x" % pl, str(R), str(i), name, ",".join(map(str, p)), info["kind"],
                                    "%s[%d]" % (ln_, pos), str(dups)]))
        percls[c] = dict(E1=sum(d for (_, d) in seen.values()), distinct=len(seen), matched=nm, t2=len(t2recs.get(c, [])),
                         t2k=len(t2key.get(c, {})), t2unused=len(t2key.get(c, {})) - len(usedkeys))
    tsv = "\n".join(lines) + "\n"
    with open(os.path.join(out, "leaf_match.tsv"), "w") as f:
        f.write(tsv)

    def termsOf(R, VT, pl, bits):   # B334/E1x/G/Bridge2.lean termsOf (bits 7) and E1x/P/Bridge2.lean (bits 8), on the printed pl
        acc = 0
        for i in range(R):
            acc |= ((VT >> (9 * (pl & ((1 << bits) - 1)))) & 511) << (9 * i)
            pl >>= bits
        return acc
    e2e = e2e_bad = 0
    for ln in tsv.split("\n")[1:]:
        if not ln:
            continue
        f = ln.split("\t")
        if f[7] == "UNMATCHED":
            continue
        c, pl, n, i, nm_, pp = int(f[0]), int(f[4], 16), int(f[5]), int(f[6]), f[7], [int(x) for x in f[8].split(",")]
        info = CLS[c]
        okr = (n == info["R"] and t2recs[c][i][0] == nm_ and
               t2match(leafdef[nm_], termsOf(n, info["VT"], pl, info["bits"]), n, info["dom"], pp))
        e2e += 1
        e2e_bad += 0 if okr else 1
    tot = dict((k, sum(v[k] for v in percls.values())) for k in ("E1", "distinct", "matched", "t2"))
    if unmatched:
        first = "UNMATCHED E1 LEAVES: %d of %d distinct leaves have no T2 record (coverage gap): %s" % (len(unmatched), tot["distinct"], sorted(set(u[0] for u in unmatched)))
    elif e2e_bad or perfile_bad or errs or nL != exp_leaves or nmir != tot["matched"]:
        first = "ANOMALY: a self-check failed (end-to-end failures %d, files with a different L count %d, parse errors %d, L records %d vs %d)" % (
            e2e_bad, len(perfile_bad), len(errs), nL, exp_leaves)
    else:
        first = "ALL %d DISTINCT E1 LEAVES (%d L records, %d classes) ARE MATCHED TO A T2 RECORD; every row passes the t2match mirror and the end-to-end re-check" % (
            tot["distinct"], tot["E1"], len(classes))
    sm = [first, ""] + S + [""]
    sm.append("mirror of PermL.lean t2match accepted %d of %d matched rows; negative control (two entries of p with different terms swapped) rejected %d of %d" % (nmir, tot["matched"], nnegrej, nneg))
    sm.append("end-to-end re-check from the TSV text alone (terms = termsOf R VT pl on the printed pl, the T2 record taken by the printed name and checked against the printed i, "
              "then t2match with the printed p): %d rows, %d failures" % (e2e, e2e_bad))
    sm.append("per class: E1 L records / distinct pl / matched / unmatched / T2 records in leaves_c / distinct T2 keys (n, dom, term multiset) / T2 keys no E1 leaf uses:")
    for c in classes:
        v = percls[c]
        sm.append("  %d: %d / %d / %d / %d / %d / %d / %d" % (c, v["E1"], v["distinct"], v["matched"], v["distinct"] - v["matched"], v["t2"], v["t2k"], v["t2unused"]))
    sm.append("total: %d / %d / %d / %d / %d / %d / %d" % (tot["E1"], tot["distinct"], tot["matched"], tot["distinct"] - tot["matched"], tot["t2"],
                                                           sum(v["t2k"] for v in percls.values()), sum(v["t2unused"] for v in percls.values())))
    summary = "\n".join(sm) + "\n"
    with open(os.path.join(out, "leaf_match_summary.txt"), "w") as f:
        f.write(summary)
    print("python " + sys.version.split()[0])
    print("script %s sha256 %s" % (os.path.basename(__file__), hashlib.sha256(open(__file__, "rb").read()).hexdigest()[:12]))
    print("=== BEGIN leaf_match_summary.txt ===")
    print(summary, end="")
    print("=== END leaf_match_summary.txt ===")
    print("=== BEGIN leaf_match.tsv ===")
    print(tsv, end="")
    print("=== END leaf_match.tsv ===")
    print("leaf_match.tsv sha256 %s lines %d" % (hashlib.sha256(tsv.encode()).hexdigest(), len(lines)))
    if unmatched:
        sys.exit(1)


main()
