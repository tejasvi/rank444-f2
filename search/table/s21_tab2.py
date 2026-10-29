#!/usr/bin/env python3
"""s21_tab2.py IN_DIR OUT_DIR [--allow-partial]   (standard library only)

The row-table inventory table_v2.tsv for the 710 classes of seeded334.tsv, and its summary.  OUT_DIR must not exist.
Writes OUT_DIR/table_v2.tsv and OUT_DIR/table_v2_summary.txt and prints both to stdout between "=== BEGIN/END <name> ===" lines.

Inputs (all in IN_DIR): seeded334.tsv, certs334.tsv (the entries of Wang's certificate file), pilot1_results.tsv,
raised_lines_r1.tsv, raised_planes_r1.tsv, raised_spaces_r1.tsv, routeb/rb_c<c>.done|.fail (the result files of the Route B searches),
result_dependencies_r1.tsv and result27_rows_used.tsv (cross-checks only),
ip_P707R2b_seeded_L25.txt, ip_P708R2_seeded_L25.txt and cls_P707.npy, cls_P708.npy (the member cls.npy of data/sup_P707.npz and
sup_P708.npz: the G0-class of every C row of the IP, in file order, as mkcand.py states).  --allow-partial accepts an IP file with
fewer C rows than the cls array (test runs on truncated IPs only); without it the row counts must be equal.

Encoding (checked on the data, see the summary): a 3x3 matrix over F2 is a 9-bit mask with entry (i, j) at bit 3i+j (s16_row44.py,
common334.py); the group acts by v -> l v s^-1 with l = query & 0xffff, s = store (Wang's encoding of the witness).

Columns of table_v2.tsv (tab separated, one line per class, ascending c):
  c dim basis seeded wang kind flatrank
  rows707 lb707 rows708 lb708     rows and lb = R - cap used by ip_P707R2b / ip_P708R2 for the class ('-' if no row; 'a/b' if two lbs)
  lb_used                         max of lb707 and lb708 ('-' if the class has no row in either IP)
  tv2                             table_v2 value: the new lb of a raised line/plane (raised_lines_r1, raised_planes_r1) else seeded
  route cert_lb routes_all detail the route that gives the largest certified value (ties: raised, lift, point, flat, methodK, lcc,
                                  routeB, deg: the provenance of the table value first), that value, all routes with their values,
                                  and the evidence of the chosen one
  rb_L rb_mono lift_L raised_old raised_new raised_L
                                  Route B search length L and MONOTONE (yes/no), lift search length L, and the raised row's old lb,
                                  new lb and search L ('-' if the class has no such row)
  deg_e deg_q deg_s deg_j seeded_j tv2_j cert_j deg_ok deg_ok_tv2
                                  Wang's witness of a degenerate class; j = the stored class equal to l (S+e) s^-1 (dim + 1);
                                  deg_ok: seeded(j) >= lbref, deg_ok_tv2: tv2(j) >= lbref, lbref = lb_used (seeded if unused)
  pilot raisedS flags             the pilot1 'wang' search of the class, the raised_spaces row, and flags
Routes and the value each certifies (the value the route is meant to prove; nothing is replayed here):
  flat    the class is of kind flatten, or one of 5 11 15 32 (the 17 flattening rows of the Lean modules are these without class 0): the exact
          maximum flattening rank of T mod S, computed here
  methodK the 21 forced-product classes 6 12 13 16 17 23 26 28 33 35 37 38 41 42 45 52 54 55 65 135 147: wang
  lcc     class 44 (row 44, coset count): wang
  deg     kind degenerate: cert_j, the certified value of the class j that Wang's witness maps S+e onto (j has dim + 1)
  routeB  routeb/rb_c<c>.done with search DONE, replay PASS COMPLETE and 0 leaves, or MONOTONE: L + 1
  lift    pilot1_results.tsv, phase lift, replay PASS COMPLETE and every leaf refuted: L + 1
  raised  raised_lines_r1.tsv / raised_planes_r1.tsv, replay PASS COMPLETE and every leaf refuted: new_lb
  point   classes 707 and 708: R + 1 with R the header of their point IP (25 -> 26)
  MISSING none of the above.
"""
import ast, hashlib, os, re, struct, sys
from array import array


def die(msg):
    print("FATAL: " + msg)
    sys.exit(2)


# ------------------------------------------------------------------------------------------------ F2 helpers
def rref(vs):
    piv = {}
    for b in vs:
        v = b
        for p in sorted(piv, reverse=True):
            if (v >> p) & 1:
                v ^= piv[p]
        if v:
            p = v.bit_length() - 1
            for q in list(piv):
                if (piv[q] >> p) & 1:
                    piv[q] ^= v
            piv[p] = v
    return tuple(sorted(piv.values()))


def rank2(rows):
    piv = {}
    r = 0
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                r += 1
                break
    return r


def mat(m):
    return [[(m >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)]


def unmat(A):
    return sum(A[i][j] << (3 * i + j) for i in range(3) for j in range(3))


def mul(A, B):
    return [[sum(A[i][k] & B[k][j] for k in range(3)) & 1 for j in range(3)] for i in range(3)]


def act(l, v, s):   # unmat(mat(l) mat(v) mat(s))
    return unmat(mul(mul(mat(l), mat(v)), mat(s)))


def transpose9(m):
    A = mat(m)
    return unmat([[A[j][i] for j in range(3)] for i in range(3)])


IDENT = unmat([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
GL = [m for m in range(512) if len(rref([(m >> (3 * i)) & 7 for i in range(3)])) == 3]
assert len(GL) == 168 and IDENT == 273
INV = {}
for _m in GL:
    for _n in GL:
        if unmat(mul(mat(_m), mat(_n))) == IDENT:
            INV[_m] = _n
assert len(INV) == 168

TENT = [(3 * i + j, 4 * j + k, 3 * k + i) for i in range(3) for j in range(3) for k in range(4)]   # T[x][y][z] = 1


def flat_ranks(basis):
    """the three flattening ranks of T mod span(basis): first factors reduced modulo S, non-pivot coordinates kept"""
    R = rref(basis)
    pivots = {v.bit_length() - 1: v for v in R}
    nonpiv = [x for x in range(9) if x not in pivots]
    D = len(nonpiv)
    if D == 0:
        return (0, 0, 0)

    def L(a):
        for p, v in pivots.items():
            if (a >> p) & 1:
                a ^= v
        r = 0
        for i, x in enumerate(nonpiv):
            if (a >> x) & 1:
                r |= 1 << i
        return r
    Lx = [L(1 << x) for x in range(9)]
    ent = set()
    for x, y, z in TENT:
        for xp in range(D):
            if (Lx[x] >> xp) & 1:
                ent ^= {(xp, y, z)}
    m1 = [0] * D
    m2 = [0] * 12
    m3 = [0] * 12
    for xp, y, z in ent:
        m1[xp] |= 1 << (y * 12 + z)
        m2[y] |= 1 << (xp * 12 + z)
        m3[z] |= 1 << (xp * 12 + y)
    return (rank2(m1), rank2(m2), rank2(m3))


# ------------------------------------------------------------------------------------------------ file readers
def read_tsv(path):
    with open(path) as f:
        lines = f.read().split("\n")
    hdr = lines[0].split("\t")
    return [dict(zip(hdr, ln.split("\t"))) for ln in lines[1:] if ln.strip()]


def ints(s):
    return [int(x) for x in s.split(",") if x not in ("", "-")]


def sha12(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()[:12]


def read_npy(path):
    with open(path, "rb") as f:
        if f.read(6) != b"\x93NUMPY":
            die("not an npy file: " + path)
        major = f.read(2)[0]
        hl = struct.unpack("<H", f.read(2))[0] if major == 1 else struct.unpack("<I", f.read(4))[0]
        hdr = ast.literal_eval(f.read(hl).decode("latin1").strip())
        data = f.read()
    codes = {"<i2": "h", "<u2": "H", "<i4": "i", "<u4": "I", "<i8": "q", "<u8": "Q", "|u1": "B", "|i1": "b"}
    if hdr["descr"] not in codes or hdr["fortran_order"] or len(hdr["shape"]) != 1:
        die("unsupported npy header %r in %s" % (hdr, path))
    a = array(codes[hdr["descr"]])
    a.frombytes(data)
    if len(a) != hdr["shape"][0]:
        die("npy length mismatch in " + path)
    return a


def read_ip(path):
    caps = array("h")
    dims = array("b")
    ms = array("h")
    with open(path) as f:
        h = f.readline().split()
        if len(h) != 4 or h[0] != "R" or h[2] != "N":
            die("bad IP header in " + path)
        R, N = int(h[1]), int(h[3])
        f.readline()
        ngroup = None
        for ln in f:
            c0 = ln[0:1]
            if c0 == "C":
                p = ln.split(None, 4)
                dims.append(int(p[1]))
                caps.append(int(p[2]))
                ms.append(int(p[3]))
            elif c0 == "G":
                ngroup = int(ln.split()[1])
                break
    return R, N, dims, caps, ms, ngroup


def completion_status(text):
    """'complete' iff every leaf was refuted: all stages have SAT 0, each later stage re-runs exactly the aborted leaves of the
    stage before, and the last stage has ABORT 0.  'leaves 0' is complete; sampled completions are incomplete."""
    t = text.strip()
    if t == "leaves 0":
        return "complete"
    if "sampled" in t:
        return "incomplete"
    # stage 1: "leaves N: UNSAT u ABORT a SAT s" or "leaves N (D distinct): ..." (the counts are of distinct leaves);
    # later stages: "limit T: N leaves -> UNSAT u ABORT a SAT s"
    stages = re.findall(r"(?:leaves (\d+)(?: \((\d+) distinct\))?:|limit \d+: (\d+) leaves ->) *UNSAT (\d+) ABORT\w* (\d+) SAT (\d+)", t)
    if not stages:
        return "incomplete"
    prev_abort = None
    for k, (n1, nd, n2, u, a, s) in enumerate(stages):
        n = int(nd if nd != "" else (n1 if n1 != "" else n2))
        u, a, s = int(u), int(a), int(s)
        if s != 0:
            return "SAT"
        if k == 0 and n != u + a:
            return "incomplete"
        if k > 0 and n != prev_abort:
            return "incomplete"
        if n != u + a:
            return "incomplete"
        prev_abort = a
    return "complete" if prev_abort == 0 else "incomplete"


# ------------------------------------------------------------------------------------------------ main
def main():
    if len(sys.argv) < 3:
        die("usage: s21_tab2.py IN_DIR OUT_DIR [--allow-partial]")
    inp, out = sys.argv[1], sys.argv[2]
    allow_partial = "--allow-partial" in sys.argv[3:]
    os.makedirs(out)
    S = []

    def say(s=""):
        S.append(s)

    def P(name):
        return os.path.join(inp, name)

    # ---- the table of record and Wang's certificate
    cls = {}
    for r in read_tsv(P("seeded334.tsv")):
        c = int(r["idx"])
        cls[c] = dict(dim=int(r["dim"]), basis=ints(r["basis"]), wang=int(r["wang334"]), kind=r["kind"], seeded=int(r["seeded"]),
                      flatcol=int(r["flat"]))
    NC = len(cls)
    if sorted(cls) != list(range(NC)):
        die("class indices are not 0..%d" % (NC - 1))
    KINDS = {"flatten": "flatten_matrix_proof", "forced": "forced_product_proof", "degenerate": "degenerate_proof",
             "backtrack": "backtracking_proof"}
    certs = {}
    for r in read_tsv(P("certs334.tsv")):
        params = {}
        if r["params"] != "-":
            for kv in r["params"].split(","):
                k, v = kv.split("=")
                params[k] = int(v)
        certs[int(r["index"])] = dict(basis=ints(r["rows"]), lb=int(r["lb"]), kind=r["kind"], params=params, nrows=int(r["nrows"]))
    STORED = {}
    for c in range(NC):
        cls[c]["rref"] = rref(cls[c]["basis"])
        if len(cls[c]["rref"]) != cls[c]["dim"]:
            die("class %d: dim is not the rank of its basis" % c)
        if cls[c]["rref"] in STORED:
            die("classes %d and %d store the same subspace" % (STORED[cls[c]["rref"]], c))
        STORED[cls[c]["rref"]] = c
    bad = []
    for c in range(NC):
        ce = certs.get(c)
        if ce is None or rref(ce["basis"]) != cls[c]["rref"] or ce["lb"] != cls[c]["wang"] or KINDS[ce["kind"]] != cls[c]["kind"]:
            bad.append(c)
    say("INPUT CHECK seeded334.tsv vs certs334.tsv: %d classes, basis/lb/kind disagree on %d %s" % (NC, len(bad), bad[:20]))
    kinds = {}
    for c in range(NC):
        kinds.setdefault(cls[c]["kind"], []).append(c)
    say("kinds: " + ", ".join("%s %d" % (k, len(v)) for k, v in sorted(kinds.items())))

    # ---- flattening ranks of all classes (independent of the table's 'flat' column)
    flatrank = {}
    for c in range(NC):
        flatrank[c] = max(flat_ranks(cls[c]["basis"]))
    say("flatrank (exact max flattening rank) vs wang: > wang on %d classes, == wang on %d; vs the 'flat' column of seeded334.tsv: differ on %d"
        % (sum(1 for c in range(NC) if flatrank[c] > cls[c]["wang"]), sum(1 for c in range(NC) if flatrank[c] == cls[c]["wang"]),
           sum(1 for c in range(NC) if flatrank[c] != cls[c]["flatcol"])))

    # ---- route lists
    flat_set = set(kinds.get("flatten_matrix_proof", [])) | {5, 11, 15, 32}
    METHODK = [6, 12, 13, 16, 17, 23, 26, 28, 33, 35, 37, 38, 41, 42, 45, 52, 54, 55, 65, 135, 147]
    FLAT17 = {1, 2, 3, 4, 5, 7, 8, 10, 11, 14, 15, 18, 21, 24, 29, 32, 56}
    forced = set(kinds.get("forced_product_proof", []))
    say("route lists: flat = %d flatten-kind classes + 5 11 15 32 = %d classes; flat minus class 0 == the 17 flattening rows of the Lean modules: %s; "
        "flatten kind = %s" % (len(kinds.get("flatten_matrix_proof", [])), len(flat_set), (flat_set - {0}) == FLAT17,
                               " ".join(map(str, sorted(kinds.get("flatten_matrix_proof", []))))))
    say("methodK list: %d classes, all of kind forced: %s; forced kind = methodK + 5 11 15 32: %s"
        % (len(METHODK), all(c in forced for c in METHODK), forced == set(METHODK) | {5, 11, 15, 32}))
    say("flat route check: flatrank == wang on %d of %d flat classes; short: %s"
        % (sum(1 for c in flat_set if flatrank[c] == cls[c]["wang"]), len(flat_set),
           " ".join("%d(%d<%d)" % (c, flatrank[c], cls[c]["wang"]) for c in sorted(flat_set) if flatrank[c] != cls[c]["wang"]) or "none"))

    # ---- Route B, lift, raised, pilot
    routeb, rb_fail = {}, {}
    rbdir = P("routeb")
    for fn in sorted(os.listdir(rbdir)):
        m = re.match(r"rb_c(\d+)\.(done|fail)$", fn)
        if not m:
            continue
        c = int(m.group(1))
        txt = open(os.path.join(rbdir, fn)).read().strip()
        if m.group(2) == "fail":
            rb_fail[c] = txt
            continue
        mm = re.match(r"(\d+) L=(\d+) (\S+)", txt)
        if not mm or int(mm.group(1)) != c:
            die("bad Route B line in " + fn)
        L = int(mm.group(2))
        if mm.group(3) == "MONOTONE":
            routeb[c] = dict(L=L, ok=True, text="L=%d MONOTONE" % L)
        else:
            ok = ("search[DONE" in txt and "replay[PASS COMPLETE]" in txt and "leaves[0] completion[leaves 0]" in txt)
            routeb[c] = dict(L=L, ok=ok, text="L=%d %s %s" % (L, mm.group(3), "PASS 0 leaves" if ok else "NOT COMPLETE: " + txt[:80]))
    lift, pilot = {}, {}
    for r in read_tsv(P("pilot1_results.tsv")):
        c = int(r["cls"])
        if r["phase"] == "lift":
            st = completion_status(r["completion"])
            ok = r["replay"].startswith("PASS COMPLETE") and st == "complete"
            lift[c] = dict(L=int(r["L"]), ok=ok, text="L=%s %s %s" % (r["L"], r["enum"], "PASS %s" % r["completion"] if ok else "NOT COMPLETE: %s / %s" % (r["replay"], r["completion"])))
        elif r["phase"] == "wang":
            if r["L"]:
                pilot[c] = "L=%s %s %s" % (r["L"], r["replay"], r["completion"])
            else:
                pilot[c] = "no run: " + r["replay"]
    raised, raisedS = {}, {}
    for name, tab in (("lines", "raised_lines_r1.tsv"), ("planes", "raised_planes_r1.tsv"), ("spaces", "raised_spaces_r1.tsv")):
        for r in read_tsv(P(tab)):
            c = int(r["cls"])
            old, new, L = int(r["old_lb"]), int(r["new_lb"]), int(r["search_L"])
            if name == "lines":
                st = "complete" if r["leaves"] == "0" else "incomplete"
            else:
                st = completion_status(r["completion"])
            ok = r["replay"].startswith("PASS COMPLETE") and st == "complete"
            ent = dict(old=old, new=new, L=L, ok=ok, tab=name,
                       text="%s old %d new %d L=%d %s" % (name, old, new, L, "PASS COMPLETE" if ok else "NOT COMPLETE: %s / %s" % (r["replay"], st)))
            if name == "spaces":
                raisedS[c] = ent
            else:
                if c in raised:
                    die("class %d is in two raised tables" % c)
                raised[c] = ent
    say("Route B: %d done (%d MONOTONE, %d not complete), %d fail file(s) %s; lift: %d rows (%d not complete); raised lines+planes: %d (%d not complete); "
        "raised spaces: %d (not a route)" % (len(routeb), sum(1 for v in routeb.values() if v["text"].endswith("MONOTONE")),
                                             sum(1 for v in routeb.values() if not v["ok"]), len(rb_fail), sorted(rb_fail),
                                             len(lift), sum(1 for v in lift.values() if not v["ok"]), len(raised),
                                             sum(1 for v in raised.values() if not v["ok"]), len(raisedS)))
    tv2 = {}
    for c in range(NC):
        tv2[c] = raised[c]["new"] if (c in raised and raised[c]["ok"]) else cls[c]["seeded"]
    odd = [c for c in raised if raised[c]["old"] != cls[c]["seeded"] or raised[c]["new"] != raised[c]["old"] + 1 or raised[c]["L"] != raised[c]["new"] - 1]
    say("raised rows: old_lb != seeded or new != old+1 or L != new-1 on %d classes %s" % (len(odd), odd[:20]))
    odd = [c for c in routeb if routeb[c]["L"] + 1 != cls[c]["seeded"]]
    say("Route B: L+1 != seeded on %d classes %s; lift: L+1 != seeded on %s" % (len(odd), odd[:20],
                                                                              [c for c in lift if lift[c]["L"] + 1 != cls[c]["seeded"]][:20]))

    # ---- Wang's degenerate witnesses
    DEG = {}
    T9 = {m: transpose9(m) for m in GL}
    variants = {"A": "v -> l v s^-1, row-major masks (the encoding used)", "B": "v -> l^T v (s^T)^-1 (witness read column-major)",
                "C": "v -> l v s (no inverse)", "D": "v -> s^-1 v l (roles swapped)"}
    vmatch = dict((k, [0, 0]) for k in variants)
    nontriv = 0
    for c in kinds.get("degenerate_proof", []):
        pr = certs[c]["params"]
        e, q, s = pr["extra"], pr["query"], pr["store"]
        l, flag = q & 0xffff, q >> 16
        basis = cls[c]["basis"]
        info = dict(e=e, q=q, s=s, l=l, flag=flag, j=None, problems=[])
        if rref(basis + [e]) == cls[c]["rref"]:
            info["problems"].append("e_in_S")
        if flag != 0:
            info["problems"].append("transpose_flag")
        if l not in INV or s not in INV:
            info["problems"].append("singular")
        else:
            vs = basis + [e]
            im = {"A": rref([act(l, v, INV[s]) for v in vs]), "B": rref([act(T9[l], v, INV[T9[s]]) for v in vs]),
                  "C": rref([act(l, v, s) for v in vs]), "D": rref([act(INV[s], v, l) for v in vs])}
            trivial = (l == IDENT and s == IDENT)
            if not trivial:
                nontriv += 1
            for k, key in im.items():
                j = STORED.get(key)
                if j is not None and cls[j]["dim"] == cls[c]["dim"] + 1:
                    vmatch[k][0] += 1
                    if not trivial:
                        vmatch[k][1] += 1
                    if k == "A":
                        info["j"] = j
            if info["j"] is None:
                info["problems"].append("no_match")
        DEG[c] = info
    ndeg = len(DEG)
    say("DEGENERATE WITNESSES: %d classes, %d with a non-identity witness; classes with a problem: %d %s"
        % (ndeg, nontriv, sum(1 for d in DEG.values() if d["problems"]),
           [(c, d["problems"]) for c, d in sorted(DEG.items()) if d["problems"]][:10]))
    for k in sorted(variants):
        say("  encoding %s %-52s: S+e lands on a stored subspace of dim+1 for %3d of %d classes (non-identity witnesses: %3d of %d)"
            % (k, variants[k], vmatch[k][0], ndeg, vmatch[k][1], nontriv))

    # ---- the two point IPs
    ipfiles = [("707", "ip_P707R2b_seeded_L25.txt", "cls_P707.npy", "P707R2b"), ("708", "ip_P708R2_seeded_L25.txt", "cls_P708.npy", "P708R2")]
    ipd = {}
    partial = False
    for key, ipf, cf, run in ipfiles:
        cl = read_npy(P(cf))
        R, N, dims, caps, ms, ngroup = read_ip(P(ipf))
        n = len(caps)
        if n != len(cl):
            if not allow_partial:
                die("%s has %d C rows, %s has %d classes" % (ipf, n, cf, len(cl)))
            partial = True
            cl = cl[:n]
        lbs = {}
        bad_dim = bad_m = 0
        cdim = [cls[c]["dim"] for c in range(NC)]
        for s in range(n):
            c = cl[s]
            if c < 0 or c >= NC:
                die("class id %d out of range in %s" % (c, cf))
            lb = R - caps[s]
            d = lbs.get(c)
            if d is None:
                d = lbs[c] = {}
            d[lb] = d.get(lb, 0) + 1
            if dims[s] != cdim[c]:
                bad_dim += 1
            if ms[s] != (1 << (dims[s] - 1)) - 1:
                bad_m += 1
        multi = sorted(c for c in lbs if len(lbs[c]) > 1)
        ipd[key] = dict(run=run, R=R, N=N, n=n, ngroup=ngroup, lbs=lbs, multi=multi)
        say("IP %s (%s): R %d N %d, %d C rows, group %s, %d classes with rows; row dim != class dim on %d rows, label count != 2^(dim-1)-1 on %d rows; "
            "classes whose rows carry more than one lb: %d %s" % (run, ipf, R, N, n, ngroup, len(lbs), bad_dim, bad_m, len(multi), multi[:10]))
    if partial:
        say("WARNING: partial IP rows (--allow-partial): the lb_used columns are incomplete; test run only")

    # ---- cross-checks against the team's own dependency tables (they feed no value of the table)
    deps = dict((r["point_run"], r) for r in read_tsv(P("result_dependencies_r1.tsv")))
    ru = {}
    for r in read_tsv(P("result27_rows_used.tsv")):
        cnt = {}
        for part in r["rows_in_ip(run:count)"].split(","):
            k, v = part.split(":")
            cnt[k] = int(v)
        ru[int(r["cls"])] = cnt
    for key, ipf, cf, run in ipfiles:
        lbk = ipd[key]["lbs"]
        md5 = hashlib.md5(open(P(ipf), "rb").read()).hexdigest()[:12]
        dr = deps.get(run)
        if dr is None:
            say("CROSS-CHECK: %s is not in result_dependencies_r1.tsv" % run)
            continue
        want = set(ints(dr["line_rows_used(raised_lines_r1)"])) | set(ints(dr["plane_rows_used(raised_planes_r1)"]))
        app = set(c for c in raised if c in lbk and max(lbk[c]) == raised[c]["new"])
        say("CROSS-CHECK %s: md5 of the IP %s, result_dependencies_r1 says %s; raised lines/planes applied in the IP %d, listed as used there %d; "
            "applied but not listed %s; listed but not applied %s" % (run, md5, dr["ip_md5"], len(app), len(want), sorted(app - want),
                                                                        sorted(want - app)))
    mine = {}
    for key in ("707", "708"):
        for c, d in ipd[key]["lbs"].items():
            mine.setdefault(c, {})[ipd[key]["run"]] = sum(d.values())
    say("CROSS-CHECK result27_rows_used.tsv: %d classes (here %d with rows); per-class row counts per IP equal on %d, differ on %d %s"
        % (len(ru), len(mine), sum(1 for c in mine if ru.get(c) == mine[c]), sum(1 for c in set(mine) | set(ru) if ru.get(c) != mine.get(c)),
           sorted(c for c in set(mine) | set(ru) if ru.get(c) != mine.get(c))[:10]))

    def lbtext(key, c):
        d = ipd[key]["lbs"].get(c)
        if d is None:
            return "-", "-", None
        return str(sum(d.values())), "/".join(str(x) for x in sorted(d)), max(d)

    # ---- certified values, by decreasing dimension (a degenerate class looks up the class one dimension up)
    order = sorted(range(NC), key=lambda c: (-cls[c]["dim"], c))
    ORD = ["flat", "methodK", "lcc", "deg", "routeB", "lift", "raised", "point"]
    # ties between routes with the same value: the route that is the provenance of the table value wins (a raised line whose
    # target plane is raised too is 'raised', not 'deg'; a lifted class is 'lift'), then the kind-based routes
    TIE = ["raised", "lift", "point", "flat", "methodK", "lcc", "routeB", "deg"]
    cert, route, cands, detail = {}, {}, {}, {}
    for c in order:
        cd = {}
        dt = {}
        if c in flat_set:
            cd["flat"] = flatrank[c]
            dt["flat"] = "flatrank=%d wang=%d" % (flatrank[c], cls[c]["wang"])
        if c in METHODK:
            cd["methodK"] = cls[c]["wang"]
            dt["methodK"] = "forced product (Lean method K), wang=%d" % cls[c]["wang"]
        if c == 44:
            cd["lcc"] = cls[c]["wang"]
            dt["lcc"] = "row 44 coset-count certificate, wang=%d" % cls[c]["wang"]
        if c in DEG:
            d = DEG[c]
            if d["j"] is not None and cert.get(d["j"]) is not None:
                cd["deg"] = cert[d["j"]]
                dt["deg"] = "e=%d q=%d s=%d -> j=%d cert_j=%d" % (d["e"], d["q"], d["s"], d["j"], cert[d["j"]])
        if c in routeb and routeb[c]["ok"]:
            cd["routeB"] = routeb[c]["L"] + 1
            dt["routeB"] = routeb[c]["text"]
        if c in lift and lift[c]["ok"]:
            cd["lift"] = lift[c]["L"] + 1
            dt["lift"] = lift[c]["text"]
        if c in raised and raised[c]["ok"]:
            cd["raised"] = raised[c]["new"]
            dt["raised"] = raised[c]["text"]
        if str(c) in ipd:
            cd["point"] = ipd[str(c)]["R"] + 1
            dt["point"] = "%s R=%d (IP header): R+1; its trace result is not checked here" % (ipd[str(c)]["run"], ipd[str(c)]["R"])
        cands[c] = cd
        if cd:
            best = max(cd.values())
            rt = [r for r in TIE if cd.get(r) == best][0]
            cert[c], route[c], detail[c] = best, rt, dt[rt]
        else:
            cert[c], route[c], detail[c] = None, "MISSING", ""

    # ---- the table
    cols = ["c", "dim", "basis", "seeded", "wang", "kind", "flatrank", "rows707", "lb707", "rows708", "lb708", "lb_used", "tv2", "route",
            "cert_lb", "routes_all", "detail", "rb_L", "rb_mono", "lift_L", "raised_old", "raised_new", "raised_L",
            "deg_e", "deg_q", "deg_s", "deg_j", "seeded_j", "tv2_j", "cert_j", "deg_ok", "deg_ok_tv2", "pilot", "raisedS", "flags"]
    lines = ["\t".join(cols)]
    lbused, flags = {}, {}
    for c in range(NC):
        r707, l707, m707 = lbtext("707", c)
        r708, l708, m708 = lbtext("708", c)
        ms_ = [x for x in (m707, m708) if x is not None]
        lbu = max(ms_) if ms_ else None
        lbused[c] = lbu
        fl = []
        if lbu is None:
            fl.append("UNUSED")
        if route[c] == "MISSING":
            fl.append("MISSING")
        if lbu is not None and (cert[c] is None or lbu > cert[c]):
            fl.append("IP>CERT")
        if lbu is not None and lbu > tv2[c]:
            fl.append("IP>TV2")
        if lbu is not None and lbu < tv2[c]:
            fl.append("IP<TV2")
        if cert[c] is None or tv2[c] > cert[c]:
            fl.append("TV2>CERT")
        if c in ipd["707"]["multi"] or c in ipd["708"]["multi"]:
            fl.append("IPMULTI")
        if c in flat_set and flatrank[c] != cls[c]["wang"]:
            fl.append("FLAT_NE_WANG")
        for rn, tabn in ((routeb, "ROUTEB"), (lift, "LIFT"), (raised, "RAISED")):
            if c in rn and not rn[c]["ok"]:
                fl.append(tabn + "_NOT_COMPLETE")
        if c in rb_fail:
            fl.append("ROUTEB_FAILED")
        dj = ["-"] * 9
        if c in DEG:
            d = DEG[c]
            for p in d["problems"]:
                fl.append("DEG_" + p.upper())
            if d["j"] is not None:
                j = d["j"]
                lbref = lbu if lbu is not None else cls[c]["seeded"]
                ok = cls[j]["seeded"] >= lbref
                ok2 = tv2[j] >= lbref
                dj = [str(d["e"]), str(d["q"]), str(d["s"]), str(j), str(cls[j]["seeded"]), str(tv2[j]),
                      "-" if cert[j] is None else str(cert[j]), "yes" if ok else "NO", "yes" if ok2 else "NO"]
                if not ok:
                    fl.append("DEG_SHORT")
            else:
                dj = [str(d["e"]), str(d["q"]), str(d["s"])] + ["-"] * 6
        flags[c] = fl
        ra = ",".join("%s:%d" % (rt, cands[c][rt]) for rt in ORD if rt in cands[c])
        row = [str(c), str(cls[c]["dim"]), ",".join(map(str, cls[c]["basis"])) or "-", str(cls[c]["seeded"]), str(cls[c]["wang"]),
               cls[c]["kind"], str(flatrank[c]), r707, l707, r708, l708, "-" if lbu is None else str(lbu), str(tv2[c]), route[c],
               "-" if cert[c] is None else str(cert[c]), ra or "-", detail[c] or "-",
               str(routeb[c]["L"]) if c in routeb else "-",
               ("yes" if routeb[c]["text"].endswith("MONOTONE") else "no") if c in routeb else "-",
               str(lift[c]["L"]) if c in lift else "-",
               str(raised[c]["old"]) if c in raised else "-", str(raised[c]["new"]) if c in raised else "-",
               str(raised[c]["L"]) if c in raised else "-"] + dj + [
               pilot.get(c, "-"), raisedS[c]["text"] if c in raisedS else "-", ",".join(fl) or "-"]
        lines.append("\t".join(x.replace("\t", " ").replace("\n", " ") for x in row))
    tsv = "\n".join(lines) + "\n"
    with open(os.path.join(out, "table_v2.tsv"), "w") as f:
        f.write(tsv)
    tsv_sha = hashlib.sha256(tsv.encode()).hexdigest()

    # ---- summary
    used = [c for c in range(NC) if lbused[c] is not None]
    unused = [c for c in range(NC) if lbused[c] is None]
    say()
    say("SUMMARY: %d classes (idx 0..%d), %d with rows in a point IP, %d without" % (NC, NC - 1, len(used), len(unused)))
    say("cert_lb = the value the chosen route is meant to prove: flat = the exact flattening rank computed here; methodK, lcc = wang (Lean routes, "
        "not replayed here); deg = cert_lb of the target class j; routeB, lift, raised = L+1 / new_lb from run files whose replay and completions "
        "are complete; point = R+1 (IP header, trace not checked here)")
    say("route counts (all classes / classes with IP rows):")
    for rt in ORD + ["MISSING"]:
        say("  %-8s %4d / %4d" % (rt, sum(1 for c in range(NC) if route[c] == rt), sum(1 for c in used if route[c] == rt)))
    say("MISSING among classes with IP rows: %s" % (" ".join("%d(d%d,%s,seeded %d,used %s)" % (c, cls[c]["dim"], cls[c]["kind"][:4], cls[c]["seeded"], lbused[c])
                                                            for c in used if route[c] == "MISSING") or "none"))
    say("MISSING among classes without IP rows: %s" % (" ".join("%d(d%d,%s,seeded %d)" % (c, cls[c]["dim"], cls[c]["kind"][:4], cls[c]["seeded"])
                                                              for c in unused if route[c] == "MISSING") or "none"))
    say("classes without IP rows (all): %s" % " ".join(map(str, unused)))
    ipx = [c for c in used if "IP>CERT" in flags[c]]
    say("IP-USED LB ABOVE THE CERTIFIED VALUE (lb_used > cert_lb or no route): %d classes" % len(ipx))
    for c in ipx:
        say("  %d d%d %s seeded %d tv2 %d lb_used %s cert %s route %s  routes_all: %s" % (c, cls[c]["dim"], cls[c]["kind"][:4], cls[c]["seeded"], tv2[c], lbused[c],
                                                                                    cert[c], route[c], ",".join("%s:%d" % (r, cands[c][r]) for r in ORD if r in cands[c]) or "-"))
    ipt = [c for c in used if "IP>TV2" in flags[c]]
    ipl = [c for c in used if "IP<TV2" in flags[c]]
    say("IP-USED LB ABOVE THE table_v2 VALUE (seeded or raised new_lb): %d classes %s" % (len(ipt), " ".join("%d(used %s > tv2 %d)" % (c, lbused[c], tv2[c]) for c in ipt) or "none"))
    say("IP-used lb BELOW the table_v2 value (weaker than the table; the raise is not in these IPs): %d classes %s" %
        (len(ipl), " ".join("%d(used %s < tv2 %d)" % (c, lbused[c], tv2[c]) for c in ipl[:60]) or "none"))
    for key in ("707", "708"):
        a = [c for c in ipd[key]["lbs"] if max(ipd[key]["lbs"][c]) != tv2[c]]
        say("  per IP %s: classes whose lb differs from tv2: %d %s" % (ipd[key]["run"], len(a), " ".join("%d(%s vs %d)" % (c, "/".join(map(str, sorted(ipd[key]["lbs"][c]))), tv2[c]) for c in sorted(a)[:60])))
    for key in ("707", "708"):
        lbk = ipd[key]["lbs"]
        app = [c for c in sorted(raised) if c in lbk and max(lbk[c]) == raised[c]["new"]]
        nap = [c for c in sorted(raised) if c in lbk and max(lbk[c]) != raised[c]["new"]]
        nrw = [c for c in sorted(raised) if c not in lbk]
        say("  per IP %s: raised lines/planes (%d): lb = new_lb in %d, lb != new_lb in %d %s, no rows in %d %s" % (
            ipd[key]["run"], len(raised), len(app), len(nap), nap, len(nrw), nrw))
    shorts = [c for c in sorted(DEG) if "DEG_SHORT" in flags[c]]
    say("DEGENERATE ROWS WHOSE TARGET BOUND IS SHORT (seeded(j) < lbref; lbref = lb_used, or seeded if the class has no IP row): %d of %d" % (len(shorts), ndeg))
    for c in shorts:
        d = DEG[c]
        j = d["j"]
        lbref = lbused[c] if lbused[c] is not None else cls[c]["seeded"]
        note = []
        if tv2[j] >= lbref:
            note.append("ok by tv2(j) (j is raised)")
        elif cert[j] is not None and cert[j] >= lbref:
            note.append("ok by cert(j)")
        if route[c] != "deg" and cert[c] is not None and cert[c] >= lbref:
            note.append("another route certifies the class")
        say("  %d d%d seeded %d lbref %d%s -> j=%d seeded_j %d tv2_j %d cert_j %s | route %s cert %s %s" % (
            c, cls[c]["dim"], cls[c]["seeded"], lbref, "" if lbused[c] is not None else "(unused)", j, cls[j]["seeded"], tv2[j],
            cert[j], route[c], cert[c], ("<- " + "; ".join(note)) if note else "<- NOT RESOLVED by any route"))
    nres = sum(1 for c in shorts if tv2[DEG[c]["j"]] >= (lbused[c] if lbused[c] is not None else cls[c]["seeded"]))
    say("short by seeded(j): %d; of these ok by tv2(j): %d; short even by tv2(j): %d" % (len(shorts), nres, len(shorts) - nres))
    unres = [c for c in shorts if cert[c] is None or cert[c] < (lbused[c] if lbused[c] is not None else cls[c]["seeded"])]
    say("short rows that no route certifies (cert_lb < lbref): %d %s" % (len(unres), " ".join("%d(%s)" % (c, "unused" if lbused[c] is None else "used") for c in unres) or "none"))
    nt2 = [c for c in sorted(DEG) if DEG[c]["j"] is not None and "DEG_SHORT" not in flags[c] and tv2[DEG[c]["j"]] < (lbused[c] if lbused[c] is not None else cls[c]["seeded"])]
    say("degenerate rows with seeded(j) ok but tv2(j) short: %d" % len(nt2))
    tc = [c for c in range(NC) if "TV2>CERT" in flags[c]]
    say("TABLE VALUES (tv2) ABOVE THE CERTIFIED VALUE, any class: %d classes (%d with IP rows)" % (len(tc), sum(1 for c in tc if lbused[c] is not None)))
    for c in tc:
        say("  %d d%d %s seeded %d tv2 %d cert %s route %s%s" % (c, cls[c]["dim"], cls[c]["kind"][:4], cls[c]["seeded"], tv2[c], cert[c], route[c],
                                                                  "" if lbused[c] is not None else " (unused)"))
    say("other flags: " + ", ".join("%s %d" % (f, sum(1 for c in range(NC) if f in flags[c]))
                                    for f in ("IPMULTI", "FLAT_NE_WANG", "ROUTEB_NOT_COMPLETE", "LIFT_NOT_COMPLETE", "RAISED_NOT_COMPLETE", "ROUTEB_FAILED")))
    say("pilot1 'wang' searches (informational, not a route): %d classes; complete with 0 leaves: %s" % (
        len(pilot), " ".join(str(c) for c in sorted(pilot) if pilot[c].endswith("leaves 0"))))
    say("table_v2.tsv: %d lines (header + %d classes), sha256 %s" % (len(lines), NC, tsv_sha))
    summary = "\n".join(S) + "\n"
    with open(os.path.join(out, "table_v2_summary.txt"), "w") as f:
        f.write(summary)

    # ---- provenance of the inputs, then the two outputs
    print("python " + sys.version.split()[0])
    print("script %s sha256 %s" % (os.path.basename(__file__), sha12(__file__)))
    for fn in ("seeded334.tsv", "certs334.tsv", "pilot1_results.tsv", "raised_lines_r1.tsv", "raised_planes_r1.tsv", "raised_spaces_r1.tsv",
               "result_dependencies_r1.tsv", "result27_rows_used.tsv", "ip_P707R2b_seeded_L25.txt", "ip_P708R2_seeded_L25.txt", "cls_P707.npy",
               "cls_P708.npy"):
        print("input %-28s sha256 %s" % (fn, sha12(P(fn))))
    h = hashlib.sha256()
    for fn in sorted(os.listdir(P("routeb"))):
        h.update(fn.encode())
        h.update(open(os.path.join(P("routeb"), fn), "rb").read())
    print("input routeb/ (%d files)        sha256 %s" % (len(os.listdir(P("routeb"))), h.hexdigest()[:12]))
    print("=== BEGIN table_v2_summary.txt ===")
    print(summary, end="")
    print("=== END table_v2_summary.txt ===")
    print("=== BEGIN table_v2.tsv ===")
    print(tsv, end="")
    print("=== END table_v2.tsv ===")
    print("table_v2.tsv sha256 %s lines %d" % (tsv_sha, len(lines)))


main()
