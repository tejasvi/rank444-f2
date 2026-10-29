#!/usr/bin/env python3
"""s23_monowit.py IN_DIR OUT_DIR [CLASS ...]   (standard library only)

Witnesses for the Route B classes that were certified as MONOTONE (no trace: mkipS9c found a strict superspace whose lb is
above L and wrote no IP).  For a class c with basis B_c a witness is a class j with dim j > dim c and lbOf j >= lbOf c
(lbOf = the lb_used column of table_v2.tsv) and a group element g = (l, s) of G0 = GL3 x GL3 acting as v -> l v s^-1 (3x3
matrices over F2 as 9-bit masks, entry (i, j) at bit 3i+j, as in certs334.tsv and s21_tab2.py), such that g maps every basis
vector of c into span(basis j).  Then R(T mod S_c) = R(T mod g S_c) >= R(T mod S_j) >= lbOf j.

Search (no IP file exists for a MONOTONE class): the strict superspaces T of S_c are enumerated by dimension, dim c + 1 first
(2^(9-d) - 1 of them); the class j of T is found among the stored classes of dimension dim T with the same rank distribution
(n1, n2, n3) by a scan over all 168 x 168 pairs (l, s) for g with g(T) in span(basis j) (every basis vector of T has its
image in S_j, g invertible, equal dimensions, so g(T) = S_j).  The first level that has a superspace whose class has
lbOf j >= lbOf c is used; among its valid superspaces the smallest class index j, then the first (l, s) in the order of the
GL list (ascending masks, l outer, s inner).  For that level the log of every superspace class is printed.

Every witness is then re-checked with separate code (the reference matrix product and this file's rref, not the lookup
tables of the search): l, s invertible; all 2^d elements of S_c map into span(basis j) (rref test); the images of the d basis
vectors are independent; each image equals the XOR of the listed subset of basis(j); dim and lb conditions.  Two negative
controls (a flipped subset bit; l replaced by its successor in the GL list) must be rejected.

Inputs in IN_DIR: seeded334.tsv, table_v2.tsv (from s21_tab2.py), routeb/rb_c<c>.done (the MONOTONE set is read from these
and must equal the requested classes).  Output OUT_DIR/mono_wit.tsv (also printed between "=== BEGIN/END mono_wit.tsv ===").
Columns: c j l s sub0 sub1 sub2 sub3 sinv dim_c dim_j lb_c lb_j tv2_j imgs basis_c basis_j
  sub<i>: bitmask over the positions of basis(j) in its stored order (bit k = basis(j)[k]); its XOR is the image of
          basis(c)[i] ('-' if i >= dim c); imgs: the images g(basis(c)[i]) as 9-bit masks; sinv = s^-1.
"""
import os, re, sys

REQUESTED = [388, 407, 443, 518, 527, 588, 612]


def die(msg):
    print("FATAL: " + msg)
    sys.exit(2)


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


def act(l, v, s):   # unmat(mat(l) mat(v) mat(s)); the group acts by act(l, v, INV[s])
    return unmat(mul(mul(mat(l), mat(v)), mat(s)))


def span_list(vs):
    s = [0]
    for v in vs:
        s = s + [x ^ v for x in s]
    return s


def read_tsv(path):
    with open(path) as f:
        lines = f.read().split("\n")
    hdr = lines[0].split("\t")
    return [dict(zip(hdr, ln.split("\t"))) for ln in lines[1:] if ln.strip()]


def ints(s):
    return [int(x) for x in s.split(",") if x not in ("", "-")]


IDENT = unmat([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
GL = [m for m in range(512) if len(rref([(m >> (3 * i)) & 7 for i in range(3)])) == 3]
assert len(GL) == 168 and IDENT == 273
INV = {}
for _m in GL:
    for _n in GL:
        if unmat(mul(mat(_m), mat(_n))) == IDENT:
            INV[_m] = _n
assert len(INV) == 168
GLIDX = {m: i for i, m in enumerate(GL)}
# lookup tables of the search: g = (p, q) acts as v -> LP[p][v] -> RT[q][.] = l_p v s_q^-1
LP = [[unmat(mul(mat(GL[p]), mat(v))) for v in range(512)] for p in range(168)]
RT = [[unmat(mul(mat(u), mat(INV[GL[q]]))) for u in range(512)] for q in range(168)]
RANK9 = [rank2([(v >> (3 * i)) & 7 for i in range(3)]) for v in range(512)]


def membership(vs):
    m = bytearray(512)
    for x in span_list(vs):
        m[x] = 1
    return m


def invariants(elems):
    n = [0, 0, 0, 0]
    for x in elems:
        n[RANK9[x]] += 1
    return (n[1], n[2], n[3])


def find_g(tb, memj):
    """first (p, q) with every vector of tb mapped into the subspace with membership table memj"""
    b0 = tb[0]
    rest = tb[1:]
    for p in range(168):
        lp = LP[p]
        x0 = lp[b0]
        xs = [lp[b] for b in rest]
        for q in range(168):
            rq = RT[q]
            if memj[rq[x0]]:
                ok = True
                for x in xs:
                    if not memj[rq[x]]:
                        ok = False
                        break
                if ok:
                    return p, q
    return None


def solve_subset(basis, target):
    """bitmask over positions of basis with XOR == target, or None (Gaussian elimination with tracked combinations)"""
    piv = {}
    for k, b in enumerate(basis):
        v, comb = b, 1 << k
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h][0]
                comb ^= piv[h][1]
            else:
                piv[h] = (v, comb)
                break
    v, comb = target, 0
    while v:
        h = v.bit_length() - 1
        if h not in piv:
            return None
        v ^= piv[h][0]
        comb ^= piv[h][1]
    return comb


def xor_subset(basis, mask):
    x = 0
    for k, b in enumerate(basis):
        if (mask >> k) & 1:
            x ^= b
    return x


def main():
    if len(sys.argv) < 3:
        die("usage: s23_monowit.py IN_DIR OUT_DIR [CLASS ...]")
    inp, out = sys.argv[1], sys.argv[2]
    want = [int(x) for x in sys.argv[3:]] or REQUESTED
    os.makedirs(out)
    S = []

    def say(s=""):
        S.append(s)
        print(s)

    def P(name):
        return os.path.join(inp, name)

    cls = {}
    for r in read_tsv(P("seeded334.tsv")):
        c = int(r["idx"])
        cls[c] = dict(dim=int(r["dim"]), basis=ints(r["basis"]), n=(int(r["n1"]), int(r["n2"]), int(r["n3"])), seeded=int(r["seeded"]))
    NC = len(cls)
    tv = {}
    for r in read_tsv(P("table_v2.tsv")):
        tv[int(r["c"])] = dict(lb_used=None if r["lb_used"] == "-" else int(r["lb_used"]), tv2=int(r["tv2"]), route=r["route"])
    if sorted(tv) != list(range(NC)):
        die("table_v2.tsv does not have the classes of seeded334.tsv")
    mono = []
    for fn in sorted(os.listdir(P("routeb"))):
        m = re.match(r"rb_c(\d+)\.done$", fn)
        if m and "MONOTONE" in open(os.path.join(P("routeb"), fn)).read():
            mono.append(int(m.group(1)))
    say("MONOTONE classes in rb_c*.done: %s; requested: %s; equal: %s" % (mono, want, sorted(mono) == sorted(want)))

    memb, key = {}, {}
    bad_inv = 0
    byinv = {}
    for c in range(NC):
        b = cls[c]["basis"]
        if len(rref(b)) != cls[c]["dim"] or len(b) != cls[c]["dim"]:
            die("class %d: basis is not independent of size dim" % c)
        memb[c] = membership(b)
        key[c] = rref(b)
        inv = invariants(span_list(b))
        if inv != cls[c]["n"]:
            bad_inv += 1
        byinv.setdefault((cls[c]["dim"], inv), []).append(c)
    say("rank distributions (n1, n2, n3) of the stored subspaces recomputed here differ from seeded334.tsv on %d of %d classes; "
        "invariant (dim, n1, n2, n3) groups: %d" % (bad_inv, NC, len(byinv)))

    def lbof(j):
        return tv[j]["lb_used"]

    def classify(T):
        k = len(T)
        inv = invariants(span_list(T))
        for j in byinv.get((k, inv), []):
            hit = find_g(list(T), memb[j])
            if hit is not None:
                return j, hit
        die("a subspace of dimension %d with distribution %s is in no stored class" % (k, inv))

    def verify(c, j, l, s, subs):
        """problems found by the separate re-check (empty list = verified)"""
        pr = []
        bc, bj = cls[c]["basis"], cls[j]["basis"]
        if l not in INV or s not in INV:
            return ["l or s not invertible"]
        if not len(bj) > len(bc):
            pr.append("dim j <= dim c")
        if lbof(j) is None or lbof(c) is None or lbof(j) < lbof(c):
            pr.append("lbOf j < lbOf c")
        rj = rref(bj)
        imgs = [act(l, b, INV[s]) for b in bc]
        for b, img in zip(bc, imgs):
            if rref(list(bj) + [img]) != rj:
                pr.append("image of %d is not in span(basis j)" % b)
        for x in span_list(bc):
            if rref(list(bj) + [act(l, x, INV[s])]) != rj:
                pr.append("element %d of S_c does not map into S_j" % x)
                break
        if rank2(imgs) != len(bc):
            pr.append("images dependent")
        for b, img, m in zip(bc, imgs, subs):
            if m < 0 or m >= (1 << len(bj)) or xor_subset(bj, m) != img:
                pr.append("subset mask %s of basis %d does not XOR to its image" % (m, b))
        return pr

    rows = []
    allok = True
    for c in want:
        d = cls[c]["dim"]
        lbc = lbof(c)
        if lbc is None:
            die("class %d has no lb_used in table_v2.tsv" % c)
        say("")
        say("class %d: dim %d, seeded %d, lbOf (lb_used) %d, tv2 %d, route %s" % (c, d, cls[c]["seeded"], lbc, tv[c]["tv2"], tv[c]["route"]))
        level = [key[c]]
        chosen = None
        k = d
        while chosen is None and k < 9:
            nxt = set()
            for T in level:
                memT = membership(list(T))
                for v in range(1, 512):
                    if not memT[v]:
                        nxt.add(rref(list(T) + [v]))
            level = sorted(nxt)
            k += 1
            res = []
            for T in level:
                j, (p, q) = classify(T)
                res.append((T, j, p, q))
            cnt = {}
            for T, j, p, q in res:
                cnt[j] = cnt.get(j, 0) + 1
            say("  level dim %d: %d superspaces, classes (j: count, lbOf): %s" % (
                k, len(level), " ".join("%d:%d(lb %s)" % (j, n, lbof(j)) for j, n in sorted(cnt.items()))))
            valid = [(j, T, p, q) for T, j, p, q in res if lbof(j) is not None and lbof(j) >= lbc]
            say("  level dim %d: max lb of a superspace class %s; %d superspaces have lbOf j >= %d" % (
                k, max(lbof(j) for j in cnt), len(valid), lbc))
            if valid:
                valid.sort()
                j, T, p, q = valid[0]
                chosen = (j, T, p, q)
        if chosen is None:
            say("  NO WITNESS: no strict superspace class has lbOf >= %d" % lbc)
            allok = False
            continue
        j, T, p, q = chosen
        l, s = GL[p], GL[q]
        bc, bj = cls[c]["basis"], cls[j]["basis"]
        imgs = [act(l, b, INV[s]) for b in bc]
        subs = [solve_subset(bj, img) for img in imgs]
        if any(m is None for m in subs):
            die("class %d: an image is not in span(basis %d) (search bug)" % (c, j))
        pr = verify(c, j, l, s, subs)
        say("  witness: j=%d (dim %d, lb_used %s, tv2 %d), via the superspace %s; l=%d s=%d (s^-1 = %d); images %s; subset masks %s; "
            "re-check: %s" % (j, cls[j]["dim"], lbof(j), tv[j]["tv2"], list(T), l, s, INV[s], imgs, subs, "VERIFIED" if not pr else "FAILED " + str(pr)))
        if pr:
            allok = False
        # negative controls: they must be rejected
        bad1 = list(subs)
        bad1[0] ^= 1
        bad2l = GL[(GLIDX[l] + 1) % 168]
        sub2 = [solve_subset(bj, act(bad2l, b, INV[s])) for b in bc]
        r1 = verify(c, j, l, s, bad1)
        r2 = verify(c, j, bad2l, s, [m if m is not None else 0 for m in sub2])
        say("  controls: flipped subset bit rejected: %s; l replaced by its successor in GL rejected: %s" % (bool(r1), bool(r2)))
        rows.append((c, j, l, s, subs, INV[s], d, cls[j]["dim"], lbc, lbof(j), tv[j]["tv2"], imgs, bc, bj, bool(r1), bool(r2)))

    cols = ["c", "j", "l", "s", "sub0", "sub1", "sub2", "sub3", "sinv", "dim_c", "dim_j", "lb_c", "lb_j", "tv2_j", "imgs", "basis_c", "basis_j"]
    lines = ["\t".join(cols)]
    for (c, j, l, s, subs, sinv, dc, dj, lbc, lbj, tv2j, imgs, bc, bj, r1, r2) in rows:
        sub = [str(m) for m in subs] + ["-"] * (4 - len(subs))
        lines.append("\t".join([str(c), str(j), str(l), str(s)] + sub + [str(sinv), str(dc), str(dj), str(lbc), str(lbj), str(tv2j),
                                                                       ",".join(map(str, imgs)), ",".join(map(str, bc)), ",".join(map(str, bj))]))
    tsv = "\n".join(lines) + "\n"
    with open(os.path.join(out, "mono_wit.tsv"), "w") as f:
        f.write(tsv)
    nctl = sum(1 for r in rows if r[14] and r[15])
    say("")
    say("SUMMARY: %d of %d requested classes have a verified witness; negative controls rejected for %d of %d witnesses" % (
        len(rows), len(want), nctl, len(rows)))
    print("=== BEGIN mono_wit.tsv ===")
    print(tsv, end="")
    print("=== END mono_wit.tsv ===")
    if not allok or len(rows) != len(want) or nctl != len(rows):
        sys.exit(1)


main()
