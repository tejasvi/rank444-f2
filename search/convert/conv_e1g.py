#!/usr/bin/env python3
"""conv_e1g.py v0: lineenum9vr --cert traces (format 'LEB9') -> E1G block literals for <3,3,4>
(B334/E1x/CheckG.lean), with a Python mirror of the Lean checker.  First version.

Usage: conv_e1g.py IPFILE TRACE --basis b1,b2,.. --lean OUT.lean --ns NAMESPACE [--block K]
  IPFILE   the IP text file (as read by lineenum9vr); TRACE the trace file; --block K picks the K-th block (default 0).
  --basis  the class basis of E (9-bit masks, from seeded334.tsv): gives the leaf domain DOM = E^perp minus 0.
  --lean   writes a NEW Lean module (refuses to overwrite) with the block literal, its slots, the context, the replay
           theorem `block_ok` (decide +kernel) and negative controls (mutants that the mirror rejects).
v0 limits (reported as errors, not handled): one block per run, no frontier (F) records, no leaves (L), no delegation or
block splitting; the C++ converter of the <3,3,3> project (cpp/enum/e1pemit.h of rank333-f2) covers these.

Semantics (port of Job::check / node2 of cpp/enum/e1pemit.h of rank333-f2, Apache-2.0, doi:10.5281/zenodo.23236154): the model keeps E1's budgets (one copy less per added label, and
the rows that reach their cap zero their labels); a child whose budget is 0 in the model is emitted as a skip and its
trace subtree dropped; an O node whose dual already kills in the model's state is emitted as a K record.
"""
import argparse
import os
import re
import sys

SC = 1 << 30
NL, LB, RW, SIB = 127, 7, 695, 15  # E1G widths for <3,3,4> (CheckG.lean)
MAGIC = 0x3942454C


class Fail(Exception):
    pass


def req(c, msg):
    if not c:
        raise Fail(msg)


def nsub(a, b):
    return a - b if a > b else 0


# ------------------------------------------------------------------------------------------------ the IP
class IP:
    def __init__(self, path):
        with open(path) as f:
            t = f.readline().split()
            req(t[0] == "R" and t[2] == "N", "IP line 1")
            self.R, self.N = int(t[1]), int(t[3])
            self.vecs = [int(x) for x in f.readline().split()]
            req(len(self.vecs) == self.N, "IP line 2")
            self.ub = [self.R] * self.N
            self.cap, self.kdim, self.rowl = [], [], []
            self.G = []
            for line in f:
                t = line.split()
                if not t:
                    continue
                if t[0] == "C":
                    k, c, m = int(t[1]), int(t[2]), int(t[3])
                    ls = [int(x) for x in t[4:4 + m]]
                    req(len(ls) == m, "C row length")
                    if m == 1:
                        self.ub[ls[0]] = min(self.ub[ls[0]], max(0, c))
                        continue
                    req(k != 0 and c >= 0, "row kind / negative cap not supported in v0")
                    self.kdim.append(k)
                    self.cap.append(c)
                    self.rowl.append(sorted(ls))
                elif t[0] == "G":
                    for _ in range(int(t[1])):
                        self.G.append([int(x) for x in f.readline().split()])
                    break
                else:
                    raise Fail("IP line kind %r" % t[0])
        req(self.N <= NL, "N above 127")
        for gi, P in enumerate(self.G):
            if all(P[l] == l for l in range(self.N)):
                self.G[0], self.G[gi] = self.G[gi], self.G[0]
                break
        req(self.G and all(self.G[0][l] == l for l in range(self.N)), "no identity in G")
        req(len(self.G) <= 2048, "group above 2048")
        self.nrows = len(self.cap)
        self.inc = [[] for _ in range(self.N)]
        for r, ls in enumerate(self.rowl):
            for l in ls:
                self.inc[l].append(r)
        self.lab = {v: l for l, v in enumerate(self.vecs)}
        self.rmaskv = [sum(1 << l for l in ls) for ls in self.rowl]


# ------------------------------------------------------------------------------------------------ the checked tree
class Node:
    def __init__(self, tag):
        self.tag = tag
        self.cut, self.kind, self.crow, self.hd = 0, 0, -1, False
        self.dual, self.fixes, self.items = [], [], []


class Item:
    def __init__(self, code, l):
        self.code, self.l = code, l  # 0 skip, 3 non-canonical, 1 lookahead-killed child, 2 child subtree
        self.g, self.sat, self.pk, self.prow, self.child = 0, [], 0, -1, None


class Job:
    def __init__(self, ip):
        self.ip = ip
        self.st = {}

    def stat(self, k, v=1):
        self.st[k] = self.st.get(k, 0) + v

    # trace reader
    def u8(self):
        req(self.bi < len(self.b), "trace truncated")
        x = self.b[self.bi]
        self.bi += 1
        return x

    def var(self):
        x, s = 0, 0
        while True:
            c = self.u8()
            x |= (c & 127) << s
            s += 7
            if c < 128:
                return x
            req(s < 63, "varint")

    def dual(self):
        n = self.var()
        d = []
        for _ in range(n):
            r = self.var()
            y = self.var()
            req(r < self.ip.nrows, "dual row")
            req(y <= 1 << 50, "Y above 2^50")
            d.append((r, y))
        req(len(d) <= self.ip.nrows, "dual length")
        return d

    # model
    def bound(self, du, lo):
        ip = self.ip
        T = [0] * ip.N
        B = 0
        for r, y in du:
            B += y * (ip.cap[r] - self.cnt[r])
            for x in ip.rowl[r]:
                T[x] += y
        for l in range(lo, ip.N):
            if self.u[l] > 0 and T[l] < SC:
                B += self.u[l] * (SC - T[l])
        return B, T

    def weight(self, lo, notin=-1):
        ip = self.ip
        s = 0
        for l in range(lo, ip.N):
            if notin < 0 or l not in ip.rowl[notin]:
                s += self.u[l]
        return s

    def start(self, pre):
        ip = self.ip
        self.cnt = [0] * ip.nrows
        self.mult = [0] * ip.N
        self.u = list(ip.ub)
        self.seq = []
        for l in pre:
            self.mult[l] += 1
            self.seq.append(l)
            self.u[l] -= 1
            for r in ip.inc[l]:
                self.cnt[r] += 1
        req(all(x >= 0 for x in self.u), "prefix exceeds a label cap")
        sat = []
        for r in range(ip.nrows):
            req(self.cnt[r] <= ip.cap[r], "prefix exceeds a row cap")
            if self.cnt[r] == ip.cap[r]:
                z = False
                for x in ip.rowl[r]:
                    if self.u[x] > 0:
                        self.u[x] = 0
                        z = True
                if z:
                    sat.append(r)
        return sat

    def add(self, l, pos_after):
        ip = self.ip
        saved = list(self.u)
        self.mult[l] += 1
        self.seq.append(l)
        self.u[l] -= 1
        req(self.u[l] >= 0, "label over its cap")
        sat = []
        for r in ip.inc[l]:
            self.cnt[r] += 1
            if self.cnt[r] == ip.cap[r]:
                z = False
                for x in ip.rowl[r]:
                    if self.u[x] > 0:
                        self.u[x] = 0
                        if x >= pos_after:
                            z = True
                if z:
                    sat.append(r)
        return sat, saved

    def undo(self, l, saved):
        self.mult[l] -= 1
        self.seq.pop()
        self.u = saved
        for r in self.ip.inc[l]:
            self.cnt[r] -= 1

    def noncanon(self, l):
        s = sorted(self.seq + [l])
        for gi in range(1, len(self.ip.G)):
            P = self.ip.G[gi]
            if sorted(P[x] for x in s) < s:
                return gi
        return -1

    def skip(self, nd, s):
        it = Item(0, s)
        if self.u[s] == 0:
            self.stat("skip0")
        else:
            g = self.noncanon(s)
            req(g >= 0, "skip not justified")
            it.code, it.g = 3, g
            self.stat("skipNC")
        nd.items.append(it)

    def skipnode(self):
        tag = chr(self.u8())
        if tag in "LF":
            return
        if tag == "K":
            self.dual()
            return
        req(tag == "O", "unknown node tag")
        self.u8()
        kind = self.u8()
        if kind == 1:
            self.var()
        if self.u8():
            self.dual()
        self.skipkids()

    def skipkids(self):
        while True:
            c = chr(self.u8())
            if c == "E":
                return
            req(c == "C", "expected C")
            self.u8()
            if self.bi < len(self.b) and self.b[self.bi] == ord("P"):
                self.bi += 1
                if self.u8() == 1:
                    self.var()
            else:
                self.skipnode()

    def node2(self, pos):
        ip = self.ip
        d = len(self.seq)
        rem = ip.R - d
        tag = chr(self.u8())
        nd = Node(tag)
        self.nodes.append(nd)
        if tag == "L":
            req(rem == 0, "leaf with rem > 0")
            raise Fail("leaf records are not supported in v0")
        if tag == "F":
            raise Fail("frontier records are not supported in v0")
        req(rem > 0, "node at depth R")
        if tag == "K":
            du = self.dual()
            B, _ = self.bound(du, pos)
            req(B < rem * SC, "K fails")
            nd.dual = du
            self.stat("K")
            return nd
        req(tag == "O", "unknown node tag")
        cut = self.u8()
        kind = self.u8()
        row = -1
        if kind == 1:
            row = self.var()
            req(row < ip.nrows, "cut row")
        hd = self.u8()
        du = self.dual() if hd else []
        saved_u = list(self.u)
        fixes = []
        if hd:
            B, T = self.bound(du, pos)
            gap = B - rem * SC
            if gap < 0:
                # the node dual already kills in E1's (smaller) budgets: emit a K record, drop the subtree
                nd.tag = "K"
                nd.dual = du
                self.skipkids()
                self.stat("OtoK")
                return nd
            for l in range(pos, ip.N):
                if self.u[l] > 0 and T[l] > SC:
                    km = gap // (T[l] - SC)
                    if km < self.u[l]:
                        self.u[l] = km
                        fixes.append((l, km))
                        self.stat("fixed")
        if kind == 0:
            req(cut >= ip.N, "cut kind 0")
        elif kind == 1:
            need = rem - (ip.cap[row] - self.cnt[row])
            req(need >= 1, "cut1 need")
            req(self.weight(cut, row) < need, "cut1")
        elif kind == 2:
            req(self.weight(cut) < rem, "cut2")
        elif kind == 3:
            req(hd, "cut3 without dual")
            B3, _ = self.bound(du, cut)
            req(B3 < rem * SC, "cut3")
        else:
            raise Fail("cut kind")
        self.stat("cut%d" % kind)
        nd.cut, nd.kind, nd.crow, nd.hd, nd.dual, nd.fixes = cut, kind, row, bool(hd), du, fixes
        nxt = pos
        while True:
            c = chr(self.u8())
            if c == "E":
                break
            req(c == "C", "expected C")
            l = self.u8()
            req(pos <= l < min(cut, ip.N), "child label range")
            for s in range(nxt, l):
                self.skip(nd, s)
            nxt = l + 1
            if self.u[l] == 0:
                self.stat("fixPruned")
                self.skip(nd, l)
                if self.bi < len(self.b) and self.b[self.bi] == ord("P"):
                    self.bi += 1
                    if self.u8() == 1:
                        self.var()
                else:
                    self.skipnode()
                continue
            sat, saved = self.add(l, l)
            self.stat("child")
            self.stat("satev", len(sat))
            it = Item(2, l)
            it.sat = sat
            if self.bi < len(self.b) and self.b[self.bi] == ord("P"):
                self.bi += 1
                k = self.u8()
                prow = -1
                if k == 1:
                    prow = self.var()
                    req(prow < ip.nrows, "P row")
                rem2 = rem - 1
                if k == 2:
                    req(self.weight(l) < rem2, "P2")
                else:
                    req(k == 1, "P kind")
                    need = rem2 - (ip.cap[prow] - self.cnt[prow])
                    req(need >= 1, "P1 need")
                    req(self.weight(l, prow) < need, "P1")
                self.stat("P%d" % k)
                it.code, it.pk, it.prow = 1, k, prow
                nd.items.append(it)
            else:
                nd.items.append(it)
                it.child = self.node2(l)
            self.undo(l, saved)
        for s in range(nxt, min(cut, ip.N)):
            self.skip(nd, s)
        self.u = saved_u
        return nd

    def check(self, payload):
        self.b, self.bi = payload, 0
        self.nodes = []
        t = chr(self.u8())
        req(t in "TJ", "block tag")
        n = self.u8()
        self.pre = []
        for _ in range(n):
            v = self.u8() | (self.u8() << 8)
            req(v in self.ip.lab, "prefix vector")
            self.pre.append(self.ip.lab[v])
        req(self.pre == sorted(self.pre), "prefix not sorted")
        if t == "T":
            self.u8()
        self.sat0 = self.start(self.pre)
        self.stat("startsat", len(self.sat0))
        self.root = self.node2(self.pre[-1] if self.pre else 0)
        req(chr(self.u8()) == "Z", "expected Z")
        self.blocknodes = self.var()
        req(self.bi == len(self.b), "trailing bytes")


# ------------------------------------------------------------------------------------------------ emission (E1G)
class BW:
    def __init__(self):
        self.v, self.n = 0, 0

    def put(self, x, k):
        req(0 <= x < (1 << k), "field overflow: %d in %d bits" % (x, k))
        self.v |= x << self.n
        self.n += k

    def cat(self, o):
        self.v |= o.v << self.n
        self.n += o.n


def collect_rows(job):
    rows, idx = [], {}

    def ref(r):
        if r not in idx:
            idx[r] = len(rows)
            rows.append(r)

    for r in job.sat0:
        ref(r)
    stack = [job.root]
    while stack:
        nd = stack.pop()
        if nd.tag == "K":
            for r, _ in nd.dual:
                ref(r)
        elif nd.tag == "O":
            if nd.kind == 1:
                ref(nd.crow)
            for r, _ in nd.dual:
                ref(r)
            for it in nd.items:
                if it.code in (1, 2):
                    for r in it.sat:
                        ref(r)
                    if it.code == 1 and it.pk == 1:
                        ref(it.prow)
                    if it.code == 2:
                        stack.append(it.child)
    req(len(rows) < 4096, "more than 4095 rows in the block")
    return rows, idx


def emit_node(nd, ip, idx):
    w = BW()
    if nd.tag == "K":
        w.put(1, 2)
        w.put(len(nd.dual), 8)
        for r, y in nd.dual:
            w.put(idx[r], 12)
            w.put(y, 36)
        return w
    req(nd.tag == "O", "emit: node tag")
    w.put(2, 2)
    w.put(min(nd.cut, ip.N), 7)
    w.put(nd.kind, 2)
    if nd.kind == 1:
        w.put(idx[nd.crow], 12)
    w.put(1 if nd.hd else 0, 1)
    if nd.hd:
        w.put(len(nd.dual), 8)
        for r, y in nd.dual:
            w.put(idx[r], 12)
            w.put(y, 36)
        w.put(len(nd.fixes), 7)
        for l, nu in nd.fixes:
            w.put(l, 7)
            w.put(nu, 4)
    for it in nd.items:
        if it.code == 0:
            w.put(0, 2)
        elif it.code == 3:
            w.put(3, 2)
            w.put(it.g, 11)
        else:
            w.put(it.code, 2)
            req(len(it.sat) < 64, "more than 63 saturating rows")
            w.put(len(it.sat), 6)
            for r in it.sat:
                w.put(idx[r], 12)
            if it.code == 1:
                w.put(1 if it.pk == 1 else 0, 1)
                if it.pk == 1:
                    w.put(idx[it.prow], 12)
            else:
                c = emit_node(it.child, ip, idx)
                w.put(c.n, 24)
                w.cat(c)
    return w


def emit_block(job, ip):
    rows, idx = collect_rows(job)
    w = BW()
    w.put(0, 1)  # mode 0
    w.put(len(job.pre), 5)
    w.put(job.pre[-1] if job.pre else 0, 7)
    for l in job.pre:
        w.put(l, 7)
    w.put(0, 8)  # no delegated children
    w.put(len(rows), 12)
    for r in rows:
        w.put(r, SIB)  # slot index = multi-label row index (file order)
    w.put(len(job.sat0), 8)
    for r in job.sat0:
        w.put(idx[r], 12)
    w.cat(emit_node(job.root, ip, idx))
    return w, rows


# ------------------------------------------------------------------------------------------------ the mirror of CheckG.lean
class Mirror:
    FM = (1 << 128) - 1
    M64 = (1 << 64) - 1
    M127 = (1 << 127) - 1
    MSL = (1 << 264) - 1
    REP = sum(1 << (128 * l) for l in range(128))
    SPM = sum(1 << (127 * j) for j in range(128))
    FMALL = (1 << (128 * 128)) - 1
    DSCREP = ((1 << 30) + (1 << 64)) * REP

    def __init__(self, R, N, VT, DOM, GP, LF, sl):
        self.R, self.N, self.VT, self.DOM, self.GP, self.LF, self.sl = R, N, VT, DOM, GP, LF, sl

    @staticmethod
    def rd(k, S):
        return S & ((1 << k) - 1)

    def spread(self, m):
        return (m * self.SPM) & self.REP

    def fmask(self, m):
        return self.spread(m) * self.FM

    def fsum(self, v):
        return v % self.FM

    def dot(self, vr, x):
        return ((vr * x) >> 16128) & self.FM

    def fld(self, v, l):
        return (v >> (128 * l)) & self.FM

    def hif(self, lo):
        return (self.FMALL >> (128 * lo)) << (128 * lo)

    @staticmethod
    def one(l):
        return 1 << (128 * l)

    @staticmethod
    def oner(l):
        return 1 << (128 * nsub(126, l))

    def deficit(self, T, UFR, lo):
        D = nsub(self.DSCREP, T)
        return self.dot(UFR, (D & (((D >> 64) & self.REP) * self.M64)) & self.hif(lo))

    def slotAt(self, RTb, j):
        return (RTb >> (264 * j)) & self.MSL

    def rmask(self, RTb, j):
        return self.slotAt(RTb, j) & self.M127

    def rmaskr(self, RTb, j):
        return (self.slotAt(RTb, j) >> 127) & self.M127

    def rcap(self, RTb, j):
        return (self.slotAt(RTb, j) >> 254) & 31

    def wout(self, UF, m, lo):
        return self.fsum(UF & (self.FMALL ^ self.fmask(m)) & self.hif(lo))

    def mkRTd(self, h, n, IX):
        if h == 0:
            return self.sl(self.rd(15, IX)) if n == 1 else 0
        if n <= 1:
            return self.sl(self.rd(15, IX)) if n == 1 else 0
        a = n >> 1
        return self.mkRTd(h - 1, a, self.rd(15 * a, IX)) | (self.mkRTd(h - 1, n - a, IX >> (15 * a)) << (264 * a))

    def rdual(self, RTb, k, S):
        BC = T = 0
        for _ in range(k):
            y = self.rd(36, S >> 12)
            j = self.rd(12, S)
            BC += y * self.rcap(RTb, j)
            T += y * self.spread(self.rmask(RTb, j))
            S >>= 48
        return BC, T, S

    def sats(self, RTb, n, MV, UF, UFR, S):
        ok, M, MR = True, 0, 0
        for _ in range(n):
            j = self.rd(12, S)
            ok = ok and self.fsum(MV & self.fmask(self.rmask(RTb, j))) == self.rcap(RTb, j)
            M |= self.rmask(RTb, j)
            MR |= self.rmaskr(RTb, j)
            S >>= 12
        return ok, UF & (self.FMALL ^ self.fmask(M)), UFR & (self.FMALL ^ self.fmask(MR)), S

    def fixes(self, n, T, gap, UF, UFR, S):
        ok = True
        for _ in range(n):
            l = self.rd(7, S)
            nu = self.rd(4, S >> 7)
            u = self.fld(UF, l)
            t = self.fld(T, l)
            ok = ok and SC + 1 <= t and nu + 1 <= u and gap + 1 <= (nu + 1) * nsub(t, SC)
            UF = nsub(UF, nsub(u, nu) * self.one(l))
            UFR = nsub(UFR, nsub(u, nu) * self.oner(l))
            S >>= 11
        return ok, UF, UFR, S

    def imgR(self, gp, pl, m):
        acc = 0
        for _ in range(m):
            acc += self.oner((gp >> (7 * self.rd(7, pl))) & 127)
            pl >>= 7
        return acc

    def leafRec(self, pl, cert):
        terms = 0
        for i in range(self.R):
            terms |= ((self.VT >> (9 * self.rd(7, pl))) & 511) << (9 * i)
            pl >>= 7
        return self.R | (terms << 6) | ((1 | (self.DOM << 2) | (cert << 514)) << (6 + 9 * self.R))

    def budU(self, B, rev=False):
        U = 0
        for l in range(127):
            U += self.rd(4, B >> (4 * l)) * (self.oner(l) if rev else self.one(l))
        return U

    def stEq(self, r, d, pos, pl, UF):
        return (self.rd(5, r) == d and self.rd(7, r >> 5) == pos and self.rd(7 * d, r >> 12) == pl
                and self.budU(r >> (12 + 7 * d)) == UF)

    def kids(self, fuel, RTb, H, cnt, d, pl, MV, MVR, UF, UFR, l, S):
        for _ in range(cnt):
            code = self.rd(2, S)
            if code == 0:
                if self.fld(UF, l) != 0:
                    return False
                S >>= 2
            elif code == 3:
                g = self.rd(11, S >> 2)
                if not (MVR + self.oner(l) < self.imgR(self.GP(g), pl | (l << (7 * d)), d + 1)):
                    return False
                S >>= 13
            else:
                if not (1 <= self.fld(UF, l)):
                    return False
                n = self.rd(6, S >> 2)
                ok, UF2, UFR2, S2 = self.sats(RTb, n, MV + self.one(l), nsub(UF, self.one(l)), nsub(UFR, self.oner(l)),
                                              S >> 8)
                if not ok:
                    return False
                if code == 1:
                    if self.rd(1, S2) == 0:
                        if not (self.wout(UF2, 0, l) < nsub(self.R, d + 1)):
                            return False
                        S = S2 >> 1
                    else:
                        j = self.rd(12, S2 >> 1)
                        need = nsub(nsub(self.R, d + 1) + self.fsum((MV + self.one(l)) & self.fmask(self.rmask(RTb, j))),
                                    self.rcap(RTb, j))
                        if not (1 <= need and self.wout(UF2, self.rmask(RTb, j), l) < need):
                            return False
                        S = S2 >> 13
                else:
                    ln = self.rd(24, S2)
                    if ln == 0:
                        ix = self.rd(8, S2 >> 24)
                        if not self.stEq(self.rd(RW, H >> (RW * ix)), d + 1, l, pl | (l << (7 * d)), UF2):
                            return False
                        S = S2 >> 32
                    else:
                        if not self.node(fuel, RTb, H, d + 1, l, pl | (l << (7 * d)), MV + self.one(l),
                                         MVR + self.oner(l), UF2, UFR2, self.rd(ln, S2 >> 24)):
                            return False
                        S = S2 >> (24 + ln)
            l += 1
        return True

    def node(self, fuel, RTb, H, d, pos, pl, MV, MVR, UF, UFR, S):
        if fuel == 0:
            return False
        R, N = self.R, self.N
        tag = self.rd(2, S)
        S1 = S >> 2
        if tag == 0:
            return nsub(R, d) == 0 and self.LF(pl)  # CheckG: the leaf test is on the packed prefix
        if not (1 <= nsub(R, d)):
            return False
        rem = nsub(R, d)
        if tag == 1:
            BC, T, _ = self.rdual(RTb, self.rd(8, S1), S1 >> 8)
            return BC + self.deficit(T, UFR, pos) < rem * SC + self.dot(MVR, T)
        cut = self.rd(7, S1)
        kind = self.rd(2, S1 >> 7)
        cj = self.rd(12, S1 >> 9)
        S3 = (S1 >> 9 >> 12) if kind == 1 else (S1 >> 9)
        hd = self.rd(1, S3) == 1
        S4 = S3 >> 1
        if hd:
            BC, T, S5 = self.rdual(RTb, self.rd(8, S4), S4 >> 8)
        else:
            BC, T, S5 = 0, 0, S4
        RS = rem * SC + self.dot(MVR, T)
        if hd:
            if not (RS <= BC + self.deficit(T, UFR, pos)):
                return False
            gap = nsub(BC + self.deficit(T, UFR, pos), RS)
            ok, UF2, UFR2, S6 = self.fixes(self.rd(7, S5), T, gap, UF, UFR, S5 >> 7)
        else:
            ok, UF2, UFR2, S6 = True, UF, UFR, S5
        if not ok:
            return False
        if kind == 0:
            cok = N <= cut
        elif kind == 1:
            need = nsub(rem + self.fsum(MV & self.fmask(self.rmask(RTb, cj))), self.rcap(RTb, cj))
            cok = 1 <= need and self.wout(UF2, self.rmask(RTb, cj), cut) < need
        elif kind == 2:
            cok = self.wout(UF2, 0, cut) < rem
        else:
            cok = hd and BC + self.deficit(T, UFR2, cut) < RS
        if not cok:
            return False
        cnt = nsub(N if N <= cut else cut, pos)
        return self.kids(fuel - 1, RTb, H, cnt, d, pl, MV, MVR, UF2, UFR2, pos, S6)

    def mvOf(self, d, pl):
        MV = MVR = 0
        for _ in range(d):
            MV += self.one(self.rd(7, pl))
            MVR += self.oner(self.rd(7, pl))
            pl >>= 7
        return MV, MVR

    def block(self, UB, UBR, S):
        mode = self.rd(1, S)
        d = self.rd(5, S >> 1)
        pos = self.rd(7, S >> 6)
        pl = self.rd(7 * d, S >> 13)
        S1 = S >> (13 + 7 * d)
        S2 = (S1 >> 508) if mode == 1 else S1
        nd = self.rd(8, S2)
        H = self.rd(RW * nd, S2 >> 8)
        rest = S2 >> (8 + RW * nd)
        k = self.rd(12, rest)
        RTb = self.mkRTd(13, k, self.rd(15 * k, rest >> 12))
        S3 = rest >> 12 >> (15 * k)
        MV, MVR = self.mvOf(d, pl)
        if mode == 1:
            UF, UFR, ok, S4 = self.budU(S1), self.budU(S1, True), True, S3
        else:
            UF0, UFR0 = nsub(UB, MV), nsub(UBR, MVR)
            ok, UF, UFR, S4 = self.sats(RTb, self.rd(8, S3), MV, UF0, UFR0, S3 >> 8)
        return ok and d <= self.R and self.node(32, RTb, H, d, pos, pl, MV, MVR, UF, UFR, S4)


# ------------------------------------------------------------------------------------------------ the Lean module
def slot_value(ip, r):
    m = ip.rmaskv[r]
    mr = sum(1 << (126 - l) for l in ip.rowl[r])
    # the labels >= N lie in every row as SlotG.slot computes it (their label planes are 0): the slots of the IPOK
    # replay; their budgets and multiplicities are 0, so the mirror's verdict carries over
    hi = ((1 << 127) - 1) ^ ((1 << ip.N) - 1)
    lo = (1 << (127 - ip.N)) - 1
    req(ip.cap[r] < 32, "cap above 31")
    return (m | hi) | ((mr | lo) << 127) | (ip.cap[r] << 254)


def tabg_check(tabg):
    """the ECT constants of B334/E1x/TabG.lean equal the mirror's formulas"""
    vals = {}
    for line in open(tabg):
        t = line.split()
        if len(t) >= 4 and t[0] == "def" and t[2] == ":" and t[3] == "Nat":
            vals[t[1]] = int(t[5], 16)
    req(vals.get("REP") == Mirror.REP and vals.get("SPM") == Mirror.SPM and vals.get("FMALL") == Mirror.FMALL
        and vals.get("DSCREP") == Mirror.DSCREP, "TabG constants differ from the formulas")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ip")
    ap.add_argument("trace")
    ap.add_argument("--basis", required=True)
    ap.add_argument("--lean", default="")
    ap.add_argument("--ns", default="")
    ap.add_argument("--block", type=int, default=0)
    ap.add_argument("--tabg", required=True)
    ap.add_argument("--bin", default="", help="write the block literal for #e1lits (u32 count 1, u32 nbytes, LE bytes)")
    a = ap.parse_args()
    req(bool(a.lean) != bool(a.bin), "give exactly one of --lean, --bin")
    req(not a.lean or a.ns, "--lean needs --ns")
    req(not os.path.exists(a.lean or a.bin), "output exists: %s" % (a.lean or a.bin))
    tabg_check(a.tabg)
    ip = IP(a.ip)
    data = open(a.trace, "rb").read()
    q, k, payload = 0, 0, None
    while q + 12 <= len(data):
        mg = int.from_bytes(data[q:q + 4], "little")
        ln = int.from_bytes(data[q + 4:q + 12], "little")
        req(mg == MAGIC, "magic")
        req(q + 12 + ln <= len(data), "truncated block")
        if k == a.block:
            payload = data[q + 12:q + 12 + ln]
        q += 12 + ln
        k += 1
    req(payload is not None, "no such block")
    job = Job(ip)
    job.check(payload)
    w, rows = emit_block(job, ip)
    basis = [int(x) for x in a.basis.split(",")]
    DOM = 0
    for X in range(1, 512):
        if all(bin(X & e).count("1") % 2 == 0 for e in basis):
            DOM |= 1 << X
    VT = sum(v << (9 * l) for l, v in enumerate(ip.vecs))
    UB = sum(ip.ub[l] << (128 * l) for l in range(ip.N))
    UBR = sum(ip.ub[l] << (128 * (126 - l)) for l in range(ip.N))
    GPv = [sum(P[l] << (7 * l) for l in range(ip.N)) for P in ip.G]
    IDP = sum(l << (7 * l) for l in range(127))
    slots = {r: slot_value(ip, r) for r in rows}

    def sl(i):
        return slots.get(i, 0)

    def GP(g):
        return GPv[g] if g < len(GPv) else IDP

    mir = Mirror(ip.R, ip.N, VT, DOM, GP, lambda r: False, sl)
    ok = mir.block(UB, UBR, w.v)
    req(ok, "the mirror rejects the emitted block")
    if a.bin:
        nb = (w.v.bit_length() + 7) // 8
        with open(a.bin, "xb") as f:
            f.write((1).to_bytes(4, "little") + nb.to_bytes(4, "little") + w.v.to_bytes(nb, "little"))
        print("OK block bits=%d rows=%d nodes=%d bin=%s stats=%s" % (
            w.n, len(rows), len(job.nodes), a.bin, " ".join("%s=%d" % kv for kv in sorted(job.st.items()))))
        return
    # negative controls: mutants the mirror rejects
    muts = []
    nodes = job.nodes
    nc = [it for nd in nodes if nd.tag == "O" for it in nd.items if it.code == 3]
    if nc:
        it = nc[0]
        g_old = it.g
        it.g = 0  # the identity: its image is the multiset itself, never smaller
        wm, _ = emit_block(job, ip)
        it.g = g_old
        if not mir.block(UB, UBR, wm.v):
            muts.append(("neg_g0", "the first non-canonical skip with the identity as witness", wm.v))
    ks = [nd for nd in nodes if nd.tag == "K"]
    if ks:
        nd = ks[0]
        d_old = nd.dual
        nd.dual = [(r, y // 2) for r, y in d_old]
        wm, _ = emit_block(job, ip)
        nd.dual = d_old
        if not mir.block(UB, UBR, wm.v):
            muts.append(("neg_yhalf", "the first kill with every Y halved", wm.v))
    os_ = [nd for nd in nodes if nd.tag == "O"]
    if os_:
        nd = os_[0]
        cut_old, kind_old = nd.cut, nd.kind
        if kind_old == 1:
            nd.cut = nd.cut  # same cut, but claimed by total weight (kind 2)
            nd.kind = 2
            wm, _ = emit_block(job, ip)
            nd.kind = kind_old
            if not mir.block(UB, UBR, wm.v):
                muts.append(("neg_cut2", "the root cut claimed by total weight instead of its row", wm.v))
    with open(a.lean, "x") as f:
        f.write("import B334.E1x.CheckG\n\n")
        mc = re.match(r"ipS_c(\d+)_L\d+\.txt$", os.path.basename(a.ip))
        req(mc is not None and a.trace.endswith("_top.bin"), "--lean names the class by the IP file name ipS_c<c>_L<L>.txt "
            "and expects the top trace (a file *_top.bin)")
        f.write("/-! # Kernel replay of a real trace block through E1G for <3,3,4> (generated by\n")
        f.write("a script, not part of the library)\n\n")
        f.write("Class %s, top trace, block %d.\n" % (mc.group(1), a.block))
        f.write("R = %d, N = %d, |G| = %d, rows referenced: %d, block bits: %d, model stats: %s.\n" % (
            ip.R, ip.N, len(ip.G), len(rows), w.n, " ".join("%s=%d" % kv for kv in sorted(job.st.items()))))
        f.write("The leaf checker is `fun _ => false` (the block has no leaves). Negative controls (mutants the Python\n")
        f.write("mirror rejects) must be rejected by the kernel too: %s. -/\n\n" % (
            "; ".join("`%s`: %s" % (n, dsc) for n, dsc, _ in muts) or "none"))
        f.write("set_option autoImplicit false\nset_option maxHeartbeats 0\n\n")
        f.write("namespace %s\nopen B334.E1x.E1G\n\nnoncomputable section\n\n" % a.ns)
        f.write("def lk (L : List (Nat × Nat)) (d i : Nat) : Nat :=\n")
        f.write("  @List.rec (Nat × Nat) (fun _ => Nat) d (fun p _ ih => @Bool.rec (fun _ => Nat) ih p.2 (Nat.beq p.1 i)) L\n\n")
        # the slot table in chunks of 64 slots with a dispatcher of one small definition per tree node, as the 333
        # `#rttablew` loader (RT/Load.lean); only the referenced rows are filled in.  (One big lookup-tree lambda
        # costs an instantiation of the whole tree per lookup: 160 s and 6.5 GB for 2,561 rows, Rep693c.)
        nslot = ip.nrows + ip.N
        nch = (nslot + 63) // 64
        chunks = {}
        for r in rows:
            chunks[r >> 6] = chunks.get(r >> 6, 0) | (slots[r] << (264 * (r & 63)))
        dep = SIB - 6  # every 15-bit slot index has its own chunk path (no aliasing of indices above the table)
        req((nch - 1).bit_length() <= dep, "slot table too large for 15-bit indices")
        f.write("/-- slot-table chunks (64 slots of 264 bits; slot index `64 c + j` at bit `264 j` of chunk `c`) -/\n")
        for c in sorted(chunks):
            f.write("def SLc%d : Nat := 0x%x\n" % (c, chunks[c]))
        f.write("\n")

        def present(lvl, idx):
            lo, hi = idx << lvl, (idx + 1) << lvl
            return any(lo <= c < hi for c in chunks)

        for lvl in range(1, dep + 1):
            for idx in range((nch + (1 << lvl) - 1) >> lvl):
                if not present(lvl, idx):
                    continue

                def child(cix):
                    if lvl == 1:
                        return "SLc%d" % cix if cix in chunks else "0"
                    return "(D%d_%d k)" % (lvl - 1, cix) if present(lvl - 1, cix) else "0"

                f.write("def D%d_%d (k : Nat) : Nat := @Bool.rec (fun _ => Nat) %s %s "
                        "(Nat.beq (Nat.land (Nat.shiftRight k %d) 1) 1)\n" % (lvl, idx, child(2 * idx), child(2 * idx + 1),
                                                                            lvl - 1))
        f.write("\n/-- the chunk dispatcher and the slot function (CheckG's `slc`) -/\n")
        f.write("def ch (k : Nat) : Nat := D%d_0 k\n\n" % dep)
        f.write("def sl (i : Nat) : Nat := slc ch i\n\n")
        f.write("/-- the group: element index, packed label permutation (7-bit fields) -/\n")
        f.write("def gpA : List (Nat × Nat) := [\n")
        f.write(",\n".join("  (%d, 0x%x)" % (g, v) for g, v in enumerate(GPv)))
        f.write("]\n\n")
        f.write("def IDP : Nat := 0x%x\n\n" % IDP)
        f.write("def GPf (g : Nat) : Nat := lk gpA IDP g\n\n")
        f.write("/-- no leaves in this block: the leaf checker rejects everything -/\n")
        f.write("def LFf (_r : Nat) : Bool := false\n\n")
        f.write("def VTv : Nat := 0x%x\n\n" % VT)
        f.write("def DOMv : Nat := 0x%x\n\n" % DOM)
        f.write("def C : Ctx := { R := %d, N := %d, VT := VTv, DOM := DOMv, GP := GPf, LF := LFf }\n\n" % (ip.R, ip.N))
        f.write("def UB : Nat := 0x%x\n" % UB)
        f.write("def UBR : Nat := 0x%x\n\n" % UBR)
        f.write("/-- the block literal (%d bits) -/\n" % w.n)
        f.write("def S : Nat := 0x%x\n\n" % w.v)
        for n, dsc, v in muts:
            f.write("/-- mutant: %s -/\n" % dsc)
            f.write("def S_%s : Nat := 0x%x\n\n" % (n, v))
        f.write("end\n\n")
        f.write("set_option maxRecDepth 100000\n\n")
        f.write("theorem block_ok : block C sl UB UBR S = true := by decide +kernel\n\n")
        for n, dsc, v in muts:
            f.write("theorem block_%s : block C sl UB UBR S_%s = false := by decide +kernel\n\n" % (n, n))
        f.write("end %s\n" % a.ns)
    print("OK block bits=%d rows=%d nodes=%d mutants=%d stats=%s" % (
        w.n, len(rows), len(job.nodes), len(muts), " ".join("%s=%d" % kv for kv in sorted(job.st.items()))))


if __name__ == "__main__":
    try:
        main()
    except Fail as e:
        print("FAIL", e)
        sys.exit(1)
