#!/usr/bin/env python3
"""conv_e1p.py: lineenum9vr --cert traces (format 'LEB9') of the point runs -> E1P block literals for <3,3,4>
(B334/E1x/CheckP.lean), with a bit-exact Python mirror of the Lean checker and the glue checks.

Started from conv_e1g.py v0; changes: E1P widths (8-bit labels, N <= 255, 1233-bit
records, 19-bit slot indices, 520-bit slots, 8-bit fixing counts), F (frontier) and L (leaf) records, splitting of a
trace block into several E1P blocks, and whole runs (all trace files, and the coverage of the search tree).

Usage:
  conv_e1p.py test IPFILE TRACE --tabp TabP.lean --out PFX [--nmax N]
      every block of one trace file as a stand-alone block (J blocks: no F records); mirror-checks every piece and the
      glue of every split record; mutants (rejected by the mirror) for the first block that has each feature; writes
      PFX_lits.bin (#e1lits: all pieces of the first block, then the mutants) and PFX_info.txt.
  conv_e1p.py run IPFILE --traces GLOB --tabp TabP.lean --out DIR [--leaves FILE] [--jobs N] [--nmax N]
      a whole run (see `run_main`).

Model (E1 semantics, port of Job::check / node2 of cpp/enum/e1pemit.h of rank333-f2, Apache-2.0, as in conv_e1g.py): the model's budget vector `u` is
E1's exact budget vector UF: one copy less per added label; a row that becomes full is listed as a saturation event
(and all its labels' budgets are zeroed, as E1 does) iff it zeroes the budget of some label >= the new position;
fixings min(u, floor(gap / (T_l - SC))) with E1's own gap; a child whose budget is 0 is a skip (code 0) and its trace
subtree is dropped; an O node whose dual already kills in E1's budgets becomes a K record.  E1's budgets are <= the
trace's (lechk9vr) bounds, so every K, cut, P and canonicity record of the trace stays valid.

Pieces: the root piece of a trace block is a mode-0 E1P block (start budgets from the label caps, start saturations
listed); a child subtree that does not fit (nodes > --nmax, rows > 4000, records > 255, child length >= 2^24) is cut
out as a mode-1 piece whose header is the exact E1 state at that child, recorded in the parent piece and glued by
E1P.glue.  An F child is a header record glued by E1P.glue0 to the mode-0 root piece of the block covering its prefix.
"""
import argparse
import glob as globmod
import hashlib
import os
import sys
import time
from bisect import bisect_right

SC = 1 << 30
NL, RW, SIB = 255, 1233, 19          # E1P label count, record width, slot-index width (CheckP.lean)
MAGIC = 0x3942454C
RLIM = 4000
T0 = time.time()


class Fail(Exception):
    pass


def req(c, msg):
    if not c:
        raise Fail(msg)


def nsub(a, b):
    return a - b if a > b else 0


def log(msg):
    print("# %8.1fs %s" % (time.time() - T0, msg), file=sys.stderr, flush=True)


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
            self.cap, self.rowl = [], []
            self.G = []
            for line in f:
                t = line.split()
                if not t:
                    continue
                if t[0] == "C":
                    c, m = int(t[2]), int(t[3])
                    ls = [int(x) for x in t[4:4 + m]]
                    req(len(ls) == m and len(t) == 4 + m, "C row length")
                    req(all(0 <= l < self.N for l in ls) and len(set(ls)) == m, "C row labels")
                    if m == 1:
                        self.ub[ls[0]] = min(self.ub[ls[0]], max(0, c))
                        continue
                    req(c >= 0, "negative cap on a multi-label row")
                    self.cap.append(c)
                    self.rowl.append(sorted(ls))
                elif t[0] == "G":
                    for _ in range(int(t[1])):
                        self.G.append([int(x) for x in f.readline().split()])
                    break
                else:
                    raise Fail("IP line kind %r" % t[0])
        req(self.N <= NL, "N above 255")
        for gi, P in enumerate(self.G):
            if all(P[l] == l for l in range(self.N)):
                self.G[0], self.G[gi] = self.G[gi], self.G[0]
                break
        req(self.G and all(self.G[0][l] == l for l in range(self.N)), "no identity in G")
        req(all(sorted(P) == list(range(self.N)) for P in self.G), "G: not permutations")
        req(len(self.G) <= 2048, "group above 2048")
        req(max(self.ub) <= 15, "label bound above 15 (4-bit budgets)")
        self.nrows = len(self.cap)
        req(self.nrows + self.N <= 1 << SIB, "slots above 2^19")
        self.inc = [[] for _ in range(self.N)]
        for r, ls in enumerate(self.rowl):
            for l in ls:
                self.inc[l].append(r)
        self.rowset = [frozenset(ls) for ls in self.rowl]
        self.lab = {v: l for l, v in enumerate(self.vecs)}

    def slot(self, r):
        """the slot of multi-label row r (CheckP: [255] mask, [255] reversed mask, [5] cap)"""
        m = sum(1 << l for l in self.rowl[r])
        mr = sum(1 << (254 - l) for l in self.rowl[r])
        req(self.cap[r] < 32, "cap above 31")
        return m | (mr << 255) | (self.cap[r] << 510)


# ------------------------------------------------------------------------------------------------ the checked tree
class Node:
    __slots__ = ("tag", "d", "pos", "seq", "cut", "kind", "crow", "hd", "dual", "fixes", "items", "nn", "nf", "rows",
                 "restart")

    def __init__(self, tag, d, pos):
        self.tag, self.d, self.pos = tag, d, pos
        self.seq = None
        self.cut, self.kind, self.crow, self.hd = 0, 0, -1, False
        self.dual, self.fixes, self.items = [], [], []
        self.nn, self.nf, self.rows = 1, 0, ()
        self.restart = False


class Item:
    __slots__ = ("code", "l", "g", "sat", "pk", "prow", "child", "ust", "seq", "rs")

    def __init__(self, code, l):
        self.code, self.l = code, l  # 0 skip, 3 non-canonical, 1 lookahead-killed child, 2 child subtree
        self.g, self.sat, self.pk, self.prow, self.child, self.ust, self.seq = 0, (), 0, -1, None, None, None
        self.rs = None    # restart child: the start saturations of its mode-0 piece


BMAX = 400000      # piece size limit in bits (kernel memory is ~5-7 KB per literal bit, superlinear in piece size)
SATW = 6           # width of a child's saturation count: 6 in CheckP.lean; 8 in the planned E1Q copy (--satw 8)
SATR = 63          # a child with more saturation events is restarted as a mode-0 piece (if no fixing is lost)
PENDMAX = 63       # at most this many events are listed at a child; the rest are pending rows (node2 `pend`)
NODE_RLIM = 3000   # ... and so is a child whose events would push its node's own rows above this


class Job:
    """one trace block through the E1 model"""

    def __init__(self, ip, gorder):
        self.ip = ip
        self.st = {}
        self.gorder = gorder

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
            req(s < 64, "varint")

    def dual(self):
        n = self.var()
        req(n <= self.ip.nrows, "dual length")
        d = []
        for _ in range(n):
            r = self.var()
            y = self.var()
            req(r < self.ip.nrows, "dual row")
            req(y <= 1 << 50, "Y above 2^50")
            d.append((r, y))
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
        u = self.u
        for l in range(lo, ip.N):
            if u[l] > 0 and T[l] < SC:
                B += u[l] * (SC - T[l])
        return B, T

    def weight(self, lo, notin=-1):
        u = self.u
        if notin < 0:
            return sum(u[lo:])
        rs = self.ip.rowset[notin]
        return sum(u[l] for l in range(lo, self.ip.N) if l not in rs)

    def start(self, pre):
        ip = self.ip
        self.cnt = [0] * ip.nrows
        self.mult = [0] * ip.N
        self.u = list(ip.ub)
        self.seq = []
        for l in pre:
            self.mult[l] += 1
            self.seq.append(l)
            req(self.u[l] >= 1, "prefix label over its cap")
            self.u[l] -= 1
            for r in ip.inc[l]:
                self.cnt[r] += 1
        full = []
        for r in range(ip.nrows):
            req(self.cnt[r] <= ip.cap[r], "prefix exceeds a row cap")
            if self.cnt[r] == ip.cap[r]:
                full.append(r)
        self.full = set(full)
        return self.cover(full, self.pre[-1] if self.pre else 0)

    def restart_state(self, l):
        """E1's mode-0 start state for the current prefix (ending in l): budgets from the label caps, then a cover of
        the full rows at labels >= l; returns (budgets, start saturations)"""
        ip = self.ip
        keep = self.u
        self.u = [ip.ub[x] - self.mult[x] for x in range(ip.N)]
        req(min(self.u) >= 0, "restart: prefix over a label cap")
        sat = self.cover(sorted(self.full), l)
        ur = self.u
        self.u = keep
        return ur, sat

    def cover(self, full, lo):
        """the saturation events among the full rows `full`: a greedy cover of the labels >= lo with budget > 0 in
        their union (the lechk9vr rule zeroes all of them; E1 zeroes the union of the listed rows, so the budgets at
        labels >= lo agree); zeroes the listed rows' labels in u (E1's semantics) and returns the listed rows"""
        ip = self.ip
        u = self.u
        Z = set()
        for r in full:
            for x in ip.rowl[r]:
                if x >= lo and u[x] > 0:
                    Z.add(x)
        sat = []
        if Z:
            cand = [r for r in full if not ip.rowset[r].isdisjoint(Z)]
            while Z:
                best, bc = -1, 0
                for r in cand:
                    c = len(Z & ip.rowset[r])
                    if c > bc:
                        best, bc = r, c
                req(best >= 0, "cover")
                sat.append(best)
                Z -= ip.rowset[best]
            for r in sat:
                for x in ip.rowl[r]:
                    u[x] = 0
        return sat

    def add(self, l):
        """add label l (E1: UF - one l, then the listed rows zero their labels); returns (sat rows, saved u)"""
        ip = self.ip
        saved = list(self.u)
        u = self.u
        self.mult[l] += 1
        self.seq.append(l)
        u[l] -= 1
        req(u[l] >= 0, "label over its cap")
        cnt, cap = self.cnt, ip.cap
        full = []
        for r in ip.inc[l]:
            cnt[r] += 1
            if cnt[r] == cap[r]:
                full.append(r)
        self.full.update(full)
        return self.cover(full, l), saved

    def undo(self, l, saved):
        self.mult[l] -= 1
        self.seq.pop()
        self.u = saved
        cnt, cap, full = self.cnt, self.ip.cap, self.full
        for r in self.ip.inc[l]:
            if cnt[r] == cap[r]:
                full.discard(r)
            cnt[r] -= 1

    def noncanon(self, l):
        s = self.seq + [l]
        G = self.ip.G
        order = self.gorder
        for idx in range(len(order)):
            gi = order[idx]
            P = G[gi]
            if sorted([P[x] for x in s]) < s:
                if idx:
                    order.insert(0, order.pop(idx))
                return gi
        return -1

    def skip(self, nd, s):
        it = Item(0, s)
        if self.u[s] == 0:
            self.stat("skip0")
        else:
            g = self.noncanon(s)
            req(g > 0, "skip not justified (label %d at depth %d)" % (s, len(self.seq)))
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

    def node2(self, pos, pend=()):
        """`pend`: full rows the parent's item could not list (more than 63 events); their labels >= pos still
        have budget in E1 and this node zeroes them: a kill adds them to its dual with Y = SC (full rows add nothing
        to the bound, and their labels lose their deficit terms); an open node adds them with Y = SC + gap + 1, so
        that its fixings set those labels to 0 (a node without a dual gets the dual of these rows)"""
        ip = self.ip
        d = len(self.seq)
        rem = ip.R - d
        tag = chr(self.u8())
        nd = Node(tag, d, pos)
        if tag == "L":
            req(rem == 0, "leaf with rem > 0")
            nd.seq = tuple(self.seq)
            self.leaves.append(nd.seq)
            self.stat("L")
            return nd
        if tag == "F":
            req(self.btag == "T" and d == self.fd, "F record outside a T block's frontier depth")
            nd.seq = tuple(self.seq)
            nd.nn, nd.nf = 0, 1
            self.stat("F")
            return nd
        req(rem > 0, "node at depth R")
        self.stat("nodes")
        if tag == "K":
            du = self.dual() + [(r, SC) for r in pend]
            req(len(du) < 256, "kill dual above 255 rows")
            B, _ = self.bound(du, pos)
            req(B < rem * SC, "K fails")
            nd.dual = du
            nd.rows = tuple(r for r, _ in du)
            self.stat("K")
            return nd
        req(tag == "O", "unknown node tag %r" % tag)
        cut = self.u8()
        kind = self.u8()
        row = -1
        if kind == 1:
            row = self.var()
            req(row < ip.nrows, "cut row")
        hd = self.u8()
        du = self.dual() if hd else []
        if pend:
            dp = du + [(r, SC) for r in pend]
            Bp, _ = self.bound(dp, pos)
            gp = Bp - rem * SC
            if gp < 0:
                nd.tag = "K"
                nd.dual = dp
                nd.rows = tuple(r for r, _ in dp)
                req(len(dp) < 256, "kill dual above 255 rows")
                self.skipkids()
                self.stat("pendK")
                return nd
            Y = SC + gp + 1
            req(Y < 1 << 36, "pending rows need Y = %d (gap %d) above 2^36" % (Y, gp))
            du = du + [(r, Y) for r in pend]
            req(len(du) < 256, "dual above 255 rows")
            hd = 1
            self.stat("pendO")
        saved_u = list(self.u)
        fixes = []
        if hd:
            B, T = self.bound(du, pos)
            gap = B - rem * SC
            if gap < 0:
                nd.tag = "K"
                nd.dual = du
                nd.rows = tuple(r for r, _ in du)
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
        rows = [r for r, _ in du]
        if kind == 1:
            rows.append(row)
        rset = set(rows)
        nn, nf = 1, 0
        nxt = pos
        top = min(cut, ip.N)
        while True:
            c = chr(self.u8())
            if c == "E":
                break
            req(c == "C", "expected C")
            l = self.u8()
            req(pos <= l < top, "child label range")
            req(l >= nxt, "children out of order")
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
            sat, saved = self.add(l)
            self.stat("child")
            it = Item(2, l)
            isP = self.bi < len(self.b) and self.b[self.bi] == ord("P")
            k, prow = 0, -1
            if isP:
                self.bi += 1
                k = self.u8()
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
            if len(sat) > SATR or len(rset.union(sat)) > NODE_RLIM:
                ur, rs = self.restart_state(l)
                lost = any(ur[x] != self.u[x] for x in range(l, ip.N))
                # restart: the parent lists no events, its record holds the parent's budgets minus one copy of l;
                # the child is the root of a mode-0 piece (glue0) whose start events are `rs`.  A lookahead (P)
                # child becomes a kill with the dual of its lookahead: none for kind 2, (row, SC) for kind 1.
                # If the restart budgets exceed the model's at some label >= l (an ancestor's fixing is lost), the
                # child is converted under the larger budgets and the restart is kept only if every record still
                # checks; otherwise the trace position is restored and the events are listed in the parent.
                if not lost:
                    req(len(rs) < 256, "more than 255 start events in a restart")
                    bi0, nleaves0, st0 = self.bi, len(self.leaves), dict(self.st)
                    keep_u = self.u
                    if lost:
                        cnt0, mult0, seq0, full0 = list(self.cnt), list(self.mult), list(self.seq), set(self.full)
                    self.u = ur
                    try:
                        if isP:
                            ch = Node("K", d + 1, l)
                            ch.dual = [] if k == 2 else [(prow, SC)]
                            ch.rows = tuple(r for r, _ in ch.dual)
                            B, _ = self.bound(ch.dual, l)
                            req(B < (rem - 1) * SC, "lookahead kill fails in the restart state")
                        else:
                            ch = self.node2(l)
                        ok = True
                    except Fail as e:
                        if not lost:
                            raise
                        ok = False
                        err = str(e)
                    if ok:
                        ust = list(saved)
                        ust[l] -= 1
                        it.ust, it.seq, it.rs, it.sat = bytes(ust), tuple(self.seq), tuple(rs), ()
                        nd.items.append(it)
                        ch.restart = True
                        it.child = ch
                        nf += 1
                        if isP:
                            self.stat("PtoK")
                        self.stat("restart")
                        self.stat("restartsat", len(rs))
                        if lost:
                            self.stat("restartlostok")
                        self.undo(l, saved)
                        continue
                    self.bi, self.st = bi0, st0
                    del self.leaves[nleaves0:]
                    self.u = keep_u
                    self.cnt, self.mult, self.seq, self.full = cnt0, mult0, seq0, full0
                    req(len(sat) < (1 << SATW), "restart with a lost fixing fails (%s) and the child needs %d "
                        "saturation rows (label %d, depth %d)" % (err, len(sat), l, d + 1))
                self.stat("restartlost")
            pend = ()
            if len(sat) > PENDMAX:
                # list the first PENDMAX (63) rows of the cover (largest coverage first); the child node zeroes the
                # rest (node2's `pend`). E1's budgets: the parent's minus one copy of l, the listed rows zeroed.
                pend = tuple(sat[PENDMAX:])
                sat = sat[:PENDMAX]
                ue = list(saved)
                ue[l] -= 1
                for r in sat:
                    for x in ip.rowl[r]:
                        ue[x] = 0
                self.u = ue
                self.stat("pend")
                self.stat("pendrows", len(pend))
            self.stat("satev", len(sat))
            it.sat = tuple(sat)
            rows.extend(sat)
            rset.update(sat)
            if isP and pend:
                # a lookahead child with pending rows: a kill with the lookahead's dual and the pending rows (Y = SC)
                ch = Node("K", d + 1, l)
                ch.dual = ([] if k == 2 else [(prow, SC)]) + [(r, SC) for r in pend]
                ch.rows = tuple(r for r, _ in ch.dual)
                req(len(ch.dual) < 256, "kill dual above 255 rows")
                B, _ = self.bound(ch.dual, l)
                req(B < (rem - 1) * SC, "lookahead kill with pending rows fails")
                it.ust, it.seq = bytes(self.u), tuple(self.seq)
                nd.items.append(it)
                it.child = ch
                nn += 1
                self.stat("PtoKp")
            elif isP:
                if k == 1:
                    rows.append(prow)
                    rset.add(prow)
                self.stat("P%d" % k)
                it.code, it.pk, it.prow = 1, k, prow
                nd.items.append(it)
            else:
                it.ust = bytes(self.u)
                it.seq = tuple(self.seq)
                nd.items.append(it)
                ch = self.node2(l, pend)
                it.child = ch
                nn += ch.nn
                nf += ch.nf
            self.undo(l, saved)
        for s in range(nxt, top):
            self.skip(nd, s)
        self.u = saved_u
        nd.nn, nd.nf, nd.rows = nn, nf, tuple(rows)
        return nd

    def check(self, payload):
        self.b, self.bi = payload, 0
        self.leaves = []
        t = chr(self.u8())
        req(t in "TJ", "block tag")
        self.btag = t
        n = self.u8()
        req(n <= self.ip.R, "prefix length")
        self.pre = []
        for _ in range(n):
            v = self.u8() | (self.u8() << 8)
            req(v in self.ip.lab, "prefix vector")
            self.pre.append(self.ip.lab[v])
        req(self.pre == sorted(self.pre), "prefix not sorted")
        self.fd = 255
        if t == "T":
            self.fd = self.u8()
            req(self.fd == 255 or self.fd > n, "frontier depth")
        self.sat0 = self.start(self.pre)
        req(len(self.sat0) < 256, "more than 255 start saturations")
        self.stat("startsat", len(self.sat0))
        self.root = self.node2(self.pre[-1] if self.pre else 0)
        req(chr(self.u8()) == "Z", "expected Z")
        self.blocknodes = self.var()
        req(self.bi == len(self.b), "trailing bytes")


# ------------------------------------------------------------------------------------------------ emission (E1P)
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


def rec_value(d, pos, seq, ust):
    """the header record of state (d, pos, prefix seq, budgets ust): [5] d, [8] pos, d x [8], 255 x [4]"""
    req(len(seq) == d and d <= 25, "record depth")
    v = d | (pos << 5)
    for i, l in enumerate(seq):
        v |= l << (13 + 8 * i)
    o = 13 + 8 * d
    for l in range(NL):
        x = ust[l] if l < len(ust) else 0
        req(x < 16, "budget above 15")
        v |= x << (o + 4 * l)
    req(v < 1 << RW, "record width")
    return v


class Piece:
    """one E1P block: a root node (mode 0: the trace block's root; mode 1: a delegated child) and its region"""

    def __init__(self, root, mode, d, pos, seq, ust, sat0):
        self.root, self.mode, self.d, self.pos, self.seq, self.ust, self.sat0 = root, mode, d, pos, seq, ust, sat0
        self.T, self.FT = 0, 0
        self.lit, self.bits = 0, 0
        self.recs = []          # (kind 'S' (split child: Item) or 'F' (frontier: prefix), record value)
        self.rows = []
        self.nodes = 0

    def inline(self, c):
        return c.tag != "F" and not c.restart and c.nn <= self.T and c.nf <= self.FT


def region(p):
    nodes, recs, rows = 0, 0, set(p.sat0)
    stack = [p.root]
    while stack:
        n = stack.pop()
        if n.tag == "L":
            nodes += 1
            continue
        nodes += 1
        rows.update(n.rows)
        for it in n.items:
            if it.code == 2:
                c = it.child
                if p.inline(c):
                    stack.append(c)
                else:
                    recs += 1
    return nodes, recs, rows


def emit_node(nd, p, idx, N):
    w = BW()
    if nd.tag == "L":
        w.put(0, 2)
        return w
    if nd.tag == "K":
        w.put(1, 2)
        w.put(len(nd.dual), 8)
        for r, y in nd.dual:
            w.put(idx[r], 12)
            w.put(y, 36)
        return w
    req(nd.tag == "O", "emit: node tag")
    w.put(2, 2)
    w.put(min(nd.cut, N), 8)
    w.put(nd.kind, 2)
    if nd.kind == 1:
        w.put(idx[nd.crow], 12)
    w.put(1 if nd.hd else 0, 1)
    if nd.hd:
        w.put(len(nd.dual), 8)
        for r, y in nd.dual:
            w.put(idx[r], 12)
            w.put(y, 36)
        w.put(len(nd.fixes), 8)
        for l, nu in nd.fixes:
            w.put(l, 8)
            w.put(nu, 4)
    for it in nd.items:
        if it.code == 0:
            w.put(0, 2)
        elif it.code == 3:
            w.put(3, 2)
            w.put(it.g, 11)
        else:
            w.put(it.code, 2)
            w.put(len(it.sat), SATW)
            for r in it.sat:
                w.put(idx[r], 12)
            if it.code == 1:
                w.put(1 if it.pk == 1 else 0, 1)
                if it.pk == 1:
                    w.put(idx[it.prow], 12)
            else:
                c = it.child
                if p.inline(c):
                    cw = emit_node(c, p, idx, N)
                    req(cw.n > 0, "empty child")
                    w.put(cw.n, 24)
                    w.cat(cw)
                else:
                    w.put(0, 24)
                    w.put(len(p.recs), 8)
                    if c.tag == "F":
                        p.recs.append(("F", c.seq, rec_value(nd.d + 1, it.l, it.seq, it.ust)))
                    elif c.restart:
                        p.recs.append(("R", it, rec_value(nd.d + 1, it.l, it.seq, it.ust)))
                    else:
                        p.recs.append(("S", it, rec_value(nd.d + 1, it.l, it.seq, it.ust)))
    return w


def collect_rows(p):
    """the piece's rows in first-reference order (start saturations first)"""
    rows, idx = [], {}

    def ref(r):
        if r not in idx:
            idx[r] = len(rows)
            rows.append(r)

    for r in p.sat0:
        ref(r)
    stack = [p.root]
    while stack:
        n = stack.pop()
        for r in n.rows:
            ref(r)
        for it in reversed(n.items):
            if it.code == 2 and p.inline(it.child):
                stack.append(it.child)
    return rows, idx


def emit_piece(p, N):
    rows, idx = collect_rows(p)
    req(len(rows) < 4096, "more than 4095 rows in a piece")
    p.recs = []
    nb = emit_node(p.root, p, idx, N)
    req(len(p.recs) < 256, "more than 255 records in a piece")
    w = BW()
    w.put(p.mode, 1)
    w.put(p.d, 5)
    w.put(p.pos, 8)
    for l in p.seq:
        w.put(l, 8)
    if p.mode == 1:
        for l in range(NL):
            w.put(p.ust[l] if l < len(p.ust) else 0, 4)
    w.put(len(p.recs), 8)
    for _, _, rv in p.recs:
        w.put(rv, RW)
    w.put(len(rows), 12)
    for r in rows:
        w.put(r, SIB)
    if p.mode == 0:
        w.put(len(p.sat0), 8)
        for r in p.sat0:
            w.put(idx[r], 12)
    w.cat(nb)
    p.lit, p.bits, p.rows = w.v, w.n, rows


def split_block(job, ip, nmax):
    """the E1P pieces of one converted trace block, parents first"""
    pieces = []
    root = job.root
    p0 = Piece(root, 0, len(job.pre), job.pre[-1] if job.pre else 0, tuple(job.pre), None, list(job.sat0))
    todo = [p0]
    while todo:
        p = todo.pop(0)
        T, FT = nmax, 200
        while True:
            p.T, p.FT = T, FT
            nodes, recs, rows = region(p)
            ok = nodes <= nmax and recs <= 255 and len(rows) <= RLIM
            if ok:
                try:
                    emit_piece(p, ip.N)
                    ok = p.bits <= BMAX or (T == 0 and FT == 0)
                except Fail as e:
                    if "overflow" not in str(e) and "more than" not in str(e):
                        raise
                    ok = False
            if ok:
                break
            req(T > 0 or FT > 0, "cannot split a piece (root alone does not fit)")
            T, FT = T // 2, FT // 2
        p.nodes = nodes
        pieces.append(p)
        for kind, obj, rv in p.recs:
            if kind == "S":
                it = obj
                c = it.child
                todo.append(Piece(c, 1, c.d, it.l, it.seq, it.ust, []))
            elif kind == "R":
                it = obj
                c = it.child
                todo.append(Piece(c, 0, c.d, it.l, it.seq, None, list(it.rs)))
    # the split and restart records point to the pieces in creation order
    k = 1
    for p in pieces:
        tg = []
        for kind, obj, rv in p.recs:
            if kind in "SR":
                tg.append(k)
                k += 1
            else:
                tg.append(None)
        p.tg = tg
    req(k == len(pieces), "split bookkeeping")
    return pieces


# ------------------------------------------------------------------------------------------------ the mirror of CheckP.lean
class Mirror:
    FM = (1 << 256) - 1
    M64 = (1 << 64) - 1
    M255 = (1 << 255) - 1
    MSL = (1 << 520) - 1
    REP = sum(1 << (256 * l) for l in range(256))
    SPM = sum(1 << (255 * j) for j in range(256))
    FMALL = (1 << (256 * 256)) - 1
    DSCREP = ((1 << 30) + (1 << 64)) * REP

    def __init__(self, R, N, GP, LF, sl):
        self.R, self.N, self.GP, self.LF, self.sl = R, N, GP, LF, sl

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
        return ((vr * x) >> 65024) & self.FM

    def fld(self, v, l):
        return (v >> (256 * l)) & self.FM

    def hif(self, lo):
        return (self.FMALL >> (256 * lo)) << (256 * lo)

    @staticmethod
    def one(l):
        return 1 << (256 * l)

    @staticmethod
    def oner(l):
        return 1 << (256 * nsub(254, l))

    def deficit(self, T, UFR, lo):
        D = nsub(self.DSCREP, T)
        return self.dot(UFR, (D & (((D >> 64) & self.REP) * self.M64)) & self.hif(lo))

    def slotAt(self, RTb, j):
        return (RTb >> (520 * j)) & self.MSL

    def rmask(self, RTb, j):
        return self.slotAt(RTb, j) & self.M255

    def rmaskr(self, RTb, j):
        return (self.slotAt(RTb, j) >> 255) & self.M255

    def rcap(self, RTb, j):
        return (self.slotAt(RTb, j) >> 510) & 31

    def wout(self, UF, m, lo):
        return self.fsum(UF & (self.FMALL ^ self.fmask(m)) & self.hif(lo))

    def mkRTd(self, h, n, IX):
        if h == 0 or n <= 1:
            return self.sl(self.rd(19, IX)) if n == 1 else 0
        a = n >> 1
        return self.mkRTd(h - 1, a, self.rd(19 * a, IX)) | (self.mkRTd(h - 1, n - a, IX >> (19 * a)) << (520 * a))

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
            l = self.rd(8, S)
            nu = self.rd(4, S >> 8)
            u = self.fld(UF, l)
            t = self.fld(T, l)
            ok = ok and SC + 1 <= t and nu + 1 <= u and gap + 1 <= (nu + 1) * nsub(t, SC)
            UF = nsub(UF, nsub(u, nu) * self.one(l))
            UFR = nsub(UFR, nsub(u, nu) * self.oner(l))
            S >>= 12
        return ok, UF, UFR, S

    def imgR(self, gp, pl, m):
        acc = 0
        for _ in range(m):
            acc += self.oner((gp >> (8 * self.rd(8, pl))) & 255)
            pl >>= 8
        return acc

    def budU(self, B, rev=False):
        U = 0
        for l in range(255):
            U += self.rd(4, B >> (4 * l)) * (self.oner(l) if rev else self.one(l))
        return U

    def stEq(self, r, d, pos, pl, UF):
        return (self.rd(5, r) == d and self.rd(8, r >> 5) == pos and self.rd(8 * d, r >> 13) == pl
                and self.budU(r >> (13 + 8 * d)) == UF)

    def kids(self, fuel, RTb, H, cnt, d, pl, MV, MVR, UF, UFR, l, S):
        R = self.R
        for _ in range(cnt):
            code = self.rd(2, S)
            if code == 0:
                if self.fld(UF, l) != 0:
                    return False
                S >>= 2
            elif code == 3:
                g = self.rd(11, S >> 2)
                if not (MVR + self.oner(l) < self.imgR(self.GP(g), pl | (l << (8 * d)), d + 1)):
                    return False
                S >>= 13
            else:
                if not (1 <= self.fld(UF, l)):
                    return False
                n = self.rd(SATW, S >> 2)
                ok, UF2, UFR2, S2 = self.sats(RTb, n, MV + self.one(l), nsub(UF, self.one(l)), nsub(UFR, self.oner(l)),
                                              S >> (2 + SATW))
                if not ok:
                    return False
                if code == 1:
                    if self.rd(1, S2) == 0:
                        if not (self.wout(UF2, 0, l) < nsub(R, d + 1)):
                            return False
                        S = S2 >> 1
                    else:
                        j = self.rd(12, S2 >> 1)
                        need = nsub(nsub(R, d + 1) + self.fsum((MV + self.one(l)) & self.fmask(self.rmask(RTb, j))),
                                    self.rcap(RTb, j))
                        if not (1 <= need and self.wout(UF2, self.rmask(RTb, j), l) < need):
                            return False
                        S = S2 >> 13
                else:
                    ln = self.rd(24, S2)
                    if ln == 0:
                        ix = self.rd(8, S2 >> 24)
                        if not self.stEq(self.rd(RW, H >> (RW * ix)), d + 1, l, pl | (l << (8 * d)), UF2):
                            return False
                        S = S2 >> 32
                    else:
                        if not self.node(fuel, RTb, H, d + 1, l, pl | (l << (8 * d)), MV + self.one(l),
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
            return nsub(R, d) == 0 and self.LF(pl)
        if not (1 <= nsub(R, d)):
            return False
        rem = nsub(R, d)
        if tag == 1:
            BC, T, _ = self.rdual(RTb, self.rd(8, S1), S1 >> 8)
            return BC + self.deficit(T, UFR, pos) < rem * SC + self.dot(MVR, T)
        cut = self.rd(8, S1)
        kind = self.rd(2, S1 >> 8)
        cj = self.rd(12, S1 >> 10)
        S3 = (S1 >> 10 >> 12) if kind == 1 else (S1 >> 10)
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
            ok, UF2, UFR2, S6 = self.fixes(self.rd(8, S5), T, gap, UF, UFR, S5 >> 8)
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
            MV += self.one(self.rd(8, pl))
            MVR += self.oner(self.rd(8, pl))
            pl >>= 8
        return MV, MVR

    def block(self, UB, UBR, S):
        mode = self.rd(1, S)
        d = self.rd(5, S >> 1)
        pos = self.rd(8, S >> 6)
        pl = self.rd(8 * d, S >> 14)
        S1 = S >> (14 + 8 * d)
        S2 = (S1 >> 1020) if mode == 1 else S1
        nd = self.rd(8, S2)
        H = self.rd(RW * nd, S2 >> 8)
        rest = S2 >> (8 + RW * nd)
        k = self.rd(12, rest)
        RTb = self.mkRTd(13, k, self.rd(19 * k, rest >> 12))
        S3 = rest >> 12 >> (19 * k)
        MV, MVR = self.mvOf(d, pl)
        if mode == 1:
            UF, UFR, ok, S4 = self.budU(S1), self.budU(S1, True), True, S3
        else:
            ok, UF, UFR, S4 = self.sats(RTb, self.rd(8, S3), MV, nsub(UB, MV), nsub(UBR, MVR), S3 >> 8)
        return ok and d <= self.R and self.node(32, RTb, H, d, pos, pl, MV, MVR, UF, UFR, S4)

    # glue (CheckP.glue, glue0)
    def glue(self, r, Sc):
        return self.rd(1, Sc) == 1 and self.rd(1033 + 8 * self.rd(5, r), Sc >> 1) == r

    def glue0(self, r, Sc):
        w = 13 + 8 * self.rd(5, r)
        return self.rd(1, Sc) == 0 and self.rd(w, Sc >> 1) == self.rd(w, r)

    def recOf(self, S, j):
        """record j of block S (P/Asm.lean recOf)"""
        mode = self.rd(1, S)
        d = self.rd(5, S >> 1)
        S1 = S >> (14 + 8 * d)
        S2 = (S1 >> 1020) if mode == 1 else S1
        nd = self.rd(8, S2)
        H = self.rd(RW * nd, S2 >> 8)
        return (H >> (RW * j)) & ((1 << RW) - 1), nd


def tabp_check(tabp):
    """the ECTP constants of B334/E1x/TabP.lean equal the mirror's formulas"""
    vals = {}
    for line in open(tabp):
        t = line.split()
        if len(t) >= 6 and t[0] == "def" and t[2] == ":" and t[3] == "Nat":
            vals[t[1]] = int(t[5], 16)
    req(vals.get("REP") == Mirror.REP, "TabP REP differs from the formula")
    req(vals.get("SPM") == Mirror.SPM, "TabP SPM differs from the formula")
    req(vals.get("FMALL") == Mirror.FMALL, "TabP FMALL differs from the formula")
    req(vals.get("DSCREP") == Mirror.DSCREP, "TabP DSCREP differs from the formula")


# ------------------------------------------------------------------------------------------------ run context
class Ctx:
    def __init__(self, ip, leaves=()):
        self.ip = ip
        self.UB = sum(ip.ub[l] << (256 * l) for l in range(ip.N))
        self.UBR = sum(ip.ub[l] << (256 * (254 - l)) for l in range(ip.N))
        self.GPv = [sum(P[l] << (8 * l) for l in range(ip.N)) for P in ip.G]
        self.leafset = set(leaves)
        self.slots = {}
        self.mir = Mirror(ip.R, ip.N, self.GP, self.LF, self.sl)

    def GP(self, g):
        return self.GPv[g] if g < len(self.GPv) else self.GPv[0]

    def LF(self, pl):
        return pl in self.leafset

    def sl(self, i):
        ip = self.ip
        if i < ip.nrows:
            v = self.slots.get(i)
            if v is None:
                v = ip.slot(i)
                self.slots[i] = v
            return v
        return 0


def pack_pl(seq):
    v = 0
    for i, l in enumerate(seq):
        v |= l << (8 * i)
    return v


def read_blocks(path):
    """(offset, payload) of every complete block of a trace file; a truncated last block is reported and skipped"""
    data = open(path, "rb").read()
    out, q = [], 0
    trunc = 0
    while q + 12 <= len(data):
        mg = int.from_bytes(data[q:q + 4], "little")
        ln = int.from_bytes(data[q + 4:q + 12], "little")
        req(mg == MAGIC, "magic in %s at %d" % (path, q))
        if q + 12 + ln > len(data):
            trunc = 1
            break
        out.append((q, data[q + 12:q + 12 + ln]))
        q += 12 + ln
    req(trunc or q == len(data), "trailing bytes in %s" % path)
    return out, trunc


def convert(ip, gorder, payload, nmax):
    job = Job(ip, gorder)
    job.check(payload)
    pieces = split_block(job, ip, nmax)
    return job, pieces


# ------------------------------------------------------------------------------------------------ test mode
def write_e1lits(path, lits):
    with open(path, "xb") as f:
        f.write(len(lits).to_bytes(4, "little"))
        for v in lits:
            nb = (v.bit_length() + 7) // 8
            f.write(nb.to_bytes(4, "little"))
            f.write(v.to_bytes(nb, "little"))


def mutants(cx, pieces):
    """mutants of the first piece that has each feature; each must be rejected by the mirror"""
    out = []
    ip = cx.ip
    for p in pieces:
        nodes = []
        st = [p.root]
        while st:
            n = st.pop()
            nodes.append(n)
            for it in n.items:
                if it.code == 2 and p.inline(it.child):
                    st.append(it.child)
        nc = [it for n in nodes if n.tag == "O" for it in n.items if it.code == 3]
        if nc and not any(m[0] == "neg_g0" for m in out):
            it = nc[0]
            g_old = it.g
            it.g = 0
            emit_piece(p, ip.N)
            v = p.lit
            it.g = g_old
            emit_piece(p, ip.N)
            out.append(("neg_g0", "the first non-canonical skip with the identity as witness", v, p))
        ks = [n for n in nodes if n.tag == "K"]
        if ks and not any(m[0] == "neg_yhalf" for m in out):
            n = ks[0]
            d_old = n.dual
            n.dual = [(r, y // 2) for r, y in d_old]
            emit_piece(p, ip.N)
            v = p.lit
            n.dual = d_old
            emit_piece(p, ip.N)
            out.append(("neg_yhalf", "the first kill with every Y halved", v, p))
        o1 = [n for n in nodes if n.tag == "O" and n.kind == 1]
        if o1 and not any(m[0] == "neg_cut2" for m in out):
            n = o1[0]
            n.kind = 2
            emit_piece(p, ip.N)
            v = p.lit
            n.kind = 1
            emit_piece(p, ip.N)
            out.append(("neg_cut2", "the first row cut claimed by total weight", v, p))
        if p.recs and not any(m[0] == "neg_rec" for m in out):
            # the first header record with budget field 254 raised by one
            j = 0
            hdr_bits = 14 + 8 * p.d + (1020 if p.mode == 1 else 0) + 8
            rd = p.recs[j][2]
            dd = rd & 31
            off = hdr_bits + RW * j + 13 + 8 * dd + 4 * 254
            v = p.lit + (1 << off)
            out.append(("neg_rec", "the first header record with label 254's budget raised by one", v, p))
    return out


def test_main(a):
    ip = IP(a.ip)
    tabp_check(a.tabp)
    cx = Ctx(ip)
    gorder = list(range(1, len(ip.G)))
    blocks, trunc = read_blocks(a.trace)
    log("IP R=%d N=%d rows=%d |G|=%d; trace %s: %d blocks (truncated tail %d)" % (
        ip.R, ip.N, ip.nrows, len(ip.G), os.path.basename(a.trace), len(blocks), trunc))
    allst = {}
    npieces = 0
    conv = []
    for bi, (off, payload) in enumerate(blocks):
        t1 = time.time()
        job, pieces = convert(ip, gorder, payload, a.nmax)
        t2 = time.time()
        req(job.btag == "J", "test mode takes J blocks only")
        for k, v in job.st.items():
            allst[k] = allst.get(k, 0) + v
        for p in pieces:
            req(cx.mir.block(cx.UB, cx.UBR, p.lit), "mirror rejects block %d piece" % bi)
            for j, (kind, obj, rv) in enumerate(p.recs):
                req(kind in "SR", "F record in a J block")
                tgt = pieces[p.tg[j]]
                rj, nd = cx.mir.recOf(p.lit, j)
                req(rj == rv and nd == len(p.recs), "record readback")
                if kind == "S":
                    req(cx.mir.glue(rv, tgt.lit), "glue fails: block %d" % bi)
                else:
                    req(cx.mir.glue0(rv, tgt.lit), "glue0 fails: block %d" % bi)
        t3 = time.time()
        npieces += len(pieces)
        print("block %d off %d prefix %d nodes %d pieces %d bits %s rows %s recs %s conv %.2fs mirror %.2fs" % (
            bi, off, len(job.pre), job.blocknodes, len(pieces), ",".join(str(p.bits) for p in pieces),
            ",".join(str(len(p.rows)) for p in pieces), ",".join(str(len(p.recs)) for p in pieces), t2 - t1, t3 - t2))
        conv.append((bi, job, pieces))
    req(conv, "no blocks")
    log("all %d pieces of %d blocks accepted by the mirror; split glue checked" % (npieces, len(blocks)))
    # mutants of the converted pieces, first occurrence of each feature
    muts = []
    for bi, job, pieces in conv:
        for m in mutants(cx, pieces):
            if not any(x[0] == m[0] for x in muts):
                muts.append((m[0], m[1], m[2], bi, pieces.index(m[3])))
    req(0 <= a.block < len(conv), "--block out of range")
    first = conv[a.block]
    for name, dsc, v, bi, pi in muts:
        req(not cx.mir.block(cx.UB, cx.UBR, v), "mirror ACCEPTS mutant %s" % name)
        print("mutant %s (block %d piece %d): rejected by the mirror (%s)" % (name, bi, pi, dsc))
    bi, job, pieces = first
    lits = [p.lit for p in pieces] + [v for _, _, v, b, _ in muts if b == bi]
    write_e1lits(a.out + "_lits.bin", lits)
    with open(a.out + "_info.txt", "x") as f:
        f.write("trace %s block %d: %d pieces then mutants %s\n" % (
            a.trace, bi, len(pieces), " ".join("%s@%d.%d" % (n, b, q) for n, _, _, b, q in muts if b == bi)))
        for k, p in enumerate(pieces):
            f.write("piece %d mode %d d %d bits %d rows %d recs %d sha %s\n" % (
                k, p.mode, p.d, p.bits, len(p.rows), len(p.recs),
                hashlib.sha256(p.lit.to_bytes((p.bits + 7) // 8, "little")).hexdigest()[:16]))
    print("OK test: %d blocks, %d pieces, mutants %s; stats %s" % (
        len(blocks), npieces, ",".join(m[0] for m in muts), " ".join("%s=%d" % kv for kv in sorted(allst.items()))))
    print("lits %s_lits.bin: %d literals (first block %d's pieces, then its mutants)" % (a.out, len(lits), bi))


# ------------------------------------------------------------------------------------------------ run mode
G = {}   # globals of the pool workers (set before the fork)


def payload_at(path, off):
    with open(path, "rb") as f:
        f.seek(off)
        h = f.read(12)
        req(len(h) == 12 and int.from_bytes(h[:4], "little") == MAGIC, "magic at %s:%d" % (path, off))
        ln = int.from_bytes(h[4:12], "little")
        b = f.read(ln)
        req(len(b) == ln, "short read at %s:%d" % (path, off))
        return b


def head_of(ip, payload):
    t = chr(payload[0])
    n = payload[1]
    pre = []
    for i in range(n):
        v = payload[2 + 2 * i] | (payload[3 + 2 * i] << 8)
        req(v in ip.lab, "prefix vector")
        pre.append(ip.lab[v])
    return t, tuple(pre)


def work(task):
    """convert one trace block; every piece mirror-checked, split/restart glue checked (pool worker)"""
    path, off = task
    ip, cx = G["ip"], G["cx"]
    gorder = list(range(1, len(ip.G)))
    t0 = time.time()
    job, pieces = convert(ip, gorder, payload_at(path, off), G["nmax"])
    out = []
    for p in pieces:
        req(cx.mir.block(cx.UB, cx.UBR, p.lit), "mirror rejects a piece of %s:%d" % (path, off))
        recs = []
        for j, (kind, obj, rv) in enumerate(p.recs):
            if kind == "F":
                recs.append(("F", obj, rv))
            else:
                tgt = pieces[p.tg[j]]
                ok = cx.mir.glue(rv, tgt.lit) if kind == "S" else cx.mir.glue0(rv, tgt.lit)
                req(ok, "split/restart glue fails in %s:%d" % (path, off))
                recs.append((kind, p.tg[j], rv))
        out.append((p.lit, p.bits, p.mode, p.nodes, recs))
    return (path, off, job.btag, tuple(job.pre), out, [pack_pl(s) for s in job.leaves], job.st, job.blocknodes,
            time.time() - t0)


def wlits(path, lits):
    with open(path, "xb") as f:
        f.write(len(lits).to_bytes(4, "little"))
        for v in lits:
            nb = (v.bit_length() + 7) // 8
            f.write(nb.to_bytes(4, "little"))
            f.write(v.to_bytes(nb, "little"))


def wtab(path, vals, nbytes):
    with open(path, "xb") as f:
        for v in vals:
            f.write(v.to_bytes(nbytes, "little"))


def ctree(lo, hi, leaf):
    if hi - lo == 1:
        return leaf(lo)
    mid = (lo + hi) // 2
    return "cond (Nat.blt k %d) (%s) (%s)" % (mid, ctree(lo, mid, leaf), ctree(mid, hi, leaf))


def pack(sizes, budget):
    """consecutive ranges [a, b) with sum of sizes <= budget (a single oversized item gets its own range)"""
    out, a, s = [], 0, 0
    for i, z in enumerate(sizes):
        if i > a and s + z > budget:
            out.append((a, i))
            a, s = i, 0
        s += z
    if a < len(sizes):
        out.append((a, len(sizes)))
    return out


def run_main(a):
    import multiprocessing as mp
    ip = IP(a.ip)
    tabp_check(a.tabp)
    leaves = [int(x, 16) for x in a.leaves.split(",") if x]
    cx = Ctx(ip, leaves)
    G.update(ip=ip, cx=cx, nmax=a.nmax)
    files = sorted(globmod.glob(a.traces))
    req(files, "no trace files")
    byJ, byT = {}, {}
    nblk = nempty = ntrunc = 0
    for path in files:
        if os.path.getsize(path) == 0:
            nempty += 1
            continue
        blocks, trunc = read_blocks(path)
        ntrunc += trunc
        for off, payload in blocks:
            t, pre = head_of(ip, payload)
            (byJ if t == "J" else byT).setdefault(pre, []).append((path, off))
            nblk += 1
    log("%d files (%d empty, %d truncated tails), %d blocks: %d J prefixes, %d T prefixes" % (
        len(files), nempty, ntrunc, nblk, len(byJ), len(byT)))
    req(len(byT.get((), [])) == 1, "root: %d T blocks with the empty prefix" % len(byT.get((), [])))
    pool = mp.get_context("fork").Pool(a.jobs)
    Tres, Torder, cover, jobs, jidx, Tseen = {}, [], {}, [], {}, {()}
    level = [byT[()][0]]
    lev = 0
    while level:
        res = pool.map(work, level, chunksize=1)
        nxt = []
        for r in res:
            pre = r[3]
            Tres[pre] = r
            Torder.append(pre)
            for (lit, bits, mode, nodes, recs) in r[4]:
                for kind, obj, rv in recs:
                    if kind != "F":
                        continue
                    req(obj not in cover, "frontier prefix met twice")
                    if obj in byJ:
                        if obj not in jidx:
                            jidx[obj] = len(jobs)
                            jobs.append(byJ[obj][0])
                        cover[obj] = ("J", jidx[obj])
                    elif obj in byT:
                        cover[obj] = ("T", obj)
                        if obj not in Tseen:
                            Tseen.add(obj)
                            nxt.append(byT[obj][0])
                    else:
                        raise Fail("uncovered frontier prefix %s" % (obj,))
        log("T level %d: %d blocks converted; %d frontier prefixes so far, %d jobs" % (lev, len(res), len(cover),
                                                                                    len(jobs)))
        level = nxt
        lev += 1
    Jres = pool.map(work, jobs, chunksize=2)
    pool.close()
    pool.join()
    for r in Jres:
        req(r[2] == "J", "job is not a J block")
        for (lit, bits, mode, nodes, recs) in r[4]:
            req(all(k != "F" for k, _, _ in recs), "F record in a J block")
    log("%d jobs converted (%.0f s of worker time)" % (len(Jres), sum(r[8] for r in Jres)))
    # the top chain and its witnesses
    Ss, Tbase = [], {}
    for pre in Torder:
        Tbase[pre] = len(Ss)
        Ss.extend(Tres[pre][4])
    nS, nJ = len(Ss), len(Jres)
    req(Ss[0][0] % (1 << 14) == 0, "root piece is not the empty-prefix mode-0 block")
    W = []
    for pre in Torder:
        base = Tbase[pre]
        for pi, (lit, bits, mode, nodes, recs) in enumerate(Tres[pre][4]):
            ws = []
            for kind, obj, rv in recs:
                if kind == "F":
                    c = cover[obj]
                    if c[0] == "J":
                        w = nS + c[1]
                        tgt = Jres[c[1]][4][0][0]
                    else:
                        w = Tbase[c[1]]
                        tgt = Ss[w][0]
                        req(w > base + pi, "frontier T block not later in the chain")
                    req(cx.mir.glue0(rv, tgt), "frontier glue0 fails")
                else:
                    w = base + obj
                    req(w > base + pi, "split witness not later")
                ws.append(w)
            W.append(ws)
    HT = []
    for r in Jres:
        s0 = r[4][0][0]
        req(s0 % 2 == 0, "job root piece not mode 0")
        HT.append(s0 % (1 << (14 + 8 * ((s0 >> 1) % 32))))
    allleaves = set()
    for r in list(Tres.values()) + Jres:
        allleaves.update(r[5])
    req(allleaves <= set(leaves), "a converted leaf is not in --leaves")
    st = {}
    for r in list(Tres.values()) + Jres:
        for k, v in r[6].items():
            st[k] = st.get(k, 0) + v
    tbits = sum(p[1] for p in Ss)
    jbits = sum(p[1] for r in Jres for p in r[4])
    npieces = nS + sum(len(r[4]) for r in Jres)
    log("top chain: %d pieces (%d bits), %d records; jobs: %d, %d pieces (%d bits); leaves met %d" % (
        nS, tbits, sum(len(w) for w in W), nJ, npieces - nS, jbits, len(allleaves)))
    rp, ro = byT[()][0]
    job0, pcs0 = convert(ip, list(range(1, len(ip.G))), payload_at(rp, ro), a.nmax)
    req([p.lit for p in pcs0] == [p[0] for p in Tres[()][4]], "root block conversion is not deterministic")
    negs = []
    for nm, dsc, v, p in mutants(cx, pcs0):
        req(not cx.mir.block(cx.UB, cx.UBR, v), "mirror accepts mutant %s" % nm)
        negs.append((nm, dsc, v))
    G["negs"] = negs
    log("negative controls: %s (all rejected by the mirror)" % ", ".join(n for n, _, _ in negs))
    write_stage(a, ip, cx, leaves, Ss, W, Jres, HT, st, npieces, tbits, jbits)


def write_stage(a, ip, cx, leaves, Ss, W, Jres, HT, st, npieces, tbits, jbits):
    NS, IPNS = a.ns, a.ipns
    M = "B334.E1x.Pts.%s" % NS
    P = "B334/E1x/Pts/%s" % NS
    os.makedirs("data", exist_ok=False)
    os.makedirs("lean/%s" % P, exist_ok=False)
    mods = {}

    def mod(name, text):
        path = "lean/%s/%s.lean" % (P, name)
        with open(path, "x") as f:
            f.write(text)
        mods[name] = path

    hdr = "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n"
    gen = "a script"
    nS, nJ = len(Ss), len(Jres)
    # data
    wlits("data/top.bin", [p[0] for p in Ss])
    OF, WT = [], []
    for ws in W:
        OF.append(len(WT))
        WT.extend(ws)
    wtab("data/top_of.bin", OF + [len(WT)], 4)
    wtab("data/top_wt.bin", WT if WT else [0], 4)
    wtab("data/ht.bin", HT if HT else [0], 27)
    X0 = 1
    lfdef = (" || ".join("Nat.beq pl 0x%x" % pl for pl in leaves)) if leaves else "false"
    mod("Ctx", """import B334.E1x.Pts.%(IP)s.Data

/-! # The checker context of the point run `%(NS)s` (generated by %(gen)s): the IP data of `Pts.%(IP)s`
(the generator) with the run's leaf test (%(nl)d leaf prefixes, packed 8-bit labels). -/

namespace %(M)s

noncomputable section

def LFL (%(pl)s : Nat) : Bool := %(lf)s
def CL : E1P.Ctx := Pts.%(IP)s.Cx LFL

end

end %(M)s
""" % {"IP": IPNS, "NS": NS, "gen": gen, "nl": len(leaves), "M": M, "lf": lfdef, "pl": "pl" if leaves else "_pl"})
    mod("HT", """import B334.E1x.Load

/-! # Tables of the point run `%(NS)s` (generated by %(gen)s; binary files in the stage's `data/`)

* `HT.entry k`: the `14 + 8 d`-bit header of job `k`'s first piece (%(nJ)d jobs; 27-byte entries).
* `Wf i j`: the glue witness of header record `j` of top-chain block `i` (`OF`: per block the offset of its first
  record in `WT`; a witness `w < %(nS)d` is a later top-chain block, `w - %(nS)d` a job). -/

#rttablew %(M)s.HT "../data/ht.bin" 64 216
#rttablew %(M)s.OF "../data/top_of.bin" 64 32
#rttablew %(M)s.WT "../data/top_wt.bin" 64 32

namespace %(M)s

noncomputable section

def nJ : Nat := %(nJ)d
def NT : Nat := %(nS)d
def Wf (i j : Nat) : Nat := WT.entry (OF.entry i + j)

end

end %(M)s
""" % {"NS": NS, "gen": gen, "nJ": nJ, "nS": nS, "M": M})
    mod("TopL", """import B334.E1x.Load

/-! # The top chain of the point run `%(NS)s` (generated by %(gen)s): %(n)d E1P blocks, root first (the T blocks'
pieces in breadth-first order of the frontier coverage) -/

#e1lits %(M)s.Top "../data/top.bin"
""" % {"NS": NS, "gen": gen, "n": nS, "M": M})
    ctx = "CL Pts.%s.sl Pts.%s.UB Pts.%s.UBR" % (IPNS, IPNS, IPNS)
    layer3, layer4 = [], []
    # top-chain block checks and glue checks: one theorem per range of <= tbits, modules of <= mbits
    tb = pack([p[1] for p in Ss], a.tbits)
    tbm = pack([sum(Ss[i][1] for i in range(lo, hi)) for lo, hi in tb], a.mbits)
    for q, (ta, tz) in enumerate(tbm):
        ths = "".join("theorem tb_%d : IPChk.allR (fun i => E1P.block %s (Top.lits.getD i 0)) %d %d = true := by\n"
                      "  decide +kernel\n" % (lo, ctx, lo, hi - lo) for lo, hi in tb[ta:tz])
        mod("TB%d" % q, """import %(M)s.Ctx
import %(M)s.TopL
import B334.E1x.IPChk

%(hdr)s/-! # Top-chain blocks %(lo)d … %(hi1)d of `%(NS)s` (generated by %(gen)s; core Lean, `decide +kernel`) -/

namespace %(M)s

%(ths)s
end %(M)s
""" % {"M": M, "hdr": hdr, "lo": tb[ta][0], "hi1": tb[tz - 1][1] - 1, "NS": NS, "gen": gen, "ths": ths})
        layer3.append("TB%d" % q)
    tg = pack([p[1] for p in Ss], 4 * a.tbits)
    tgm = pack([sum(Ss[i][1] for i in range(lo, hi)) for lo, hi in tg], 4 * a.mbits)
    for q, (ta, tz) in enumerate(tgm):
        ths = "".join("theorem tg_%d : IPChk.allR (Pts.glueWB Top.lits nJ HT.entry Wf) %d %d = true := by decide +kernel\n"
                      % (lo, lo, hi - lo) for lo, hi in tg[ta:tz])
        mod("TG%d" % q, """import %(M)s.TopL
import %(M)s.HT
import B334.E1x.Pts.ChkB

%(hdr)s/-! # Glue of the top-chain blocks %(lo)d … %(hi1)d of `%(NS)s` (generated by %(gen)s; core Lean) -/

namespace %(M)s

%(ths)s
end %(M)s
""" % {"M": M, "hdr": hdr, "lo": tg[ta][0], "hi1": tg[tz - 1][1] - 1, "NS": NS, "gen": gen, "ths": ths})
        layer3.append("TG%d" % q)
    # jobs: small ones packed by bits, big ones split over several modules
    jb = [sum(p[1] for p in r[4]) for r in Jres]
    small = [b <= a.tbits for b in jb]
    ranges = []      # (kind, a, b): 'J' small range [a, b) or 'K' single big job a
    k = 0
    while k < nJ:
        if not small[k]:
            ranges.append(("K", k, k + 1))
            k += 1
            continue
        s, b = 0, k
        while b < nJ and small[b] and (b == k or s + jb[b] <= a.tbits):
            s += jb[b]
            b += 1
        ranges.append(("J", k, b))
        k = b
    groups, cur, cs = [], [], 0
    for kind, lo, hi in ranges:
        if kind == "K":
            if cur:
                groups.append(("J", cur))
                cur, cs = [], 0
            groups.append(("K", lo, hi))
            continue
        bsum = sum(jb[lo:hi])
        if cur and cs + bsum > a.mbits:
            groups.append(("J", cur))
            cur, cs = [], 0
        cur.append((lo, hi))
        cs += bsum
    if cur:
        groups.append(("J", cur))
    finj = []
    for g in groups:
        if g[0] == "J":
            rs = g[1]
            lo, hi = rs[0][0], rs[-1][1]
            nm = "J%d" % lo
            lits, start = [], {}
            for kk in range(lo, hi):
                start[kk] = len(lits)
                lits.extend(p[0] for p in Jres[kk][4])
            wlits("data/%s.bin" % nm.lower(), lits)

            def jl(kk):
                return "[%s]" % ", ".join("%s.L%d" % (nm, start[kk] + i) for i in range(len(Jres[kk][4])))

            def jw(kk):
                return "[%s]" % ", ".join("[%s]" % ", ".join(str(t) for _, t, _ in p[4]) for p in Jres[kk][4])

            mod(nm, """import %(M)s.Ctx
import %(M)s.HT
import B334.E1x.Pts.ChkB

%(hdr)s/-! # Jobs %(lo)d … %(hi1)d of `%(NS)s` (generated by %(gen)s; core Lean, `decide +kernel`): each job's
pieces pass, are glued inside, and its first piece has the job's header `HT.entry k` -/

#e1lits %(M)s.%(nm)s "../data/%(lnm)s.bin"

namespace %(M)s

noncomputable section

def JL_%(lo)d (k : Nat) : List Nat :=
  %(jl)s
def JW_%(lo)d (k : Nat) : List (List Nat) :=
  %(jw)s

end

%(ths)s
end %(M)s
""" % {"M": M, "hdr": hdr, "lo": lo, "hi1": hi - 1, "NS": NS, "gen": gen, "nm": nm, "lnm": nm.lower(),
       "jl": ctree(lo, hi, jl), "jw": ctree(lo, hi, jw),
       "ths": "".join("theorem jr_%d : IPChk.allR (fun k => Pts.jobB %s (HT.entry k) (JL_%d k) (JW_%d k)) %d %d = true "
                      ":= by\n  decide +kernel\n" % (tlo, ctx, lo, lo, tlo, thi - tlo) for tlo, thi in rs)})
            layer3.append(nm)
            finj.extend(("J", tlo, thi, lo) for tlo, thi in rs)
        else:
            kk = g[1]
            nm = "K%d" % kk
            ps = Jres[kk][4]
            wlits("data/%s.bin" % nm.lower(), [p[0] for p in ps])
            wl = "[%s]" % ", ".join("[%s]" % ", ".join(str(t) for _, t, _ in p[4]) for p in ps)
            mod(nm + "L", """import B334.E1x.Load

%(hdr)s/-! # The pieces of job %(kk)d of `%(NS)s` (generated by %(gen)s): %(n)d pieces, %(b)d bits -/

#e1lits %(M)s.%(nm)s "../data/%(lnm)s.bin"

namespace %(M)s

noncomputable section

def KW_%(kk)d : List (List Nat) := %(wl)s

end

end %(M)s
""" % {"M": M, "hdr": hdr, "kk": kk, "NS": NS, "gen": gen, "n": len(ps), "b": jb[kk], "nm": nm, "lnm": nm.lower(),
       "wl": wl})
            layer3.append(nm + "L")
            parts = pack([p[1] for p in ps], a.tbits)
            pm = pack([sum(ps[i][1] for i in range(plo, phi)) for plo, phi in parts], a.mbits)
            for q, (ta, tz) in enumerate(pm):
                ths = "".join(
                    "theorem kb_%d_%d : IPChk.allR (fun i => E1P.block %s (%s.lits.getD i 0)) %d %d = true := by\n"
                    "  decide +kernel\n"
                    "theorem kg_%d_%d : IPChk.allR (Pts.glueIB %s.lits KW_%d) %d %d = true := by decide +kernel\n"
                    % (kk, plo, ctx, nm, plo, phi - plo, kk, plo, nm, kk, plo, phi - plo) for plo, phi in parts[ta:tz])
                mod("%sC%d" % (nm, q), """import %(M)s.Ctx
import %(M)s.%(nm)sL
import B334.E1x.Pts.ChkB

%(hdr)s/-! # Job %(kk)d of `%(NS)s`, pieces %(lo)d … %(hi1)d (generated by %(gen)s; core Lean): blocks and glue -/

namespace %(M)s

%(ths)s
end %(M)s
""" % {"M": M, "hdr": hdr, "kk": kk, "NS": NS, "gen": gen, "lo": parts[ta][0], "hi1": parts[tz - 1][1] - 1,
       "nm": nm, "ths": ths})
                layer4.append("%sC%d" % (nm, q))
            finj.append(("K", kk, [(plo, phi) for plo, phi in parts], len(ps)))
    write_fin(a, M, P, NS, IPNS, ctx, mod, mods, hdr, gen, tb, tg, finj, nS, nJ, leaves, layer3, layer4,
              npieces, tbits, jbits, st)


def joins(name, f, parts, total, ind="  "):
    """tactic lines joining range facts `name_<lo>` of IPChk.allR f lo m into IPChk.allR f 0 total"""
    out = []
    lo0, hi0 = parts[0]
    req(lo0 == 0, "ranges start at 0")
    out.append("%shave h0 : IPChk.allR %s 0 %d = true := %s_%d\n" % (ind, f, hi0, name, lo0))
    for q, (lo, hi) in enumerate(parts[1:], 1):
        req(lo == parts[q - 1][1], "ranges are adjacent")
        out.append("%shave h%d : IPChk.allR %s 0 %d = true := IPChk.allR_join %s 0 %d %d h%d %s_%d\n" % (
            ind, q, f, hi, f, lo, hi - lo, q - 1, name, lo))
    req(parts[-1][1] == total, "ranges end at the total")
    out.append("%sexact h%d\n" % (ind, len(parts) - 1))
    return "".join(out)


def write_fin(a, M, P, NS, IPNS, ctx, mod, mods, hdr, gen, tb, tg, finj, nS, nJ, leaves, layer3, layer4,
              npieces, tbits, jbits, st):
    cls = a.cls
    pfx = "Pts.%s" % IPNS
    imports = ["%s.%s" % (M, n) for n in layer3 + layer4]
    fb = "(fun i => E1P.block %s (Top.lits.getD i 0))" % ctx
    fg = "(Pts.glueWB Top.lits nJ HT.entry Wf)"
    hj = []
    for q, it in enumerate(finj):
        if it[0] == "J":
            _, lo, hi, mlo = it
            hj.append("  have r%d : ∀ k, %d ≤ k → k < %d → JobOK CL %s.sl %s.UB (HT.entry k) :=\n"
                      "    Pts.jobs_of_allR CL %s.sl %s.UB %s.UBR %s.UB_eq %s.UBR_eq %s.UB_le HT.entry JL_%d JW_%d %d %d jr_%d\n"
                      % (q, lo, hi, pfx, pfx, pfx, pfx, pfx, pfx, pfx, pfx, mlo, mlo, lo, hi - lo, lo))
        else:
            _, kk, parts, npc = it
            fbk = "(fun i => E1P.block %s (K%d.lits.getD i 0))" % (ctx, kk)
            fgk = "(Pts.glueIB K%d.lits KW_%d)" % (kk, kk)
            hj.append("  have r%d : ∀ k, %d ≤ k → k < %d → JobOK CL %s.sl %s.UB (HT.entry k) := by\n" % (
                q, kk, kk + 1, pfx, pfx))
            hj.append("    have hb : IPChk.allR %s 0 %d = true := by\n" % (fbk, npc))
            hj.append(joins("kb_%d" % kk, fbk, parts, npc, "      "))
            hj.append("    have hg : IPChk.allR %s 0 %d = true := by\n" % (fgk, npc))
            hj.append(joins("kg_%d" % kk, fgk, parts, npc, "      "))
            hj.append("    have hlen : K%d.lits.length = %d := by decide\n" % (kk, npc))
            hj.append("    intro k h1 h2\n    obtain rfl : k = %d := by omega\n" % kk)
            hj.append("    exact Pts.jobOK_of_parts CL %s.sl %s.UB %s.UBR %s.UB_eq %s.UBR_eq %s.UB_le (HT.entry %d) "
                      "K%d.lits KW_%d\n      (by rw [hlen]; decide) (by rw [hlen]; exact hb) (by rw [hlen]; exact hg) "
                      "(by decide +kernel)\n      (by decide +kernel)\n" % (pfx, pfx, pfx, pfx, pfx, pfx, kk, kk, kk))
    # the chain of fa_join over the job ranges
    ends = []
    for it in finj:
        ends.append((it[1], it[2]) if it[0] == "J" else (it[1], it[1] + 1))
    fj = ["  have a0 := r0\n"]
    for q in range(1, len(ends)):
        fj.append("  have a%d := Pts.fa_join a%d r%d\n" % (q, q - 1, q))
    req(ends[0][0] == 0 and ends[-1][1] == nJ and all(ends[q][1] == ends[q + 1][0] for q in range(len(ends) - 1)),
        "job ranges")
    if leaves:
        hlf = """theorem hLF : ∀ pl, CL.LF pl = true → B334.BCP.NoDecomp (Pts.termsOfP CL.R CL.VT pl) CL.R CL.DOM := by
  intro pl h
  have hpl : pl = 0x%x := Nat.eq_of_beq_eq_true h
  subst hpl
  exact B334.BCP.noDecomp_of_t2 (R := B334.T2.leaves_%d.getD %d 0) (List.range %d) (by decide +kernel)
    (B334.T2.ok_%d _ (by decide +kernel))
""" % (leaves[0], cls, a.t2i, ip_R(a), cls)
        req(len(leaves) == 1, "one leaf supported by the generated hLF")
    else:
        hlf = """theorem hLF : ∀ pl, CL.LF pl = true → B334.BCP.NoDecomp (Pts.termsOfP CL.R CL.VT pl) CL.R CL.DOM :=
  fun _ h => absurd h (by decide)
"""
    hlf = hlf.replace("Pts.termsOfP", "E1PS.termsOf")
    t2imp = "import B334.T2.Index\nimport B334.BCP.PermL\n" if leaves else ""
    text = "".join("import %s\n" % m for m in imports) + """import %(PF)s.OK
import B334.E1x.Pts.JobS
import B334.E1x.Pts.Enum
import B334.E1x.Bridge
%(t2imp)s
%(hdr)s/-! # The point run `%(NS)s` (generated by %(gen)s): `E1Concl Em %(R)d` and `QuotLB T334 P%(cls)d 26`

Top chain: %(nS)d E1P blocks (`TopL`), checked in `TB*`, glued in `TG*` (`HT`: job headers, glue witnesses `Wf`);
%(nJ)d search jobs checked in `J*` (small jobs, `jobB`) and `K*` (big jobs, by parts). `enum_of_chain_w` gives the
canonical-point statement, `e1_sound_enum` the E1 conclusion with the IP facts of `%(PF)s` and the class
facts, and `quotLB_of_e1` the point bound. Totals: %(np)d pieces, %(tb)d + %(jb)d literal bits; model stats %(st)s. -/

namespace %(M)s
open B334 B334.E1x B334.E1x.E1PS

theorem topBlk : IPChk.allR %(fb)s 0 NT = true := by
%(jtb)s
theorem topGlue : IPChk.allR %(fg)s 0 NT = true := by
%(jtg)s
theorem topLen : Top.lits.length = NT := by decide
theorem hroot : Top.lits.getD 0 0 %% 2 ^ 14 = 0 := by decide +kernel

theorem hjobs : ∀ k < nJ, JobOK CL %(pfx)s.sl %(pfx)s.UB (HT.entry k) := by
%(hj)s%(fj)s  exact fun k hk => a%(last)d k (Nat.zero_le k) hk

theorem enum : ∀ x : ℕ → ℕ, Glob CL x → (∀ i < 2 ^ 19, SlotV x (%(pfx)s.sl i)) →
    (∀ l < 255, x l ≤ E1P.fld %(pfx)s.UB l) → (∃ l < 255, 0 < x l) → False :=
  enum_of_chain_w CL %(pfx)s.sl %(pfx)s.UB %(pfx)s.UBR %(pfx)s.UB_eq %(pfx)s.UBR_eq %(pfx)s.UB_le Top.lits nJ HT.entry Wf
    (by rw [topLen]; decide) hroot
    (blkChk_spec CL %(pfx)s.sl %(pfx)s.UB %(pfx)s.UBR Top.lits Top.lits.length (by rw [Pts.blk_eq, topLen]; exact topBlk))
    (by rw [Pts.glueChkW_eq, topLen]; exact topGlue) hjobs

theorem ipokL : IPOK CL %(pfx)s.Em %(pfx)s.LB %(pfx)s.LBR %(pfx)s.UB %(pfx)s.UBR %(pfx)s.Ntab %(pfx)s.nrows %(pfx)s.sl
    %(pfx)s.tab %(pfx)s.GE :=
  ⟨%(pfx)s.ipok.N_le, %(pfx)s.ipok.R_le, %(pfx)s.ipok.R_pos, %(pfx)s.ipok.DOM_lt, %(pfx)s.ipok.cosets,
   %(pfx)s.ipok.domperp, %(pfx)s.ipok.planes, %(pfx)s.ipok.planesR, %(pfx)s.ipok.sl_spec, %(pfx)s.ipok.sl_zero,
   %(pfx)s.ipok.Ntab_le, %(pfx)s.ipok.UB_eq, %(pfx)s.ipok.UBR_eq, %(pfx)s.ipok.UB_le, %(pfx)s.ipok.capslot,
   %(pfx)s.ipok.grp⟩

%(hlf)s
theorem concl (hcf : ∀ c, c < Tab2.nCls → Tab2.lbOf c ≠ 0 → RowValid (Tab2.basisOf c) (Tab2.lbOf c)) :
    E1Concl %(pfx)s.Em %(R)d :=
  Pts.e1_sound_enum CL %(pfx)s.Em %(pfx)s.LB %(pfx)s.LBR %(pfx)s.UB %(pfx)s.UBR %(pfx)s.Ntab %(pfx)s.nrows %(pfx)s.sl
    %(pfx)s.tab %(pfx)s.GE ipokL (%(pfx)s.rows (fun c' hc _ hlb => hcf c' hc hlb)) hLF enum

theorem one_ok : oneOK %(pfx)s.Em %(X0)d = true := by decide +kernel
theorem em_ok : emOK %(pfx)s.Em [%(eb)s] = true := by decide +kernel

/-- **The point bound of P%(cls)d** (the `h%(cls)d` of `B334/Final.lean`'s `rank444_ge_35_of_runs`) -/
theorem h%(cls)d (hcf : ∀ c, c < Tab2.nCls → Tab2.lbOf c ≠ 0 → RowValid (Tab2.basisOf c) (Tab2.lbOf c)) :
    QuotLB T334 P%(cls)d 26 := by
  rw [p%(cls)d_eq]; exact quotLB_of_e1 (by decide) (concl hcf) one_ok em_ok

end %(M)s
""" % {"PF": "B334.E1x." + pfx, "t2imp": t2imp, "hdr": hdr, "NS": NS, "gen": gen, "R": a.R, "cls": cls, "nS": nS,
       "nJ": nJ, "np": npieces, "tb": tbits, "jb": jbits, "st": " ".join("%s=%d" % kv for kv in sorted(st.items())),
       "M": M, "fb": fb, "fg": fg, "jtb": joins("tb", fb, tb, nS), "jtg": joins("tg", fg, tg, nS), "pfx": pfx,
       "hj": "".join(hj), "fj": "".join(fj), "last": len(ends) - 1, "hlf": hlf, "X0": 1, "eb": a.ebasis}
    mod("Fin", text)
    mod("Ax", """import %(M)s.Fin
import B334.E1x.AxCheck

/-! # Axiom gate of the point run `%(NS)s` (generated by %(gen)s): standard axioms only -/

#assert_std_axioms %(M)s.h%(cls)d
#assert_std_axioms %(M)s.concl
#assert_std_axioms %(M)s.enum
#print axioms %(M)s.h%(cls)d
""" % {"M": M, "NS": NS, "gen": gen, "cls": cls})
    # negative controls: mutants of the root T block's pieces (each must be rejected: theorems `... = false`)
    negs = G.get("negs", [])
    if negs:
        wlits("data/neg.bin", [v for _, _, v in negs])
        mod("NegL", """import B334.E1x.Load

/-! # Mutant blocks of the point run `%(NS)s` (generated by %(gen)s): %(d)s -/

#e1lits %(M)s.NEG "../data/neg.bin"
""" % {"NS": NS, "gen": gen, "M": M, "d": "; ".join("L%d `%s`: %s" % (i, n, dsc) for i, (n, dsc, _) in enumerate(negs))})
        for i, (n, dsc, _) in enumerate(negs):
            mod("Neg%d" % i, """import %(M)s.Ctx
import %(M)s.NegL

%(hdr)s/-! # Negative control `%(n)s` of `%(NS)s` (generated by %(gen)s): %(dsc)s; the checker rejects it -/

namespace %(M)s

theorem neg_%(n)s : E1P.block %(ctx)s NEG.L%(i)d = false := by decide +kernel

end %(M)s
""" % {"M": M, "hdr": hdr, "n": n, "NS": NS, "gen": gen, "dsc": dsc, "ctx": ctx, "i": i})
    IPP = "B334/E1x/Pts/%s" % IPNS
    with open("layers.txt", "x") as f:
        f.write("B334/E1x/Pts/IPBP B334/E1x/Pts/ChkB B334/E1x/Pts/Enum %s/Data %s/HT %s/TopL%s\n" % (
            IPP, P, P, (" %s/NegL" % P) if negs else ""))
        f.write("B334/E1x/Pts/JobS %s/Base %s/F %s/Ctx\n" % (IPP, IPP, P))
        f.write(" ".join(["%s/S%d" % (IPP, s) for s in range(a.ipS)] + ["%s/%s" % (P, n) for n in layer3] +
                         ["%s/Neg%d" % (P, i) for i in range(len(negs))]) + "\n")
        f.write(" ".join(["%s/OK" % IPP] + ["%s/%s" % (P, n) for n in layer4]) + "\n")
        f.write("%s/Fin\n%s/Ax\n" % (P, P))
    log("stage: %d modules (%d top block, %d top glue, %d job modules, %d big-job parts, %d negative controls) + "
        "Fin, Ax; layers.txt" % (len(mods), len(tb), len(tg), len(layer3) - len(tb) - len(tg), len(layer4), len(negs)))


def ip_R(a):
    return a.R


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("ip")
    r.add_argument("--traces", required=True)
    r.add_argument("--tabp", required=True)
    r.add_argument("--ns", required=True)
    r.add_argument("--ipns", required=True)
    r.add_argument("--cls", type=int, required=True)
    r.add_argument("--R", type=int, default=25)
    r.add_argument("--ebasis", required=True)
    r.add_argument("--leaves", default="")
    r.add_argument("--t2i", type=int, default=0)
    r.add_argument("--jobs", type=int, default=32)
    r.add_argument("--nmax", type=int, default=3000)
    r.add_argument("--tbits", type=int, default=250000)
    r.add_argument("--mbits", type=int, default=4000000)
    r.add_argument("--bmax", type=int, default=200000)
    r.add_argument("--ipS", type=int, required=True)
    t = sub.add_parser("test")
    t.add_argument("ip")
    t.add_argument("trace")
    t.add_argument("--tabp", required=True)
    t.add_argument("--out", required=True)
    t.add_argument("--nmax", type=int, default=3000)
    t.add_argument("--block", type=int, default=0)
    t.add_argument("--bmax", type=int, default=400000)
    for p in (t, r):
        p.add_argument("--satw", type=int, default=6)
        p.add_argument("--satr", type=int, default=-1)
        p.add_argument("--pendmax", type=int, default=63)
    a = ap.parse_args()
    global SATW, SATR, BMAX, PENDMAX
    SATW = a.satw
    req(SATW == 6, "--satw 6 (CheckP.lean); 8 needs a checker copy with an 8-bit count")
    SATR = a.satr if a.satr >= 0 else (1 << SATW) - 1
    BMAX = a.bmax
    PENDMAX = a.pendmax
    req(0 < PENDMAX < (1 << SATW), "--pendmax")
    log("saturation count width %d, restart above %d events, pieces <= %d bits" % (SATW, SATR, BMAX))
    if a.cmd == "test":
        test_main(a)
    else:
        run_main(a)


if __name__ == "__main__":
    try:
        main()
    except Fail as e:
        print("FAIL", e)
        sys.exit(1)
