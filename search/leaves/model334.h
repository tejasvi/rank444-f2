// model334.h: the generator's own model of the abstract checker together with the stream reader of
// the stream format.  The generator runs this model before writing a certificate ("it runs its own model and refuses to write a
// certificate the model rejects".
//
// The model is deliberately plain and shares no code with gen7_334.h (no slot elimination, no 4096-bit mask struct, no
// root tables): it re-derives T334 from the definition, dom_E from E, and every node from the assigned values along the
// path with Gaussian elimination on 12-bit rows, explicit std::bitset<4096> column / row spaces and an explicit
// preimage table x.  Only the pair-symmetry tables ORBM and CORB are the file's (validated by s334::validate).
//
// check_stream() reads the bits of a batch and decides every leaf.  Rules enforced (all of the checker rules and the format):
//   batch      1 leaf | 0 len24 left right;  leaf: n (6, <= 31), n labels (9), dommode (2) == 01, 512-bit mask == dom_E exactly,
//              every label the smallest vector of its coset a+E and nonzero;  the certificate must use the stream exactly
//   over X     X in dom, rank R(X) > u(X)
//   br         t active; sym => nothing assigned and cdir = 0; NT: in dom, u <= rank (and no repeated / already recorded X);
//              SL: in dom, hits a_t, u <= rank+1;  candidates in the exact order of step 5; one subtree per candidate;
//              children: records hitting a_t updated by (I), slack records dropped; fuel 64
#pragma once
#include <bits/stdc++.h>
#include "symtab334.h"

namespace m334 {

typedef unsigned long long u64;
typedef std::bitset<4096> BS;

struct Reader {
  const std::vector<u64>* w = nullptr; size_t n = 0, pos = 0; bool bad = false;
  u64 rd(int k) {   // the low k bits of the remaining stream; the first bit read is the lowest
    if (pos + (size_t)k > n) { bad = true; pos = n; return 0; }
    u64 v = 0;
    for (int i = 0; i < k; i++) { size_t p = pos + i; v |= (((*w)[p >> 6] >> (p & 63)) & 1ULL) << i; }
    pos += k; return v;
  }
};

struct Model {
  std::vector<int> E;          // a basis of E (9-bit masks)
  std::vector<int> domE;       // dom_E ascending
  u64 maskE[8];                // dom_E as a 512-bit mask
  std::vector<char> inDom;     // 512
  int TXm[512][12];            // T(X): row y (bits z)
  std::vector<BS> NPs;         // NPs[v] = {c : parity(c & v) = 1}
  BS orbm; std::vector<BS> corbs;
  std::set<int> Espan;         // all elements of E

  struct Rec { int X; std::shared_ptr<const std::vector<uint16_t>> xt; BS lm, rm; };
  struct Slk { BS col, row; };

  // per-check state
  int n = 0; int lab[32]; bool asg[32]; int bv[32], cv[32]; int nasg = 0;
  long long nodes = 0, claims = 0, kidsTotal = 0; int maxDepth = 0;
  std::string err; Reader* R = nullptr;
  int trace_left = 0; FILE* tf = nullptr;

  Model(const s334::SymTab& st, const std::vector<int>& Ebasis) : E(Ebasis), NPs(4096), corbs(4096) {
    // T334 from the definition: T[x][y][z] = 1 iff x = 3i+j, y = 4j+k, z = 3k+i
    static unsigned char T[9][12][12]; memset(T, 0, sizeof T);
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) for (int k = 0; k < 4; k++) T[3 * i + j][4 * j + k][3 * k + i] = 1;
    for (int X = 0; X < 512; X++) for (int y = 0; y < 12; y++) {
      int row = 0;
      for (int z = 0; z < 12; z++) { int v = 0; for (int x = 0; x < 9; x++) if (((X >> x) & 1) && T[x][y][z]) v ^= 1; row |= v << z; }
      TXm[X][y] = row;
    }
    // dom_E: X != 0 and parity(X & e) == 0 for every basis vector e of E
    inDom.assign(512, 0);
    for (int i = 0; i < 8; i++) maskE[i] = 0;
    for (int X = 1; X < 512; X++) {
      bool ok = true; for (int e : E) if (__builtin_parity(X & e)) { ok = false; break; }
      if (ok) { inDom[X] = 1; domE.push_back(X); maskE[X >> 6] |= 1ULL << (X & 63); }
    }
    Espan.insert(0);
    for (int e : E) { std::vector<int> cur(Espan.begin(), Espan.end()); for (int v : cur) Espan.insert(v ^ e); }
    for (int v = 0; v < 4096; v++) for (int c = 0; c < 4096; c++) if (__builtin_parity(c & v)) NPs[v][c] = 1;
    for (int o : st.orbm) { orbm[o] = 1; for (int c : st.corb.at(o)) corbs[o][c] = 1; }
  }

  bool fail(const std::string& m) { if (err.empty()) err = m; return false; }
  static std::string fmt(const char* f, ...) {
    char buf[300]; va_list ap; va_start(ap, f); vsnprintf(buf, sizeof buf, f, ap); va_end(ap); return buf;
  }

  // ---- plain linear algebra on the 12x12 residual matrix, rows[y] has bit z = R[y][z]
  void residual(int X, int* rows) const {
    for (int y = 0; y < 12; y++) rows[y] = TXm[X][y];
    for (int t = 0; t < n; t++) if (asg[t] && __builtin_parity(X & lab[t]))
      for (int y = 0; y < 12; y++) if ((bv[t] >> y) & 1) rows[y] ^= cv[t];
  }
  static int rank_rows(const int* rows) {
    int bas[12] = {0}, rk = 0;
    for (int y = 0; y < 12; y++) {
      int v = rows[y];
      while (v) { int h = 31 - __builtin_clz(v); if (!bas[h]) { bas[h] = v; rk++; break; } v ^= bas[h]; }
    }
    return rk;
  }
  int ucount(int X) const { int u = 0; for (int t = 0; t < n; t++) if (!asg[t] && __builtin_parity(X & lab[t])) u++; return u; }
  struct Lin { int rank = 0; BS col, row; std::shared_ptr<std::vector<uint16_t>> xt; };
  // column space, row space and a linear preimage table x on the column space (R x(v) = v)
  static Lin analyse(const int* rows, bool want_x) {
    Lin L; L.rank = rank_rows(rows);
    // row space
    { int bas[12] = {0}; std::vector<int> bl;
      for (int y = 0; y < 12; y++) { int v = rows[y]; while (v) { int h = 31 - __builtin_clz(v); if (!bas[h]) { bas[h] = v; bl.push_back(v); break; } v ^= bas[h]; } }
      std::vector<int> el{0}; for (int v : bl) { size_t m = el.size(); for (size_t i = 0; i < m; i++) el.push_back(el[i] ^ v); }
      for (int e : el) L.row[e] = 1; }
    // column space with combinations: col[z] = sum_y R[y][z] e_y
    { int cols[12]; for (int z = 0; z < 12; z++) { int c = 0; for (int y = 0; y < 12; y++) c |= ((rows[y] >> z) & 1) << y; cols[z] = c; }
      int bas[12] = {0}, comb[12] = {0}; std::vector<std::pair<int, int>> bl;
      for (int z = 0; z < 12; z++) {
        int v = cols[z], cm = 1 << z;
        while (v) { int h = 31 - __builtin_clz(v); if (!bas[h]) { bas[h] = v; comb[h] = cm; bl.push_back({v, cm}); break; } v ^= bas[h]; cm ^= comb[h]; }
      }
      std::vector<std::pair<int, int>> el{{0, 0}};
      for (auto& p : bl) { size_t m = el.size(); for (size_t i = 0; i < m; i++) el.push_back({el[i].first ^ p.first, el[i].second ^ p.second}); }
      if (want_x) L.xt = std::make_shared<std::vector<uint16_t>>(4096, 0);
      for (auto& p : el) { L.col[p.first] = 1; if (want_x) (*L.xt)[p.first] = (uint16_t)p.second; }
      if ((int)bl.size() != L.rank) throw std::runtime_error("model: row rank != column rank");
    }
    return L;
  }

  // the candidate list of a br node.  Returns false (with err) on a malformed node.
  struct Cand { int b, c; };
  void candidates(const std::vector<Rec>& part, const std::vector<Slk>& sl, bool sym, bool cdir, std::vector<Cand>& out,
                  size_t* nBm = nullptr, size_t* nCm = nullptr) const {
    out.clear();
    BS Bm, Cm; Bm.set(); Cm.set(); Bm[0] = 0; Cm[0] = 0;
    if (sym) Bm &= orbm;
    for (auto& r : part) { Bm &= r.lm; Cm &= r.rm; }
    if (nBm) *nBm = Bm.count();
    if (nCm) *nCm = Cm.count();
    if (!cdir) {
      for (size_t b = Bm._Find_first(); b < 4096; b = Bm._Find_next(b)) {
        BS cm = Cm;
        for (auto& r : part) cm &= NPs[(*r.xt)[b]];
        for (auto& s : sl) if (!s.col[b]) cm &= s.row;
        if (sym) cm &= corbs[b];
        for (size_t c = cm._Find_first(); c < 4096; c = cm._Find_next(c)) out.push_back({(int)b, (int)c});
      }
    } else {
      for (size_t c = Cm._Find_first(); c < 4096; c = Cm._Find_next(c)) {
        for (size_t b = Bm._Find_first(); b < 4096; b = Bm._Find_next(b)) {
          bool ok = true;
          for (auto& r : part) if (!__builtin_parity((int)c & (*r.xt)[b])) { ok = false; break; }   // <g_r(c), b> = <c, x_r(b)>, b in col_r
          if (ok) for (auto& s : sl) if (!s.row[c] && !s.col[b]) { ok = false; break; }   // (c not in row_s => b in col_s)
          if (ok) out.push_back({(int)b, (int)c});
        }
      }
    }
  }

  bool node(const std::vector<Rec>& recs, int depth) {
    nodes++; if (depth > maxDepth) maxDepth = depth;
    if (depth >= 64) return fail("fuel exhausted (depth >= 64)");
    int tag = (int)R->rd(1); if (R->bad) return fail("truncated stream (tag)");
    if (tag == 0) {   // over X
      int X = (int)R->rd(9); if (R->bad) return fail("truncated stream (over X)");
      if (X < 1 || !inDom[X]) return fail(fmt("over %d: X not in dom", X));
      int rows[12]; residual(X, rows); int rk = rank_rows(rows), u = ucount(X);
      if (!(rk > u)) return fail(fmt("over %d: rank R(X) = %d is not > u(X) = %d", X, rk, u));
      if (trace_left > 0 && tf) { trace_left--; fprintf(tf, "  node %lld (depth %d): over X=%d: rank R(X)=%d > u(X)=%d\n", nodes, depth, X, rk, u); }
      return true;
    }
    int t = (int)R->rd(5), sym = (int)R->rd(1), cdir = (int)R->rd(1);
    int nNT = (int)R->rd(4); std::vector<int> NT, SL;
    for (int i = 0; i < nNT; i++) NT.push_back((int)R->rd(9));
    int nSL = (int)R->rd(3);
    for (int i = 0; i < nSL; i++) SL.push_back((int)R->rd(9));
    if (R->bad) return fail("truncated stream (br header)");
    if (t >= n || asg[t]) return fail(fmt("br: term %d is not active", t));
    if (sym && (nasg != 0 || cdir)) return fail("br: sym needs Asg = empty and cdir = 0");
    std::vector<Rec> all = recs; std::vector<Rec> part; std::vector<Slk> sl;
    std::set<int> seen; for (auto& r : recs) seen.insert(r.X);
    for (int X : NT) {
      if (X < 1 || !inDom[X]) return fail(fmt("NT %d: X not in dom", X));
      if (!seen.insert(X).second) return fail(fmt("NT %d: repeated or already recorded", X));
      int rows[12]; residual(X, rows); int u = ucount(X);
      Lin L = analyse(rows, true);
      if (!(u <= L.rank)) return fail(fmt("NT %d: u = %d > rank R(X) = %d", X, u, L.rank));
      Rec r; r.X = X; r.xt = L.xt; r.lm = L.col; r.rm = L.row; all.push_back(r); claims++;
    }
    for (int X : SL) {
      if (X < 1 || !inDom[X]) return fail(fmt("SL %d: X not in dom", X));
      if (!__builtin_parity(X & lab[t])) return fail(fmt("SL %d: X does not hit a_t", X));
      int rows[12]; residual(X, rows); int u = ucount(X);
      Lin L = analyse(rows, false);
      if (!(u <= L.rank + 1)) return fail(fmt("SL %d: u = %d > rank R(X) + 1 = %d", X, u, L.rank + 1));
      Slk s; s.col = L.col; s.row = L.row; sl.push_back(s); claims++;
    }
    for (auto& r : all) if (__builtin_parity(r.X & lab[t])) part.push_back(r);
    std::vector<Cand> cs; size_t nBm = 0, nCm = 0;
    candidates(part, sl, sym, cdir, cs, &nBm, &nCm);
    kidsTotal += (long long)cs.size();
    if (trace_left > 0 && tf) {
      trace_left--;
      fprintf(tf, "  node %lld (depth %d): br t=%d (a_t=%d)  sym=%d cdir=%d  |NT|=%d |SL|=%d  |part|=%zu |Bm|=%zu |Cm|=%zu  #candidates=%zu\n",
              nodes, depth, t, lab[t], sym, cdir, nNT, nSL, part.size(), nBm, nCm, cs.size());
      for (int X : NT) { int rows[12]; residual(X, rows); fprintf(tf, "    NT X=%d: u(X)=%d rank R(X)=%d\n", X, ucount(X), rank_rows(rows)); }
      for (int X : SL) { int rows[12]; residual(X, rows); fprintf(tf, "    SL X=%d: u(X)=%d rank R(X)=%d\n", X, ucount(X), rank_rows(rows)); }
      for (size_t i = 0; i < cs.size() && i < 8; i++) fprintf(tf, "    candidate %zu: b=%d c=%d\n", i + 1, cs[i].b, cs[i].c);
      if (depth == 0 && !cdir && nBm > 0 && nBm <= 64) {   // how every b of Bm fares: the size of the c-set after each condition
        BS Bm2, Cm2; Bm2.set(); Cm2.set(); Bm2[0] = 0; Cm2[0] = 0;
        if (sym) Bm2 &= orbm;
        for (auto& r : part) { Bm2 &= r.lm; Cm2 &= r.rm; }
        fprintf(tf, "    Bm = {"); for (size_t b = Bm2._Find_first(); b < 4096; b = Bm2._Find_next(b)) fprintf(tf, " %zu", b); fprintf(tf, " }\n");
        for (size_t b = Bm2._Find_first(); b < 4096; b = Bm2._Find_next(b)) {
          BS cm = Cm2; fprintf(tf, "    b=%zu: |Cm|=%zu", b, cm.count());
          for (auto& r : part) { cm &= NPs[(*r.xt)[b]]; fprintf(tf, " -> %zu (X=%d: x(b)=%d)", cm.count(), r.X, (int)(*r.xt)[b]); }
          for (auto& s : sl) if (!s.col[b]) { cm &= s.row; fprintf(tf, " -> %zu (slack)", cm.count()); }
          if (sym) { cm &= corbs[b]; fprintf(tf, " -> %zu (CORB[b])", cm.count()); }
          fprintf(tf, "\n");
        }
      }
    }
    for (auto& cd : cs) {
      std::vector<Rec> rec2;
      for (auto& r : all) {
        if (!__builtin_parity(r.X & lab[t])) { rec2.push_back(r); continue; }
        Rec q = r; q.lm.reset();
        for (size_t v = r.lm._Find_first(); v < 4096; v = r.lm._Find_next(v)) if (!__builtin_parity(cd.c & (*r.xt)[v])) q.lm[v] = 1;
        q.rm = r.rm & ~NPs[(*r.xt)[cd.b]];
        rec2.push_back(q);
      }
      asg[t] = true; bv[t] = cd.b; cv[t] = cd.c; nasg++;
      bool ok = node(rec2, depth + 1);
      asg[t] = false; nasg--;
      if (!ok) return false;
    }
    return true;
  }

  // a leaf record (after the batch tag)
  bool leaf(size_t* nbitsLeaf = nullptr) {
    size_t p0 = R->pos;
    n = (int)R->rd(6); if (R->bad) return fail("truncated stream (n)");
    if (n > 31) return fail("n > 31");
    for (int t = 0; t < n; t++) { lab[t] = (int)R->rd(9); asg[t] = false; bv[t] = cv[t] = 0; }
    nasg = 0;
    int dm = (int)R->rd(2); if (R->bad) return fail("truncated stream (labels)");
    if (dm != 1) return fail(fmt("dommode %d is not 01", dm));
    u64 mk[8]; for (int i = 0; i < 8; i++) mk[i] = R->rd(64);
    if (R->bad) return fail("truncated stream (dom mask)");
    for (int i = 0; i < 8; i++) if (mk[i] != maskE[i]) return fail("dom mask differs from dom_E");
    for (int t = 0; t < n; t++) {
      if (lab[t] == 0) return fail(fmt("label %d is zero", t));
      for (int e : Espan) if ((lab[t] ^ e) < lab[t]) return fail(fmt("label %d (=%d) is not the smallest vector of its coset", t, lab[t]));
    }
    std::vector<Rec> none;
    bool ok = node(none, 0);
    if (nbitsLeaf) *nbitsLeaf = R->pos - p0;
    return ok;
  }
  bool batch(int fuel, long long* nleaves) {
    if (fuel <= 0) return fail("batch: fuel exhausted");
    int tag = (int)R->rd(1); if (R->bad) return fail("truncated stream (batch tag)");
    if (tag == 1) { if (nleaves) (*nleaves)++; return leaf(); }
    size_t len = (size_t)R->rd(24); if (R->bad) return fail("truncated stream (batch length)");
    size_t p0 = R->pos;
    if (!batch(fuel - 1, nleaves)) return false;
    if (R->pos - p0 != len) return fail("batch: left part does not have the stated length");
    return batch(fuel - 1, nleaves);
  }
  // decide a whole stream; true iff every leaf is accepted and the stream is used exactly
  bool check_stream(const std::vector<u64>& w, size_t nbits, std::string* why, long long* nleaves = nullptr) {
    Reader rd; rd.w = &w; rd.n = nbits; R = &rd; err.clear(); nodes = claims = kidsTotal = 0; maxDepth = 0;
    long long nl = 0;
    bool ok = batch(64, &nl);
    if (ok && rd.pos != nbits) ok = fail(fmt("stream has %zu unused bits", nbits - rd.pos));
    if (nleaves) *nleaves = nl;
    if (why) *why = err;
    R = nullptr;
    return ok;
  }
};

}  // namespace m334
