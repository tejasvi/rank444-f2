// gen7_334.h: the certificate generator for the completion leaves of <3,3,4> over F2 (stream format v5c-334; the checker
// rules and the stream format are those of B334/BC/BranchCheck334.lean).
//
// A port of the <3,3,3> generator gen7 (cpp/enum/gen7.h of rank333-f2, Apache-2.0, doi:10.5281/zenodo.23236154, "gen7fast" version: look-ahead branching with K = 4,
// claim minimisation, cdir per node, sym at the root, finalize = attach + hoist).  Changes for <3,3,4>:
//   * second and third factors are 12 bits (b: 3x4 matrix, entry (j,k) at bit 4j+k;  c: 4x3 matrix, entry (k,i) at bit 3k+i);
//     first factors (labels) and functionals stay 9 bits;
//   * vector sets (column spaces, row spaces, candidate masks) are 4096-bit masks (64 words) instead of 512-bit;
//   * the elimination works on 12 slots of 24 bits (12 bits of the column, 12 bits of the combination);
//   * the root symmetry is (b, c) -> (b S, S^-1 c) with S in GL4(F2): ORBM (15 masks) and CORB[b] come from symtab334.tsv;
//   * no Lemma G, no SAT-leaf (BC7L) certificates, no rank-1 fast path;  dommode is always 01 (a 512-bit dom mask follows).
// The stream layout written by enc_leaf() is the stream format, bit for bit.
//
//   g7x::init_tables(symtab);                           // once
//   g7x::Leaf L(labels, dom_list);                      // labels: 9-bit coset minima (n <= 32); dom_list: X in E^perp \ {0}, ascending
//   g7x::Cert* c = L.gen(K, maxnodes, deadk);           // throws g7x::Big past maxnodes, g7x::Sat if a decomposition exists
//   c = L.finalize(c);  BW w; g7x::enc_leaf(w, labels, dom_list, c);
//
// Doubles: node costs are computed operation by operation (volatile temporaries, no FMA), so the choice of claims does not
// depend on the compiler.
#pragma once
#include <array>
#include <bits/stdc++.h>
#include "symtab334.h"

namespace g7x {

typedef unsigned long long u64;
struct Big : std::runtime_error { Big() : std::runtime_error("maxnodes") {} };
struct Sat : std::runtime_error { Sat() : std::runtime_error("SAT") {} };

// ------------------------------------------------------------------------------------------------ 4096-bit masks
static const int NW = 64;
struct M { u64 w[NW]; };
static inline M mand(const M& a, const M& b) { M r; for (int i = 0; i < NW; i++) r.w[i] = a.w[i] & b.w[i]; return r; }
static inline M mnot(const M& a) { M r; for (int i = 0; i < NW; i++) r.w[i] = ~a.w[i]; return r; }
static inline bool mz(const M& a) { u64 o = 0; for (int i = 0; i < NW; i++) o |= a.w[i]; return o == 0; }
static inline bool meq(const M& a, const M& b) { for (int i = 0; i < NW; i++) if (a.w[i] != b.w[i]) return false; return true; }
static inline int mpop(const M& a) { int s = 0; for (int i = 0; i < NW; i++) s += __builtin_popcountll(a.w[i]); return s; }
static inline bool mbit(const M& a, int i) { return (a.w[i >> 6] >> (i & 63)) & 1; }
static inline void mset(M& a, int i) { a.w[i >> 6] |= 1ULL << (i & 63); }
static inline M mfull() { M r; for (int i = 0; i < NW; i++) r.w[i] = ~0ULL; return r; }
static inline M mzero() { M r; for (int i = 0; i < NW; i++) r.w[i] = 0; return r; }
template <class F> static inline void mbits(const M& a, F f) {
  for (int q = 0; q < NW; q++) for (u64 x = a.w[q]; x; x &= x - 1) f(64 * q + __builtin_ctzll(x));
}

// ------------------------------------------------------------------------------------------------ tables
struct Tables {
  int PAR[512];
  int TX[512][12];              // rows y of T(X), 12-bit over z (TX[0] = 0)
  M ORBM, ALLNZ, M4096F;
  std::vector<M> NPM;           // NPM[v] = {c : par(c & v) = 1}, v < 4096
  std::vector<M> CORB;          // CORB[b] = the minima of the Stab(b)-orbits of c (b in ORBM; zero mask otherwise)
  struct Root { uint32_t P[12]; int PM, rk; M lm, rm, lm2; uint16_t xlo[64], xhi[64]; };
  std::vector<Root> ROOT;       // per functional X: elimination of T(X)
  int RKV[512];                 // rank of X as a 3x3 matrix
  uint32_t RMc[512][12], RMr[512][12]; bool rmc_ok = false;

  explicit Tables(const s334::SymTab& st) : NPM(4096), CORB(4096), ROOT(512) {
    for (int i = 0; i < 512; i++) PAR[i] = __builtin_popcount(i) & 1;
    static int Tt[9][12][12];
    memset(Tt, 0, sizeof Tt);
    for (auto& e : s334::t334_support()) Tt[e[0]][e[1]][e[2]] = 1;
    for (int y = 0; y < 12; y++) TX[0][y] = 0;
    for (int X = 1; X < 512; X++) for (int y = 0; y < 12; y++) {
      int r = 0;
      for (int z = 0; z < 12; z++) { int v = 0; for (int x = 0; x < 9; x++) if ((X >> x) & 1) v ^= Tt[x][y][z]; r |= v << z; }
      TX[X][y] = r;
    }
    ALLNZ = mfull(); ALLNZ.w[0] &= ~1ULL; M4096F = mfull(); ORBM = mzero();
    for (int o : st.orbm) mset(ORBM, o);
    for (int b = 0; b < 4096; b++) CORB[b] = mzero();
    for (int o : st.orbm) { for (int c : st.corb.at(o)) mset(CORB[o], c); }
    for (int v = 0; v < 4096; v++) { NPM[v] = mzero(); for (int c = 0; c < 4096; c++) if (__builtin_popcount(c & v) & 1) mset(NPM[v], c); }
    for (int X = 0; X < 512; X++) {
      uint32_t Mc[12], Mr[12]; resRoot0(X, Mc, Mr);
      Root& R = ROOT[X]; uint32_t P[12], P2[12]; int PM, rk, PM2, rk2;
      elim(Mc, P, PM, rk); elim(Mr, P2, PM2, rk2);
      memcpy(R.P, P, sizeof P); R.PM = PM; R.rk = rk; R.lm = lm_compl(P, PM); R.rm = ker_mask(Mc); R.lm2 = ker_mask(Mr);
      { uint16_t v[12]; for (int h = 0; h < 12; h++) v[h] = (uint16_t)((P[h] >> 12) & 4095);
        R.xlo[0] = 0; for (int i = 1; i < 64; i++) R.xlo[i] = R.xlo[i & (i - 1)] ^ v[__builtin_ctz(i)];
        R.xhi[0] = 0; for (int i = 1; i < 64; i++) R.xhi[i] = R.xhi[i & (i - 1)] ^ v[6 + __builtin_ctz(i)]; }
      if (!meq(R.lm, R.lm2)) throw std::runtime_error("root masks");
    }
    for (int v = 0; v < 512; v++) {
      if (!v) { RKV[v] = 0; continue; }
      int rows[3] = {v & 7, (v >> 3) & 7, (v >> 6) & 7}; std::vector<int> basis; int rk = 0;
      for (int x : rows) { for (int bv : basis) x = std::min(x, x ^ bv); if (x) { basis.push_back(x); rk++; } }
      RKV[v] = rk;
    }
    // identity: rank T(X) = 4 * rank(X as a 3x3 matrix)
    for (int X = 1; X < 512; X++) if (ROOT[X].rk != 4 * RKV[X]) throw std::runtime_error("rank T(X) != 4 rank X");
    for (int X = 0; X < 512; X++) resRoot0(X, RMc[X], RMr[X]);
    rmc_ok = true;
  }
  // slots of 24 bits: column z (bits 0..11, index y) | identity bit 12+z;  rows likewise
  void resRoot0(int X, uint32_t* Mc, uint32_t* Mr) const {
    for (int z = 0; z < 12; z++) { int col = 0; for (int y = 0; y < 12; y++) col |= ((TX[X][y] >> z) & 1) << y; Mc[z] = (uint32_t)col | (1u << (12 + z)); }
    for (int y = 0; y < 12; y++) Mr[y] = (uint32_t)TX[X][y] | (1u << (12 + y));
  }
  void resRoot(int X, uint32_t* Mc, uint32_t* Mr) const {
    if (rmc_ok) { memcpy(Mc, RMc[X], sizeof RMc[X]); memcpy(Mr, RMr[X], sizeof RMr[X]); return; }
    resRoot0(X, Mc, Mr);
  }
  // elimination on 12 slots of 24 bits: pivots from bit 11 down, the lowest slot with the bit; P = pivot rows by pivot index
  static void elim(uint32_t* Ms, uint32_t* P, int& PM, int& rk) {
    for (int i = 0; i < 12; i++) P[i] = 0;
    PM = 0; rk = 0;
    for (int h = 11; h >= 0; h--) {
      int z0 = -1; for (int z = 0; z < 12; z++) if ((Ms[z] >> h) & 1) { z0 = z; break; }
      if (z0 < 0) continue;
      uint32_t p = Ms[z0];
      for (int z = 0; z < 12; z++) if ((Ms[z] >> h) & 1) Ms[z] ^= p;
      for (int z = 0; z < 12; z++) if ((P[z] >> h) & 1) P[z] ^= p;
      P[h] |= p; PM |= 1 << h; rk++;
    }
  }
  static bool elim_ok(const uint32_t* Ms, const uint32_t* P, int PM) {
    for (int z = 0; z < 12; z++) if (Ms[z] & 4095) return false;                      // left halves of the leftover rows
    for (int h = 0; h < 12; h++) if (P[h] & (4095u & ~((2u << h) - 1))) return false; // no bits above h in slot h
    for (int z = 0; z < 12; z++) for (int h = 0; h < 12; h++) if ((PM >> h) & 1) { int bitv = (P[z] >> h) & 1; if (bitv != (z == h)) return false; }
    for (int z = 0; z < 12; z++) if (!((PM >> z) & 1) && P[z]) return false;
    return true;
  }
  M perp(int v) const { return mnot(NPM[v & 4095]); }
  static int gather(const uint32_t* P, int j) { int r = 0; for (int h = 0; h < 12; h++) r |= ((P[h] >> j) & 1) << h; return r; }
  M lm_compl(const uint32_t* P, int PM) const { M lm = M4096F; for (int j = 0; j < 12; j++) if (!((PM >> j) & 1)) lm = mand(lm, perp(gather(P, j) | (1 << j))); return lm; }
  M ker_mask(const uint32_t* Ms) const { M m = M4096F; for (int z = 0; z < 12; z++) if (Ms[z]) m = mand(m, perp((int)(Ms[z] >> 12))); return m; }
  static int xof(const uint32_t* P, int b) { int x = 0; for (int h = 0; h < 12; h++) if ((b >> h) & 1) x ^= (P[h] >> 12) & 4095; return x; }
  static int gof(const uint32_t* P, int c) { int g = 0; for (int h = 0; h < 12; h++) g |= (__builtin_parity(((P[h] >> 12) & 4095) & c)) << h; return g; }
};
static std::unique_ptr<Tables>& tables_ptr() { static std::unique_ptr<Tables> p; return p; }
static void init_tables(const s334::SymTab& st) { tables_ptr().reset(new Tables(st)); }
static const Tables& T() { return *tables_ptr(); }

// ------------------------------------------------------------------------------------------------ certificates
struct Cert {
  bool over = false; int X = 0;                       // OVER(X)
  int t = 0; std::vector<int> NT, SL; std::vector<Cert*> kids; bool sym = false, cdir = false;
  std::vector<std::pair<int, int>> cs;                // attach annotation: the candidate list of the node
};

struct BW {
  std::vector<u64> w; size_t n = 0;
  void put(u64 x, int k) {
    if (k < 64 && x >= (1ULL << k)) throw std::runtime_error("cert field overflow");
    if (!k) return;
    size_t q = n >> 6; int s = n & 63;
    if (w.size() < q + 2) w.resize(q + 2, 0);
    w[q] |= x << s; if (s && s + k > 64) w[q + 1] |= x >> (64 - s);
    n += k;
  }
};
// the certificate part of the stream format: nodes in preorder
static void enc_cert(BW& w, const Cert* c) {
  if (c->over) { w.put(0, 1); w.put(c->X, 9); return; }
  w.put(1, 1); w.put(c->t, 5); w.put(c->sym, 1); w.put(c->cdir, 1);
  w.put(c->NT.size(), 4); for (int X : c->NT) w.put(X, 9);
  w.put(c->SL.size(), 3); for (int X : c->SL) w.put(X, 9);
  for (auto* k : c->kids) enc_cert(w, k);
}
// a one-leaf batch of the stream format:  1 | n (6) | n labels (9 each) | dommode 01 (2) | 512-bit dom mask | certificate
static void enc_leaf(BW& w, const std::vector<int>& labels, const std::vector<int>& dom, const Cert* c) {
  if (labels.size() > 31) throw std::runtime_error("cert field overflow: n > 31");
  w.put(1, 1);
  w.put(labels.size(), 6);
  for (int a : labels) w.put(a, 9);
  w.put(1, 2);
  u64 mw[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  for (int X : dom) mw[X >> 6] |= 1ULL << (X & 63);
  for (int i = 0; i < 8; i++) w.put(mw[i], 64);
  enc_cert(w, c);
}

// ------------------------------------------------------------------------------------------------ one leaf
struct XT { uint16_t lo[64], hi[64]; };
static inline void mkxt(const uint32_t* P, XT& t) {
  uint16_t v[12]; for (int h = 0; h < 12; h++) v[h] = (uint16_t)((P[h] >> 12) & 4095);
  t.lo[0] = 0; for (int i = 1; i < 64; i++) { int h = __builtin_ctz(i); t.lo[i] = t.lo[i & (i - 1)] ^ v[h]; }
  t.hi[0] = 0; for (int i = 1; i < 64; i++) { int h = __builtin_ctz(i); t.hi[i] = t.hi[i & (i - 1)] ^ v[6 + h]; }
}
struct Rec { int X; uint32_t P[12]; int PM; M lm, rm; XT xt; };
struct Slk { M lm, rm; };
struct Asg { int a, b, c, t; };

struct Leaf {
  const Tables& Tb;
  std::vector<int> terms; std::vector<int> dom;         // dom_list, ascending
  int n; uint32_t hxm[512];                             // terms through X
  long long cnt = 0, maxnodes = 300000; int deadk = 6, K = 4;
  bool symroot = true;                                   // sym at the root; false only to compare certificate sizes
  // fit: the overflow fallback.  enc_cert writes |NT| in 4 bits and |SL| in 3; with fit, a node's chosen sets are cut to 15 / 7
  // (dropping the entry whose removal leaves the fewest candidates; the extra candidates become kids, refuted as usual) and
  // hoist lifts at most 15 - |NT| claims (the most shared).  Off by default.
  bool fit = false; size_t fitNT = 15, fitSL = 7;        // the caps are 15 / 7 (the field widths); smaller values only for tests
  std::vector<Asg> sol;                                  // the decomposition, when Sat is thrown
  // follow (test hook): the planted-path test.  The decomposition F->B, F->C of a SAT leaf is followed down the tree: at every
  // branch node its pair for the node's term must be among the candidates (rgen throws FollowFail otherwise), only that kid is
  // generated, and no OVER may occur on the path; at the root with sym the whole decomposition is first moved by S in GL4 (the
  // witness pairs WB, WC of the table file) so that the pair of the root's term lies in ORBM x CORB.  Reaching the end throws Sat.
  struct Follow { std::vector<int> B, C; const s334::SymTab* st = nullptr; bool moved = false; std::vector<size_t> listsizes; };
  struct FollowFail : std::runtime_error { explicit FollowFail(const std::string& m) : std::runtime_error(m) {} };
  Follow* follow = nullptr;
  std::deque<Cert> pool;
  Leaf(const std::vector<int>& tm, const std::vector<int>& dl) : Tb(T()), terms(tm), dom(dl), n((int)tm.size()) {
    if (n > 32) throw std::runtime_error("more than 32 terms");
    for (int X = 0; X < 512; X++) { uint32_t m = 0; for (int s = 0; s < n; s++) if (Tb.PAR[terms[s] & X]) m |= 1u << s; hxm[X] = m; }
  }
  Cert* mk() { pool.emplace_back(); return &pool.back(); }
  int ucnt(uint32_t act, int X) const { return __builtin_popcount(hxm[X] & act); }
  bool noasg(int X, const std::vector<Asg>& asg) const { for (auto& g : asg) if (Tb.PAR[g.a & X]) return false; return true; }
  void resC(int X, const std::vector<Asg>& asg, uint32_t* Ms) const {
    uint32_t Mr[12]; Tb.resRoot(X, Ms, Mr);
    for (auto& g : asg) if (Tb.PAR[g.a & X]) for (int z = 0; z < 12; z++) if ((g.c >> z) & 1) Ms[z] ^= (uint32_t)g.b;
  }
  void resR(int X, const std::vector<Asg>& asg, uint32_t* Ms) const {
    uint32_t Mc[12]; Tb.resRoot(X, Mc, Ms);
    for (auto& g : asg) if (Tb.PAR[g.a & X]) for (int y = 0; y < 12; y++) if ((g.b >> y) & 1) Ms[y] ^= (uint32_t)g.c;
  }
  // rank of R(X)
  int rankR(int X, const std::vector<Asg>& asg, bool* ok = nullptr) const {
    uint32_t Ms[12], P[12]; int PM, rk; resC(X, asg, Ms); Tables::elim(Ms, P, PM, rk);
    if (ok) *ok = Tables::elim_ok(Ms, P, PM);
    return rk;
  }
  bool mkrec(int X, uint32_t act, const std::vector<Asg>& asg, Rec& r) const {
    if (noasg(X, asg)) {
      auto& R = Tb.ROOT[X]; if (R.rk < ucnt(act, X)) return false;
      r.X = X; memcpy(r.P, R.P, sizeof r.P); r.PM = R.PM; r.lm = R.lm; r.rm = R.rm;
      memcpy(r.xt.lo, R.xlo, sizeof r.xt.lo); memcpy(r.xt.hi, R.xhi, sizeof r.xt.hi); return true;
    }
    uint32_t Ms[12], P[12]; int PM, rk; resC(X, asg, Ms); Tables::elim(Ms, P, PM, rk);
    if (!Tables::elim_ok(Ms, P, PM) || rk < ucnt(act, X)) return false;
    r.X = X; memcpy(r.P, P, sizeof P); r.PM = PM; r.lm = Tb.lm_compl(P, PM); r.rm = Tb.ker_mask(Ms); mkxt(P, r.xt); return true;
  }
  bool mkslack(int X, uint32_t act, const std::vector<Asg>& asg, Slk& s) const {
    if (noasg(X, asg)) {
      auto& R = Tb.ROOT[X]; if (R.rk + 1 < ucnt(act, X)) return false;
      s.lm = R.lm2; s.rm = R.rm; return true;
    }
    uint32_t Ms[12], P[12]; int PM, rk; resC(X, asg, Ms); Tables::elim(Ms, P, PM, rk);
    if (!Tables::elim_ok(Ms, P, PM) || rk + 1 < ucnt(act, X)) return false;
    uint32_t M2[12], P2[12]; int PM2, rk2; resR(X, asg, M2); Tables::elim(M2, P2, PM2, rk2);
    if (!Tables::elim_ok(M2, P2, PM2)) return false;
    s.lm = Tb.ker_mask(M2); s.rm = Tb.ker_mask(Ms); return true;
  }
  Rec upd(const Rec& r, int a, int b, int c) const {
    if (!Tb.PAR[r.X & a]) return r;
    Rec q = r; q.lm = mand(r.lm, Tb.perp(Tables::gof(r.P, c))); q.rm = mand(r.rm, Tb.perp(Tables::xof(r.P, b))); return q;
  }
  // candidates of a branch node, in the order of the checker rules (b ascending then c ascending; with cdir: c then b)
  void cands(const std::vector<const Rec*>& recs, const std::vector<const Slk*>& slack, bool sym, bool cdir,
             std::vector<std::pair<int, int>>& out) const {
    out.clear();
    M B = mand(Tb.ALLNZ, sym ? Tb.ORBM : Tb.M4096F), Cb = Tb.ALLNZ;
    for (auto* r : recs) B = mand(B, r->lm);
    if (mz(B)) return;
    for (auto* r : recs) Cb = mand(Cb, r->rm);
    if (!cdir) {
      mbits(B, [&](int b) {
        M m = Cb; int bl = b & 63, bh = b >> 6;
        for (auto* r : recs) m = mand(m, Tb.NPM[r->xt.lo[bl] ^ r->xt.hi[bh]]);
        for (auto* s : slack) if (!mbit(s->lm, b)) m = mand(m, s->rm);
        if (sym) m = mand(m, Tb.CORB[b]);
        mbits(m, [&](int c) { out.push_back({b, c}); });
      });
    } else {
      mbits(Cb, [&](int c) {
        M m = B;
        for (auto* r : recs) m = mand(m, Tb.NPM[Tables::gof(r->P, c)]);
        for (auto* s : slack) if (!mbit(s->rm, c)) m = mand(m, s->lm);
        mbits(m, [&](int b) { out.push_back({b, c}); });
      });
    }
  }
  std::pair<int, int> domsize(const std::vector<const Rec*>& recs, bool sym) const {
    M B = mand(Tb.ALLNZ, sym ? Tb.ORBM : Tb.M4096F), C = Tb.ALLNZ;
    for (auto* r : recs) { B = mand(B, r->lm); C = mand(C, r->rm); }
    return {mpop(B), mpop(C)};
  }
  // Python's float expression CT*nt + CS*ns + (CE + CR*len(part)) * n, each operation rounded to double
  static double node_cost(int nt, int ns, size_t npart, int nb, int nc, bool cdir) {
    const double CT = 3.0, CS = 6.0, CE = 0.2, CR = 0.3;
    volatile double a = CT * (double)nt; volatile double b = CS * (double)ns; volatile double c = CR * (double)npart;
    volatile double d = CE + c; volatile double e = d * (double)(cdir ? nc : nb); volatile double f = a + b;
    return f + e;
  }

  // ---- look-ahead analysis
  struct Info { int rk, u; };
  // returns -1 = live (info filled), -2 = SAT (all terms assigned, no OVER), X >= 0 = OVER(X)
  int analyze(uint32_t act, const std::vector<Asg>& asg, const std::vector<Info>* info0, int a_new, std::vector<Info>& info) const {
    info.assign(512, Info{0, 0});
    for (int X : dom) {
      if (info0 && !Tb.PAR[X & a_new]) { info[X] = (*info0)[X]; continue; }
      int rk = rankR(X, asg); int u = ucnt(act, X);
      if (rk > u) return X;
      info[X] = Info{rk, u};
    }
    if (!act) return -2;
    return -1;
  }
  // memoised records of a node
  struct Node {
    const Leaf* L; uint32_t act; const std::vector<Asg>* asg; const std::vector<Rec>* recs; bool sym;
    M have; std::vector<int> tight, slack;
    int16_t ri[512], si[512];               // memo indices (-1: not computed, -2: failed)
    std::deque<Rec> rv; std::deque<Slk> sv;   // stable addresses
    // the parent node and the new term: for X with par(X & anew) = 0 the records are the parent's (same R(X), same count)
    Node* par = nullptr; int anew = 0;
    Node(const Leaf* L_, uint32_t act_, const std::vector<Asg>* asg_, const std::vector<Rec>* recs_, const std::vector<Info>& info,
         Node* par_ = nullptr, int anew_ = 0)
      : L(L_), act(act_), asg(asg_), recs(recs_), sym(asg_->empty() && L_->symroot), have(mzero()), par(par_), anew(anew_) {
      for (int i = 0; i < 512; i++) { ri[i] = -1; si[i] = -1; }
      for (auto& r : *recs) mset(have, r.X);
      for (int X : L->dom) { if (info[X].rk >= info[X].u) tight.push_back(X); if (info[X].rk + 1 == info[X].u) slack.push_back(X); }
    }
    const Rec* rec_of(int X) {
      if (par && !L->Tb.PAR[X & anew]) return par->rec_of(X);
      if (ri[X] == -1) { Rec r; if (L->mkrec(X, act, *asg, r)) { ri[X] = (int16_t)rv.size(); rv.push_back(r); } else ri[X] = -2; }
      if (ri[X] < 0) throw std::runtime_error("rec_of: not tight");
      return &rv[ri[X]];
    }
    const Slk* sl_of(int X) {
      if (par && !L->Tb.PAR[X & anew]) return par->sl_of(X);
      if (si[X] == -1) { Slk q; if (L->mkslack(X, act, *asg, q)) { si[X] = (int16_t)sv.size(); sv.push_back(q); } else si[X] = -2; }
      if (si[X] < 0) throw std::runtime_error("sl_of: not slack");
      return &sv[si[X]];
    }
    void term_data(int t, std::vector<const Rec*>& inh, std::vector<int>& NT, std::vector<int>& SL) const {
      int a = L->terms[t]; inh.clear(); NT.clear(); SL.clear();
      for (auto& r : *recs) if (L->Tb.PAR[r.X & a]) inh.push_back(&r);
      for (int X : tight) if (L->Tb.PAR[X & a] && !mbit(have, X)) NT.push_back(X);
      for (int X : slack) if (L->Tb.PAR[X & a]) SL.push_back(X);
    }
  };
  void part_of(Node& nd, const std::vector<const Rec*>& inh, const std::vector<int>& NT, std::vector<const Rec*>& part) {
    part = inh; for (int X : NT) part.push_back(nd.rec_of(X));
  }
  void slacks_of(Node& nd, const std::vector<int>& SL, std::vector<const Slk*>& sl) { sl.clear(); for (int X : SL) sl.push_back(nd.sl_of(X)); }
  size_t full_cands(Node& nd, int t, const std::vector<const Rec*>& inh, const std::vector<int>& NT, const std::vector<int>& SL,
                    std::vector<std::pair<int, int>>* out) {
    std::vector<const Rec*> part; part_of(nd, inh, NT, part); std::vector<const Slk*> sl; slacks_of(nd, SL, sl);
    std::vector<std::pair<int, int>> tmp; cands(part, sl, nd.sym, false, out ? *out : tmp);
    (void)t;
    return out ? out->size() : tmp.size();
  }
  // the number of candidates of term t, or some value >= lim once the count reaches lim (exact below lim)
  long long count_cands(Node& nd, int t, const std::vector<const Rec*>& inh, const std::vector<int>& NT, const std::vector<int>& SL, long long lim) {
    (void)t;
    std::vector<const Rec*>& part = sc_part; part_of(nd, inh, NT, part); std::vector<const Slk*>& sl = sc_sl; slacks_of(nd, SL, sl);
    bool sym = nd.sym;
    M B = mand(Tb.ALLNZ, sym ? Tb.ORBM : Tb.M4096F), Cb = Tb.ALLNZ;
    for (auto* r : part) B = mand(B, r->lm);
    if (mz(B)) return 0;
    for (auto* r : part) Cb = mand(Cb, r->rm);
    long long cnt_ = 0;
    for (int q = 0; q < NW; q++) for (u64 x = B.w[q]; x; x &= x - 1) {
      int b = 64 * q + __builtin_ctzll(x);
      M m = cmask(part, sl, sym, Cb, b);
      cnt_ += mpop(m);
      if (cnt_ >= lim) return cnt_;
    }
    return cnt_;
  }
  long long min_cands(uint32_t act, const std::vector<Asg>& asg, const std::vector<Rec>& recs, const std::vector<Info>& info0, int a_new, long long bound,
                      Node* pnd = nullptr) {
    std::vector<Info> info; int r = analyze(act, asg, &info0, a_new, info);
    if (r >= 0) return 0;
    if (r == -2) return 1000000000LL;
    Node nd(this, act, &asg, &recs, info, pnd, a_new);
    long long best = bound; std::vector<const Rec*> inh; std::vector<int> NT, SL;
    for (int t = 0; t < n; t++) if ((act >> t) & 1) {
      nd.term_data(t, inh, NT, SL);
      long long k = count_cands(nd, t, inh, NT, SL, best);
      if (k < best) { best = k; if (best == 0) break; }
    }
    return best;
  }
  // ---- generation
  struct Opt { size_t n0; int t; int a; std::vector<const Rec*> inh; std::vector<int> NT, SL; std::vector<std::pair<int, int>> target; };
  // the c-mask of b: Cb, the records' NPM[xof], the slacks, CORB (sym)
  bool use_corb = true;   // false only in the test hook root_counts()
  M cmask(const std::vector<const Rec*>& part, const std::vector<const Slk*>& sl, bool sym, const M& Cb, int b) const {
    M m = Cb; int bl = b & 63, bh = b >> 6;
    for (auto* r : part) m = mand(m, Tb.NPM[r->xt.lo[bl] ^ r->xt.hi[bh]]);
    for (auto* s : sl) if (!mbit(s->lm, b)) m = mand(m, s->rm);
    if (sym && use_corb) m = mand(m, Tb.CORB[b]);
    return m;
  }
  // test hook (cross-check against tsolve334's candidates()): at the root, the number of candidates (b, c), c != 0, of every term with
  // all claims, with b restricted to ORBM (sym) or not, and without the CORB filter; nts[t] = the number of tight claims through a_t.
  // counts[t] = -1 for all t if the root is refuted by an OVER.
  void root_counts(bool sym, std::vector<long long>& counts, std::vector<int>& nts) {
    std::vector<Asg> asg; std::vector<Rec> recs; std::vector<Info> info;
    uint32_t act = n == 32 ? 0xffffffffu : ((1u << n) - 1);
    counts.assign(n, -1); nts.assign(n, 0);
    if (analyze(act, asg, nullptr, 0, info) != -1) return;
    Node nd(this, act, &asg, &recs, info, nullptr, 0);
    nd.sym = sym; use_corb = false;
    for (int t = 0; t < n; t++) {
      std::vector<const Rec*> inh; std::vector<int> NT, SL; nd.term_data(t, inh, NT, SL);
      counts[t] = count_cands(nd, t, inh, NT, SL, LLONG_MAX); nts[t] = (int)NT.size();
    }
    use_corb = true;
  }
  // target as per-b masks (TB = the b's of target, TM[b] = their c's); built once per minimize call
  M TB = mzero(); std::vector<M> TM = std::vector<M>(4096);
  void set_target(const std::vector<std::pair<int, int>>& target) {
    mbits(TB, [&](int b) { TM[b] = mzero(); });
    TB = mzero();
    for (auto& [b, c] : target) { if (!mbit(TB, b)) { mset(TB, b); TM[b] = mzero(); } mset(TM[b], c); }
  }
  // cands(part, sl, sym, false) == target, decided per b without listing the pairs (exact)
  bool okset(Node& nd, const std::vector<const Rec*>& inh, const std::vector<int>& NT2, const std::vector<int>& SL2, const std::vector<std::pair<int, int>>& target) {
    (void)target;
    std::vector<const Rec*>& part = sc_part; part_of(nd, inh, NT2, part); std::vector<const Slk*>& sl = sc_sl; slacks_of(nd, SL2, sl);
    bool sym = nd.sym;
    M B = mand(Tb.ALLNZ, sym ? Tb.ORBM : Tb.M4096F), Cb = Tb.ALLNZ;
    for (auto* r : part) B = mand(B, r->lm);
    // every target b must stay in B (cands lists only b in B)
    for (int i = 0; i < NW; i++) if (TB.w[i] & ~B.w[i]) return false;
    if (mz(B)) return true;   // no candidates; TB is empty here
    for (auto* r : part) Cb = mand(Cb, r->rm);
    for (int q = 0; q < NW; q++) for (u64 x = B.w[q]; x; x &= x - 1) {
      int b = 64 * q + __builtin_ctzll(x);
      M m = cmask(part, sl, sym, Cb, b);
      if (mbit(TB, b)) { if (!meq(m, TM[b])) return false; }
      else if (!mz(m)) return false;
    }
    return true;
  }
  std::vector<const Rec*> sc_part; std::vector<const Slk*> sc_sl; std::vector<M> sc_pb, sc_pc, sc_sb, sc_sc;
  double costset(Node& nd, const std::vector<const Rec*>& inh, const std::vector<int>& NT2, const std::vector<int>& SL2) {
    std::vector<const Rec*> part; part_of(nd, inh, NT2, part);
    auto [nb, nc] = domsize(part, nd.sym);
    return node_cost((int)NT2.size(), (int)SL2.size(), part.size(), nb, nc, (nc < nb) && !nd.sym);
  }
  void fitset(Node& nd, const std::vector<const Rec*>& inh, std::vector<int>& NT, std::vector<int>& SL) {
    for (int li = 0; li < 2; li++) {
      std::vector<int>& lst = li == 0 ? SL : NT; size_t cap = li == 0 ? fitSL : fitNT;
      while (lst.size() > cap) {
        size_t bi = 0, bn = SIZE_MAX;
        for (size_t i = 0; i < lst.size(); i++) {
          int X = lst[i]; lst.erase(lst.begin() + i);
          std::vector<const Rec*> part; part_of(nd, inh, NT, part); std::vector<const Slk*> sl; slacks_of(nd, SL, sl);
          std::vector<std::pair<int, int>> cs; cands(part, sl, nd.sym, false, cs);
          if (cs.size() < bn) { bn = cs.size(); bi = i; }
          lst.insert(lst.begin() + i, X);
        }
        lst.erase(lst.begin() + bi);
      }
    }
  }
  struct MinRes { double c; std::vector<int> NT, SL; };
  MinRes minimize(Node& nd, const std::vector<const Rec*>& inh, std::vector<int> NT, std::vector<int> SL, const std::vector<std::pair<int, int>>& target) {
    set_target(target);
    double cur = costset(nd, inh, NT, SL);
    bool improved = true;
    // among removals that keep the candidates (okset) and do not raise the cost, one of least cost, the first in (SL, NT) order on
    // ties.  Testing removals by (cost, order) and taking the first that passes okset is the same.
    struct Rm { double c; int li; size_t i; };
    std::vector<Rm> rms;
    while (improved) {
      improved = false;
      rms.clear();
      {   // the cost of every single removal: costset's domsize by prefix / suffix ANDs (same masks, same node_cost arguments)
        bool sym = nd.sym;
        M B0 = mand(Tb.ALLNZ, sym ? Tb.ORBM : Tb.M4096F), C0 = Tb.ALLNZ;
        for (auto* r : inh) { B0 = mand(B0, r->lm); C0 = mand(C0, r->rm); }
        size_t k = NT.size();
        std::vector<const Rec*>& nr = sc_part; nr.clear(); for (int X : NT) nr.push_back(nd.rec_of(X));
        std::vector<M>& pb = sc_pb; std::vector<M>& pc = sc_pc; pb.resize(k + 1); pc.resize(k + 1);
        std::vector<M>& sb = sc_sb; std::vector<M>& scm = sc_sc; sb.resize(k + 1); scm.resize(k + 1);
        pb[0] = B0; pc[0] = C0;
        for (size_t j = 0; j < k; j++) { pb[j + 1] = mand(pb[j], nr[j]->lm); pc[j + 1] = mand(pc[j], nr[j]->rm); }
        sb[k] = Tb.M4096F; scm[k] = Tb.M4096F;
        for (size_t j = k; j > 0; j--) { sb[j - 1] = mand(sb[j], nr[j - 1]->lm); scm[j - 1] = mand(scm[j], nr[j - 1]->rm); }
        size_t np = inh.size() + k;
        int nbA = mpop(pb[k]), ncA = mpop(pc[k]);
        for (size_t i = 0; i < SL.size(); i++) {
          double c = node_cost((int)k, (int)SL.size() - 1, np, nbA, ncA, (ncA < nbA) && !sym);
          if (c <= cur) rms.push_back(Rm{c, 0, i});
        }
        for (size_t j = 0; j < k; j++) {
          int nb = mpop(mand(pb[j], sb[j + 1])), nc = mpop(mand(pc[j], scm[j + 1]));
          double c = node_cost((int)k - 1, (int)SL.size(), np - 1, nb, nc, (nc < nb) && !sym);
          if (c <= cur) rms.push_back(Rm{c, 1, j});
        }
      }
      std::stable_sort(rms.begin(), rms.end(), [](const Rm& x, const Rm& y) { return x.c < y.c; });
      for (auto& r : rms) {
        std::vector<int>& lst = r.li == 0 ? SL : NT;
        int X = lst[r.i]; lst.erase(lst.begin() + r.i);
        if (okset(nd, inh, NT, SL, target)) { cur = r.c; improved = true; break; }
        lst.insert(lst.begin() + r.i, X);
      }
    }
    return MinRes{cur, NT, SL};
  }
  Cert* rgen(uint32_t act, const std::vector<Asg>& asg, const std::vector<Rec>& recs, const std::vector<Info>* info0, int a_new,
             Node* pnd = nullptr) {
    if (++cnt > maxnodes) throw Big();
    std::vector<Info> info; int r = analyze(act, asg, info0, a_new, info);
    if (r >= 0 && follow) throw FollowFail("the planted decomposition is refuted by OVER(X=" + std::to_string(r) + ") after " + std::to_string(asg.size()) + " assigned terms");
    if (r >= 0) { Cert* c = mk(); c->over = true; c->X = r; return c; }
    if (r == -2) { sol = asg; throw Sat(); }   // every term assigned: a decomposition of the leaf's tensor
    Node nd(this, act, &asg, &recs, info, pnd, a_new);
    bool sym = nd.sym;
    // Only the first max(K, deadk) options of the stable sort by (n0, |NT| + 2|SL|) are ever used.  Keep them in a sorted
    // list while scanning the terms in index order; once it is full, a term needs an exact count only up to the last kept
    // n0 (count_cands stops beyond it).  The kept list equals the prefix of the full stable sort.
    std::vector<Opt> opts;
    size_t keep = (size_t)std::max(std::max(K, 1), deadk);
    auto before = [](const Opt& x, const Opt& y) {
      if (x.n0 != y.n0) return x.n0 < y.n0;
      return x.NT.size() + 2 * x.SL.size() < y.NT.size() + 2 * y.SL.size();
    };
    for (int t = 0; t < n; t++) if ((act >> t) & 1) {
      Opt o; o.t = t; o.a = terms[t]; nd.term_data(t, o.inh, o.NT, o.SL);
      long long lim = opts.size() < keep ? LLONG_MAX : (long long)opts.back().n0 + 1;
      long long k = count_cands(nd, t, o.inh, o.NT, o.SL, lim);
      if (k >= lim) continue;   // strictly after every kept option
      o.n0 = (size_t)k;
      // insert after every kept option that is not after o (stable: o comes later in index order)
      size_t pos = opts.size();
      while (pos > 0 && before(o, opts[pos - 1])) pos--;
      if (pos >= keep) continue;
      opts.insert(opts.begin() + pos, std::move(o));
      if (opts.size() > keep) opts.pop_back();
    }
    // the candidate lists, only where they are used: the look-ahead's first K options (live case)
    if (opts[0].n0 != 0)
      for (size_t oi = 0; oi < opts.size() && (int)oi < std::max(K, 1); oi++)
        full_cands(nd, opts[oi].t, opts[oi].inh, opts[oi].NT, opts[oi].SL, &opts[oi].target);
    bool hb = false; double bc = 0; int bt = -1, ba = 0; std::vector<const Rec*> binh; std::vector<int> bNT, bSL;
    if (opts[0].n0 == 0) {
      for (size_t oi = 0; oi < opts.size() && (int)oi < deadk; oi++) {
        Opt& o = opts[oi]; if (o.n0) break;
        std::vector<MinRes> sets; sets.push_back(minimize(nd, o.inh, o.NT, o.SL, {}));
        if (!sym) {
          std::vector<int> chosen, pool = o.NT;
          auto mind = [&](const std::vector<int>& ch) { std::vector<const Rec*> part; part_of(nd, o.inh, ch, part); auto d = domsize(part, sym); return std::min(d.first, d.second); };
          while (!pool.empty() && mind(chosen) > 0) {
            size_t bi = 0; int bv = INT_MAX;
            for (size_t i = 0; i < pool.size(); i++) { std::vector<int> ch = chosen; ch.push_back(pool[i]); int v = mind(ch); if (v < bv) { bv = v; bi = i; } }
            chosen.push_back(pool[bi]); pool.erase(pool.begin() + bi);
          }
          if (mind(chosen) == 0) sets.push_back(minimize(nd, o.inh, chosen, {}, {}));
        }
        for (auto& s : sets) if (!hb || s.c < bc) { hb = true; bc = s.c; bt = o.t; ba = o.a; binh = o.inh; bNT = s.NT; bSL = s.SL; }
      }
    } else {
      size_t pick = 0;
      if (K > 1) {
        bool hs = false; long long bsc = 0;
        for (size_t oi = 0; oi < opts.size() && (int)oi < K; oi++) {
          Opt& o = opts[oi]; if (o.n0 == 0) continue;
          std::vector<Rec> allrecs = recs; for (int X : o.NT) allrecs.push_back(*nd.rec_of(X));
          uint32_t act2 = act ^ (1u << o.t); long long sc = 0;
          for (auto& [b, c] : o.target) {
            if (hs && sc >= bsc) break;
            std::vector<Asg> asg2; asg2.reserve(asg.size() + 1); asg2.push_back(Asg{o.a, b, c, o.t}); asg2.insert(asg2.end(), asg.begin(), asg.end());
            std::vector<Rec> recs2; recs2.reserve(allrecs.size()); for (auto& q : allrecs) recs2.push_back(upd(q, o.a, b, c));
            long long mc = min_cands(act2, asg2, recs2, info, o.a, hs ? std::max(1LL, bsc - sc) : 1000000000LL, &nd);
            sc += mc == 0 ? 1 : 1 + mc;
          }
          if (!hs || sc < bsc) { hs = true; bsc = sc; pick = oi; }
        }
      }
      Opt& o = opts[pick];
      MinRes m = minimize(nd, o.inh, o.NT, o.SL, o.target);
      hb = true; bc = m.c; bt = o.t; ba = o.a; binh = o.inh; bNT = m.NT; bSL = m.SL;
    }
    if (fit) fitset(nd, binh, bNT, bSL);
    std::vector<const Rec*> part; part_of(nd, binh, bNT, part);
    auto [nb, nc] = domsize(part, sym);
    bool cdir = (nc < nb) && !sym;
    std::vector<const Slk*> sl; slacks_of(nd, bSL, sl);
    std::vector<std::pair<int, int>> cs; cands(part, sl, sym, cdir, cs);
    std::vector<Rec> allrecs = recs; for (int X : bNT) allrecs.push_back(*nd.rec_of(X));
    uint32_t act2 = act ^ (1u << bt);
    Cert* out = mk(); out->t = bt; out->NT = bNT; out->SL = bSL; out->sym = sym; out->cdir = cdir;
    if (follow) {   // planted-path test: only the planted pair's kid
      if (sym && !follow->moved) {   // move the planted decomposition by S = S1 S2 so that term bt gets (b, c) in ORBM x CORB[b]
        const s334::SymTab& st = *follow->st;
        int b0 = follow->B[bt], c0 = follow->C[bt];
        int S1 = st.wb[b0][0], S1i = st.wb[b0][1], o = s334::mulBS(b0, S1), c1 = s334::mulSC(S1i, c0);
        const auto& w = st.wc.at(o)[c1]; int S2 = w[0], S2i = w[1];
        int S = s334::mul44(S1, S2), Si = s334::mul44(S2i, S1i);
        for (size_t s = 0; s < follow->B.size(); s++) { follow->B[s] = s334::mulBS(follow->B[s], S); follow->C[s] = s334::mulSC(Si, follow->C[s]); }
        follow->moved = true;
      }
      int pb = follow->B[bt], pc = follow->C[bt]; bool found = false;
      for (auto& [b, c] : cs) if (b == pb && c == pc) { found = true; break; }
      follow->listsizes.push_back(cs.size());
      if (!found) throw FollowFail("planted pair (b=" + std::to_string(pb) + ", c=" + std::to_string(pc) + ") of term " + std::to_string(bt) +
                                   " is not among the " + std::to_string(cs.size()) + " candidates at depth " + std::to_string(asg.size()) +
                                   (sym ? " (sym node)" : "") + (cdir ? " (cdir)" : ""));
      std::vector<Asg> asg2; asg2.reserve(asg.size() + 1); asg2.push_back(Asg{ba, pb, pc, bt}); asg2.insert(asg2.end(), asg.begin(), asg.end());
      std::vector<Rec> recs2; recs2.reserve(allrecs.size()); for (auto& q : allrecs) recs2.push_back(upd(q, ba, pb, pc));
      out->kids.push_back(rgen(act2, asg2, recs2, &info, ba, &nd));
      return out;
    }
    for (auto& [b, c] : cs) {
      std::vector<Asg> asg2; asg2.reserve(asg.size() + 1); asg2.push_back(Asg{ba, b, c, bt}); asg2.insert(asg2.end(), asg.begin(), asg.end());
      std::vector<Rec> recs2; recs2.reserve(allrecs.size()); for (auto& q : allrecs) recs2.push_back(upd(q, ba, b, c));
      out->kids.push_back(rgen(act2, asg2, recs2, &info, ba, &nd));
    }
    (void)hb; (void)bc;
    return out;
  }
  Cert* gen(int K_ = 4, long long maxnodes_ = 300000, int deadk_ = 6) {
    K = K_; maxnodes = maxnodes_; deadk = deadk_; cnt = 0;
    std::vector<Asg> asg; std::vector<Rec> recs;
    return rgen(n == 32 ? 0xffffffffu : ((1u << n) - 1), asg, recs, nullptr, 0);
  }

  // ---- SAT search (outside the certificate machinery; its only output is a verified decomposition or "none within budget")
  // Depth-first search with every claim (the smallest candidate lists), the term with the fewest candidates (random among ties),
  // candidates in random order, a node budget per run; sat_search() restarts it with doubling budgets.  A decomposition found
  // here is a decomposition, whatever the order in which it was found (the caller verifies it against T anyway); the sym move
  // at the root is complete for decompositions (the pair symmetry fixes every slice).  A run that finishes without exception proves "no decomposition".
  struct Restart {};
  long long sbudget = 0; std::mt19937_64 rng{1}; bool srandom = true;
  bool sat_dfs(uint32_t act, const std::vector<Asg>& asg, const std::vector<Rec>& recs, const std::vector<Info>* info0, int a_new, Node* pnd) {
    if (++cnt > sbudget) throw Restart();
    std::vector<Info> info; int r = analyze(act, asg, info0, a_new, info);
    if (r >= 0) return false;
    if (r == -2) { sol = asg; return true; }
    Node nd(this, act, &asg, &recs, info, pnd, a_new);
    long long bk = LLONG_MAX; int bt = -1, nties = 0;
    std::vector<const Rec*> binh; std::vector<int> bNT, bSL;
    for (int t = 0; t < n; t++) if ((act >> t) & 1) {
      std::vector<const Rec*> inh; std::vector<int> NT, SL; nd.term_data(t, inh, NT, SL);
      long long lim = (bk == LLONG_MAX) ? LLONG_MAX : bk + 1;
      long long k = count_cands(nd, t, inh, NT, SL, lim);
      if (k < bk) { bk = k; bt = t; nties = 1; binh = inh; bNT = NT; bSL = SL; if (bk == 0) break; }
      else if (k == bk && srandom) { nties++; if (rng() % (u64)nties == 0) { bt = t; binh = inh; bNT = NT; bSL = SL; } }
    }
    if (bk == 0) return false;
    std::vector<const Rec*> part; part_of(nd, binh, bNT, part);
    std::vector<const Slk*> sl; slacks_of(nd, bSL, sl);
    std::vector<std::pair<int, int>> cs; cands(part, sl, nd.sym, false, cs);
    if (srandom) std::shuffle(cs.begin(), cs.end(), rng);
    std::vector<Rec> allrecs = recs; for (int X : bNT) allrecs.push_back(*nd.rec_of(X));
    uint32_t act2 = act ^ (1u << bt); int ba = terms[bt];
    for (auto& [b, c] : cs) {
      std::vector<Asg> asg2; asg2.reserve(asg.size() + 1); asg2.push_back(Asg{ba, b, c, bt}); asg2.insert(asg2.end(), asg.begin(), asg.end());
      std::vector<Rec> recs2; recs2.reserve(allrecs.size()); for (auto& q : allrecs) recs2.push_back(upd(q, ba, b, c));
      if (sat_dfs(act2, asg2, recs2, &info, ba, &nd)) return true;
    }
    return false;
  }
  // 1 = decomposition found (sol), 0 = none exists (a run completed), -1 = total budget exhausted
  int sat_search(long long total, long long first, uint64_t seed, long long* used = nullptr) {
    rng.seed(seed); srandom = true; long long spent = 0, b = first; int res = -1;
    std::vector<Asg> asg; std::vector<Rec> recs; uint32_t all = n == 32 ? 0xffffffffu : ((1u << n) - 1);
    while (spent < total) {
      sbudget = std::min(b, total - spent); cnt = 0;
      try { res = sat_dfs(all, asg, recs, nullptr, 0, nullptr) ? 1 : 0; spent += cnt; break; }
      catch (Restart&) { spent += sbudget; res = -1; }
      b *= 2;
    }
    if (used) *used = spent;
    return res;
  }

  // ---- finalize = hoist(attach_cands(cert))
  void mkrecs(const std::vector<int>& NT, uint32_t act, const std::vector<Asg>& asg, std::vector<Rec>& out) const {
    for (int X : NT) { Rec r; if (!mkrec(X, act, asg, r)) throw std::runtime_error("finalize: claim not tight"); out.push_back(r); }
  }
  void attach(Cert* c, uint32_t act, const std::vector<Asg>& asg, const std::vector<Rec>& recs) {
    if (c->over) return;
    int a = terms[c->t];
    std::vector<Rec> allrecs = recs; mkrecs(c->NT, act, asg, allrecs);
    std::vector<const Rec*> part; for (auto& r : allrecs) if (Tb.PAR[r.X & a]) part.push_back(&r);
    std::vector<Slk> slv(c->SL.size()); std::vector<const Slk*> sl;
    for (size_t i = 0; i < c->SL.size(); i++) { if (!mkslack(c->SL[i], act, asg, slv[i])) throw std::runtime_error("finalize: slack"); sl.push_back(&slv[i]); }
    cands(part, sl, c->sym, c->cdir, c->cs);
    if (c->cs.size() != c->kids.size()) throw std::runtime_error("attach: candidate count");
    uint32_t act2 = act ^ (1u << c->t);
    for (size_t i = 0; i < c->kids.size(); i++) {
      auto [b, cc] = c->cs[i];
      std::vector<Asg> asg2; asg2.push_back(Asg{a, b, cc, c->t}); asg2.insert(asg2.end(), asg.begin(), asg.end());
      std::vector<Rec> recs2; for (auto& q : allrecs) recs2.push_back(upd(q, a, b, cc));
      attach(c->kids[i], act2, asg2, recs2);
    }
  }
  static void claimed_below(const Cert* c, std::set<int>& s) { if (c->over) return; for (int X : c->NT) s.insert(X); for (auto* k : c->kids) claimed_below(k, s); }
  Cert* strip(const Cert* c, const std::set<int>& ex) {
    if (c->over) return const_cast<Cert*>(c);
    Cert* d = mk(); *d = *c; d->NT.clear(); for (int X : c->NT) if (!ex.count(X)) d->NT.push_back(X);
    for (auto& k : d->kids) k = strip(k, ex);
    return d;
  }
  bool tight_at(int X, uint32_t act, const std::vector<Asg>& asg) const { bool ok; int rk = rankR(X, asg, &ok); return ok && rk >= ucnt(act, X); }
  Cert* hoist(const Cert* c, uint32_t act, const std::vector<Asg>& asg, const std::vector<Rec>& recs) {
    if (c->over) return const_cast<Cert*>(c);
    std::set<int> have; for (auto& r : recs) have.insert(r.X); for (int X : c->NT) have.insert(X);
    std::map<int, int> cntX;
    for (auto* k : c->kids) { std::set<int> s; claimed_below(k, s); for (int X : s) cntX[X]++; }
    std::vector<int> extra;   // sorted (std::map order)
    for (auto& [X, m] : cntX) if (m >= 2 && !have.count(X) && tight_at(X, act, asg)) extra.push_back(X);
    if (fit && c->NT.size() + extra.size() > fitNT) {   // keep the most shared claims, then X order
      size_t keep = c->NT.size() >= fitNT ? 0 : fitNT - c->NT.size();
      std::stable_sort(extra.begin(), extra.end(), [&](int x, int y) { return cntX[x] > cntX[y]; });
      extra.resize(keep); std::sort(extra.begin(), extra.end());
    }
    std::vector<int> NT2 = c->NT; NT2.insert(NT2.end(), extra.begin(), extra.end());
    int a = terms[c->t];
    std::vector<Rec> allrecs = recs; mkrecs(NT2, act, asg, allrecs);
    std::vector<const Rec*> part; for (auto& r : allrecs) if (Tb.PAR[r.X & a]) part.push_back(&r);
    std::vector<Slk> slv(c->SL.size()); std::vector<const Slk*> sl;
    for (size_t i = 0; i < c->SL.size(); i++) { if (!mkslack(c->SL[i], act, asg, slv[i])) throw std::runtime_error("hoist: slack"); sl.push_back(&slv[i]); }
    std::vector<std::pair<int, int>> cs; cands(part, sl, c->sym, c->cdir, cs);
    std::map<std::pair<int, int>, size_t> pos; for (size_t i = 0; i < c->cs.size(); i++) pos[c->cs[i]] = i;
    std::set<int> ex(extra.begin(), extra.end());
    uint32_t act2 = act ^ (1u << c->t);
    Cert* d = mk(); d->t = c->t; d->NT = NT2; d->SL = c->SL; d->sym = c->sym; d->cdir = c->cdir;
    for (auto& [b, cc] : cs) {
      auto it = pos.find({b, cc}); if (it == pos.end()) throw std::runtime_error("hoist: candidate not in the old list");
      std::vector<Asg> asg2; asg2.push_back(Asg{a, b, cc, c->t}); asg2.insert(asg2.end(), asg.begin(), asg.end());
      std::vector<Rec> recs2; for (auto& q : allrecs) recs2.push_back(upd(q, a, b, cc));
      d->kids.push_back(hoist(strip(c->kids[it->second], ex), act2, asg2, recs2));
    }
    return d;
  }
  Cert* finalize(Cert* c) {
    uint32_t act = n == 32 ? 0xffffffffu : ((1u << n) - 1);
    std::vector<Asg> asg; std::vector<Rec> recs;
    attach(c, act, asg, recs);
    return hoist(c, act, asg, recs);
  }
};

static void stats(const Cert* c, long long& nodes) { nodes++; if (!c->over) for (auto* k : c->kids) stats(k, nodes); }
}  // namespace g7x
