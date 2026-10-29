// chk334c.cc -- independent checker of completion-refutation certificates for the tensor <3,3,4> over F2
// (stream format v5c-334).  Written from a description of the format only, independently of the generator.
// C++17, one file, single-threaded, deterministic, no external libraries.
//
// usage: chk334c --E b1,b2,... [--run NAME] [--hex] [--leaflist FILE] [--no-xcheck] STREAMFILE
//   --E        basis masks (9-bit, decimal or 0x..) of the subspace E of the run (dom_E = E^perp minus 0)
//   --run      run name used in the output lines (default "run")
//   --hex      the stream file is text: the hex digits of the natural number (most significant digit first)
//              default: raw bytes, little-endian bit order (bit i of the number = bit (i&7) of byte i>>3)
//   --leaflist FILE  optional: one covering leaf per line (decimal labels); the multiset of accepted leaves
//              must equal the multiset of lines (labels compared as ordered tuples)
//   --no-xcheck  skip the from-scratch cross-check of every inherited record (default: on)
// output: ACCEPT <run> <leaf id> nodes=<k> | REJECT <run> <leaf id> <condition> path=/i/j/...  and a SUMMARY line.
// exit 0 only if every leaf is accepted (and the leaf list, if given, matches); 1 if some leaf is rejected;
// 2 for usage errors and structural errors in the batch.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iterator>
#include <memory>
#include <sstream>
#include <string>
#include <vector>
#ifdef USE_ZLIB
#include <zlib.h>
#endif

typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

static inline int par(unsigned v) { return __builtin_parity(v); }
[[noreturn]] static void die(const std::string& m) { fprintf(stderr, "chk334c: %s\n", m.c_str()); exit(2); }

// ---------------------------------------------------------------- 4096-bit sets of 12-bit vectors
struct Bits {
  u64 w[64];
  void clear() { memset(w, 0, sizeof w); }
  void set(unsigned i) { w[i >> 6] |= 1ULL << (i & 63); }
  bool get(unsigned i) const { return (w[i >> 6] >> (i & 63)) & 1; }
  void andWith(const Bits& o) { for (int i = 0; i < 64; i++) w[i] &= o.w[i]; }
  int count() const { int c = 0; for (int i = 0; i < 64; i++) c += __builtin_popcountll(w[i]); return c; }
  bool operator==(const Bits& o) const { return memcmp(w, o.w, sizeof w) == 0; }
};
// f(unsigned element) returns false to stop; elements are visited in ascending order
template <class F> static void forEachBit(const Bits& s, F f) {
  for (int i = 0; i < 64; i++) {
    u64 x = s.w[i];
    while (x) {
      int b = __builtin_ctzll(x);
      x &= x - 1;
      if (!f((unsigned)(i * 64 + b))) return;
    }
  }
}

// ---------------------------------------------------------------- global tables (all computed here from the definitions)
static Bits PERP0[4096], PERP1[4096];  // PERP0[g] = {v : parity(g&v)=0}, PERP1[g] = {v : parity(g&v)=1}
static Bits ALLNZ;                     // {1..4095}
static u16 TXrow[512][12];             // TXrow[X][y] = bit mask over z of row y of the slice T(X)
static std::vector<std::array<u16, 4>> GLS, GLI;  // all invertible 4x4 matrices (rows as 4-bit masks) and inverses
static std::vector<u16> ORBM;          // orbit minima of B\{0} under b -> b*S
static int ORBIDX[4096];
static std::vector<Bits> CORB;         // CORB[i] = orbit minima of C\{0} under c -> S^-1 c, S in Stab(ORBM[i])

// rank of n (<=32) row vectors (12-bit masks)
static int rankOf(const u16* rows, int n) {
  u16 a[32];
  for (int i = 0; i < n; i++) a[i] = rows[i];
  int r = 0;
  for (int bit = 11; bit >= 0 && r < n; bit--) {
    int p = -1;
    for (int i = r; i < n; i++) if ((a[i] >> bit) & 1) { p = i; break; }
    if (p < 0) continue;
    std::swap(a[p], a[r]);
    for (int i = 0; i < n; i++) if (i != r && ((a[i] >> bit) & 1)) a[i] ^= a[r];
    r++;
  }
  return r;
}
static void transpose12(const u16* R, u16* Rt) {
  for (int z = 0; z < 12; z++) {
    u16 v = 0;
    for (int y = 0; y < 12; y++) if ((R[y] >> z) & 1) v |= (u16)(1 << y);
    Rt[z] = v;
  }
}
// all F2-combinations of the given vectors, as a set
static void spanSet(const u16* gens, int n, Bits& out) {
  out.clear();
  out.set(0);
  std::vector<u16> el;
  el.push_back(0);
  for (int i = 0; i < n; i++) {
    u16 g = gens[i];
    if (out.get(g)) continue;
    size_t m = el.size();
    for (size_t k = 0; k < m; k++) { u16 e = (u16)(el[k] ^ g); el.push_back(e); out.set(e); }
  }
}

// b (3x4 matrix, bit 4j+k = entry (j,k)) times S (4x4, S[l] = row l as a mask over columns k)
static u16 actB(u16 b, const std::array<u16, 4>& S) {
  u16 out = 0;
  for (int j = 0; j < 3; j++) {
    u16 rj = (b >> (4 * j)) & 15, acc = 0;
    for (int l = 0; l < 4; l++) if ((rj >> l) & 1) acc ^= S[l];
    out |= (u16)(acc << (4 * j));
  }
  return out;
}
// S^-1 (rows Si[k] over columns m) times c (4x3 matrix, bit 3k+i = entry (k,i))
static u16 actC(u16 c, const std::array<u16, 4>& Si) {
  u16 out = 0;
  for (int k = 0; k < 4; k++) {
    u16 acc = 0;
    for (int m = 0; m < 4; m++) if ((Si[k] >> m) & 1) acc ^= (c >> (3 * m)) & 7;
    out |= (u16)(acc << (3 * k));
  }
  return out;
}
static bool invert4(const std::array<u16, 4>& S, std::array<u16, 4>& inv) {
  u16 a[4], b[4];
  for (int l = 0; l < 4; l++) { a[l] = S[l]; b[l] = (u16)(1 << l); }
  for (int c = 0; c < 4; c++) {
    int p = -1;
    for (int l = c; l < 4; l++) if ((a[l] >> c) & 1) { p = l; break; }
    if (p < 0) return false;
    std::swap(a[p], a[c]);
    std::swap(b[p], b[c]);
    for (int l = 0; l < 4; l++) if (l != c && ((a[l] >> c) & 1)) { a[l] ^= a[c]; b[l] ^= b[c]; }
  }
  for (int l = 0; l < 4; l++) inv[l] = b[l];
  return true;
}

static void buildTables() {
  // T334 from the definition: T[x][y][z] = 1 iff x = 3i+j, y = 4j+k, z = 3k+i  (i,j < 3, k < 4); T(X)[y][z] = sum_x X_x T[x][y][z]
  for (int X = 0; X < 512; X++) {
    for (int y = 0; y < 12; y++) TXrow[X][y] = 0;
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) for (int k = 0; k < 4; k++) {
      int x = 3 * i + j, y = 4 * j + k, z = 3 * k + i;
      if ((X >> x) & 1) TXrow[X][y] ^= (u16)(1 << z);
    }
  }
  for (int g = 0; g < 4096; g++) {
    PERP0[g].clear();
    PERP1[g].clear();
    for (int v = 0; v < 4096; v++) { if (par((unsigned)(g & v))) PERP1[g].set(v); else PERP0[g].set(v); }
  }
  ALLNZ.clear();
  for (int v = 1; v < 4096; v++) ALLNZ.set(v);
  // GL4(F2) by brute force over all 65536 matrices
  for (u32 m = 0; m < 65536; m++) {
    std::array<u16, 4> S, Si;
    for (int l = 0; l < 4; l++) S[l] = (u16)((m >> (4 * l)) & 15);
    if (invert4(S, Si)) { GLS.push_back(S); GLI.push_back(Si); }
  }
  if (GLS.size() != 20160) die("internal: |GL4(F2)| != 20160");
  // ORBM: orbit minima of B\{0} under b -> b*S
  std::vector<char> seen(4096, 0);
  for (int b = 1; b < 4096; b++) {
    if (seen[b]) continue;
    ORBM.push_back((u16)b);
    for (size_t s = 0; s < GLS.size(); s++) seen[actB((u16)b, GLS[s])] = 1;
  }
  if (ORBM.size() != 15) die("internal: |ORBM| != 15");
  for (int b = 0; b < 4096; b++) ORBIDX[b] = -1;
  for (size_t i = 0; i < ORBM.size(); i++) ORBIDX[ORBM[i]] = (int)i;
  // CORB[b]: orbit minima of C\{0} under c -> S^-1 c, S in Stab(b) = {S : b*S = b}
  CORB.resize(ORBM.size());
  for (size_t i = 0; i < ORBM.size(); i++) {
    u16 b = ORBM[i];
    std::vector<size_t> stab;
    for (size_t s = 0; s < GLS.size(); s++) if (actB(b, GLS[s]) == b) stab.push_back(s);
    u16 rows[3];
    for (int j = 0; j < 3; j++) rows[j] = (b >> (4 * j)) & 15;
    int rk = rankOf(rows, 3);
    size_t want = rk == 1 ? 1344 : rk == 2 ? 96 : 8;
    if (stab.size() != want) die("internal: |Stab(b)| differs from 2^{r(4-r)}|GL_{4-r}|");
    CORB[i].clear();
    std::vector<char> sc(4096, 0);
    for (int c = 1; c < 4096; c++) {
      if (sc[c]) continue;
      CORB[i].set(c);
      for (size_t k = 0; k < stab.size(); k++) sc[actC((u16)c, GLI[stab[k]])] = 1;
    }
  }
}

static void selfTest() {
  // (a) rank T(X) = 4 * rank(X as 3x3 matrix), for all 511 nonzero X
  for (int X = 1; X < 512; X++) {
    u16 r3[3];
    for (int i = 0; i < 3; i++) r3[i] = (u16)((X >> (3 * i)) & 7);
    if (rankOf(TXrow[X], 12) != 4 * rankOf(r3, 3)) die("selftest: rank T(X) != 4 rank X");
  }
  // (b) the pair action (b,c) -> (b*S, S^-1 c) fixes T(e_x): the transformed trivial decomposition sums to T(e_x)
  for (size_t s = 0; s < GLS.size(); s++) {
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) {
      u16 acc[12];
      for (int y = 0; y < 12; y++) acc[y] = 0;
      for (int k = 0; k < 4; k++) {
        u16 b = (u16)(1 << (4 * j + k)), c = (u16)(1 << (3 * k + i));
        u16 b2 = actB(b, GLS[s]), c2 = actC(c, GLI[s]);
        for (int y = 0; y < 12; y++) if ((b2 >> y) & 1) acc[y] ^= c2;
      }
      int x = 3 * i + j;
      for (int y = 0; y < 12; y++) if (acc[y] != TXrow[1 << x][y]) die("selftest: pair action does not fix T");
    }
  }
}

// ---------------------------------------------------------------- records
struct Rec {
  int X;
  Bits lm, rm;   // col R(X) and row R(X) as explicit sets (inherited records: updated by rule (I))
  u16 xcol[12];  // x(e_j): a linear map with R x(v) = v on col R (values are masks over z)
};
typedef std::shared_ptr<const Rec> RecP;

// record of the 12x12 residual R (R[y] = row y as a mask over z)
static std::shared_ptr<Rec> makeRec(int X, const u16* R) {
  auto r = std::make_shared<Rec>();
  r->X = X;
  spanSet(R, 12, r->rm);
  u16 Rt[12];
  transpose12(R, Rt);
  spanSet(Rt, 12, r->lm);
  // RREF of R with the row operations tracked in U:  reduced_i = xor_{y in U[i]} R[y];  piv[i] = pivot column of row i
  u16 a[12], U[12];
  int piv[12], rk = 0;
  for (int y = 0; y < 12; y++) { a[y] = R[y]; U[y] = (u16)(1 << y); }
  for (int col = 0; col < 12 && rk < 12; col++) {
    int p = -1;
    for (int i = rk; i < 12; i++) if ((a[i] >> col) & 1) { p = i; break; }
    if (p < 0) continue;
    std::swap(a[p], a[rk]);
    std::swap(U[p], U[rk]);
    for (int i = 0; i < 12; i++) if (i != rk && ((a[i] >> col) & 1)) { a[i] ^= a[rk]; U[i] ^= U[rk]; }
    piv[rk++] = col;
  }
  // R z = v with z supported on pivot columns:  z_{piv[i]} = parity(U[i] & v)   (valid for v in col R)
  for (int j = 0; j < 12; j++) {
    u16 xc = 0;
    for (int i = 0; i < rk; i++) if ((U[i] >> j) & 1) xc |= (u16)(1 << piv[i]);
    r->xcol[j] = xc;
  }
  return r;
}
static inline u16 xOf(const Rec& r, u16 v) {  // x(v)
  u16 z = 0;
  for (int j = 0; j < 12; j++) if ((v >> j) & 1) z ^= r.xcol[j];
  return z;
}
static inline u16 gOf(const Rec& r, u16 c) {  // g(c) = adjoint of x applied to c:  <g(c), v> = <c, x(v)>
  u16 g = 0;
  for (int j = 0; j < 12; j++) if (par((unsigned)(c & r.xcol[j]))) g |= (u16)(1 << j);
  return g;
}

// ---------------------------------------------------------------- bit reader over the stream
// The stream is one natural number: bits at positions >= end (above the window, or above the top of the file) read as 0,
// exactly like `rd k S` on a natural number.  (E1's last field X = 2 ends with zero bits above the top set bit.)  A
// zero read can never make a node valid (over 0 is not in dom), so truncation is still rejected.
struct Reader {
  const std::vector<uint8_t>* data = nullptr;
  size_t pos = 0, end = 0;
  bool take(int k, u64& v) {
    v = 0;
    for (int i = 0; i < k; i++) {
      size_t p = pos + (size_t)i;
      if (p < end) v |= (u64)(((*data)[p >> 3] >> (p & 7)) & 1) << i;
    }
    pos += (size_t)k;
    return true;
  }
};

// ---------------------------------------------------------------- per-leaf context and the node checker
struct Ctx {
  int n = 0;
  u16 a[32];
  bool inDom[512];
  bool asg[32];
  u16 B[32], C[32];
  Reader rd;
  long nodes = 0;
  std::string err;
  std::vector<long> path;
  std::string failPath;
  bool xcheck = true;
};
static std::string pathStr(const Ctx& K) {
  std::string s = "/";
  for (size_t i = 0; i < K.path.size(); i++) { if (i) s += "/"; s += std::to_string(K.path[i]); }
  return s;
}
#define FAIL(...) do { char _b[320]; snprintf(_b, sizeof _b, __VA_ARGS__); K.err = _b; K.failPath = pathStr(K); return false; } while (0)
#define TAKE(var, k, what) u64 var; if (!K.rd.take((k), var)) FAIL("stream truncated in %s", what)

// R(X) = T(X) + sum_{t assigned, X(a_t)=1} b_t c_t^T   (rows y; (b c^T)[y][z] = b_y c_z)
static void residualRows(const Ctx& K, int X, u16* rows) {
  for (int y = 0; y < 12; y++) rows[y] = TXrow[X][y];
  for (int t = 0; t < K.n; t++) {
    if (!K.asg[t] || !par((unsigned)(X & K.a[t]))) continue;
    for (int y = 0; y < 12; y++) if ((K.B[t] >> y) & 1) rows[y] ^= K.C[t];
  }
}
// u(X) = number of active terms hit by X
static int hitsActive(const Ctx& K, int X) {
  int u = 0;
  for (int t = 0; t < K.n; t++) if (!K.asg[t] && par((unsigned)(X & K.a[t]))) u++;
  return u;
}
// cross-check (debug layer): an inherited record must equal the from-scratch col/row space of the true residual,
// and its x must still be a preimage map on col R.  (Equal by the mathematics for every record reached by a
// candidate descent; a failure here means a bug in this program, not a bad certificate.)
static bool recMatchesScratch(const Ctx& K, const Rec& r, std::string& why) {
  u16 R[12], Rt[12];
  residualRows(K, r.X, R);
  Bits rm, lm;
  spanSet(R, 12, rm);
  transpose12(R, Rt);
  spanSet(Rt, 12, lm);
  if (!(rm == r.rm)) { why = "row space differs"; return false; }
  if (!(lm == r.lm)) { why = "col space differs"; return false; }
  // x is linear, so it is a preimage map on col R iff R x(v) = v for the generators v = the columns of R
  for (int c = 0; c < 12; c++) {
    u16 v = Rt[c], z = xOf(r, v);
    for (int y = 0; y < 12; y++) if (par((unsigned)(R[y] & z)) != (int)((v >> y) & 1)) { why = "x is not a preimage map on col R"; return false; }
  }
  return true;
}

static bool nodeCheck(Ctx& K, const std::vector<RecP>& recs, int depth) {
  if (depth > 64) FAIL("recursion fuel 64 exhausted");
  TAKE(tag, 1, "node tag");
  K.nodes++;
  if (tag == 0) {  // over X
    TAKE(Xv, 9, "over X");
    int X = (int)Xv;
    if (!K.inDom[X]) FAIL("over: X=%d is not in dom", X);
    u16 R[12];
    residualRows(K, X, R);
    int rk = rankOf(R, 12), u = hitsActive(K, X);
    if (!(rk > u)) FAIL("over X=%d: rank R(X)=%d is not > u(X)=%d", X, rk, u);
    return true;
  }
  // br t NT SL sym cdir kids
  TAKE(tv, 5, "br t");
  TAKE(symv, 1, "br sym");
  TAKE(cdirv, 1, "br cdir");
  TAKE(nNT, 4, "br #NT");
  std::vector<int> NT, SL;
  for (u64 i = 0; i < nNT; i++) { TAKE(x, 9, "br NT list"); NT.push_back((int)x); }
  TAKE(nSL, 3, "br #SL");
  for (u64 i = 0; i < nSL; i++) { TAKE(x, 9, "br SL list"); SL.push_back((int)x); }
  const int t = (int)tv;
  const bool sym = symv != 0, cdir = cdirv != 0;
  // (1) t in Act; sym only at the root (Asg empty) and with cdir = false
  if (t >= K.n || K.asg[t]) FAIL("br: term %d is not active (n=%d)", t, K.n);
  if (sym) {
    for (int s = 0; s < K.n; s++) if (K.asg[s]) FAIL("br: sym at a non-root node");
    if (cdir) FAIL("br: sym with cdir=1 is rejected");
  }
  if (K.xcheck) {
    for (size_t i = 0; i < recs.size(); i++) {
      std::string why;
      if (!recMatchesScratch(K, *recs[i], why)) FAIL("INTERNAL: inherited record X=%d: %s", recs[i]->X, why.c_str());
    }
  }
  // (2) NT claims: in dom, u(X) <= rank R(X); each becomes a new record
  std::vector<RecP> all(recs);
  for (size_t i = 0; i < NT.size(); i++) {
    int X = NT[i];
    if (!K.inDom[X]) FAIL("br NT: X=%d is not in dom", X);
    u16 R[12];
    residualRows(K, X, R);
    int rk = rankOf(R, 12), u = hitsActive(K, X);
    if (u > rk) FAIL("br NT: X=%d has u(X)=%d > rank R(X)=%d", X, u, rk);
    all.push_back(makeRec(X, R));
  }
  // (3) SL claims: in dom, hit a_t, u(X) <= rank R(X)+1; each gives (col R, row R)
  std::vector<RecP> sl;
  for (size_t i = 0; i < SL.size(); i++) {
    int X = SL[i];
    if (!K.inDom[X]) FAIL("br SL: X=%d is not in dom", X);
    if (!par((unsigned)(X & K.a[t]))) FAIL("br SL: X=%d does not hit a_%d", X, t);
    u16 R[12];
    residualRows(K, X, R);
    int rk = rankOf(R, 12), u = hitsActive(K, X);
    if (u > rk + 1) FAIL("br SL: X=%d has u(X)=%d > rank R(X)+1=%d", X, u, rk + 1);
    sl.push_back(makeRec(X, R));
  }
  // (4) part = records whose X hits a_t;  Bm, Cm
  std::vector<const Rec*> part;
  for (size_t i = 0; i < all.size(); i++) if (par((unsigned)(all[i]->X & K.a[t]))) part.push_back(all[i].get());
  Bits Bm = ALLNZ, Cm = ALLNZ;
  for (size_t i = 0; i < part.size(); i++) { Bm.andWith(part[i]->lm); Cm.andWith(part[i]->rm); }
  if (sym) {
    Bits o;
    o.clear();
    for (size_t i = 0; i < ORBM.size(); i++) o.set(ORBM[i]);
    Bm.andWith(o);
  }
  // (5)(6) candidates in the exact order of the format; one subtree per candidate, read in that order
  long idx = 0;
  auto descend = [&](u16 b, u16 c) -> bool {
    std::vector<RecP> kids;
    kids.reserve(all.size());
    for (size_t i = 0; i < all.size(); i++) {
      const Rec& r = *all[i];
      if (!par((unsigned)(r.X & K.a[t]))) { kids.push_back(all[i]); continue; }
      auto nr = std::make_shared<Rec>(r);
      nr->lm.andWith(PERP0[gOf(r, c)]);   // lm <- lm /\ perp(g(c))
      nr->rm.andWith(PERP0[xOf(r, b)]);   // rm <- rm /\ perp(x(b))
      kids.push_back(nr);
    }
    K.asg[t] = true;
    K.B[t] = b;
    K.C[t] = c;
    K.path.push_back(idx);
    bool ok = nodeCheck(K, kids, depth + 1);
    K.path.pop_back();
    K.asg[t] = false;
    idx++;
    return ok;
  };
  bool allOk = true;
  if (!cdir) {
    forEachBit(Bm, [&](unsigned b) {
      Bits cs = Cm;
      for (size_t i = 0; i < part.size(); i++) cs.andWith(PERP1[xOf(*part[i], (u16)b)]);  // <c, x_r(b)> = 1
      for (size_t i = 0; i < sl.size(); i++) if (!sl[i]->lm.get(b)) cs.andWith(sl[i]->rm);  // b not in col_s => c in row_s
      if (sym) cs.andWith(CORB[ORBIDX[b]]);
      forEachBit(cs, [&](unsigned c) {
        if (!descend((u16)b, (u16)c)) { allOk = false; return false; }
        return true;
      });
      return allOk;
    });
  } else {
    forEachBit(Cm, [&](unsigned c) {
      Bits bs = Bm;
      for (size_t i = 0; i < part.size(); i++) bs.andWith(PERP1[gOf(*part[i], (u16)c)]);  // <g_r(c), b> = 1
      for (size_t i = 0; i < sl.size(); i++) if (!sl[i]->rm.get(c)) bs.andWith(sl[i]->lm);  // c not in row_s => b in col_s
      forEachBit(bs, [&](unsigned b) {
        if (!descend((u16)b, (u16)c)) { allOk = false; return false; }
        return true;
      });
      return allOk;
    });
  }
  return allOk;
}

// ---------------------------------------------------------------- the run's subspace E, dom_E
static std::vector<int> Ebasis, Espan;
static bool domE[512];
static u64 domMaskW[8];
static void buildDomE() {
  std::vector<char> in(512, 0);
  Espan.clear();
  Espan.push_back(0);
  in[0] = 1;
  for (size_t i = 0; i < Ebasis.size(); i++) {
    int g = Ebasis[i];
    if (in[g]) continue;
    size_t m = Espan.size();
    for (size_t k = 0; k < m; k++) { int e = Espan[k] ^ g; Espan.push_back(e); in[e] = 1; }
  }
  for (int w = 0; w < 8; w++) domMaskW[w] = 0;
  for (int X = 0; X < 512; X++) {
    bool ok = X != 0;
    for (size_t i = 0; i < Ebasis.size() && ok; i++) if (par((unsigned)(X & Ebasis[i]))) ok = false;  // X in E^perp, X != 0
    domE[X] = ok;
    if (ok) domMaskW[X >> 6] |= 1ULL << (X & 63);
  }
}

// ---------------------------------------------------------------- one leaf record
struct LeafRes {
  bool ok = false;
  std::string err;
  long nodes = 0;
  std::vector<int> labels;
};
// window [start,end): the leaf record starts at start (after the batch tag bit).  Reads above the window give 0 (natural
// number semantics); bits of the window that the leaf record does not use must all be 0.
static void checkLeaf(const std::vector<uint8_t>& data, size_t start, size_t end, bool xcheck, LeafRes& res) {
  Ctx K;
  K.rd.data = &data;
  K.rd.pos = start;
  K.rd.end = end;
  K.xcheck = xcheck;
  for (int i = 0; i < 32; i++) { K.asg[i] = false; K.a[i] = 0; K.B[i] = 0; K.C[i] = 0; }
  auto fail = [&](const std::string& m) { res.ok = false; res.err = m; res.nodes = K.nodes; };
  u64 v;
  if (!K.rd.take(6, v)) { fail("leaf: stream truncated at n"); return; }
  int n = (int)v;
  if (n > 31) { fail("leaf: n=" + std::to_string(n) + " > 31"); return; }
  K.n = n;
  for (int i = 0; i < n; i++) {
    if (!K.rd.take(9, v)) { fail("leaf: stream truncated in the first factors"); return; }
    K.a[i] = (u16)v;
    res.labels.push_back((int)v);
  }
  if (!K.rd.take(2, v)) { fail("leaf: stream truncated at dommode"); return; }
  if (v != 1) {
    if (v == 0) fail("leaf: dommode 00 (dom = all functionals) is rejected (unsound for quotient leaves, B2)");
    else if (v & 2) fail("leaf: dommode bit 1 set (Lemma G path) is rejected");
    else fail("leaf: dommode must be exactly 01");
    return;
  }
  u64 mw[8];
  for (int w = 0; w < 8; w++) if (!K.rd.take(64, mw[w])) { fail("leaf: stream truncated in the dom mask"); return; }
  {
    int ndiff = 0, firstX = -1;
    for (int X = 0; X < 512; X++) {
      bool sb = (mw[X >> 6] >> (X & 63)) & 1;
      if (sb != domE[X]) { ndiff++; if (firstX < 0) firstX = X; }
    }
    if (ndiff) {
      fail("leaf: dom mask != dom_E (" + std::to_string(ndiff) + " differences; first at X=" + std::to_string(firstX) +
           (domE[firstX] ? ": missing from the stream mask)" : ": extra in the stream mask)"));
      return;
    }
  }
  for (int i = 0; i < n; i++) {
    int a = K.a[i], mn = a;
    for (size_t k = 0; k < Espan.size(); k++) mn = std::min(mn, a ^ Espan[k]);
    if (a == 0) { fail("leaf: label a_" + std::to_string(i) + " = 0 lies in E (needs a nonzero coset)"); return; }
    if (mn != a) {
      fail("leaf: label a_" + std::to_string(i) + " = " + std::to_string(a) + " is not the smallest vector of its coset (smallest = " + std::to_string(mn) + ")");
      return;
    }
  }
  for (int X = 0; X < 512; X++) K.inDom[X] = domE[X];
  std::vector<RecP> none;
  if (!nodeCheck(K, none, 0)) {
    fail(K.err + " path=" + K.failPath + (K.rd.pos > K.rd.end ? " (stream read past its window: read as zeros)" : ""));
    return;
  }
  for (size_t p = K.rd.pos; p < K.rd.end; p++)
    if ((data[p >> 3] >> (p & 7)) & 1) { fail("leaf: nonzero bits left unused after the certificate (first at bit " + std::to_string(p) + ")"); return; }
  res.ok = true;
  res.nodes = K.nodes;
}

// ---------------------------------------------------------------- batch structure
struct Run {
  std::string name = "run";
  long leaves = 0, accepted = 0, rejected = 0, nodes = 0;
  bool xcheck = true;
  std::vector<std::string> acceptedLeaves;  // label tuples, for --leaflist
};
static std::string labelKey(const std::vector<int>& l) {
  std::string s;
  for (size_t i = 0; i < l.size(); i++) { if (i) s += ","; s += std::to_string(l[i]); }
  return s;
}
static bool structErr(Run& R, size_t pos, const char* msg) {
  printf("REJECT %s batch@bit%zu structural error: %s\n", R.name.c_str(), pos, msg);
  return false;
}
// batch := 1 leaf | 0 l(24 bits) left(l bits) right.  The left batch sees exactly l bits (zeros above them); the right batch
// is everything above, and continues in the loop.
static bool parseBatch(Run& R, const std::vector<uint8_t>& data, size_t pos, size_t end, int depth) {
  for (;;) {
    if (depth > 100000) return structErr(R, pos, "batch nesting too deep");
    if (pos >= end) return structErr(R, pos, "empty batch window");
    int tag = (data[pos >> 3] >> (pos & 7)) & 1;
    if (tag == 1) {
      long id = R.leaves++;
      LeafRes lr;
      checkLeaf(data, pos + 1, end, R.xcheck, lr);
      if (lr.ok) {
        R.accepted++;
        R.nodes += lr.nodes;
        R.acceptedLeaves.push_back(labelKey(lr.labels));
        printf("ACCEPT %s %ld nodes=%ld\n", R.name.c_str(), id, lr.nodes);
      } else {
        R.rejected++;
        printf("REJECT %s %ld %s\n", R.name.c_str(), id, lr.err.c_str());
      }
      return true;
    }
    Reader rd;
    rd.data = &data;
    rd.pos = pos + 1;
    rd.end = end;
    u64 l;
    if (!rd.take(24, l)) return structErr(R, pos, "truncated batch length field");
    size_t ls = pos + 25, le = ls + (size_t)l;
    if (le >= end) return structErr(R, pos, "left batch window overruns the enclosing window (or leaves no room for the right batch)");
    if (!parseBatch(R, data, ls, le, depth + 1)) return false;
    pos = le;
  }
}

// ---------------------------------------------------------------- input reading and main
static bool readFile(const std::string& fn, std::vector<uint8_t>& out) {
#ifdef USE_ZLIB
  if (fn.size() > 3 && fn.compare(fn.size() - 3, 3, ".gz") == 0) {  // gzip-compressed stream (zlib is the one library allowed)
    gzFile g = gzopen(fn.c_str(), "rb");
    if (!g) return false;
    out.clear();
    std::vector<uint8_t> buf(1 << 20);
    int n;
    while ((n = gzread(g, buf.data(), (unsigned)buf.size())) > 0) out.insert(out.end(), buf.begin(), buf.begin() + n);
    bool ok = n == 0;
    gzclose(g);
    return ok;
  }
#endif
  std::ifstream f(fn, std::ios::binary);
  if (!f) return false;
  out.assign(std::istreambuf_iterator<char>(f), std::istreambuf_iterator<char>());
  return true;
}
static bool parseHex(const std::vector<uint8_t>& text, std::vector<uint8_t>& out) {
  std::string s;
  for (size_t i = 0; i < text.size(); i++) { char ch = (char)text[i]; if (!isspace((unsigned char)ch)) s += ch; }
  if (s.size() >= 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) s = s.substr(2);
  for (size_t i = 0; i < s.size(); i++) if (!isxdigit((unsigned char)s[i])) return false;
  if (s.size() % 2) s = "0" + s;
  auto hv = [](char ch) { return ch <= '9' ? ch - '0' : (ch | 32) - 'a' + 10; };
  size_t nb = s.size() / 2;
  out.assign(nb, 0);
  for (size_t i = 0; i < nb; i++) out[i] = (uint8_t)(hv(s[s.size() - 2 - 2 * i]) * 16 + hv(s[s.size() - 1 - 2 * i]));  // byte 0 = least significant
  return true;
}
static int parseNum(const std::string& s) {
  char* e = nullptr;
  long v = strtol(s.c_str(), &e, 0);
  if (!e || *e || s.empty() || v < 0 || v > 511) die("bad E basis element '" + s + "' (need 0..511)");
  return (int)v;
}

int main(int argc, char** argv) {
  Run R;
  std::string file, leaflist;
  bool hex = false, haveE = false;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    if (a == "--E" && i + 1 < argc) {
      haveE = true;
      std::string s = argv[++i], tok;
      std::stringstream ss(s);
      while (std::getline(ss, tok, ',')) if (!tok.empty()) Ebasis.push_back(parseNum(tok));
    } else if (a == "--run" && i + 1 < argc) R.name = argv[++i];
    else if (a == "--hex") hex = true;
    else if (a == "--leaflist" && i + 1 < argc) leaflist = argv[++i];
    else if (a == "--no-xcheck") R.xcheck = false;
    else if (!a.empty() && a[0] == '-') die("unknown option " + a);
    else if (file.empty()) file = a;
    else die("more than one stream file");
  }
  if (!haveE || file.empty()) die("usage: chk334c --E b1,b2,... [--run NAME] [--hex] [--leaflist FILE] [--no-xcheck] STREAMFILE");
  buildTables();
  selfTest();
  buildDomE();
  std::vector<uint8_t> data;
  if (!readFile(file, data)) die("cannot read " + file);
  if (hex) {
    std::vector<uint8_t> bytes;
    if (!parseHex(data, bytes)) die("bad hex text in " + file);
    data.swap(bytes);
  }
  bool structural = !parseBatch(R, data, 0, data.size() * 8, 0);
  bool leafsetOk = true;
  if (!leaflist.empty() && !structural) {
    std::vector<uint8_t> txt;
    if (!readFile(leaflist, txt)) die("cannot read " + leaflist);
    std::vector<std::string> want;
    std::stringstream ss(std::string(txt.begin(), txt.end()));
    std::string line;
    while (std::getline(ss, line)) {
      std::stringstream ls(line);
      std::vector<int> l;
      std::string tok;
      bool any = false;
      while (ls >> tok) { if (tok[0] == '#') break; l.push_back(atoi(tok.c_str())); any = true; }
      if (any) want.push_back(labelKey(l));
    }
    std::vector<std::string> got = R.acceptedLeaves;
    std::sort(want.begin(), want.end());
    std::sort(got.begin(), got.end());
    leafsetOk = want == got;
    printf("LEAFSET %s %s want=%zu accepted=%zu\n", R.name.c_str(), leafsetOk ? "OK" : "MISMATCH", want.size(), got.size());
  }
  printf("SUMMARY %s leaves=%ld accepted=%ld rejected=%ld nodes=%ld%s\n", R.name.c_str(), R.leaves, R.accepted, R.rejected, R.nodes,
         structural ? " STRUCTURAL-ERROR" : "");
  if (structural) return 2;
  if (R.leaves == 0 || R.rejected != 0 || R.accepted != R.leaves || !leafsetOk) return 1;
  return 0;
}
