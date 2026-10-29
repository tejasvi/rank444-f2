// gen7_334: certificate generator for the completion leaves of the tensor <3,3,4> over F2 (stream format v5c-334).
//
//   gen7_334 --target qS_c610.t inst_c610.a            reduced-coordinate leaves as read by tsolve334 (the same two files)
//   gen7_334 --labels --E 1,10,68 leaves9.txt          leaves given directly as 9-bit coset minima with the subspace E
//   gen7_334 --target qS_c610.t --check-hex FILE       re-check certificate streams ("tag nbits hex" lines) with the model
//   gen7_334 --selftest                                run the model on the four worked examples E1, E1', E1-dom0, E1-domX
//
// Options: --Ks 4,8 (look-ahead widths tried in turn, the smallest accepted certificate is kept; default 4,8; --K N = one width)
//          --best (also try every width without sym at the root; slow, usually larger)  --deadk 6
//          --maxnodes 300000 (certificate nodes per attempt; BIG past it) --fit / --nofit --nosymroot
//          --symtab FILE (default: $GEN7_SYMTAB, <exe dir>/../data/symtab334.tsv)  --seeded FILE (class cross-check)
//          --class N (class number for the seeded334.tsv cross-check; default: parsed from the target name qS_c<N>.t)
//          --hex FILE (append "tag nbits hex" per certified leaf: the one-leaf batch of the stream format, a little-endian natural number
//          in hex, most significant digit first)   --nomodel (skip the self-check; NOT for production)
//          --no-tabcheck (skip the validation of symtab334.tsv)  --deep-tabcheck (recompute ORBM / CORB from scratch)
//          --from I --to J (1-based, inclusive range of instance lines)  --trace N (print the first N branch nodes of every
//          certificate, decoded by the model)  --quiet
//          --satsearch NODES [--satfirst B0] [--satonly]: after BIG (or instead of certificate generation with --satonly) look
//          for a decomposition by randomized restarts with budgets B0, 2*B0, .. (total NODES); a decomposition is verified
//          --mutants N: N random mutants per certified leaf (bit flips in the certificate, domain-mask / dommode / label changes,
//          truncation); the model must reject them, accepted ones are listed (they are valid refutations under the checker rules)
//          --dump-leaf: print a decoding of the stream header (labels, E, dom mask, bit positions, full hex) for every certified leaf
//
// How E is determined (reduced-coordinate mode).  tsolve334's instance leaves use the coordinates of quotient_map(basis of E)
// (ip/common334.py): a first factor is v = L(a), L: F2^9 -> F2^D with kernel E, D = 9 - dim E, and the target qS_c<c>.t is
// T mod E in these coordinates (mkcompS.py).  The supports of the 9 slices T[x] are disjoint, so L is read off the target:
// L[xp][x] = 1 iff the 4 entries (xp, 4j+k, 3k+i), k = 0..3, of x = 3i+j are in the target.  Then E = ker L, and
// dom_E = E^perp \ {0} = (row space of L) \ {0}, as 9-bit functionals X = sum of rows of L (X(a) = Y(L(a)) for the reduced
// functional Y).  The label of v is the smallest 9-bit a with L(a) = v (the minimum of the coset).  All of this is cross-checked:
// E against the class basis of seeded334.tsv, the two derivations of dom_E against each other, and every SAT solution against the
// target file itself.
//
// Per leaf, one line on stdout:  VERDICT <instance line>| ...   with VERDICT one of
//   UNSAT  certificate built, written in the v5c-334 format and accepted by the model of the checker rules
//   SAT    a decomposition exists (found and verified against T on dom_E and against the target file); no certificate
//   NOCERT the SAT search finished: no decomposition (UNSAT) but certificate generation exceeded --maxnodes
//   BIG    more than --maxnodes certificate nodes (undecided)       ERR   internal error / model rejection
// Apache-2.0.  Port of cpp/enum/gen7c.cc and gen7.h of rank333-f2 (Apache-2.0, doi:10.5281/zenodo.23236154).
#include <bits/stdc++.h>
#include <unistd.h>
#include "gen7_334.h"
#include "model334.h"

static bool file_exists(const std::string& p) { return access(p.c_str(), R_OK) == 0; }
static std::string exe_dir() {
  char buf[4096]; ssize_t k = readlink("/proc/self/exe", buf, sizeof buf - 1);
  if (k <= 0) return ".";
  buf[k] = 0; std::string s(buf); size_t p = s.rfind('/'); return p == std::string::npos ? "." : s.substr(0, p);
}
static std::string default_data(const char* name, const char* envname) {
  if (const char* e = getenv(envname)) if (*e) return e;
  std::string p = exe_dir() + "/../data/" + name;
  if (file_exists(p)) return p;
  return std::string("data/") + name;
}

struct Quot {
  int D = 0;
  int Lrow[9] = {0};            // row xp of L as a 9-bit functional
  int Lcol[9] = {0};            // L(1 << x), D-bit
  std::vector<int> Ebasis;      // basis of E = ker L (9-bit)
  std::set<int> Eset;
  std::vector<int> dom;         // X in rowspace(L) \ {0}, ascending
  std::vector<int> label;       // label[v] = min{a : L(a) = v}
  std::vector<std::array<int, 3>> target;   // the target entries (xp, y, z)
};
static int Lof(const Quot& q, int a) { int r = 0; for (int x = 0; x < 9; x++) if ((a >> x) & 1) r ^= q.Lcol[x]; return r; }

// read tsolve334's target file and derive L, E, dom_E, labels (see the header comment); throws on any inconsistency
static Quot quot_from_target(const std::string& tfile) {
  FILE* f = fopen(tfile.c_str(), "r"); if (!f) throw std::runtime_error("cannot open target " + tfile);
  static unsigned char tg[16][12][12]; memset(tg, 0, sizeof tg);
  int x, y, z, mx = -1; long entries = 0;
  while (fscanf(f, "%d %d %d", &x, &y, &z) == 3) {
    if (x < 0 || x >= 9 || y < 0 || y >= 12 || z < 0 || z >= 12) { fclose(f); throw std::runtime_error("target entry out of range"); }
    tg[x][y][z] ^= 1; mx = std::max(mx, x);
  }
  fclose(f);
  Quot q; q.D = mx + 1;
  if (q.D < 1 || q.D > 9) throw std::runtime_error("target: bad number of quotient coordinates");
  for (int xp = 0; xp < q.D; xp++) for (int y2 = 0; y2 < 12; y2++) for (int z2 = 0; z2 < 12; z2++) if (tg[xp][y2][z2]) { entries++; q.target.push_back({xp, y2, z2}); }
  long explained = 0;
  for (int xp = 0; xp < q.D; xp++) for (int xx = 0; xx < 9; xx++) {
    int i = xx / 3, j = xx % 3, cnt = 0;
    for (int k = 0; k < 4; k++) cnt += tg[xp][4 * j + k][3 * k + i];
    if (cnt != 0 && cnt != 4) throw std::runtime_error("target: slice of T[x] only partly present (not a quotient of T334)");
    if (cnt == 4) { q.Lrow[xp] |= 1 << xx; q.Lcol[xx] |= 1 << xp; explained += 4; }
  }
  if (explained != entries) throw std::runtime_error("target: entries outside the supports of the slices T[x]");
  // L must have rank D (independent rows)
  { int bas[9] = {0}, rk = 0;
    for (int xp = 0; xp < q.D; xp++) { int v = q.Lrow[xp]; while (v) { int h = 31 - __builtin_clz(v); if (!bas[h]) { bas[h] = v; rk++; break; } v ^= bas[h]; } }
    if (rk != q.D) throw std::runtime_error("target: the quotient map L does not have rank D"); }
  // E = ker L; a basis by greedy elimination in ascending order
  { int bas[9] = {0};
    for (int a = 1; a < 512; a++) if (Lof(q, a) == 0) {
      q.Eset.insert(a);
      int v = a; while (v) { int h = 31 - __builtin_clz(v); if (!bas[h]) { bas[h] = v; q.Ebasis.push_back(a); break; } v ^= bas[h]; }
    }
    q.Eset.insert(0); }
  if ((int)q.Eset.size() != (1 << (9 - q.D))) throw std::runtime_error("target: |ker L| != 2^(9-D)");
  // dom_E from the rows of L: all nonempty combinations
  { std::set<int> s;
    for (int m = 1; m < (1 << q.D); m++) { int X = 0; for (int xp = 0; xp < q.D; xp++) if ((m >> xp) & 1) X ^= q.Lrow[xp]; s.insert(X); }
    if ((int)s.size() != (1 << q.D) - 1 || s.count(0)) throw std::runtime_error("target: rows of L dependent");
    q.dom.assign(s.begin(), s.end()); }
  q.label.assign(1 << q.D, -1);
  for (int a = 0; a < 512; a++) { int v = Lof(q, a); if (q.label[v] < 0) q.label[v] = a; }
  for (int v = 0; v < (1 << q.D); v++) if (q.label[v] < 0) throw std::runtime_error("target: L not surjective");
  return q;
}

// the class basis of seeded334.tsv (column 3, comma separated) for class number cls
static bool seeded_basis(const std::string& path, int cls, std::vector<int>& basis) {
  std::ifstream in(path); if (!in) return false;
  std::string line;
  while (std::getline(in, line)) {
    std::vector<std::string> f; size_t p = 0;
    while (true) { size_t q = line.find('\t', p); if (q == std::string::npos) { f.push_back(line.substr(p)); break; } f.push_back(line.substr(p, q - p)); p = q + 1; }
    if (f.size() < 3 || f[0] == "idx") continue;
    if (std::stoi(f[0]) != cls) continue;
    basis = s334::parse_list(f[2]); return true;
  }
  return false;
}
static std::set<int> span_of(const std::vector<int>& basis) {
  std::set<int> s{0}; for (int e : basis) { std::vector<int> cur(s.begin(), s.end()); for (int v : cur) s.insert(v ^ e); } return s;
}

static std::string hex_of(const g7x::BW& w) {
  std::string hex; char buf[17];
  for (size_t i = (w.n + 63) / 64; i > 0; i--) { snprintf(buf, sizeof buf, hex.empty() ? "%llx" : "%016llx", (unsigned long long)w.w[i - 1]); if (hex.empty() && w.w[i - 1] == 0) continue; hex += buf; }
  if (hex.empty()) hex = "0";
  return hex;
}
// the inverse: nbits and a hex string (most significant digit first) -> words
static bool words_of_hex(const std::string& hex, size_t nbits, std::vector<unsigned long long>& w) {
  w.assign((nbits + 63) / 64 + 1, 0);
  size_t nd = hex.size();
  for (size_t i = 0; i < nd; i++) {
    char ch = hex[nd - 1 - i]; int v;
    if (ch >= '0' && ch <= '9') v = ch - '0'; else if (ch >= 'a' && ch <= 'f') v = ch - 'a' + 10; else if (ch >= 'A' && ch <= 'F') v = ch - 'A' + 10; else return false;
    for (int q = 0; q < 4; q++) if ((v >> q) & 1) { size_t pos = 4 * i + q; if (pos >= nbits) return false; w[pos >> 6] |= 1ULL << (pos & 63); }
  }
  return true;
}

// ------------------------------------------------------------------------------------------------ model self-test on the worked examples
struct StreamBits {   // an explicit bit string, built field by field (independent of g7x::BW)
  std::vector<char> b;
  void put(unsigned long long x, int k) { for (int i = 0; i < k; i++) b.push_back((x >> i) & 1); }
  void put_mask(const std::vector<int>& set) { std::vector<char> m(512, 0); for (int X : set) m[X] = 1; for (char c : m) b.push_back(c); }
  void to_words(std::vector<unsigned long long>& w) const { w.assign(b.size() / 64 + 2, 0); for (size_t i = 0; i < b.size(); i++) if (b[i]) w[i >> 6] |= 1ULL << (i & 63); }
};
static int selftest_examples(const s334::SymTab& st) {
  // E = span{1}: dom_E = the even nonzero X, M = sum_{k=1}^{255} 2^(2k)
  m334::Model m(st, std::vector<int>{1});
  std::vector<int> evens; for (int k = 1; k <= 255; k++) evens.push_back(2 * k);
  { std::vector<int> d; for (int X : m.domE) d.push_back(X); if (d != evens) { fprintf(stderr, "selftest: dom_E for E = span{1} is not the set {2k}\n"); return 1; } }
  struct Case { const char* name; int n; int dommode; bool mask_ok; int extraX; int tagX; bool expect; };
  auto build = [&](int n, int term, int dommode, bool with_mask, int addX, int X) {
    StreamBits s; s.put(1, 1);                       // batch tag: one leaf
    s.put(n, 6); for (int t = 0; t < n; t++) s.put(term, 9);
    s.put(dommode, 2);
    if (with_mask) { std::vector<int> d = evens; if (addX) d.push_back(addX); s.put_mask(d); }
    s.put(0, 1); s.put(X, 9);                        // over X
    return s;
  };
  int bad = 0;
  struct T { const char* name; StreamBits s; bool expect; };
  std::vector<T> ts;
  ts.push_back({"E1 (n=3, terms 2 2 2, over 2)", build(3, 2, 1, true, 0, 2), true});
  ts.push_back({"E1' (n=4: u = rank, strict inequality)", build(4, 2, 1, true, 0, 2), false});
  ts.push_back({"E1-dom0 (dommode 00, no mask)", build(3, 2, 0, false, 0, 2), false});
  ts.push_back({"E1-domX (mask + X=1 not in E^perp)", build(3, 2, 1, true, 1, 2), false});
  ts.push_back({"E1 with dommode 11", build(3, 2, 3, true, 0, 2), false});
  ts.push_back({"E1 with over 3 (3 not in dom_E)", build(3, 2, 1, true, 0, 3), false});
  ts.push_back({"E1 with a label 3 (not the coset minimum 2)", build(3, 3, 1, true, 0, 2), false});
  for (auto& t : ts) {
    std::vector<unsigned long long> w; t.s.to_words(w); std::string why;
    bool ok = m.check_stream(w, t.s.b.size(), &why);
    printf("selftest %-48s expect %s got %s%s%s\n", t.name, t.expect ? "ACCEPT" : "REJECT", ok ? "ACCEPT" : "REJECT", ok ? "" : "  (", ok ? "" : (why + ")").c_str());
    if (ok != t.expect) bad++;
  }
  // the bit positions of the stream format for E1: n bits 0-5 of the leaf, terms at 6/15/24, dommode 33-34, M 35-546, tag 547, X 548-556
  { StreamBits s = build(3, 2, 1, true, 0, 2); size_t expect_len = 1 + 6 + 27 + 2 + 512 + 1 + 9;
    // (one-leaf batch: every position of the leaf record is shifted by the batch tag bit)
    if (s.b.size() != expect_len || s.b[1 + 547] != 0 || s.b[1 + 549] != 1 || s.b[1 + 548] != 0 || s.b[1 + 550] != 0) { printf("selftest: E1 layout differs from the stream format\n"); bad++; } }
  printf("selftest: %s\n", bad ? "FAILED" : "all expected verdicts obtained");
  return bad ? 1 : 0;
}

// ------------------------------------------------------------------------------------------------ mutation test of the model
struct MutStats { long total = 0, rejected = 0, accepted = 0; std::map<std::string, std::pair<long, long>> byclass; };
static void run_mutants(m334::Model& model, const g7x::BW& w, int nlabels, int N, unsigned long long seed, const std::string& tag, MutStats& ms) {
  std::mt19937_64 rng(seed);
  size_t hdr = 1 + 6 + 9 * (size_t)nlabels + 2 + 512;   // batch tag, n, labels, dommode, mask
  auto flip = [](std::vector<unsigned long long>& v, size_t pos) { v[pos >> 6] ^= 1ULL << (pos & 63); };
  for (int i = 0; i < N; i++) {
    std::vector<unsigned long long> v = w.w; size_t nbits = w.n; std::string cls;
    int kind = (int)(rng() % 6);
    if (kind == 0 || kind == 1) { size_t pos = hdr + rng() % (w.n - hdr); flip(v, pos); cls = "cert-bit-flip"; }
    else if (kind == 2) { flip(v, 1 + 6 + 9 * nlabels + (rng() % 2)); cls = "dommode-flip"; }
    else if (kind == 3) { flip(v, 1 + 6 + 9 * nlabels + 2 + rng() % 512); cls = "mask-bit-flip"; }
    else if (kind == 4) { flip(v, 1 + 6 + 9 * (rng() % nlabels) + rng() % 9); cls = "label-bit-flip"; }
    else { size_t cut = 1 + rng() % 64; nbits = (w.n > cut + hdr) ? w.n - cut : w.n - 1; cls = "truncate"; }
    std::string why; bool ok = model.check_stream(v, nbits, &why);
    ms.total++; auto& c = ms.byclass[cls]; c.first++;
    if (ok) {
      ms.accepted++; c.second++;
      printf("# mutant ACCEPTED: leaf %s class %s (valid refutation under the checker rules; check by hand if the class is header-related)\n", tag.c_str(), cls.c_str());
    } else ms.rejected++;
  }
}


int main(int argc, char** argv) {
  int K = 4, deadk = 6; std::vector<int> Ks{4, 8}; long long maxnodes = 300000; bool nofit = false, fitf = false, nomodel = false, tabcheck = true, deep = false, quiet = false, labels_mode = false, symroot = true, satonly = false, selftest = false;
  long long satsearch = 0, satfirst = 1000; int mutants = 0; bool dumpleaf = false, bestmode = false, planted = false, rootcounts = false; size_t fitNT = 15, fitSL = 7;
  std::string tfile, ifile, symfile, seededfile, hexfile, Earg, checkhex; int cls = -1, from = 1, to = INT_MAX, trace = 0;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto need = [&](const char* what) { if (i + 1 >= argc) { fprintf(stderr, "missing value for %s\n", what); exit(1); } return std::string(argv[++i]); };
    if (a == "--K") { K = atoi(need("--K").c_str()); Ks = {K}; }
    else if (a == "--Ks") { Ks = s334::parse_list(need("--Ks")); if (Ks.empty()) { fprintf(stderr, "--Ks needs a comma separated list\n"); return 1; } K = Ks[0]; }
    else if (a == "--deadk") deadk = atoi(need("--deadk").c_str());
    else if (a == "--maxnodes") maxnodes = atoll(need("--maxnodes").c_str());
    else if (a == "--fit") fitf = true; else if (a == "--nofit") nofit = true; else if (a == "--nomodel") nomodel = true;
    else if (a == "--fitcaps") { fitNT = (size_t)atoi(need("--fitcaps").c_str()); fitSL = (size_t)atoi(need("--fitcaps").c_str()); }
    else if (a == "--nosymroot") symroot = false; else if (a == "--best") bestmode = true; else if (a == "--planted") planted = true;
    else if (a == "--no-tabcheck") tabcheck = false; else if (a == "--deep-tabcheck") deep = true; else if (a == "--quiet") quiet = true;
    else if (a == "--target") tfile = need("--target"); else if (a == "--symtab") symfile = need("--symtab");
    else if (a == "--seeded") seededfile = need("--seeded"); else if (a == "--class") cls = atoi(need("--class").c_str());
    else if (a == "--hex") hexfile = need("--hex"); else if (a == "--labels") labels_mode = true; else if (a == "--E") Earg = need("--E");
    else if (a == "--from") from = atoi(need("--from").c_str()); else if (a == "--to") to = atoi(need("--to").c_str());
    else if (a == "--trace") trace = atoi(need("--trace").c_str());
    else if (a == "--satsearch") satsearch = atoll(need("--satsearch").c_str()); else if (a == "--satfirst") satfirst = atoll(need("--satfirst").c_str());
    else if (a == "--satonly") satonly = true; else if (a == "--mutants") mutants = atoi(need("--mutants").c_str());
    else if (a == "--dump-leaf") dumpleaf = true; else if (a == "--rootcounts") rootcounts = true;
    else if (a == "--check-hex") checkhex = need("--check-hex"); else if (a == "--selftest") selftest = true;
    else if (!a.empty() && a[0] == '-') { fprintf(stderr, "bad option %s\n", a.c_str()); return 1; }
    else ifile = a;
  }
  if (satonly && satsearch <= 0) satsearch = 200000;
  bool need_inst = !selftest && checkhex.empty();
  if ((need_inst && ifile.empty()) || (!selftest && !labels_mode && tfile.empty()) || (!selftest && labels_mode && Earg.empty())) {
    fprintf(stderr, "usage: gen7_334 [options] --target TARGET.t INSTANCES   |   gen7_334 [options] --labels --E e1,e2,.. INSTANCES\n"
                    "       gen7_334 --target TARGET.t --check-hex STREAMS   |   gen7_334 --selftest           (see the header of gen7_334.cc)\n");
    return 1;
  }
  try {
    if (symfile.empty()) symfile = default_data("symtab334.tsv", "GEN7_SYMTAB");
    s334::SymTab st = s334::load(symfile);
    if (tabcheck) {
      std::string bad = s334::validate(st); if (!bad.empty()) { fprintf(stderr, "symtab %s INVALID: %s\n", symfile.c_str(), bad.c_str()); return 3; }
      if (deep) { bad = s334::validate_deep(st); if (!bad.empty()) { fprintf(stderr, "symtab %s INVALID (deep): %s\n", symfile.c_str(), bad.c_str()); return 3; } }
    }
    if (selftest) return selftest_examples(st);
    // ---- E, dom_E and the label map
    Quot q; std::vector<int> Ebasis, dom;
    if (!labels_mode) {
      q = quot_from_target(tfile);
      Ebasis = q.Ebasis; dom = q.dom;
      if (cls < 0) { // class number from .../qS_c<N>.t
        size_t p = tfile.rfind("_c"), e = tfile.rfind('.');
        if (p != std::string::npos && e != std::string::npos && e > p + 2) { std::string s = tfile.substr(p + 2, e - p - 2); if (!s.empty() && std::all_of(s.begin(), s.end(), ::isdigit)) cls = atoi(s.c_str()); }
      }
      if (cls >= 0) {
        if (seededfile.empty()) seededfile = default_data("seeded334.tsv", "GEN7_SEEDED");
        std::vector<int> sb;
        if (!seeded_basis(seededfile, cls, sb)) { fprintf(stderr, "WARNING: class %d not found in %s: E not cross-checked\n", cls, seededfile.c_str()); }
        else {
          std::set<int> ss = span_of(sb);
          if (ss != q.Eset) { fprintf(stderr, "E derived from the target (dim %d) differs from the class %d basis of %s\n", 9 - q.D, cls, seededfile.c_str()); return 3; }
          if (!quiet) fprintf(stderr, "E = ker L (dim %d, D = %d) equals span of the class %d basis in %s\n", 9 - q.D, q.D, cls, seededfile.c_str());
        }
      } else fprintf(stderr, "WARNING: class number unknown: E not cross-checked against seeded334.tsv\n");
    } else {
      Ebasis = s334::parse_list(Earg);
      for (int e : Ebasis) if (e < 1 || e > 511) { fprintf(stderr, "bad E vector %d\n", e); return 1; }
      for (int X = 1; X < 512; X++) { bool ok = true; for (int e : Ebasis) if (__builtin_parity(X & e)) { ok = false; break; } if (ok) dom.push_back(X); }
    }
    m334::Model model(st, Ebasis);
    if (model.domE != dom) { fprintf(stderr, "internal error: the two derivations of dom_E differ\n"); return 3; }
    std::set<int> Espan = span_of(Ebasis);

    // ---- re-check mode: certificate streams from a file
    if (!checkhex.empty()) {
      std::ifstream hin(checkhex); if (!hin) { fprintf(stderr, "cannot open %s\n", checkhex.c_str()); return 1; }
      std::string ln; long nacc = 0, nrej = 0;
      while (std::getline(hin, ln)) {
        std::stringstream ss(ln); std::string tag, hx; size_t nb = 0; if (!(ss >> tag >> nb >> hx)) continue;
        std::vector<unsigned long long> w; std::string why; long long nl = 0;
        if (!words_of_hex(hx, nb, w)) { printf("REJECT %s bad hex or length\n", tag.c_str()); nrej++; continue; }
        model.trace_left = trace; model.tf = trace ? stdout : nullptr;
        bool ok = model.check_stream(w, nb, &why, &nl);
        if (ok) { printf("ACCEPT %s nodes=%lld bits=%zu\n", tag.c_str(), model.nodes, nb); nacc++; } else { printf("REJECT %s %s\n", tag.c_str(), why.c_str()); nrej++; }
      }
      fprintf(stderr, "check-hex: accepted %ld rejected %ld\n", nacc, nrej);
      return nrej ? 2 : 0;
    }

    g7x::init_tables(st);
    FILE* hf = nullptr; if (!hexfile.empty()) { hf = fopen(hexfile.c_str(), "a"); if (!hf) { fprintf(stderr, "cannot open %s\n", hexfile.c_str()); return 1; } }
    if (!quiet) fprintf(stderr, "gen7_334: |dom_E| = %zu, dim E = %zu, K = %d, deadk = %d, maxnodes = %lld, symtab %s\n", dom.size(), Ebasis.size(), K, deadk, maxnodes, symfile.c_str());

    std::ifstream in(ifile); if (!in) { fprintf(stderr, "cannot open %s\n", ifile.c_str()); return 1; }
    std::string line; int lineno = 0;
    long nUnsat = 0, nSat = 0, nBig = 0, nErr = 0, nNoc = 0, nPlFail = 0; std::vector<size_t> bitsv; MutStats ms;
    while (std::getline(in, line)) {
      std::string tag, body = line; auto p = line.find(':');
      if (p != std::string::npos) { tag = line.substr(0, p); body = line.substr(p + 1); }
      std::stringstream ss(body); std::vector<int> v; int xx; while (ss >> xx) v.push_back(xx);
      if (v.empty()) continue;
      lineno++; if (lineno < from) continue; if (lineno > to) break;
      if (tag.empty()) tag = "line" + std::to_string(lineno);
      std::vector<int> labels; bool bad = false; std::string why;
      for (int vv : v) {
        int a;
        if (!labels_mode) { if (vv < 1 || vv >= (1 << q.D)) { bad = true; why = "term outside [1, 2^D)"; break; } a = q.label[vv]; }
        else {
          a = vv;
          if (a < 1 || a > 511) { bad = true; why = "label outside [1, 511]"; break; }
          for (int e : Espan) if ((a ^ e) < a) { bad = true; why = "label is not the smallest vector of its coset"; break; }
          if (bad) break;
        }
        labels.push_back(a);
      }
      auto pr = [&](const char* verdict, const std::string& extra) {   // same shape as tsolve334: VERDICT <instance line>| ...
        std::string full = (line.find(':') == std::string::npos) ? (tag + ": " + line) : line;
        printf("%s %s|%s\n", verdict, full.c_str(), extra.c_str());
        fflush(stdout);
      };
      if (bad) { nErr++; pr("ERR", " bad leaf: " + why); continue; }
      if (labels.size() > 31) { nErr++; pr("ERR", " n > 31 (not encodable in v5c-334)"); continue; }
      if (rootcounts) {   // cross-check hook: compare with `ts_rootcounts --rootcounts` (a copy of tsolve334 that prints the same counts)
        g7x::Leaf L(labels, dom); std::vector<long long> cs, cp; std::vector<int> n1, n2;
        L.root_counts(true, cs, n1); L.root_counts(false, cp, n2);
        if (cs.empty() || cs[0] < 0) continue;   // OVER at the root: tsolve334 prints nothing either
        printf("ROOTCOUNTS %s sym:", tag.c_str()); for (long long c : cs) printf(" %lld", c);
        printf(" | plain:"); for (long long c : cp) printf(" %lld", c);
        printf(" | nt:"); for (int c : n1) printf(" %d", c); printf("\n");
        continue;
      }
      // verify a decomposition against T on dom_E and (reduced mode) against the target file; returns the "B ... C ..." text
      auto verify_sat = [&](const std::vector<g7x::Asg>& sol, bool& ok) {
        std::vector<int> B(labels.size(), 0), C(labels.size(), 0); ok = true;
        if (sol.size() != labels.size()) ok = false;
        for (auto& g : sol) { B[g.t] = g.b; C[g.t] = g.c; if (!g.b || !g.c) ok = false; }
        for (int X : dom) for (int y = 0; y < 12 && ok; y++) {
          int row = model.TXm[X][y];
          for (size_t t = 0; t < labels.size(); t++) if (__builtin_parity(X & labels[t]) && ((B[t] >> y) & 1)) row ^= C[t];
          if (row) ok = false;
        }
        if (!labels_mode && ok) {
          std::set<std::array<int, 3>> tgt(q.target.begin(), q.target.end());
          for (int x2 = 0; x2 < q.D && ok; x2++) for (int y = 0; y < 12 && ok; y++) for (int z = 0; z < 12; z++) {
            int s = 0; for (size_t t = 0; t < labels.size(); t++) s ^= ((v[t] >> x2) & 1) & ((B[t] >> y) & 1) & ((C[t] >> z) & 1);
            if (s != (int)tgt.count({x2, y, z})) { ok = false; break; }
          }
        }
        std::string s = std::string(" | verified ") + (ok ? "1" : "0") + " | B";
        for (int bb : B) s += " " + std::to_string(bb);
        s += " C"; for (int cc : C) s += " " + std::to_string(cc);
        return s;
      };
      // the planted-path test: follow a decomposition down the certificate generator's tree (see Leaf::follow)
      auto planted_test = [&](const std::vector<g7x::Asg>& sol) -> std::string {
        g7x::Leaf::Follow F; F.B.assign(labels.size(), 0); F.C.assign(labels.size(), 0); F.st = &st;
        for (auto& g : sol) { F.B[g.t] = g.b; F.C[g.t] = g.c; }
        g7x::Leaf L2(labels, dom); L2.symroot = symroot; L2.follow = &F;
        std::string sizes; auto fill = [&]() { for (size_t s : F.listsizes) sizes += " " + std::to_string(s); };
        try { L2.gen(K, maxnodes, deadk); fill(); nPlFail++; return "FAILED: the tree was completed without reaching the planted decomposition; list sizes" + sizes; }
        catch (g7x::Sat&) { fill(); return "OK: at all " + std::to_string(F.listsizes.size()) + " branch nodes of the path the planted pair is a candidate, no OVER on the path; candidate-list sizes" + sizes; }
        catch (g7x::Leaf::FollowFail& e) { fill(); nPlFail++; return std::string("FAILED: ") + e.what() + "; list sizes" + sizes; }
        catch (g7x::Big&) { return "inconclusive (maxnodes)"; }
      };
      // certificate generation for one choice of the look-ahead width and of sym at the root
      struct CertRes { int status = 3; g7x::BW w; long long n0 = 0, n1 = 0; double gt = 0; std::string mres, msg; bool fitused = false; std::vector<g7x::Asg> sol; long long cnt = 0; int Kv = 0; bool symv = true; };
      auto try_cert = [&](int Kv, bool symv) {
        CertRes r; r.Kv = Kv; r.symv = symv;
        for (int att = fitf ? 1 : 0; att < 2; att++) {
          auto t0 = std::chrono::steady_clock::now();
          g7x::Leaf L(labels, dom); L.fit = (att == 1); L.symroot = symv; L.fitNT = fitNT; L.fitSL = fitSL;
          try {
            g7x::Cert* c = L.gen(Kv, maxnodes, deadk);
            long long nodes0 = 0; g7x::stats(c, nodes0);
            c = L.finalize(c);
            long long nodes1 = 0; g7x::stats(c, nodes1);
            g7x::BW w; g7x::enc_leaf(w, labels, dom, c);
            r.gt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
            r.n0 = nodes0; r.n1 = nodes1; r.fitused = L.fit; r.mres = "model skipped"; bool ok = true;
            if (!nomodel) {
              auto t1 = std::chrono::steady_clock::now();
              std::string why2; long long nl = 0;
              model.trace_left = 0; model.tf = nullptr;
              ok = model.check_stream(w.w, w.n, &why2, &nl);
              double mt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t1).count();
              char b[200];
              if (ok) { snprintf(b, sizeof b, "model ok (%lld nodes, %lld claims, depth %d, %.3fs)", model.nodes, model.claims, model.maxDepth, mt); r.mres = b; }
              else { r.mres = "MODEL REJECTS: " + why2; r.msg = r.mres; }
            }
            r.w = w; r.status = ok ? 0 : 3;
          } catch (g7x::Big&) {
            r.status = 1;
          } catch (g7x::Sat&) {
            r.status = 2; r.sol = L.sol; r.cnt = L.cnt;
          } catch (std::runtime_error& e) {
            if (att == 0 && !nofit && std::string(e.what()).find("overflow") != std::string::npos) continue;   // retry with the fit fallback
            r.status = 3; r.msg = std::string("exception: ") + e.what();
          }
          break;
        }
        return r;
      };
      std::string extra, verdict = "ERR"; bool big = false;
      if (!satonly) {
        // look-ahead widths tried (default 4 then 8; the smallest accepted certificate is kept); --best adds the variants without
        // sym at the root.  A tree of at most 5 nodes is not retried (no other width can make it much smaller).
        std::vector<std::pair<int, bool>> variants;
        for (int k : Ks) variants.push_back({k, symroot});
        if (bestmode) for (int k : Ks) variants.push_back({k, !symroot});
        CertRes best; bool have = false; double tt = 0;
        // preference: SAT (stop), then the smallest accepted certificate, then BIG, then an error
        auto better = [&](const CertRes& r) {
          if (!have) return true;
          if (r.status == 0) return best.status != 0 || r.w.n < best.w.n;
          if (best.status == 0) return false;
          return best.status == 3 && r.status == 1;
        };
        for (auto& vt : variants) {
          CertRes r = try_cert(vt.first, vt.second); tt += r.gt;
          if (r.status == 2) { best = r; have = true; break; }
          if (better(r)) { best = r; have = true; }
          if (best.status == 0 && best.n1 <= 5) break;
        }
        if (best.status == 0) {
          const CertRes& r = best;
          char b2[500];
          snprintf(b2, sizeof b2, " certnodes %lld bits %zu time %.4fs gen_nodes %lld%s K=%d%s | %s", r.n1, r.w.n, tt, r.n0, r.fitused ? " fit" : "", r.Kv, r.symv ? "" : " nosym", r.mres.c_str());
          extra = b2; verdict = "UNSAT"; bitsv.push_back(r.w.n);
          if (trace) { model.trace_left = trace; model.tf = stdout; std::string w2; model.check_stream(r.w.w, r.w.n, &w2); model.tf = nullptr; model.trace_left = 0; }
          if (dumpleaf) {   // human-readable decoding of the header of the stream (for the worked examples)
            g7x::BW mk; unsigned long long mw[8] = {0, 0, 0, 0, 0, 0, 0, 0}; for (int X : dom) mw[X >> 6] |= 1ULL << (X & 63);
            for (int i = 0; i < 8; i++) mk.put(mw[i], 64);
            size_t pl = 1 + 6 + 9 * labels.size(), pm = pl + 2, pc = pm + 512;
            printf("# leaf %s: n = %zu, first factors in the reduced coordinates of the instance file:", tag.c_str(), labels.size());
            for (int vv : v) printf(" %d", vv);
            printf("\n# 9-bit labels a_t (smallest vector of each coset a_t + E), in the same order:");
            for (int a : labels) printf(" %d", a);
            printf("\n# E basis (9-bit masks, bit 3i+j = entry (i,j)):"); for (int e : Ebasis) printf(" %d", e);
            printf("   |E| = %zu, |dom_E| = %zu\n", Espan.size(), dom.size());
            printf("# dom_E mask (512-bit natural number, bit X set iff X in E^perp \\ {0}), hex: %s\n", hex_of(mk).c_str());
            printf("# stream bit positions (one-leaf batch): batch tag 0 | n 1-6 | labels 7-%zu | dommode %zu-%zu | mask %zu-%zu | certificate %zu-%zu\n", pl - 1, pl, pl + 1, pm, pc - 1, pc, r.w.n - 1);
            printf("# stream (%zu bits), hex, most significant digit first: %s\n", r.w.n, hex_of(r.w).c_str());
          }
          if (hf) fprintf(hf, "%s %zu %s\n", tag.c_str(), r.w.n, hex_of(r.w).c_str());
          if (mutants > 0) run_mutants(model, r.w, (int)labels.size(), mutants, 1469598103934665603ULL ^ (unsigned long long)lineno * 1099511628211ULL, tag, ms);
        } else if (best.status == 2) {
          bool ok; std::string s = verify_sat(best.sol, ok);
          char b[100]; snprintf(b, sizeof b, " nodes %lld", best.cnt);
          verdict = ok ? "SAT" : "ERR"; extra = std::string(b) + s;
          if (ok && planted) printf("# planted-path test %s: %s\n", tag.c_str(), planted_test(best.sol).c_str());
        } else if (best.status == 1) {
          verdict = "BIG"; big = true; char b[100]; snprintf(b, sizeof b, " certnodes>%lld", maxnodes); extra = b;
        } else { verdict = "ERR"; extra = " " + best.msg; }
      } else big = true;
      if (big && satsearch > 0) {   // look for a decomposition: randomized restarts
        auto t0 = std::chrono::steady_clock::now();
        g7x::Leaf L(labels, dom); L.symroot = symroot; long long used = 0;
        int res = L.sat_search(satsearch, satfirst, 0x9e3779b97f4a7c15ULL ^ (unsigned long long)lineno, &used);
        double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        char b[160]; snprintf(b, sizeof b, " satsearch nodes %lld time %.3fs", used, dt);
        if (res == 1) {
          bool ok; std::string s = verify_sat(L.sol, ok); verdict = ok ? "SAT" : "ERR"; extra = std::string(b) + s;
          if (ok && planted) printf("# planted-path test %s: %s\n", tag.c_str(), planted_test(L.sol).c_str());
        }
        else if (res == 0) { verdict = "NOCERT"; extra = std::string(b) + " | no decomposition exists (complete search); no certificate within --maxnodes"; }
        else { verdict = "BIG"; extra += std::string(b) + " | no decomposition found within the budget"; }
      }
      if (verdict == "UNSAT") nUnsat++; else if (verdict == "SAT") nSat++; else if (verdict == "BIG") nBig++; else if (verdict == "NOCERT") nNoc++; else nErr++;
      pr(verdict.c_str(), extra);
    }
    if (hf) fclose(hf);
    std::sort(bitsv.begin(), bitsv.end());
    fprintf(stderr, "gen7_334 summary: leaves %ld  UNSAT(cert) %ld  SAT %ld  NOCERT %ld  BIG %ld  ERR %ld", nUnsat + nSat + nBig + nErr + nNoc, nUnsat, nSat, nNoc, nBig, nErr);
    if (!bitsv.empty()) fprintf(stderr, "  cert bits min %zu median %zu max %zu", bitsv.front(), bitsv[bitsv.size() / 2], bitsv.back());
    fprintf(stderr, "\n");
    if (planted) fprintf(stderr, "planted-path tests failed: %ld\n", nPlFail);
    if (mutants > 0) {
      fprintf(stderr, "mutants: total %ld rejected %ld accepted %ld\n", ms.total, ms.rejected, ms.accepted);
      for (auto& kv : ms.byclass) fprintf(stderr, "  %-16s total %ld accepted %ld\n", kv.first.c_str(), kv.second.first, kv.second.second);
    }
    return (nErr || nPlFail) ? 2 : 0;
  } catch (std::exception& e) {
    fprintf(stderr, "gen7_334: fatal: %s\n", e.what());
    return 3;
  }
}
