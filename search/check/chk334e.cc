// chk334e.cc -- independent checker of the capacity-search traces (format 'LEB9') for the tensor <3,3,4> over F2.
//
// Written from a description of the IP and trace formats and from the input files only.
// No other source or tool of the project was read.
//
// Build:  g++ -O2 -std=c++17 -o chk334e chk334e.cc          (see build.sh)
// Usage:  chk334e --table seeded334.tsv --class C --ip IP.txt [--leaves F] [--out-leaves F] TRACE...
//         chk334e --table seeded334.tsv --batch FILE        (one run per line, shared orbit pass)
//         see usage() below for all options.
//
// Output lines are stable keywords (RESULT PASS|FAIL, COVERAGE COMPLETE|INCOMPLETE, BLOCK_FAIL ... code=...).
//
// Arithmetic: every dual quantity (T_l, B, gap, products, quotients) is exact signed
// 128-bit arithmetic.  There is no 64-bit accumulation in the dual evaluation.  The test-only options
// --mut-arith64 and --mut-unsigned-slack switch to deliberately wrong evaluations (to test
// that the arithmetic mutants are caught); they print "MUTANT-EVALUATOR" and never print RESULT PASS.
//
// TYPICAL USE
//   one run  : chk334e --table seeded334.tsv --manifest MANIFEST.sha256 --base DIR
//                      --id P708R2 --class 708 --R 25 --ip ip_P708R2_seeded_L25.txt [--raise RAISES]
//                      --leaves LEAVES.txt --out-leaves COVERING_LEAVES.txt --traces-from LIST_OF_TRACE_FILES
//              (absolute paths; with --manifest every file under --base must be listed in the manifest and hash equal)
//   parallel : N workers `... --emit-blocks W<i>.sum TRACES_i` (RESULT WORKER-PASS), then one `... --merge-list SUMMARIES
//              --traces-from ALL_TRACE_FILES` (decides coverage, leaves, RESULT).  A worker repeats the IP recomputation (~10 s).
//   batch    : --batch FILE, one run per line, all runs share the orbit pass (2 s)
//
// READINGS (places where the format description leaves a choice; each is applied as stated here)
//   R1  lb of a class = column `seeded` of seeded334.tsv; classes raised for a run come from --raise FILE (lines "class_idx lb";
//       the list is an input, not derived here).  Verified: the nine line IPs match with seeded values only.
//   R2  bit 3r+c of a 9-bit vector is entry (r,c) of a 3x3 matrix; G0 = {a -> P a Q}.  Any row/column arrangement gives the same set
//       of linear maps; the table's rank counts n1,n2,n3 are re-checked for all 710 classes.
//   R3  after the dual fixings of an O node, the fixed u is used for the cut condition, for the eligible children and for the P
//       lookaheads (fixings are local to the subtree, undone at E).  Confirmed by the production traces (cut kinds 1 and 3).
//   R4  Z count = number of L, F, K and O records of the block (C and P records are not nodes).  Confirmed on the production traces.
//   R5  a `C l` record is accepted for an eligible label l whether or not s+[l] is canonical; "nothing" needs non-canonicity.
//       Canonicity test: some listed permutation (applied as listed, image of label index) maps s+[l] to a sorted sequence that is
//       strictly lexicographically smaller.
//   R6  fd: any value > n is accepted (255 = none); values above R mean "no frontier" (accepted, harmless).  fd == R is impossible
//       (a node at depth R must be L and a node at depth fd must be F).  F at depth R fails; L only at depth R.
//   R7  a block fails on any BlockFail below; a file fails only on a bad magic (or a partial header that is not a magic prefix).
//       A truncated last block is ignored and reported.  RESULT is FAIL if any block or file failed (use --lenient to count failed
//       blocks only as missing), if the coverage is incomplete, if the IP/group/rows checks fail, or if a covering leaf is not in the
//       leaf file (a missing leaf file is an error unless there are no covering leaves).
//   R8  varints: at most 10 bytes and the 10th byte at most 1 (value < 2^64); redundant zero groups are accepted.
//   R9  a negative label bound or a negative cap makes the empty profile violate its row: no leaf can verify; u starts at max(0,ub).
//   R10 cap-0 multi-label rows are enforced only at L (cnt never equals cap after an increment from below), as the description says.
//   R11 --roots lines hold label vectors ('-' = empty prefix); the format of production --covers lists is not described there.
//       Leaf file lines: R label vectors, any separators.  Row ids and the dual's rows index the multi-label rows in file order.
//   R12 an O node with a dual whose B < rem*SC is invalid (the node would be a kill); K and O at depth R fail (only L is allowed).
//   R13 a size-1 row stores cap = R - lb (never above R); a label bound is the minimum of its size-1 rows, R if none.
//   R14 the listed permutations are checked for bounds/rows/identity/distinctness, closure only reported.
//   R15 coverage: a prefix is covered by a verified J block, or a verified T block whose frontier prefixes are all covered; the
//       covering leaves are the L records of all verified blocks whose prefix is reachable from the roots through verified T blocks.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <functional>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <unistd.h>

typedef __int128 i128;
typedef unsigned __int128 u128;
typedef unsigned long long ull;
typedef long long ll;

static const uint32_t MAGIC = 0x3942454Cu;   // bytes 'L','E','B','9'
static const ll SC = 1LL << 30;               // dual scale
static const ull YMAX = 1ULL << 50;           // largest allowed dual weight

// ---------------------------------------------------------------------------------------------
// small utilities
// ---------------------------------------------------------------------------------------------
static inline int msb(unsigned v) { return 31 - __builtin_clz(v); }

static std::string i128str(i128 v) {
    if (v == 0) return "0";
    bool neg = v < 0;
    u128 u = neg ? (u128)(-(v + 1)) + 1 : (u128)v;
    std::string s;
    while (u) { s += (char)('0' + (int)(u % 10)); u /= 10; }
    if (neg) s += '-';
    std::reverse(s.begin(), s.end());
    return s;
}

static std::vector<std::string> splitWS(const std::string& s) {
    std::vector<std::string> r;
    size_t i = 0;
    while (i < s.size()) {
        while (i < s.size() && (s[i] == ' ' || s[i] == '\t' || s[i] == '\r' || s[i] == '\n')) i++;
        size_t j = i;
        while (j < s.size() && !(s[j] == ' ' || s[j] == '\t' || s[j] == '\r' || s[j] == '\n')) j++;
        if (j > i) r.push_back(s.substr(i, j - i));
        i = j;
    }
    return r;
}

static std::vector<std::string> splitChar(const std::string& s, char c) {
    std::vector<std::string> r;
    size_t i = 0;
    for (;;) {
        size_t j = s.find(c, i);
        if (j == std::string::npos) { r.push_back(s.substr(i)); break; }
        r.push_back(s.substr(i, j - i));
        i = j + 1;
    }
    return r;
}

static bool slurp(const std::string& path, std::vector<uint8_t>& out) {
    FILE* f = fopen(path.c_str(), "rb");
    if (!f) return false;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz < 0) { fclose(f); return false; }
    out.resize((size_t)sz);
    size_t got = sz ? fread(out.data(), 1, (size_t)sz, f) : 0;
    fclose(f);
    return got == (size_t)sz;
}

static bool parseInt(const std::string& s, long long& v) {
    if (s.empty()) return false;
    char* e = nullptr;
    v = strtoll(s.c_str(), &e, 10);
    return e && *e == 0;
}

// ---------------------------------------------------------------------------------------------
// SHA-256 (for the manifest check; self-tested in --selftest)
// ---------------------------------------------------------------------------------------------
struct Sha256 {
    uint32_t h[8];
    uint64_t total;
    uint8_t buf[64];
    size_t bl;
    Sha256() { reset(); }
    void reset() {
        static const uint32_t iv[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                                       0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
        memcpy(h, iv, sizeof h);
        total = 0;
        bl = 0;
    }
    static inline uint32_t rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
    void block(const uint8_t* p) {
        static const uint32_t K[64] = {
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
            0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
            0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
            0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
            0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
            0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
            0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
        uint32_t w[64];
        for (int i = 0; i < 16; i++)
            w[i] = ((uint32_t)p[4 * i] << 24) | ((uint32_t)p[4 * i + 1] << 16) | ((uint32_t)p[4 * i + 2] << 8) |
                   (uint32_t)p[4 * i + 3];
        for (int i = 16; i < 64; i++) {
            uint32_t s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
            uint32_t s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16] + s0 + w[i - 7] + s1;
        }
        uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
        for (int i = 0; i < 64; i++) {
            uint32_t S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
            uint32_t ch = (e & f) ^ (~e & g);
            uint32_t t1 = hh + S1 + ch + K[i] + w[i];
            uint32_t S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
            uint32_t mj = (a & b) ^ (a & c) ^ (b & c);
            uint32_t t2 = S0 + mj;
            hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
        }
        h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
    }
    void update(const uint8_t* p, size_t n) {
        total += n;
        while (n) {
            size_t take = 64 - bl;
            if (take > n) take = n;
            memcpy(buf + bl, p, take);
            bl += take; p += take; n -= take;
            if (bl == 64) { block(buf); bl = 0; }
        }
    }
    std::string hex() {
        uint64_t bits = total * 8;
        uint8_t pad = 0x80;
        update(&pad, 1);
        uint8_t z = 0;
        while (bl != 56) update(&z, 1);
        uint8_t lenb[8];
        for (int i = 0; i < 8; i++) lenb[i] = (uint8_t)(bits >> (56 - 8 * i));
        update(lenb, 8);
        char out[65];
        for (int i = 0; i < 8; i++) snprintf(out + 8 * i, 9, "%08x", h[i]);
        return std::string(out, 64);
    }
};

static std::string sha256hex(const std::vector<uint8_t>& v) {
    Sha256 s;
    if (!v.empty()) s.update(v.data(), v.size());
    return s.hex();
}

// manifest: lines "<sha256>  <relative path>"; --base DIR is the directory the paths are relative to
struct Manifest {
    bool loaded = false;
    std::string base;
    std::map<std::string, std::string> hashOf;   // relative path -> sha256
    bool load(const std::string& path, const std::string& baseDir, std::string& err) {
        std::vector<uint8_t> b;
        if (!slurp(path, b)) { err = "cannot read manifest " + path; return false; }
        std::string s(b.begin(), b.end());
        size_t i = 0;
        while (i < s.size()) {
            size_t j = s.find('\n', i);
            if (j == std::string::npos) j = s.size();
            std::string ln = s.substr(i, j - i);
            i = j + 1;
            if (ln.empty()) continue;
            size_t sp = ln.find("  ");
            if (sp == std::string::npos || sp != 64) continue;
            hashOf[ln.substr(sp + 2)] = ln.substr(0, 64);
        }
        base = baseDir;
        while (base.size() > 1 && base.back() == '/') base.pop_back();
        loaded = true;
        return true;
    }
    // lexical absolute path: relative paths get the working directory, "//" and "/./" are collapsed
    static std::string absPath(const std::string& p) {
        std::string s = p;
        if (s.empty() || s[0] != '/') {
            char cwd[4096];
            if (getcwd(cwd, sizeof cwd)) s = std::string(cwd) + "/" + s;
        }
        std::string out;
        for (size_t i = 0; i < s.size(); i++) {
            if (s[i] == '/' && !out.empty() && out.back() == '/') continue;
            if (s[i] == '/' && s.compare(i, 3, "/./") == 0) { i++; continue; }
            out += s[i];
        }
        return out;
    }
    // returns "OK", "MISMATCH", "UNLISTED" or "OUTSIDE_BASE"
    std::string check(const std::string& path0, const std::string& hex) const {
        std::string path = absPath(path0);
        std::string pre = absPath(base) + "/";
        if (path.compare(0, pre.size(), pre) != 0) return "OUTSIDE_BASE";
        auto it = hashOf.find(path.substr(pre.size()));
        if (it == hashOf.end()) return "UNLISTED";
        return it->second == hex ? "OK" : "MISMATCH";
    }
};

// ---------------------------------------------------------------------------------------------
// G0 = { a -> P a Q : P, Q in GL3(F2) } acting on 9-bit vectors; bit 3r+c is entry (r,c) of the 3x3 matrix.
// (Any row/column arrangement of the 9 bits gives the same set of linear maps; the class table's rank counts
// n1,n2,n3 are re-checked below, which pins the arrangement down up to that symmetry.)
// ---------------------------------------------------------------------------------------------
static int mul3(int P, int M) {
    int R = 0;
    for (int r = 0; r < 3; r++)
        for (int c = 0; c < 3; c++) {
            int b = 0;
            for (int k = 0; k < 3; k++) b ^= ((P >> (3 * r + k)) & 1) & ((M >> (3 * k + c)) & 1);
            R |= b << (3 * r + c);
        }
    return R;
}
static int rank3(int M) {
    int rows[3] = {M & 7, (M >> 3) & 7, (M >> 6) & 7};
    int rk = 0;
    for (int bit = 2; bit >= 0; bit--) {
        int piv = -1;
        for (int i = rk; i < 3; i++)
            if ((rows[i] >> bit) & 1) { piv = i; break; }
        if (piv < 0) continue;
        std::swap(rows[rk], rows[piv]);
        for (int i = 0; i < 3; i++)
            if (i != rk && ((rows[i] >> bit) & 1)) rows[i] ^= rows[rk];
        rk++;
    }
    return rk;
}

struct G0Tables {
    std::vector<int> GL;                       // the 168 invertible matrices, ascending
    int glIndex[512];
    std::vector<uint16_t> LT, RT;              // [168*512]: LT[i*512+v] = GL[i]*v, RT[i*512+v] = v*GL[i]
    int genA = -1, genB = -1;                  // indices of two matrices generating GL3(F2)
    bool init(std::string& err) {
        GL.clear();
        for (int i = 0; i < 512; i++) glIndex[i] = -1;
        for (int M = 1; M < 512; M++)
            if (rank3(M) == 3) { glIndex[M] = (int)GL.size(); GL.push_back(M); }
        if (GL.size() != 168) { err = "GL3(F2) enumeration gave " + std::to_string(GL.size()); return false; }
        LT.assign(168 * 512, 0);
        RT.assign(168 * 512, 0);
        for (int i = 0; i < 168; i++)
            for (int v = 0; v < 512; v++) {
                LT[i * 512 + v] = (uint16_t)mul3(GL[i], v);
                RT[i * 512 + v] = (uint16_t)mul3(v, GL[i]);
            }
        const int ID = 1 | (1 << 4) | (1 << 8);
        for (int i = 0; i < 168 && genA < 0; i++)
            for (int j = i + 1; j < 168; j++) {
                bool seen[512] = {false};
                std::vector<int> q;
                q.push_back(ID);
                seen[ID] = true;
                for (size_t h = 0; h < q.size(); h++)
                    for (int g : {GL[i], GL[j]}) {
                        int y = mul3(q[h], g);
                        if (!seen[y]) { seen[y] = true; q.push_back(y); }
                    }
                if (q.size() == 168) { genA = i; genB = j; break; }
            }
        if (genA < 0) { err = "no generating pair for GL3(F2)"; return false; }
        return true;
    }
    inline int apply(int pi, int qi, int v) const { return RT[qi * 512 + LT[pi * 512 + v]]; }
};

// ---------------------------------------------------------------------------------------------
// Subspaces of F2^9: dense ranking by (pivot mask, free bits) of the reduced echelon basis.
// Pivot of a basis vector = its highest set bit.  Number of subspaces = 8,283,458.
// ---------------------------------------------------------------------------------------------
static inline void rrefAdd(int* b, int& k, int v) {
    for (int i = 0; i < k; i++)
        if ((v >> msb(b[i])) & 1) v ^= b[i];
    if (!v) return;
    int h = msb(v);
    for (int i = 0; i < k; i++)
        if ((b[i] >> h) & 1) b[i] ^= v;
    b[k++] = v;
}
static inline void sortDesc(int* b, int k) {
    for (int i = 1; i < k; i++) {
        int x = b[i], j = i - 1;
        while (j >= 0 && b[j] < x) { b[j + 1] = b[j]; j--; }
        b[j + 1] = x;
    }
}

struct SubIdx {
    uint32_t off[513];
    uint8_t kk[512];
    uint8_t tf[512];
    int8_t piv[512][9];
    uint16_t fmask[512][9];
    uint8_t nf[512][9];
    std::vector<uint16_t> pextT;    // [mask*512 + v]
    std::vector<uint16_t> pdepT;    // [mask*512 + c]
    uint32_t total = 0;
    void init() {
        uint32_t tot = 0;
        for (int pm = 0; pm < 512; pm++) {
            off[pm] = tot;
            int k = 0, ps[9];
            for (int q = 8; q >= 0; q--)
                if ((pm >> q) & 1) ps[k++] = q;
            kk[pm] = (uint8_t)k;
            int tfree = 0;
            for (int i = 0; i < k; i++) {
                piv[pm][i] = (int8_t)ps[i];
                int fm = 0;
                for (int q = 0; q < ps[i]; q++)
                    if (!((pm >> q) & 1)) fm |= 1 << q;
                fmask[pm][i] = (uint16_t)fm;
                nf[pm][i] = (uint8_t)__builtin_popcount(fm);
                tfree += nf[pm][i];
            }
            tf[pm] = (uint8_t)tfree;
            tot += 1u << tfree;
        }
        off[512] = tot;
        total = tot;
        pextT.assign(512 * 512, 0);
        pdepT.assign(512 * 512, 0);
        for (int m = 0; m < 512; m++) {
            int pc = __builtin_popcount(m);
            for (int v = 0; v < 512; v++) {
                int c = 0, t = 0;
                for (int q = 0; q < 9; q++)
                    if ((m >> q) & 1) { c |= ((v >> q) & 1) << t; t++; }
                pextT[m * 512 + v] = (uint16_t)c;
            }
            for (int c = 0; c < (1 << pc); c++) {
                int v = 0, t = 0;
                for (int q = 0; q < 9; q++)
                    if ((m >> q) & 1) { v |= ((c >> t) & 1) << q; t++; }
                pdepT[m * 512 + c] = (uint16_t)v;
            }
        }
    }
    // rows[0..k) must be a reduced echelon basis sorted by value descending
    inline uint32_t encode(const int* rows, int k) const {
        int pm = 0;
        for (int i = 0; i < k; i++) pm |= 1 << msb(rows[i]);
        uint32_t val = 0;
        for (int i = 0; i < k; i++) val = (val << nf[pm][i]) | pextT[fmask[pm][i] * 512 + rows[i]];
        return off[pm] + val;
    }
    inline int decode(uint32_t idx, int* rows) const {
        int lo = 0, hi = 512;
        while (hi - lo > 1) {
            int mid = (lo + hi) >> 1;
            if (off[mid] <= idx) lo = mid; else hi = mid;
        }
        int pm = lo, k = kk[pm], shift = tf[pm];
        uint32_t val = idx - off[pm];
        for (int i = 0; i < k; i++) {
            shift -= nf[pm][i];
            uint32_t c = (val >> shift) & ((1u << nf[pm][i]) - 1);
            rows[i] = (1 << piv[pm][i]) | pdepT[fmask[pm][i] * 512 + c];
        }
        return k;
    }
    // index of span(vs[0..n))
    inline uint32_t indexOfSpan(const int* vs, int n, int* dimOut = nullptr) const {
        int b[9], k = 0;
        for (int i = 0; i < n; i++) rrefAdd(b, k, vs[i]);
        sortDesc(b, k);
        if (dimOut) *dimOut = k;
        return encode(b, k);
    }
};

// ---------------------------------------------------------------------------------------------
// class table (seeded334.tsv) and the orbit labelling of all subspaces
// ---------------------------------------------------------------------------------------------
struct ClassRow {
    int idx = -1, dim = 0;
    std::vector<int> basis;
    int n1 = -1, n2 = -1, n3 = -1;
    int seeded = 0;
};

static bool loadClassTable(const std::string& path, std::vector<ClassRow>& out, std::string& err) {
    std::vector<uint8_t> b;
    if (!slurp(path, b)) { err = "cannot read class table " + path; return false; }
    std::string s(b.begin(), b.end());
    std::vector<std::string> lines = splitChar(s, '\n');
    if (lines.empty()) { err = "empty class table"; return false; }
    std::vector<std::string> hdr = splitChar(lines[0], '\t');
    auto col = [&](const char* name) {
        for (size_t i = 0; i < hdr.size(); i++) {
            std::string h = hdr[i];
            while (!h.empty() && (h.back() == '\r' || h.back() == ' ')) h.pop_back();
            if (h == name) return (int)i;
        }
        return -1;
    };
    int cIdx = col("idx"), cDim = col("dim"), cBasis = col("basis"), cN1 = col("n1"), cN2 = col("n2"),
        cN3 = col("n3"), cSeeded = col("seeded");
    if (cIdx < 0 || cDim < 0 || cBasis < 0 || cSeeded < 0) { err = "class table header lacks idx/dim/basis/seeded"; return false; }
    out.clear();
    for (size_t li = 1; li < lines.size(); li++) {
        std::string ln = lines[li];
        while (!ln.empty() && ln.back() == '\r') ln.pop_back();
        if (ln.empty()) continue;
        std::vector<std::string> t = splitChar(ln, '\t');
        if (t.size() < hdr.size()) { err = "short row in class table at line " + std::to_string(li + 1); return false; }
        ClassRow r;
        long long v;
        if (!parseInt(t[cIdx], v)) { err = "bad idx"; return false; }
        r.idx = (int)v;
        if (!parseInt(t[cDim], v)) { err = "bad dim"; return false; }
        r.dim = (int)v;
        if (!t[cBasis].empty())
            for (const std::string& x : splitChar(t[cBasis], ',')) {
                if (!parseInt(x, v) || v < 0 || v >= 512) { err = "bad basis vector in class " + t[cIdx]; return false; }
                r.basis.push_back((int)v);
            }
        if (cN1 >= 0 && parseInt(t[cN1], v)) r.n1 = (int)v;
        if (cN2 >= 0 && parseInt(t[cN2], v)) r.n2 = (int)v;
        if (cN3 >= 0 && parseInt(t[cN3], v)) r.n3 = (int)v;
        if (!parseInt(t[cSeeded], v)) { err = "bad seeded value in class " + t[cIdx]; return false; }
        r.seeded = (int)v;
        out.push_back(r);
    }
    return true;
}

struct ClassCtx {
    G0Tables g0;
    SubIdx sub;
    std::vector<ClassRow> cls;
    std::vector<int32_t> orb;           // subspace index -> orbit id
    int nOrb = 0;
    std::vector<int> classOfOrbit;      // orbit id -> class idx (-1 none)
    std::map<int, int> rowOfClass;      // class idx -> row in cls
    bool ready = false, ok = false;
    std::vector<std::string> report;    // human readable lines for the RECOMPUTE section
    std::string err;

    // 710 class bases with pairwise distinct G0-orbits covering all subspaces
    bool prepare(const std::string& tablePath) {
        if (ready) return ok;
        ready = true;
        ok = false;
        if (!loadClassTable(tablePath, cls, err)) return false;
        if (!g0.init(err)) return false;
        sub.init();
        char tmp[256];
        if (sub.total != 8283458u) { err = "subspace count " + std::to_string(sub.total) + " != 8283458"; return false; }
        // per-class sanity: independent basis of the stated dimension; rank counts n1,n2,n3
        int badRank = 0, badDim = 0;
        for (size_t i = 0; i < cls.size(); i++) {
            const ClassRow& c = cls[i];
            if (rowOfClass.count(c.idx)) { err = "duplicate class idx " + std::to_string(c.idx); return false; }
            rowOfClass[c.idx] = (int)i;
            int b[9], k = 0;
            for (int v : c.basis) rrefAdd(b, k, v);
            if (k != c.dim || (int)c.basis.size() != c.dim) badDim++;
            int cnt[4] = {0, 0, 0, 0};
            std::vector<int> el(1, 0);
            for (int j = 0; j < k; j++) { size_t m = el.size(); for (size_t t = 0; t < m; t++) el.push_back(el[t] ^ b[j]); }
            for (int v : el) if (v) cnt[rank3(v)]++;
            if (c.n1 >= 0 && (cnt[1] != c.n1 || cnt[2] != c.n2 || cnt[3] != c.n3)) badRank++;
        }
        snprintf(tmp, sizeof tmp, "classtable rows=%zu dim_mismatch=%d rankcount_mismatch=%d", cls.size(), badDim, badRank);
        report.push_back(tmp);
        if (badDim || badRank) { err = "class table inconsistent (dimension or rank counts)"; return false; }
        // orbit labelling of all 8,283,458 subspaces by the four generators of G0
        orb.assign(sub.total, -1);
        const uint16_t* gen[4] = {&g0.LT[g0.genA * 512], &g0.LT[g0.genB * 512], &g0.RT[g0.genA * 512], &g0.RT[g0.genB * 512]};
        std::vector<uint32_t> stack;
        std::vector<uint32_t> orbSize;
        for (uint32_t idx = 0; idx < sub.total; idx++) {
            if (orb[idx] >= 0) continue;
            int id = nOrb++;
            orb[idx] = id;
            stack.clear();
            stack.push_back(idx);
            uint32_t sz = 0;
            while (!stack.empty()) {
                uint32_t x = stack.back();
                stack.pop_back();
                sz++;
                int rows[9];
                int k = sub.decode(x, rows);
                for (int g = 0; g < 4; g++) {
                    int b[9], kk = 0;
                    for (int j = 0; j < k; j++) rrefAdd(b, kk, gen[g][rows[j]]);
                    sortDesc(b, kk);
                    uint32_t y = sub.encode(b, kk);
                    if (orb[y] < 0) { orb[y] = id; stack.push_back(y); }
                }
            }
            orbSize.push_back(sz);
        }
        uint32_t maxOrb = 0;
        for (uint32_t s : orbSize) maxOrb = std::max(maxOrb, s);
        snprintf(tmp, sizeof tmp, "orbits=%d largest_orbit=%u (|G0|=28224)", nOrb, maxOrb);
        report.push_back(tmp);
        if (maxOrb > 28224) { err = "orbit larger than |G0|: generator set is wrong"; return false; }
        classOfOrbit.assign(nOrb, -1);
        int dupClasses = 0;
        for (const ClassRow& c : cls) {
            uint32_t idx = sub.indexOfSpan(c.basis.data(), (int)c.basis.size());
            int o = orb[idx];
            if (classOfOrbit[o] >= 0) { dupClasses++; continue; }
            classOfOrbit[o] = c.idx;
        }
        int uncovered = 0;
        for (int o = 0; o < nOrb; o++) if (classOfOrbit[o] < 0) uncovered++;
        snprintf(tmp, sizeof tmp, "classes_distinct=%s orbits_without_class=%d classes=%zu orbits=%d",
                 dupClasses ? "NO" : "yes", uncovered, cls.size(), nOrb);
        report.push_back(tmp);
        if (dupClasses || uncovered || (int)cls.size() != nOrb) {
            err = "class table is not a bijection onto the G0-orbits of subspaces";
            return false;
        }
        ok = true;
        return true;
    }
    inline int classOfSpan(uint32_t subIdx) const { return classOfOrbit[orb[subIdx]]; }
};

// ---------------------------------------------------------------------------------------------
// the IP file
// ---------------------------------------------------------------------------------------------
struct Bits256 {
    uint64_t w[4] = {0, 0, 0, 0};
    inline void set(int l) { w[l >> 6] |= 1ULL << (l & 63); }
    inline bool get(int l) const { return (w[l >> 6] >> (l & 63)) & 1; }
    bool operator==(const Bits256& o) const { return w[0] == o.w[0] && w[1] == o.w[1] && w[2] == o.w[2] && w[3] == o.w[3]; }
    bool operator<(const Bits256& o) const {
        for (int i = 3; i >= 0; i--) if (w[i] != o.w[i]) return w[i] < o.w[i];
        return false;
    }
    int count() const { return __builtin_popcountll(w[0]) + __builtin_popcountll(w[1]) + __builtin_popcountll(w[2]) + __builtin_popcountll(w[3]); }
};
struct Bits256Hash {
    size_t operator()(const Bits256& b) const {
        uint64_t h = 0x9e3779b97f4a7c15ULL;
        for (int i = 0; i < 4; i++) {
            h ^= b.w[i] + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
            h *= 0xff51afd7ed558ccdULL;
            h ^= h >> 33;
        }
        return (size_t)h;
    }
};

struct IPRow { int dim = 0, cap = 0; std::vector<uint8_t> lab; };

struct IPData {
    int R = 0, N = 0;
    std::vector<int> lv;                      // label vectors in file order
    std::vector<IPRow> rows;                  // every C line in file order (labels sorted)
    std::vector<std::vector<uint8_t>> G;      // listed permutations
    // derived
    std::vector<int> ub;                      // label bounds (size-1 rows; R if none)
    int numMulti = 0;                         // multi-label rows (m >= 2) in file order = row ids
    std::vector<int> rowStart, rowCap;        // CSR of the multi-label rows
    std::vector<uint8_t> rowLab;
    std::vector<int> ofStart, ofRows;         // rows containing each label
    int initViol = 0;                         // multi rows with cap < 0 (violated by the empty profile)
    int labelOfVec[512];
};

static bool parseIP(const std::vector<uint8_t>& B, IPData& ip, std::string& err) {
    size_t p = 0, n = B.size();
    auto ws = [&]() { while (p < n && (B[p] == ' ' || B[p] == '\n' || B[p] == '\r' || B[p] == '\t')) p++; };
    auto word = [&](char& c) -> bool {
        ws();
        if (p >= n) return false;
        c = (char)B[p++];
        if (p < n && !(B[p] == ' ' || B[p] == '\n' || B[p] == '\r' || B[p] == '\t')) return false;
        return true;
    };
    auto num = [&](long long& v) -> bool {
        ws();
        if (p >= n) return false;
        bool neg = false;
        if (B[p] == '-') { neg = true; p++; }
        if (p >= n || B[p] < '0' || B[p] > '9') return false;
        long long x = 0;
        while (p < n && B[p] >= '0' && B[p] <= '9') {
            x = x * 10 + (B[p] - '0');
            if (x > (1LL << 40)) return false;
            p++;
        }
        v = neg ? -x : x;
        return true;
    };
    char c;
    long long v;
    if (!word(c) || c != 'R' || !num(v)) { err = "IP: expected 'R <R>'"; return false; }
    ip.R = (int)v;
    if (!word(c) || c != 'N' || !num(v)) { err = "IP: expected 'N <N>'"; return false; }
    if (v < 1 || v > 255) { err = "IP: N out of range 1..255"; return false; }
    ip.N = (int)v;
    if (ip.R < 1 || ip.R > 255) { err = "IP: R out of range"; return false; }
    ip.lv.resize(ip.N);
    for (int i = 0; i < ip.N; i++) {
        if (!num(v) || v < 0 || v >= 512) { err = "IP: bad label vector"; return false; }
        ip.lv[i] = (int)v;
    }
    bool sawG = false;
    for (;;) {
        ws();
        if (p >= n) break;
        if (!word(c)) { err = "IP: bad record word"; return false; }
        if (c == 'C') {
            long long d, cap, m;
            if (!num(d) || !num(cap) || !num(m)) { err = "IP: bad C line"; return false; }
            if (m < 1 || m > ip.N || d < 0 || d > 9 || cap < -100000 || cap > 100000) { err = "IP: C line out of range"; return false; }
            IPRow r;
            r.dim = (int)d;
            r.cap = (int)cap;
            Bits256 seen;
            for (long long i = 0; i < m; i++) {
                if (!num(v) || v < 0 || v >= ip.N) { err = "IP: label index out of range in C line"; return false; }
                if (seen.get((int)v)) { err = "IP: repeated label in a C line"; return false; }
                seen.set((int)v);
                r.lab.push_back((uint8_t)v);
            }
            std::sort(r.lab.begin(), r.lab.end());
            ip.rows.push_back(std::move(r));
        } else if (c == 'G') {
            long long g;
            if (!num(g) || g < 0 || g > 100000) { err = "IP: bad G count"; return false; }
            for (long long i = 0; i < g; i++) {
                std::vector<uint8_t> perm(ip.N);
                for (int j = 0; j < ip.N; j++) {
                    if (!num(v) || v < 0 || v >= ip.N) { err = "IP: bad permutation entry"; return false; }
                    perm[j] = (uint8_t)v;
                }
                ip.G.push_back(std::move(perm));
            }
            sawG = true;
            ws();
            if (p < n) { err = "IP: data after the G block"; return false; }
            break;
        } else { err = std::string("IP: unknown record '") + c + "'"; return false; }
    }
    if (!sawG) { err = "IP: no G block"; return false; }
    return true;
}

static void finishIP(IPData& ip) {
    ip.ub.assign(ip.N, ip.R);
    ip.numMulti = 0;
    ip.rowStart.assign(1, 0);
    ip.rowLab.clear();
    ip.rowCap.clear();
    for (const IPRow& r : ip.rows) {
        if (r.lab.size() == 1) {
            int l = r.lab[0], c = std::min(r.cap, ip.R);
            if (c < ip.ub[l]) ip.ub[l] = c;
        } else {
            ip.rowLab.insert(ip.rowLab.end(), r.lab.begin(), r.lab.end());
            ip.rowStart.push_back((int)ip.rowLab.size());
            ip.rowCap.push_back(r.cap);
            ip.numMulti++;
        }
    }
    ip.ofStart.assign(ip.N + 1, 0);
    for (uint8_t l : ip.rowLab) ip.ofStart[l + 1]++;
    for (int l = 0; l < ip.N; l++) ip.ofStart[l + 1] += ip.ofStart[l];
    ip.ofRows.assign(ip.rowLab.size(), 0);
    std::vector<int> fill(ip.ofStart.begin(), ip.ofStart.end() - 1);
    for (int r = 0; r < ip.numMulti; r++)
        for (int j = ip.rowStart[r]; j < ip.rowStart[r + 1]; j++) ip.ofRows[fill[ip.rowLab[j]]++] = r;
    ip.initViol = 0;
    for (int c : ip.rowCap) if (c < 0) ip.initViol++;
    for (int v = 0; v < 512; v++) ip.labelOfVec[v] = -1;
    for (int l = ip.N - 1; l >= 0; l--) ip.labelOfVec[ip.lv[l]] = l;   // first index wins if repeated
}

// ---------------------------------------------------------------------------------------------
// group checks from the IP alone; closure is reported, never required
// ---------------------------------------------------------------------------------------------
static bool checkGroupIP(const IPData& ip, std::vector<std::string>& rep) {
    bool ok = true;
    char tmp[512];
    const int N = ip.N;
    int bad = 0, dups = 0;
    bool hasId = false;
    std::unordered_set<std::string> seen;
    std::vector<char> valid(ip.G.size(), 0);
    for (size_t gi = 0; gi < ip.G.size(); gi++) {
        const std::vector<uint8_t>& p = ip.G[gi];
        std::vector<char> hit(N, 0);
        bool isPerm = (int)p.size() == N;
        bool isId = isPerm;
        for (int i = 0; isPerm && i < N; i++) {
            if (p[i] >= N || hit[p[i]]) isPerm = false; else hit[p[i]] = 1;
            if (p[i] != i) isId = false;
        }
        if (!isPerm) { bad++; continue; }
        valid[gi] = 1;
        if (isId) hasId = true;
        if (!seen.insert(std::string(p.begin(), p.end())).second) dups++;
    }
    snprintf(tmp, sizeof tmp, "GROUPCHECK1 elements=%zu not_permutation=%d duplicates=%d identity=%s", ip.G.size(), bad, dups, hasId ? "yes" : "NO");
    rep.push_back(tmp);
    if (bad || dups || !hasId) ok = false;
    // 2. label bounds preserved
    int boundBad = 0;
    for (size_t gi = 0; gi < ip.G.size(); gi++) {
        if (!valid[gi]) continue;
        for (int l = 0; l < N; l++) if (ip.ub[ip.G[gi][l]] != ip.ub[l]) { boundBad++; break; }
    }
    snprintf(tmp, sizeof tmp, "GROUPCHECK2 elements_not_preserving_label_bounds=%d", boundBad);
    rep.push_back(tmp);
    if (boundBad) ok = false;
    // 3. every element maps each multi-label row to a row whose (minimum) cap is <= its cap
    std::unordered_map<Bits256, int, Bits256Hash> capEff;
    std::vector<Bits256> rb(ip.numMulti);
    for (int r = 0; r < ip.numMulti; r++) {
        for (int j = ip.rowStart[r]; j < ip.rowStart[r + 1]; j++) rb[r].set(ip.rowLab[j]);
        auto it = capEff.find(rb[r]);
        if (it == capEff.end()) capEff[rb[r]] = ip.rowCap[r];
        else it->second = std::min(it->second, ip.rowCap[r]);
    }
    std::vector<int> capOfRow(ip.numMulti);
    for (int r = 0; r < ip.numMulti; r++) capOfRow[r] = capEff[rb[r]];
    long long rowBad = 0, rowMissing = 0;
    int elemBad = 0;
    for (size_t gi = 0; gi < ip.G.size(); gi++) {
        if (!valid[gi]) continue;
        const std::vector<uint8_t>& p = ip.G[gi];
        bool badHere = false;
        for (int r = 0; r < ip.numMulti; r++) {
            Bits256 img;
            for (int j = ip.rowStart[r]; j < ip.rowStart[r + 1]; j++) img.set(p[ip.rowLab[j]]);
            auto it = capEff.find(img);
            if (it == capEff.end()) { rowMissing++; badHere = true; continue; }
            if (it->second > capOfRow[r]) { rowBad++; badHere = true; }
        }
        if (badHere) elemBad++;
    }
    snprintf(tmp, sizeof tmp, "GROUPCHECK3 elements_with_bad_row_map=%d image_row_missing=%lld image_cap_larger=%lld", elemBad, rowMissing, rowBad);
    rep.push_back(tmp);
    if (elemBad) ok = false;
    // closure (reported only)
    std::string closed = "skipped";
    if (ip.G.size() <= 2100 && bad == 0) {
        closed = "yes";
        for (size_t a = 0; a < ip.G.size() && closed == "yes"; a++)
            for (size_t b = 0; b < ip.G.size(); b++) {
                std::string c(N, 0);
                for (int l = 0; l < N; l++) c[l] = (char)ip.G[a][ip.G[b][l]];
                if (!seen.count(c)) { closed = "NO"; break; }
            }
    }
    rep.push_back("GROUPCHECK4 closed_under_composition=" + closed + " (reported only; not required)");
    return ok;
}

// ---------------------------------------------------------------------------------------------
// independent recomputation of the IP
// ---------------------------------------------------------------------------------------------
struct RowKey {
    Bits256 b;
    int dim, cap;
    bool operator<(const RowKey& o) const {
        if (b == o.b) { if (dim != o.dim) return dim < o.dim; return cap < o.cap; }
        return b < o.b;
    }
    bool operator==(const RowKey& o) const { return b == o.b && dim == o.dim && cap == o.cap; }
};

static std::string rowKeyStr(const RowKey& k) {
    std::string s = "dim=" + std::to_string(k.dim) + " cap=" + std::to_string(k.cap) + " labels=";
    int shown = 0, tot = k.b.count();
    for (int l = 0; l < 256 && shown < 12; l++) if (k.b.get(l)) { s += std::to_string(l) + ","; shown++; }
    if (tot > shown) s += "..(" + std::to_string(tot) + ")";
    return s;
}

static ll gaussSubspaceCount(int q) {   // number of subspaces of F2^q
    ll g[10][10];
    for (int n = 0; n <= 9; n++) for (int k = 0; k <= 9; k++) g[n][k] = 0;
    for (int n = 0; n <= 9; n++) g[n][0] = 1;
    for (int n = 1; n <= 9; n++)
        for (int k = 1; k <= n; k++) g[n][k] = g[n - 1][k - 1] + (1LL << k) * g[n - 1][k];
    ll t = 0;
    for (int k = 0; k <= q; k++) t += g[q][k];
    return t;
}

// step 3: every strict superspace S'' of E (found by scanning all 8,283,458 subspaces for E <= S'' with dim S'' > dim E)
// gives one row: the nonzero cosets of E inside S'' (as label indices, via cosetLabel) and cap = R - lb(class of S'')
static bool enumerateSuperspaces(const ClassCtx& cc, const ClassRow& E, int R, const std::map<int, int>& raise,
                                 const int* cosetLabel, const bool* inE, std::vector<RowKey>& exp, std::string& err) {
    const int dimE = E.dim, q = 9 - dimE;
    auto lbOf = [&](int cls) {
        auto it = raise.find(cls);
        if (it != raise.end()) return it->second;
        return cc.cls[cc.rowOfClass.at(cls)].seeded;
    };
    exp.clear();
    exp.reserve((size_t)gaussSubspaceCount(q));
    int rows[9];
    const SubIdx& S = cc.sub;
    for (uint32_t idx = 0; idx < S.total; idx++) {
        int k = S.decode(idx, rows);
        if (k <= dimE) continue;
        bool contains = true;
        for (int e : E.basis) {
            int v = e;
            for (int i = 0; i < k; i++) if ((v >> msb(rows[i])) & 1) v ^= rows[i];
            if (v) { contains = false; break; }
        }
        if (!contains) continue;
        int vec[512];
        vec[0] = 0;
        for (int m = 1; m < (1 << k); m++) vec[m] = vec[m & (m - 1)] ^ rows[__builtin_ctz(m)];
        RowKey rk;
        rk.dim = k;
        for (int m = 1; m < (1 << k); m++) if (!inE[vec[m]]) rk.b.set(cosetLabel[vec[m]]);
        if (rk.b.count() != (1 << (k - dimE)) - 1) { err = "internal: superspace label count"; return false; }
        rk.cap = R - lbOf(cc.classOfSpan(idx));
        exp.push_back(rk);
    }
    return true;
}

// returns true when every item of steps 1-5 holds.  witnesses[i] = (pi,qi) indices into GL for listed perm i.
static bool recomputeIP(ClassCtx& cc, const IPData& ip, int clsIdx, const std::map<int, int>& raise,
                        std::vector<std::string>& rep, std::vector<std::array<int, 2>>& witnesses) {
    bool ok = true;
    char tmp[1024];
    auto rit = cc.rowOfClass.find(clsIdx);
    if (rit == cc.rowOfClass.end()) { rep.push_back("RECOMPUTE FAIL: class " + std::to_string(clsIdx) + " is not in the class table"); return false; }
    const ClassRow& E = cc.cls[rit->second];
    const int dimE = E.dim, q = 9 - dimE;
    std::vector<int> Eel(1, 0);
    for (int b : E.basis) { size_t m = Eel.size(); for (size_t t = 0; t < m; t++) Eel.push_back(Eel[t] ^ b); }
    bool inE[512];
    for (int v = 0; v < 512; v++) inE[v] = false;
    for (int v : Eel) inE[v] = true;
    int cosetMin[512];
    for (int v = 0; v < 512; v++) { int m = v; for (int e : Eel) m = std::min(m, v ^ e); cosetMin[v] = m; }
    // step 1: labels
    std::vector<int> expLab;
    for (int v = 1; v < 512; v++) if (!inE[v] && cosetMin[v] == v) expLab.push_back(v);
    std::vector<int> got(ip.lv);
    std::sort(got.begin(), got.end());
    bool labOk = ((int)expLab.size() == (1 << q) - 1) && got == expLab;
    bool asc = std::is_sorted(ip.lv.begin(), ip.lv.end());
    snprintf(tmp, sizeof tmp, "RECOMPUTE step1 class=%d dimE=%d expected_labels=%zu ip_labels=%d every_nonzero_coset_once_by_smallest_vector=%s listed_in_ascending_order=%s",
             clsIdx, dimE, expLab.size(), ip.N, labOk ? "yes" : "NO", asc ? "yes" : "no");
    rep.push_back(tmp);
    if (!labOk) return false;
    int cosetLabel[512];
    for (int v = 0; v < 512; v++) cosetLabel[v] = inE[v] ? -1 : ip.labelOfVec[cosetMin[v]];
    // step 2 (class table) is reported by the caller from cc.report
    // step 3: every strict superspace gets a class; lb from the table of record, raised only where listed
    std::vector<RowKey> exp;
    {
        std::string e3;
        if (!enumerateSuperspaces(cc, E, ip.R, raise, cosetLabel, inE, exp, e3)) { rep.push_back("RECOMPUTE FAIL " + e3); return false; }
    }
    ll want = gaussSubspaceCount(q) - 1;
    snprintf(tmp, sizeof tmp, "RECOMPUTE step3 strict_superspaces=%zu expected_count=%lld lb_raised_classes=%zu", exp.size(), want, raise.size());
    rep.push_back(tmp);
    if ((ll)exp.size() != want) { rep.push_back("RECOMPUTE FAIL: superspace enumeration count"); return false; }
    // step 4: rows and caps as sets of (dim, label set, cap)
    std::vector<RowKey> ipk;
    ipk.reserve(ip.rows.size());
    for (const IPRow& r : ip.rows) {
        RowKey k;
        k.dim = r.dim;
        k.cap = r.cap;
        for (uint8_t l : r.lab) k.b.set(l);
        ipk.push_back(k);
    }
    // expected stored cap for a size-1 row is min(cap, R) (label bound ub = min(cap, R))
    for (RowKey& k : exp) if (k.b.count() == 1 && k.cap > ip.R) k.cap = ip.R;
    std::sort(exp.begin(), exp.end());
    std::sort(ipk.begin(), ipk.end());
    size_t i = 0, j = 0;
    long long onlyExp = 0, onlyIp = 0;
    std::vector<std::string> exs;
    while (i < exp.size() || j < ipk.size()) {
        if (j >= ipk.size() || (i < exp.size() && exp[i] < ipk[j])) { if (exs.size() < 6) exs.push_back("expected-only: " + rowKeyStr(exp[i])); onlyExp++; i++; }
        else if (i >= exp.size() || ipk[j] < exp[i]) { if (exs.size() < 6) exs.push_back("ip-only: " + rowKeyStr(ipk[j])); onlyIp++; j++; }
        else { i++; j++; }
    }
    snprintf(tmp, sizeof tmp, "RECOMPUTE step4 ip_rows=%zu expected_rows=%zu expected_only=%lld ip_only=%lld rows_and_caps_match=%s",
             ipk.size(), exp.size(), onlyExp, onlyIp, (onlyExp || onlyIp) ? "NO" : "yes");
    rep.push_back(tmp);
    for (const std::string& s : exs) rep.push_back("RECOMPUTE step4 diff " + s);
    if (onlyExp || onlyIp) ok = false;
    // step 5: a witness (P,Q) in Stab_G0(E) for every listed permutation
    const G0Tables& g0 = cc.g0;
    std::unordered_map<std::string, std::array<int, 2>> induced;
    int stabOrder = 0;
    for (int pi = 0; pi < 168; pi++)
        for (int qi = 0; qi < 168; qi++) {
            bool stab = true;
            for (int e : E.basis) if (!inE[g0.apply(pi, qi, e)]) { stab = false; break; }
            if (!stab) continue;
            stabOrder++;
            std::string perm(ip.N, 0);
            for (int l = 0; l < ip.N; l++) perm[l] = (char)cosetLabel[g0.apply(pi, qi, ip.lv[l])];
            induced.emplace(perm, std::array<int, 2>{pi, qi});
        }
    witnesses.assign(ip.G.size(), std::array<int, 2>{-1, -1});
    int found = 0;
    for (size_t gi = 0; gi < ip.G.size(); gi++) {
        std::string perm(ip.G[gi].begin(), ip.G[gi].end());
        auto it = induced.find(perm);
        if (it != induced.end()) { witnesses[gi] = it->second; found++; }
    }
    snprintf(tmp, sizeof tmp, "RECOMPUTE step5 stabilizer_order=%d distinct_induced_permutations=%zu listed=%zu with_witness=%d every_listed_has_witness=%s",
             stabOrder, induced.size(), ip.G.size(), found, found == (int)ip.G.size() ? "yes" : "NO");
    rep.push_back(tmp);
    if (found != (int)ip.G.size()) ok = false;
    // distinctness of the listed permutations is part of GROUPCHECK1
    return ok;
}

// ---------------------------------------------------------------------------------------------
// trace replay
// ---------------------------------------------------------------------------------------------
static bool g_mutArith64 = false;        // test-only wrong evaluator: 64-bit wrapping dual arithmetic
static bool g_mutUnsignedSlack = false;  // test-only wrong evaluator: cap-cnt taken as an unsigned 32-bit value
static bool g_dump = false;              // print every record while replaying
static bool g_xcheck = false;            // cross-check every exact dual value against a long double recomputation
static ull g_xcheckN = 0, g_xcheckBad = 0;

struct BlockFail { std::string code, detail; size_t off; };
struct Span { size_t a, b; const char* name; };

struct Reader {
    const uint8_t* base = nullptr;
    size_t pos = 0, end = 0;
    std::vector<Span>* ann = nullptr;
    [[noreturn]] void fail(const char* code, const std::string& detail = "") const { throw BlockFail{code, detail, pos}; }
    uint8_t byte(const char* name) {
        if (pos >= end) fail("PAYLOAD_TRUNCATED", name);
        if (ann) ann->push_back({pos, pos + 1, name});
        return base[pos++];
    }
    int peek(size_t k) const { return pos + k < end ? (int)base[pos + k] : -1; }
    ull varint(const char* name) {
        size_t s = pos;
        ull v = 0;
        for (int i = 0;; i++) {
            if (pos >= end) fail("PAYLOAD_TRUNCATED", name);
            uint8_t b = base[pos++];
            if (i == 9) {                      // 10th byte: only bit 63 may be set, no continuation
                if ((b & 0x7f) > 1 || (b & 0x80)) fail("VARINT_64", name);
            }
            v |= (ull)(b & 0x7f) << (7 * i);
            if (!(b & 0x80)) break;
        }
        if (ann) ann->push_back({s, pos, name});
        return v;
    }
};

struct BlockOut {
    bool ok = false;
    std::string code, detail;
    size_t off = 0;
    char tag = 0;
    int fd = 255;
    std::string prefix;                    // label indices
    std::vector<std::string> frontier;     // label-index strings
    std::vector<std::string> leaves;
    ull nodes = 0, nL = 0, nF = 0, nK = 0, nO = 0, nP = 0, nChild = 0, nSkip = 0, nDualO = 0, nForced = 0, nFixed = 0;
    ull kinds[4] = {0, 0, 0, 0};
};

struct Replayer {
    const IPData& ip;
    int N, R, M;
    std::vector<int> mult, u, u0;
    std::vector<int16_t> cnt;
    std::vector<uint8_t> seq;
    int viol = 0;
    bool isT = false;
    int fd = 255;
    Reader rd;
    BlockOut* out = nullptr;
    std::vector<int> gorder;
    std::vector<i128> Tbuf;
    std::vector<char> inRow;
    std::vector<int> dualRows;
    std::vector<ull> dualY;
    std::vector<std::vector<int>> uEntry, uMid;

    explicit Replayer(const IPData& ip_) : ip(ip_) {
        N = ip.N; R = ip.R; M = ip.numMulti;
        mult.assign(N, 0);
        cnt.assign(M, 0);
        u0.resize(N);
        for (int l = 0; l < N; l++) u0[l] = std::max(0, ip.ub[l]);
        u = u0;
        viol = ip.initViol;
        Tbuf.assign(N, 0);
        inRow.assign(N, 0);
        uEntry.assign(R + 3, std::vector<int>(N, 0));
        uMid.assign(R + 3, std::vector<int>(N, 0));
        for (size_t g = 0; g < ip.G.size(); g++) gorder.push_back((int)g);
    }

    inline void add(int l) {
        mult[l]++;
        int room = ip.ub[l] - mult[l];
        if (room < 0) room = 0;
        if (room < u[l]) u[l] = room;
        for (int t = ip.ofStart[l]; t < ip.ofStart[l + 1]; t++) {
            int r = ip.ofRows[t];
            int c = ++cnt[r];
            int cp = ip.rowCap[r];
            if (c == cp) for (int j = ip.rowStart[r]; j < ip.rowStart[r + 1]; j++) u[ip.rowLab[j]] = 0;
            if (c == cp + 1) viol++;
        }
        seq.push_back((uint8_t)l);
    }
    inline void undoAdd() {
        int l = seq.back();
        seq.pop_back();
        for (int t = ip.ofStart[l]; t < ip.ofStart[l + 1]; t++) {
            int r = ip.ofRows[t];
            int c = cnt[r];
            if (c == ip.rowCap[r] + 1) viol--;
            cnt[r] = (int16_t)(c - 1);
        }
        mult[l]--;
    }
    void removeLast(const std::vector<int>& usave) {
        undoAdd();
        u = usave;
    }
    void cleanup() {
        while (!seq.empty()) undoAdd();
        u = u0;
    }

    // exact signed 128-bit dual evaluation; T is left in Tbuf
    i128 evalDual(int pos) {
        std::fill(Tbuf.begin(), Tbuf.end(), (i128)0);
        i128 S = 0;
        for (size_t i = 0; i < dualRows.size(); i++) {
            int r = dualRows[i];
            ll slack = (ll)ip.rowCap[r] - (ll)cnt[r];
            if (g_mutUnsignedSlack) S += (i128)dualY[i] * (i128)(uint32_t)(int32_t)slack;
            else S += (i128)dualY[i] * (i128)slack;
            for (int j = ip.rowStart[r]; j < ip.rowStart[r + 1]; j++) Tbuf[ip.rowLab[j]] += (i128)dualY[i];
        }
        for (int l = pos; l < N; l++)
            if (u[l] >= 1 && Tbuf[l] < (i128)SC) S += (i128)u[l] * ((i128)SC - Tbuf[l]);
        if (g_xcheck) xcheckDual(pos, S);
        return S;
    }
    // --xcheck: recompute B in long double (64-bit mantissa) and compare with the exact value; counts disagreements
    void xcheckDual(int pos, i128 S) {
        std::vector<long double> T(N, 0.0L);
        long double B = 0.0L;
        for (size_t i = 0; i < dualRows.size(); i++) {
            int r = dualRows[i];
            B += (long double)dualY[i] * (long double)((ll)ip.rowCap[r] - (ll)cnt[r]);
            for (int j = ip.rowStart[r]; j < ip.rowStart[r + 1]; j++) T[ip.rowLab[j]] += (long double)dualY[i];
        }
        for (int l = pos; l < N; l++)
            if (u[l] >= 1 && T[l] < (long double)SC) B += (long double)u[l] * ((long double)SC - T[l]);
        long double ex = (long double)S, diff = ex > B ? ex - B : B - ex, mag = (ex > 0 ? ex : -ex) + (B > 0 ? B : -B) + 1.0L;
        g_xcheckN++;
        if (diff > 1e-12L * mag + 4096.0L) g_xcheckBad++;
    }
    // deliberately wrong evaluator (test only): everything in 64-bit wrapping arithmetic
    i128 evalDual64(int pos) {
        std::vector<uint64_t> T(N, 0);
        uint64_t S = 0;
        for (size_t i = 0; i < dualRows.size(); i++) {
            int r = dualRows[i];
            int64_t slack = (int64_t)ip.rowCap[r] - (int64_t)cnt[r];
            S += (uint64_t)dualY[i] * (uint64_t)slack;
            for (int j = ip.rowStart[r]; j < ip.rowStart[r + 1]; j++) T[ip.rowLab[j]] += dualY[i];
        }
        for (int l = pos; l < N; l++)
            if (u[l] >= 1 && (int64_t)T[l] < (int64_t)SC) S += (uint64_t)u[l] * ((uint64_t)SC - T[l]);
        return (i128)(int64_t)S;
    }
    i128 readDual(int pos) {
        ull k = rd.varint("dual.k");
        if (k > (ull)M) rd.fail("DUAL_K_TOO_LONG", "k=" + std::to_string(k) + " rows=" + std::to_string(M));
        dualRows.resize((size_t)k);
        dualY.resize((size_t)k);
        for (ull i = 0; i < k; i++) {
            ull r = rd.varint("dual.row");
            if (r >= (ull)M) rd.fail("DUAL_ROW_RANGE", "row=" + std::to_string(r));
            ull y = rd.varint("dual.Y");
            if (y > YMAX) rd.fail("DUAL_Y_RANGE", "Y=" + std::to_string(y));
            dualRows[(size_t)i] = (int)r;
            dualY[(size_t)i] = y;
        }
        if (g_mutArith64) { evalDual(pos); return evalDual64(pos); }
        return evalDual(pos);
    }

    bool nonCanonical(int l) {
        size_t len = seq.size() + 1;
        uint8_t s[300], t[300];
        for (size_t i = 0; i + 1 < len; i++) s[i] = seq[i];
        s[len - 1] = (uint8_t)l;
        for (size_t gi = 0; gi < gorder.size(); gi++) {
            const uint8_t* p = ip.G[gorder[gi]].data();
            for (size_t i = 0; i < len; i++) t[i] = p[s[i]];
            for (size_t i = 1; i < len; i++) {
                uint8_t x = t[i];
                size_t j = i;
                while (j > 0 && t[j - 1] > x) { t[j] = t[j - 1]; j--; }
                t[j] = x;
            }
            int c = 0;
            for (size_t i = 0; i < len; i++) if (t[i] != s[i]) { c = t[i] < s[i] ? -1 : 1; break; }
            if (c < 0) {
                if (gi > 0) std::swap(gorder[gi], gorder[0]);
                return true;
            }
        }
        return false;
    }

    ll sumFrom(int from) const {
        ll s = 0;
        for (int l = from; l < N; l++) s += u[l];
        return s;
    }
    ll sumFromOutsideRow(int from, int r) {
        for (int j = ip.rowStart[r]; j < ip.rowStart[r + 1]; j++) inRow[ip.rowLab[j]] = 1;
        ll s = 0;
        for (int l = from; l < N; l++) if (!inRow[l]) s += u[l];
        for (int j = ip.rowStart[r]; j < ip.rowStart[r + 1]; j++) inRow[ip.rowLab[j]] = 0;
        return s;
    }

    void node(int d) {
        size_t recOff = rd.pos;
        uint8_t t = rd.byte("tag");
        const int rem = R - d;
        if (d == R && t != 'L') rd.fail("DEPTH_R_NOT_L", std::string("record '") + (char)t + "' at depth R");
        if (isT && d == fd && t != 'F') rd.fail("NODE_AT_FD_NOT_F", std::string("record '") + (char)t + "' at depth fd");
        if (t == 'F') {
            if (!(isT && d == fd)) rd.fail("F_WRONG_PLACE");
            out->nodes++; out->nF++;
            out->frontier.push_back(std::string(seq.begin(), seq.end()));
            if (g_dump) printf("DUMP d=%d F\n", d);
            return;
        }
        if (t == 'L') {
            if (d != R) rd.fail("L_WRONG_DEPTH", "depth " + std::to_string(d));
            if (viol != 0) rd.fail("L_NOT_CAPPED", "a row count exceeds its cap");
            for (int l = 0; l < N; l++) if (mult[l] > ip.ub[l]) rd.fail("L_NOT_CAPPED", "label " + std::to_string(l) + " exceeds its bound");
            out->nodes++; out->nL++;
            out->leaves.push_back(std::string(seq.begin(), seq.end()));
            if (g_dump) printf("DUMP d=%d L\n", d);
            return;
        }
        if (t == 'K') {
            out->nodes++; out->nK++;
            int pos = seq.empty() ? 0 : seq[seq.size() - 1];
            i128 B = readDual(pos);
            i128 lim = (i128)rem * (i128)SC;
            if (g_dump) printf("DUMP d=%d K k=%zu B=%s rem*SC=%s\n", d, dualRows.size(), i128str(B).c_str(), i128str(lim).c_str());
            if (!(B < lim)) rd.fail("K_NOT_KILL", "B=" + i128str(B) + " rem*SC=" + i128str(lim));
            return;
        }
        if (t != 'O') rd.fail("UNKNOWN_TAG", "byte " + std::to_string((int)t) + " at " + std::to_string(recOff));
        // ---- open node ----
        out->nodes++; out->nO++;
        const int cut = rd.byte("O.cut");
        const int kind = rd.byte("O.kind");
        ull rowId = 0;
        if (kind == 1) rowId = rd.varint("O.row");
        const int hasDual = rd.byte("O.hasDual");
        if (hasDual > 1) rd.fail("BAD_HASDUAL");
        if (kind > 3) rd.fail("BAD_KIND", "kind=" + std::to_string(kind));
        if (kind == 3 && !hasDual) rd.fail("KIND3_NO_DUAL");
        if (kind == 1 && rowId >= (ull)M) rd.fail("CUT_ROW_RANGE", "row=" + std::to_string(rowId));
        out->kinds[kind]++;
        const int pos = seq.empty() ? 0 : seq[seq.size() - 1];
        uEntry[d] = u;
        int lreq = -1;
        if (hasDual) {
            out->nDualO++;
            i128 B = readDual(pos);
            i128 gap = B - (i128)rem * (i128)SC;
            if (gap < 0) rd.fail("O_DUAL_IS_KILL", "gap=" + i128str(gap));
            for (int l = pos; l < N; l++) {
                if (u[l] < 1) continue;
                i128 T = Tbuf[l];
                if (T > (i128)SC) {
                    u128 q = (u128)gap / (u128)(T - (i128)SC);
                    if (q < (u128)u[l]) { u[l] = (int)q; out->nFixed++; }
                } else if (T < (i128)SC) {
                    u128 q = (u128)gap / (u128)((i128)SC - T);
                    if ((i128)u[l] - (i128)q >= 1) { if (lreq < 0) lreq = l; }
                }
            }
            if (lreq >= 0) out->nForced++;
        }
        if (cut < pos || cut > N) rd.fail("CUT_RANGE", "cut=" + std::to_string(cut) + " pos=" + std::to_string(pos));
        if (kind == 0) {
            if (cut != N) rd.fail("CUT_KIND0_NOT_N", "cut=" + std::to_string(cut));
        } else if (kind == 1) {
            ll sum = sumFromOutsideRow(cut, (int)rowId);
            ll rhs = (ll)rem - ((ll)ip.rowCap[rowId] - (ll)cnt[rowId]);
            if (!(sum < rhs)) rd.fail("CUT_KIND1_FAILS", "sum=" + std::to_string(sum) + " rhs=" + std::to_string(rhs));
        } else if (kind == 2) {
            ll sum = sumFrom(cut);
            if (!(sum < rem)) rd.fail("CUT_KIND2_FAILS", "sum=" + std::to_string(sum) + " rem=" + std::to_string(rem));
        } else {
            if (lreq < 0) rd.fail("CUT_KIND3_NO_FORCED_LABEL");
            if (cut != lreq + 1) rd.fail("CUT_KIND3_BAD_CUT", "cut=" + std::to_string(cut) + " lreq=" + std::to_string(lreq));
        }
        if (g_dump) printf("DUMP d=%d O cut=%d kind=%d dual=%d lreq=%d pos=%d\n", d, cut, kind, hasDual, lreq, pos);
        uMid[d] = u;
        for (int l = pos; l < cut; l++) {
            if (u[l] < 1) continue;
            bool child = (rd.peek(0) == 'C' && rd.peek(1) == l);
            if (!child) {
                if (!nonCanonical(l)) rd.fail("MISSING_CHILD", "label " + std::to_string(l) + " is canonical and has no C record");
                out->nSkip++;
                continue;
            }
            rd.byte("C.tag");
            rd.byte("C.label");
            out->nChild++;
            add(l);
            if (rd.peek(0) == 'P') {
                rd.byte("P.tag");
                int k = rd.byte("P.k");
                const int rem2 = R - (d + 1);
                out->nP++;
                if (k == 1) {
                    ull row = rd.varint("P.row");
                    if (row >= (ull)M) rd.fail("P_ROW_RANGE", "row=" + std::to_string(row));
                    ll sum = sumFromOutsideRow(l, (int)row);
                    ll rhs = (ll)rem2 - ((ll)ip.rowCap[row] - (ll)cnt[row]);
                    if (!(sum < rhs)) rd.fail("P_NOT_DEAD", "k=1 sum=" + std::to_string(sum) + " rhs=" + std::to_string(rhs));
                } else if (k == 2) {
                    ll sum = sumFrom(l);
                    if (!(sum < rem2)) rd.fail("P_NOT_DEAD", "k=2 sum=" + std::to_string(sum) + " rem'=" + std::to_string(rem2));
                } else rd.fail("P_BAD_K", "k=" + std::to_string(k));
            } else {
                node(d + 1);
            }
            removeLast(uMid[d]);
        }
        if (rd.byte("E") != 'E') rd.fail("E_EXPECTED", "stray record after the last eligible label");
        u = uEntry[d];
    }

    void verifyBlock(const uint8_t* pl, size_t len, BlockOut& o, std::vector<Span>* ann) {
        out = &o;
        rd.base = pl; rd.pos = 0; rd.end = len; rd.ann = ann;
        try {
            uint8_t tag = rd.byte("block.tag");
            if (tag != 'T' && tag != 'J') rd.fail("BAD_BLOCK_TAG", "byte " + std::to_string((int)tag));
            isT = (tag == 'T');
            o.tag = (char)tag;
            int n = rd.byte("block.n");
            if (n > R) rd.fail("N_GT_R", "n=" + std::to_string(n));
            int prev = -1;
            for (int i = 0; i < n; i++) {
                if (rd.pos + 2 > rd.end) rd.fail("PAYLOAD_TRUNCATED", "prefix vector");
                unsigned v = (unsigned)pl[rd.pos] | ((unsigned)pl[rd.pos + 1] << 8);
                if (ann) ann->push_back({rd.pos, rd.pos + 2, "prefix.vec"});
                rd.pos += 2;
                int l = v < 512 ? ip.labelOfVec[v] : -1;
                if (l < 0) rd.fail("PREFIX_NOT_LABEL", "vector " + std::to_string(v));
                if (l < prev) rd.fail("PREFIX_UNSORTED");
                if (u[l] < 1) rd.fail("PREFIX_U0", "label " + std::to_string(l) + " has u=0 when added");
                add(l);
                prev = l;
            }
            fd = 255;
            if (isT) {
                fd = rd.byte("block.fd");
                if (fd != 255 && fd <= n) rd.fail("FD_LE_N", "fd=" + std::to_string(fd) + " n=" + std::to_string(n));
            }
            o.fd = fd;
            o.prefix = std::string(seq.begin(), seq.end());
            node(n);
            if (rd.byte("Z.tag") != 'Z') rd.fail("Z_MISSING");
            ull cz = rd.varint("Z.count");
            if (cz != o.nodes) rd.fail("Z_COUNT", "stated " + std::to_string(cz) + " counted " + std::to_string(o.nodes));
            if (rd.pos != rd.end) rd.fail("TRAILING_BYTES", std::to_string(rd.end - rd.pos) + " bytes");
            o.ok = true;
        } catch (BlockFail& f) {
            o.ok = false;
            o.code = f.code;
            o.detail = f.detail;
            o.off = f.off;
        }
        cleanup();
    }
};

// ---------------------------------------------------------------------------------------------
// trace container
// ---------------------------------------------------------------------------------------------
static inline uint32_t le32(const uint8_t* p) { return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24); }
static inline uint64_t le64(const uint8_t* p) { return (uint64_t)le32(p) | ((uint64_t)le32(p + 4) << 32); }

struct BlockRef { size_t start, len; };   // start = offset of the block header, payload at start+12
struct ContainerScan {
    std::vector<BlockRef> blocks;
    bool bad = false;
    std::string badWhy;
    size_t badOff = 0;
    bool truncated = false;
    size_t truncOff = 0;
    ull truncAnnounced = 0, truncAvail = 0;
};
static void scanContainer(const uint8_t* B, size_t n, ContainerScan& cs) {
    static const uint8_t mg[4] = {0x4C, 0x45, 0x42, 0x39};
    size_t p = 0;
    while (p < n) {
        size_t rem = n - p;
        if (rem < 12) {
            bool consistent = true;
            for (size_t i = 0; i < std::min<size_t>(rem, 4); i++) if (B[p + i] != mg[i]) consistent = false;
            if (consistent) { cs.truncated = true; cs.truncOff = p; cs.truncAnnounced = 0; cs.truncAvail = rem; }
            else { cs.bad = true; cs.badWhy = "BAD_MAGIC"; cs.badOff = p; }
            return;
        }
        if (le32(B + p) != MAGIC) { cs.bad = true; cs.badWhy = "BAD_MAGIC"; cs.badOff = p; return; }
        uint64_t len = le64(B + p + 4);
        if (len > (uint64_t)(rem - 12)) { cs.truncated = true; cs.truncOff = p; cs.truncAnnounced = len; cs.truncAvail = rem - 12; return; }
        cs.blocks.push_back({p, (size_t)len});
        p += 12 + (size_t)len;
    }
}

// ---------------------------------------------------------------------------------------------
// runs
// ---------------------------------------------------------------------------------------------
static std::string csvOf(const std::string& p) {   // label-index string -> "a,b,c" ("-" for empty)
    std::string s;
    for (size_t i = 0; i < p.size(); i++) { if (i) s += ','; s += std::to_string((int)(uint8_t)p[i]); }
    return s.empty() ? "-" : s;
}
static std::string csvParse(const std::string& s) {
    std::string r;
    if (s == "-") return r;
    for (const std::string& x : splitChar(s, ',')) r += (char)atoi(x.c_str());
    return r;
}

struct RunSpec {
    std::string id = "run";
    std::string ipPath, leavesPath, outLeaves, witnessOut, raisePath, rootsPath, flipSave, emitIP, emitBlocks;
    std::vector<std::string> merges;
    int cls = -1, Rarg = -1;
    bool noRecompute = false, lenient = false, sha = false, flipsAll = false, rootsIdx = false, verboseBlocks = false;
    int flips = 0;
    ull seed = 1;
    std::vector<std::string> traces;
};

struct Global {
    std::string table;
    Manifest man;
    ClassCtx cc;
};

static std::string prefixToVectors(const IPData& ip, const std::string& p) {
    std::string s;
    for (size_t i = 0; i < p.size(); i++) { if (i) s += ' '; s += std::to_string(ip.lv[(uint8_t)p[i]]); }
    return s.empty() ? "-" : s;
}

static bool readLinesOfInts(const std::string& path, std::vector<std::vector<long long>>& out, std::string& err, std::vector<uint8_t>* raw) {
    std::vector<uint8_t> b;
    if (!slurp(path, b)) { err = "cannot read " + path; return false; }
    if (raw) *raw = b;
    size_t i = 0;
    while (i <= b.size()) {
        size_t j = i;
        while (j < b.size() && b[j] != '\n') j++;
        std::vector<long long> row;
        bool any = false;
        size_t k = i;
        while (k < j) {
            if (b[k] == '-' || (b[k] >= '0' && b[k] <= '9')) {
                size_t s = k;
                if (b[k] == '-') k++;
                while (k < j && b[k] >= '0' && b[k] <= '9') k++;
                std::string t((const char*)&b[s], k - s);
                if (t == "-") { any = true; row.push_back(-1); } else { row.push_back(atoll(t.c_str())); any = true; }
            } else k++;
        }
        if (any) out.push_back(row);
        if (j >= b.size()) break;
        i = j + 1;
    }
    return true;
}

static std::string checkManifestFor(Global& G, const std::string& path, const std::vector<uint8_t>& bytes, std::string& hexOut, bool force) {
    if (!G.man.loaded && !force) return "";
    hexOut = sha256hex(bytes);
    if (!G.man.loaded) return "";
    return G.man.check(path, hexOut);
}

static ull splitmix(ull& s) {
    ull z = (s += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

struct LoadedFile {
    std::string path;
    std::vector<uint8_t> bytes;   // kept only in flip mode
    ContainerScan cs;
    std::vector<BlockOut> res;    // per block of the container
    bool fileFail = false;
};

static int runOne(Global& G, const RunSpec& rs) {
    std::vector<std::string> reasons;
    g_xcheckN = g_xcheckBad = 0;
    printf("=== RUN %s\n", rs.id.c_str());
    bool mutantMode = g_mutArith64 || g_mutUnsignedSlack;
    if (mutantMode) printf("MUTANT-EVALUATOR arith64=%d unsigned_slack=%d (test-only wrong evaluation; the verdict below is not a proof)\n", g_mutArith64 ? 1 : 0, g_mutUnsignedSlack ? 1 : 0);
    auto finish = [&](void) -> int {
        bool pass = reasons.empty();
        std::string verdict = pass ? "PASS" : "FAIL";
        if (!rs.emitBlocks.empty() && rs.merges.empty()) verdict = "WORKER-" + verdict;   // a worker only emits its block summary
        if (rs.noRecompute) verdict += "-BYPASS";
        if (mutantMode) verdict += "-MUTANT-EVALUATOR";
        std::string why;
        for (const std::string& r : reasons) why += " [" + r + "]";
        printf("RESULT %s%s\n", verdict.c_str(), why.c_str());
        fflush(stdout);
        return pass ? 0 : 1;
    };
    // ---- IP ----
    std::vector<uint8_t> ipBytes;
    if (!slurp(rs.ipPath, ipBytes)) { printf("IP cannot read %s\n", rs.ipPath.c_str()); reasons.push_back("ip-unreadable"); return finish(); }
    std::string ipHex;
    std::string mres = checkManifestFor(G, rs.ipPath, ipBytes, ipHex, true);
    printf("IP %s sha256=%s%s\n", rs.ipPath.c_str(), ipHex.c_str(), mres.empty() ? "" : (" manifest=" + mres).c_str());
    if (!mres.empty() && mres != "OK") reasons.push_back("manifest-ip-" + mres);
    IPData ip;
    std::string err;
    if (!parseIP(ipBytes, ip, err)) { printf("IP PARSE FAIL: %s\n", err.c_str()); reasons.push_back("ip-parse"); return finish(); }
    finishIP(ip);
    printf("IP R=%d N=%d rows=%zu multi_label_rows=%d listed_group_elements=%zu\n", ip.R, ip.N, ip.rows.size(), ip.numMulti, ip.G.size());
    if (rs.Rarg >= 0 && rs.Rarg != ip.R) { printf("IP R=%d differs from --R %d\n", ip.R, rs.Rarg); reasons.push_back("R-mismatch"); }
    // ---- recomputation ----
    if (!rs.noRecompute) {
        if (rs.cls < 0) { printf("RECOMPUTE needs --class\n"); reasons.push_back("no-class"); }
        else {
            std::map<int, int> raise;
            if (!rs.raisePath.empty()) {
                std::vector<std::vector<long long>> rows;
                std::vector<uint8_t> raw;
                std::string e2;
                if (!readLinesOfInts(rs.raisePath, rows, e2, &raw)) { printf("RAISE %s\n", e2.c_str()); reasons.push_back("raise-unreadable"); }
                else {
                    std::string h;
                    std::string mr = checkManifestFor(G, rs.raisePath, raw, h, true);
                    printf("RAISE %s sha256=%s%s entries=%zu\n", rs.raisePath.c_str(), h.c_str(), mr.empty() ? "" : (" manifest=" + mr).c_str(), rows.size());
                    if (mr == "MISMATCH") reasons.push_back("manifest-raise-MISMATCH");   // a converted raise file is not in the manifest: only a wrong hash fails
                    for (auto& r : rows) if (r.size() >= 2) raise[(int)r[0]] = (int)r[1];
                }
            }
            if (!G.cc.ready) {
                std::vector<uint8_t> tb;
                if (slurp(G.table, tb)) {
                    std::string h;
                    std::string mr = checkManifestFor(G, G.table, tb, h, true);
                    printf("TABLE %s sha256=%s%s\n", G.table.c_str(), h.c_str(), mr.empty() ? "" : (" manifest=" + mr).c_str());
                    if (!mr.empty() && mr != "OK") reasons.push_back("manifest-table-" + mr);
                }
                clock_t t0 = clock();
                G.cc.prepare(G.table);
                fprintf(stderr, "orbit pass %.1fs\n", (double)(clock() - t0) / CLOCKS_PER_SEC);
            }
            for (const std::string& l : G.cc.report) printf("RECOMPUTE step2 %s\n", l.c_str());
            if (!G.cc.ok) { printf("RECOMPUTE step2 FAIL: %s\n", G.cc.err.c_str()); reasons.push_back("class-table"); }
            else {
                std::vector<std::string> rep;
                std::vector<std::array<int, 2>> wit;
                bool ok = recomputeIP(G.cc, ip, rs.cls, raise, rep, wit);
                for (const std::string& l : rep) printf("%s\n", l.c_str());
                if (!ok) reasons.push_back("ip-recompute");
                if (!rs.witnessOut.empty()) {
                    FILE* f = fopen(rs.witnessOut.c_str(), "w");
                    if (f) {
                        for (size_t i = 0; i < wit.size(); i++)
                            if (wit[i][0] >= 0) fprintf(f, "%zu P=%d Q=%d\n", i, G.cc.g0.GL[wit[i][0]], G.cc.g0.GL[wit[i][1]]);
                            else fprintf(f, "%zu NONE\n", i);
                        fclose(f);
                    }
                }
            }
        }
    } else printf("RECOMPUTE bypassed by --no-recompute (synthetic IP); RESULT can never be a plain PASS\n");
    {
        std::vector<std::string> rep;
        bool ok = checkGroupIP(ip, rep);
        for (const std::string& l : rep) printf("%s\n", l.c_str());
        if (!ok) reasons.push_back("group-checks");
    }
    // ---- traces ----
    Replayer rp(ip);
    std::vector<LoadedFile> files;
    std::vector<BlockOut> verified;           // blocks that verified (all files)
    ull nBlocks = 0, nFailed = 0, nFilesFailed = 0, nTrunc = 0;
    ull sumNodes = 0, sumL = 0, sumF = 0, sumK = 0, sumO = 0, sumP = 0, sumChild = 0, sumSkip = 0, sumDualO = 0, sumForced = 0, sumFixed = 0;
    ull sumKinds[4] = {0, 0, 0, 0};
    std::map<std::string, ull> failCodes;
    std::string emitText;                                   // worker summary (--emit-blocks)
    const std::vector<std::string> noTraces;
    const std::vector<std::string>& loopList = rs.merges.empty() ? rs.traces : noTraces;   // merge mode replays nothing
    for (const std::string& path : loopList) {
        LoadedFile lf;
        lf.path = path;
        std::vector<uint8_t> bytes;
        if (!slurp(path, bytes)) {
            printf("FILE %s UNREADABLE\n", path.c_str());
            nFilesFailed++;
            reasons.push_back("trace-unreadable");
            if (!rs.emitBlocks.empty()) emitText += "FILE\t" + path + "\tUNREADABLE\t-\t-\t0\t0\t0\t0\n";
            continue;
        }
        std::string h, mr;
        if (G.man.loaded || rs.sha) mr = checkManifestFor(G, path, bytes, h, true);
        scanContainer(bytes.data(), bytes.size(), lf.cs);
        size_t nb = lf.cs.blocks.size(), okb = 0, badb = 0;
        if (lf.cs.bad) {
            lf.fileFail = true;
            nFilesFailed++;
            printf("FILE_FAIL %s code=%s off=%zu (the whole file is rejected)\n", path.c_str(), lf.cs.badWhy.c_str(), lf.cs.badOff);
            failCodes[lf.cs.badWhy]++;
        } else {
            for (size_t bi = 0; bi < nb; bi++) {
                BlockOut o;
                const BlockRef& br = lf.cs.blocks[bi];
                rp.verifyBlock(bytes.data() + br.start + 12, br.len, o, nullptr);
                nBlocks++;
                if (o.ok) {
                    okb++;
                    sumNodes += o.nodes; sumL += o.nL; sumF += o.nF; sumK += o.nK; sumO += o.nO; sumP += o.nP; sumChild += o.nChild;
                    sumSkip += o.nSkip; sumDualO += o.nDualO; sumForced += o.nForced; sumFixed += o.nFixed;
                    for (int k = 0; k < 4; k++) sumKinds[k] += o.kinds[k];
                    if (rs.verboseBlocks)
                        printf("BLOCK_OK file=%s block=%zu tag=%c fd=%d nodes=%llu L=%llu F=%llu K=%llu O=%llu prefix(label vectors)= %s\n", path.c_str(), bi, o.tag, o.fd, o.nodes, o.nL, o.nF, o.nK, o.nO, prefixToVectors(ip, o.prefix).c_str());
                    verified.push_back(o);
                } else {
                    badb++;
                    nFailed++;
                    failCodes[o.code]++;
                    printf("BLOCK_FAIL file=%s block=%zu file_off=%zu payload_off=%zu code=%s detail=%s\n", path.c_str(), bi, br.start, o.off, o.code.c_str(), o.detail.c_str());
                }
                lf.res.push_back(std::move(o));
            }
            if (lf.cs.truncated) {
                nTrunc++;
                printf("TRUNCATED_LAST_BLOCK file=%s off=%zu announced=%llu available=%llu (ignored and reported)\n", path.c_str(), lf.cs.truncOff, lf.cs.truncAnnounced, lf.cs.truncAvail);
            }
        }
        printf("FILE %s bytes=%zu%s%s blocks=%zu verified=%zu failed=%zu truncated=%d\n", path.c_str(), bytes.size(),
               h.empty() ? "" : (" sha256=" + h).c_str(), mr.empty() ? "" : (" manifest=" + mr).c_str(), nb, okb, badb, lf.cs.truncated ? 1 : 0);
        if (!mr.empty() && mr != "OK") reasons.push_back("manifest-trace-" + mr);
        if (!rs.emitBlocks.empty()) {
            emitText += "FILE\t" + path + "\t" + (lf.fileFail ? "FILE_FAIL:" + lf.cs.badWhy : std::string("OK")) + "\t" + (h.empty() ? "-" : h) + "\t" + (mr.empty() ? "-" : mr) + "\t" +
                        std::to_string(nb) + "\t" + std::to_string(okb) + "\t" + std::to_string(badb) + "\t" + (lf.cs.truncated ? "1" : "0") + "\n";
            for (size_t bi = 0; bi < lf.res.size(); bi++) {
                const BlockOut& o = lf.res[bi];
                if (o.ok) {
                    emitText += std::string("B\t") + o.tag + "\t" + std::to_string(o.fd) + "\t" + std::to_string(o.nodes) + "\t" + std::to_string(o.nL) + "\t" + std::to_string(o.nF) + "\t" + csvOf(o.prefix) + "\n";
                    for (const std::string& f : o.frontier) emitText += "F\t" + csvOf(f) + "\n";
                    for (const std::string& l : o.leaves) emitText += "L\t" + csvOf(l) + "\n";
                } else emitText += "BF\t" + path + "\t" + std::to_string(bi) + "\t" + o.code + "\n";
            }
        }
        if (rs.flips > 0 || rs.flipsAll) { lf.bytes = std::move(bytes); files.push_back(std::move(lf)); }
    }
    if (!rs.merges.empty()) {
        // merge mode: the verified blocks come from worker summaries (same IP, same checks); positional traces = expected file list
        std::map<std::string, std::string> fileStatus;
        bool ipBad = false;
        for (const std::string& mp : rs.merges) {
            std::vector<uint8_t> mb;
            if (!slurp(mp, mb)) { printf("MERGE cannot read %s\n", mp.c_str()); reasons.push_back("merge-unreadable"); continue; }
            size_t cur = (size_t)-1;
            bool hdr = false;
            ull nb0 = 0;
            for (const std::string& ln : splitChar(std::string(mb.begin(), mb.end()), '\n')) {
                if (ln.empty()) continue;
                std::vector<std::string> t = splitChar(ln, '\t');
                if (t[0] == "CHK334E_BLOCKS") { hdr = true; continue; }
                if (t[0] == "IPSHA") {
                    if (t.size() < 4 || t[1] != ipHex || atoi(t[2].c_str()) != ip.R || atoi(t[3].c_str()) != ip.N) ipBad = true;
                } else if (t[0] == "FILE" && t.size() >= 9) {
                    if (fileStatus.count(t[1])) reasons.push_back("merge-duplicate-file");
                    fileStatus[t[1]] = t[2];
                    if (t[2] != "OK") { nFilesFailed++; if (t[2] != "UNREADABLE") failCodes[t[2].substr(10)]++; }
                    if (t[4] != "-" && t[4] != "OK") reasons.push_back("manifest-trace-" + t[4]);
                    nb0 = (ull)atoll(t[6].c_str()) + (ull)atoll(t[7].c_str());
                    nBlocks += nb0;
                    nFailed += (ull)atoll(t[7].c_str());
                    nTrunc += (ull)atoll(t[8].c_str());
                    cur = (size_t)-1;
                } else if (t[0] == "B" && t.size() >= 7) {
                    BlockOut o;
                    o.ok = true;
                    o.tag = t[1][0];
                    o.fd = atoi(t[2].c_str());
                    o.nodes = (ull)atoll(t[3].c_str()); o.nL = (ull)atoll(t[4].c_str()); o.nF = (ull)atoll(t[5].c_str());
                    o.prefix = csvParse(t[6]);
                    sumNodes += o.nodes; sumL += o.nL; sumF += o.nF;
                    verified.push_back(o);
                    cur = verified.size() - 1;
                } else if (t[0] == "F" && t.size() >= 2 && cur != (size_t)-1) verified[cur].frontier.push_back(csvParse(t[1]));
                else if (t[0] == "L" && t.size() >= 2 && cur != (size_t)-1) verified[cur].leaves.push_back(csvParse(t[1]));
                else if (t[0] == "BF" && t.size() >= 4) failCodes[t[3]]++;
            }
            if (!hdr) { printf("MERGE %s is not a block summary\n", mp.c_str()); reasons.push_back("merge-bad-summary"); }
        }
        if (ipBad) { printf("MERGE summaries were produced for a different IP (sha256/R/N differ)\n"); reasons.push_back("merge-ip-mismatch"); }
        printf("MERGE summaries=%zu files=%zu\n", rs.merges.size(), fileStatus.size());
        if (!rs.traces.empty()) {
            std::set<std::string> want(rs.traces.begin(), rs.traces.end());
            size_t missing = 0, extra = 0;
            for (const std::string& p : want) if (!fileStatus.count(p)) { if (missing++ < 10) printf("MERGE listed trace file not checked by any worker: %s\n", p.c_str()); }
            for (auto& kv : fileStatus) if (!want.count(kv.first)) { if (extra++ < 10) printf("MERGE checked file is not in the expected list: %s\n", kv.first.c_str()); }
            printf("MERGE expected_files=%zu not_checked=%zu unexpected=%zu\n", want.size(), missing, extra);
            if (missing) reasons.push_back("files-not-checked=" + std::to_string(missing));
            if (extra) reasons.push_back("unexpected-files=" + std::to_string(extra));
        } else printf("MERGE no expected file list given (positional traces): completeness of the file set is not checked\n");
    }
    if (!rs.emitBlocks.empty() && rs.merges.empty()) {
        std::string head = "CHK334E_BLOCKS\t1\nIPSHA\t" + ipHex + "\t" + std::to_string(ip.R) + "\t" + std::to_string(ip.N) + "\n";
        FILE* f = fopen(rs.emitBlocks.c_str(), "w");
        if (!f) { printf("WORKER cannot write %s\n", rs.emitBlocks.c_str()); reasons.push_back("emit-blocks-unwritable"); }
        else {
            fwrite(head.data(), 1, head.size(), f);
            fwrite(emitText.data(), 1, emitText.size(), f);
            fclose(f);
            printf("WORKER emitted %s files=%zu blocks_verified=%zu blocks_failed=%llu files_failed=%llu\n", rs.emitBlocks.c_str(), rs.traces.size(), verified.size(), nFailed, nFilesFailed);
        }
        if (!rs.lenient && (nFailed || nFilesFailed)) reasons.push_back("failed-blocks=" + std::to_string(nFailed) + ",failed-files=" + std::to_string(nFilesFailed));
        return finish();
    }
    printf("BLOCKS total=%llu verified=%zu failed=%llu files_failed=%llu truncated_last_blocks=%llu\n", nBlocks, verified.size(), nFailed, nFilesFailed, nTrunc);
    for (auto& kv : failCodes) printf("BLOCKS fail_code %s %llu\n", kv.first.c_str(), kv.second);
    printf("RECORDS nodes=%llu L=%llu F=%llu K=%llu O=%llu children=%llu P_dead=%llu noncanonical_skips=%llu O_with_dual=%llu O_forced_label=%llu labels_fixed_by_dual=%llu cut_kinds=%llu/%llu/%llu/%llu\n",
           sumNodes, sumL, sumF, sumK, sumO, sumChild, sumP, sumSkip, sumDualO, sumForced, sumFixed, sumKinds[0], sumKinds[1], sumKinds[2], sumKinds[3]);
    if (!rs.lenient && (nFailed || nFilesFailed)) reasons.push_back("failed-blocks=" + std::to_string(nFailed) + ",failed-files=" + std::to_string(nFilesFailed));
    // ---- coverage ----
    std::vector<std::string> roots;
    if (rs.rootsPath.empty()) roots.push_back(std::string());
    else {
        std::vector<std::vector<long long>> rows;
        std::vector<uint8_t> raw;
        std::string e2;
        // a line holding only '-' (or an empty-prefix marker) is the empty prefix
        if (!readLinesOfInts(rs.rootsPath, rows, e2, &raw)) { printf("ROOTS %s\n", e2.c_str()); reasons.push_back("roots-unreadable"); }
        else {
            std::string h;
            std::string mr = checkManifestFor(G, rs.rootsPath, raw, h, true);
            printf("ROOTS %s sha256=%s%s lines=%zu\n", rs.rootsPath.c_str(), h.c_str(), mr.empty() ? "" : (" manifest=" + mr).c_str(), rows.size());
            if (!mr.empty() && mr != "OK") reasons.push_back("manifest-roots-" + mr);
            for (auto& r : rows) {
                std::string p;
                bool okp = true;
                for (long long v : r) {
                    if (v == -1 && r.size() == 1) continue;
                    int l = rs.rootsIdx ? ((v >= 0 && v < ip.N) ? (int)v : -1) : ((v >= 0 && v < 512) ? ip.labelOfVec[v] : -1);
                    if (l < 0) { okp = false; break; }
                    p += (char)l;
                }
                if (okp) roots.push_back(p); else { printf("ROOTS line with a non-label vector ignored\n"); reasons.push_back("roots-bad-line"); }
            }
        }
    }
    std::unordered_map<std::string, std::vector<const BlockOut*>> byPrefix;
    for (const BlockOut& b : verified) byPrefix[b.prefix].push_back(&b);
    std::unordered_map<std::string, signed char> memo;   // 0 in progress, 1 covered, 2 not covered
    std::function<bool(const std::string&)> cov = [&](const std::string& p) -> bool {
        auto it = memo.find(p);
        if (it != memo.end()) return it->second == 1;
        memo[p] = 0;
        bool res = false;
        auto bi = byPrefix.find(p);
        if (bi != byPrefix.end())
            for (const BlockOut* b : bi->second) {
                if (b->tag == 'J') { res = true; break; }
                bool all = true;
                for (const std::string& f : b->frontier) if (!cov(f)) { all = false; break; }
                if (all) { res = true; break; }
            }
        memo[p] = res ? 1 : 2;
        return res;
    };
    bool complete = true;
    for (const std::string& r : roots) if (!cov(r)) complete = false;
    std::set<std::string> reach;
    std::vector<std::string> queue;
    for (const std::string& r : roots) if (reach.insert(r).second) queue.push_back(r);
    for (size_t qi = 0; qi < queue.size(); qi++) {
        auto bi = byPrefix.find(queue[qi]);
        if (bi == byPrefix.end()) continue;
        for (const BlockOut* b : bi->second) if (b->tag == 'T') for (const std::string& f : b->frontier) if (reach.insert(f).second) queue.push_back(f);
    }
    std::vector<std::string> uncovered;
    for (const std::string& p : reach) if (!byPrefix.count(p) && !cov(p)) uncovered.push_back(p);
    if (complete) printf("COVERAGE COMPLETE roots=%zu reachable_prefixes=%zu\n", roots.size(), reach.size());
    else {
        printf("COVERAGE INCOMPLETE roots=%zu reachable_prefixes=%zu uncovered_missing_prefixes=%zu\n", roots.size(), reach.size(), uncovered.size());
        for (const std::string& p : uncovered) printf("UNCOVERED prefix(label vectors)= %s\n", prefixToVectors(ip, p).c_str());
        reasons.push_back("coverage-incomplete");
    }
    // ---- leaves ----
    std::set<std::string> covering;
    ull unreachableLeaves = 0;
    for (const BlockOut& b : verified) {
        if (reach.count(b.prefix)) for (const std::string& l : b.leaves) covering.insert(l);
        else unreachableLeaves += b.leaves.size();
    }
    printf("LEAVES covering=%zu in_unreachable_verified_blocks=%llu (reported, not required)\n", covering.size(), unreachableLeaves);
    if (!rs.outLeaves.empty()) {
        std::string lt;
        for (const std::string& l : covering) lt += prefixToVectors(ip, l) + "\n";
        FILE* f = fopen(rs.outLeaves.c_str(), "w");
        if (f) {
            fwrite(lt.data(), 1, lt.size(), f);
            fclose(f);
            printf("LEAVES written %s lines=%zu sha256=%s\n", rs.outLeaves.c_str(), covering.size(), sha256hex(std::vector<uint8_t>(lt.begin(), lt.end())).c_str());
        } else { printf("LEAVES cannot write %s\n", rs.outLeaves.c_str()); reasons.push_back("out-leaves-unwritable"); }
    }
    if (rs.leavesPath.empty()) {
        if (!covering.empty()) { printf("LEAVES leaf file not supplied but covering leaves exist\n"); reasons.push_back("leaves-file-required"); }
        else printf("LEAVES leaf file not supplied; covering set is empty so the subset check holds trivially\n");
    } else {
        std::vector<std::vector<long long>> lrows;
        std::vector<uint8_t> raw;
        std::string e2;
        if (!readLinesOfInts(rs.leavesPath, lrows, e2, &raw)) { printf("LEAVES %s\n", e2.c_str()); reasons.push_back("leaves-unreadable"); }
        else {
            std::string h;
            std::string mr = checkManifestFor(G, rs.leavesPath, raw, h, true);
            printf("LEAVES file %s bytes=%zu sha256=%s%s lines=%zu\n", rs.leavesPath.c_str(), raw.size(), h.c_str(), mr.empty() ? "" : (" manifest=" + mr).c_str(), lrows.size());
            if (mr == "MISMATCH") reasons.push_back("manifest-leaves-MISMATCH");
            std::set<std::string> fileLeaves;
            int badLines = 0;
            for (auto& r : lrows) {
                std::string s;
                bool okl = (int)r.size() == ip.R;
                for (long long v : r) { int l = (v >= 0 && v < 512) ? ip.labelOfVec[v] : -1; if (l < 0) { okl = false; break; } s += (char)l; }
                if (!okl) { badLines++; continue; }
                std::sort(s.begin(), s.end(), [](char a, char b) { return (uint8_t)a < (uint8_t)b; });
                fileLeaves.insert(s);
            }
            ull missing = 0;
            for (const std::string& l : covering) if (!fileLeaves.count(l)) missing++;
            ull fileOnly = 0;
            for (const std::string& l : fileLeaves) if (!covering.count(l)) fileOnly++;
            printf("LEAVES covering_in_leaf_file=%llu covering_not_in_leaf_file=%llu leaf_file_only=%llu leaf_file_unparsed_lines=%d\n", (ull)covering.size() - missing, missing, fileOnly, badLines);
            if (missing) reasons.push_back("covering-leaves-not-in-leaf-file=" + std::to_string(missing));
            if (badLines) reasons.push_back("leaf-file-unparsed-lines");
        }
    }
    // ---- byte-flip mutants ----
    if (rs.flips > 0 || rs.flipsAll) {
        std::vector<std::pair<size_t, size_t>> pool;   // (file, block)
        for (size_t fi = 0; fi < files.size(); fi++)
            if (!files[fi].fileFail) for (size_t bi = 0; bi < files[fi].cs.blocks.size(); bi++) pool.push_back({fi, bi});
        std::vector<ull> cumBits(1, 0);
        for (auto& pr0 : pool) cumBits.push_back(cumBits.back() + (ull)(12 + files[pr0.first].cs.blocks[pr0.second].len) * 8);
        const ull nTrials = rs.flipsAll ? cumBits.back() : (ull)rs.flips;
        ull rng = rs.seed;
        ull cBlockFail = 0, cFileFail = 0, cTrunc = 0, cValid = 0, cSame = 0, cChanged = 0;
        std::map<std::string, ull> codes, accByField;
        if (pool.empty()) printf("FLIPS no blocks to mutate\n");
        ull printedSame = 0;
        for (ull t = 0; t < nTrials && !pool.empty(); t++) {
            size_t pidx, bitIndex;
            if (rs.flipsAll) {
                pidx = (size_t)(std::upper_bound(cumBits.begin(), cumBits.end(), t) - cumBits.begin()) - 1;
                bitIndex = (size_t)(t - cumBits[pidx]);
            } else {
                pidx = (size_t)(splitmix(rng) % pool.size());
                size_t totalBytes0 = 12 + files[pool[pidx].first].cs.blocks[pool[pidx].second].len;
                bitIndex = (size_t)(splitmix(rng) % (ull)(totalBytes0 * 8));
            }
            auto pr = pool[pidx];
            LoadedFile& lf = files[pr.first];
            const BlockRef br = lf.cs.blocks[pr.second];
            const BlockOut& orig = lf.res[pr.second];
            size_t byteOff = bitIndex / 8;
            int bit = (int)(bitIndex % 8);
            std::string outcome, code, field;
            std::vector<uint8_t> payload(lf.bytes.begin() + br.start + 12, lf.bytes.begin() + br.start + 12 + br.len);
            BlockOut mo;
            if (byteOff < 4) { outcome = "FILE_FAIL"; code = "BAD_MAGIC"; field = "magic"; }
            else if (byteOff < 12) {
                field = "length";
                uint64_t newLen = (uint64_t)br.len ^ (1ULL << ((byteOff - 4) * 8 + bit));
                uint64_t avail = (uint64_t)(lf.bytes.size() - br.start - 12);
                if (newLen > avail) { outcome = "TRUNC"; code = "ignored-as-truncated-last-block"; }
                else {
                    size_t q = br.start + 12 + (size_t)newLen;
                    rp.verifyBlock(lf.bytes.data() + br.start + 12, (size_t)newLen, mo, nullptr);
                    bool contBad = false;
                    if (q < lf.bytes.size()) {
                        if (lf.bytes.size() - q >= 4) contBad = le32(&lf.bytes[q]) != MAGIC;
                        else contBad = false;
                    }
                    if (!mo.ok) { outcome = "BLOCK_FAIL"; code = mo.code; }
                    else if (contBad) { outcome = "FILE_FAIL"; code = "BAD_MAGIC"; }
                    else outcome = "VALID";
                }
            } else {
                size_t po = byteOff - 12;
                payload[po] ^= (uint8_t)(1u << bit);
                rp.verifyBlock(payload.data(), payload.size(), mo, nullptr);
                if (!mo.ok) { outcome = "BLOCK_FAIL"; code = mo.code; }
                else outcome = "VALID";
                // field name (only for accepted mutants) from an annotated run of the original block
                field = "unknown";
                if (outcome == "VALID") {
                    std::vector<Span> ann;
                    BlockOut tmp;
                    rp.verifyBlock(lf.bytes.data() + br.start + 12, br.len, tmp, &ann);
                    for (const Span& s : ann) if (po >= s.a && po < s.b) { field = s.name; break; }
                }
            }
            if (outcome == "BLOCK_FAIL") { cBlockFail++; codes[code]++; }
            else if (outcome == "FILE_FAIL") { cFileFail++; codes[code]++; }
            else if (outcome == "TRUNC") { cTrunc++; codes[code]++; }
            else {
                cValid++;
                bool same = orig.ok && mo.ok && mo.tag == orig.tag && mo.prefix == orig.prefix && mo.fd == orig.fd && mo.frontier == orig.frontier && mo.leaves == orig.leaves;
                if (same) cSame++; else cChanged++;
                accByField[field + (same ? "/same" : "/CHANGED")]++;
                bool show = !same || printedSame < 40;
                if (same) printedSame++;
                if (show) printf("FLIP_ACCEPTED trial=%llu file=%s block=%zu byte=%zu bit=%d field=%s claim=%s\n", t, lf.path.c_str(), pr.second, byteOff, bit, field.c_str(), same ? "same" : "CHANGED");
                if (show && !rs.flipSave.empty()) {
                    std::string fn = rs.flipSave + "/acc_" + rs.id + "_" + std::to_string(t) + ".bin";
                    FILE* f = fopen(fn.c_str(), "wb");
                    if (f) {
                        std::vector<uint8_t> hdr(lf.bytes.begin() + br.start, lf.bytes.begin() + br.start + 12);
                        if (byteOff >= 4 && byteOff < 12) hdr[byteOff] ^= (uint8_t)(1u << bit);
                        fwrite(hdr.data(), 1, 12, f);
                        if (byteOff >= 12) fwrite(payload.data(), 1, payload.size(), f);
                        else fwrite(lf.bytes.data() + br.start + 12, 1, br.len, f);
                        fclose(f);
                    }
                }
            }
        }
        printf("FLIPS mode=%s trials=%llu block_fail=%llu file_fail=%llu truncated_ignored=%llu accepted=%llu (claim_same=%llu claim_CHANGED=%llu)\n", rs.flipsAll ? "exhaustive" : "random", nTrials, cBlockFail, cFileFail, cTrunc, cValid, cSame, cChanged);
        for (auto& kv : codes) printf("FLIPS code %s %llu\n", kv.first.c_str(), kv.second);
        for (auto& kv : accByField) printf("FLIPS accepted_by_field %s %llu\n", kv.first.c_str(), kv.second);
        // state check: after all the failed and accepted mutant replays, every original block must still verify identically
        size_t leaks = 0;
        for (auto& pr : pool) {
            LoadedFile& lf = files[pr.first];
            const BlockRef br = lf.cs.blocks[pr.second];
            BlockOut o2;
            rp.verifyBlock(lf.bytes.data() + br.start + 12, br.len, o2, nullptr);
            const BlockOut& o0 = lf.res[pr.second];
            if (o2.ok != o0.ok || o2.nodes != o0.nodes || o2.leaves != o0.leaves || o2.frontier != o0.frontier || o2.prefix != o0.prefix) leaks++;
        }
        printf("FLIPS state_check blocks=%zu state_leaks=%zu\n", pool.size(), leaks);
        if (leaks) reasons.push_back("state-leak");
    }
    if (g_xcheck) {
        printf("XCHECK dual_evaluations=%llu long_double_disagreements=%llu\n", g_xcheckN, g_xcheckBad);
        if (g_xcheckBad) reasons.push_back("xcheck-disagreement");
    }
    return finish();
}

// ---------------------------------------------------------------------------------------------
// --emit-ip: the IP this checker derives for (class, R): labels ascending, rows of step 3, group = every distinct induced
// permutation (identity first).  Used for sizing/performance tests of point IPs and to diff against production IPs as sets.
// ---------------------------------------------------------------------------------------------
static bool emitIPFile(ClassCtx& cc, int clsIdx, int R, const std::map<int, int>& raise, const std::string& path, std::string& msg) {
    auto rit = cc.rowOfClass.find(clsIdx);
    if (rit == cc.rowOfClass.end()) { msg = "class not in the class table"; return false; }
    const ClassRow& E = cc.cls[rit->second];
    std::vector<int> Eel(1, 0);
    for (int b : E.basis) { size_t m = Eel.size(); for (size_t t = 0; t < m; t++) Eel.push_back(Eel[t] ^ b); }
    bool inE[512];
    for (int v = 0; v < 512; v++) inE[v] = false;
    for (int v : Eel) inE[v] = true;
    int cosetMin[512];
    for (int v = 0; v < 512; v++) { int m = v; for (int e : Eel) m = std::min(m, v ^ e); cosetMin[v] = m; }
    std::vector<int> lab;
    for (int v = 1; v < 512; v++) if (!inE[v] && cosetMin[v] == v) lab.push_back(v);
    const int N = (int)lab.size();
    int idxOf[512];
    for (int v = 0; v < 512; v++) idxOf[v] = -1;
    for (int i = 0; i < N; i++) idxOf[lab[i]] = i;
    int cosetLabel[512];
    for (int v = 0; v < 512; v++) cosetLabel[v] = inE[v] ? -1 : idxOf[cosetMin[v]];
    std::vector<RowKey> exp;
    if (!enumerateSuperspaces(cc, E, R, raise, cosetLabel, inE, exp, msg)) return false;
    std::set<std::string> perms;
    const G0Tables& g0 = cc.g0;
    for (int pi = 0; pi < 168; pi++)
        for (int qi = 0; qi < 168; qi++) {
            bool stab = true;
            for (int e : E.basis) if (!inE[g0.apply(pi, qi, e)]) { stab = false; break; }
            if (!stab) continue;
            std::string p(N, 0);
            for (int l = 0; l < N; l++) p[l] = (char)cosetLabel[g0.apply(pi, qi, lab[l])];
            perms.insert(p);
        }
    std::string idp(N, 0);
    for (int l = 0; l < N; l++) idp[l] = (char)l;
    FILE* f = fopen(path.c_str(), "w");
    if (!f) { msg = "cannot write " + path; return false; }
    fprintf(f, "R %d N %d\n", R, N);
    for (int i = 0; i < N; i++) fprintf(f, "%s%d", i ? " " : "", lab[i]);
    fprintf(f, "\n");
    std::vector<const RowKey*> one(N, nullptr);
    std::vector<const RowKey*> multi;
    for (const RowKey& k : exp) {
        if (k.b.count() == 1) { for (int l = 0; l < N; l++) if (k.b.get(l)) one[l] = &k; }
        else multi.push_back(&k);
    }
    for (int l = 0; l < N; l++) if (one[l]) fprintf(f, "C %d %d 1 %d\n", one[l]->dim, std::min(one[l]->cap, R), l);
    std::sort(multi.begin(), multi.end(), [](const RowKey* a, const RowKey* b) { if (a->dim != b->dim) return a->dim < b->dim; return a->b < b->b; });
    for (const RowKey* k : multi) {
        fprintf(f, "C %d %d %d", k->dim, k->cap, k->b.count());
        for (int l = 0; l < N; l++) if (k->b.get(l)) fprintf(f, " %d", l);
        fprintf(f, "\n");
    }
    fprintf(f, "G %zu\n", perms.size());
    std::vector<const std::string*> order;
    order.push_back(&idp);
    for (const std::string& p : perms) if (p != idp) order.push_back(&p);
    for (const std::string* p : order) {
        for (int l = 0; l < N; l++) fprintf(f, "%s%d", l ? " " : "", (int)(uint8_t)(*p)[l]);
        fprintf(f, "\n");
    }
    fclose(f);
    msg = "labels=" + std::to_string(N) + " rows=" + std::to_string(exp.size()) + " group=" + std::to_string(perms.size());
    return true;
}

static int emitRun(Global& G, const RunSpec& rs) {
    printf("=== EMIT %s\n", rs.id.c_str());
    if (rs.cls < 0 || rs.Rarg < 0) { printf("EMIT needs --class and --R\nRESULT FAIL [usage]\n"); return 1; }
    std::map<int, int> raise;
    if (!rs.raisePath.empty()) {
        std::vector<std::vector<long long>> rows;
        std::string e2;
        if (!readLinesOfInts(rs.raisePath, rows, e2, nullptr)) { printf("EMIT %s\nRESULT FAIL [raise]\n", e2.c_str()); return 1; }
        for (auto& r : rows) if (r.size() >= 2) raise[(int)r[0]] = (int)r[1];
    }
    G.cc.prepare(G.table);
    for (const std::string& l : G.cc.report) printf("EMIT step2 %s\n", l.c_str());
    if (!G.cc.ok) { printf("EMIT class table FAIL: %s\nRESULT FAIL [class-table]\n", G.cc.err.c_str()); return 1; }
    std::string msg;
    if (!emitIPFile(G.cc, rs.cls, rs.Rarg, raise, rs.emitIP, msg)) { printf("EMIT FAIL: %s\nRESULT FAIL [emit]\n", msg.c_str()); return 1; }
    printf("EMIT written %s %s\nRESULT PASS-EMIT\n", rs.emitIP.c_str(), msg.c_str());
    return 0;
}

// ---------------------------------------------------------------------------------------------
// command line
// ---------------------------------------------------------------------------------------------
static void usage() {
    fprintf(stderr,
        "usage: chk334e --table seeded334.tsv [--manifest M --base DIR] RUN-OPTIONS TRACE...\n"
        "       chk334e --table seeded334.tsv [--manifest M --base DIR] --batch FILE   (one run per line; shared orbit pass)\n"
        "       chk334e --selftest\n"
        "run options: --id S --class C --ip F [--R n] [--leaves F] [--out-leaves F] [--witness-out F] [--raise F]\n"
        "             [--roots F] [--no-recompute] [--lenient] [--sha] [--blocks] [--dump] [--xcheck] [--traces-from F]\n"
        "             (--blocks prints one BLOCK_OK line per verified block: tag, fd, record counts, prefix; for block-for-block comparisons)\n"
        "emit mode:   chk334e --table T --class C --R n --emit-ip FILE [--raise F]   (writes the IP this checker derives)\n"
        "parallel:    worker: run options + --emit-blocks FILE  (verifies its traces, writes a block summary, RESULT WORKER-PASS|FAIL, no coverage verdict)\n"
        "             merge : run options + --merge SUMMARY... | --merge-list LIST, positional TRACE... = expected file list (every listed file must be\n"
        "                     in exactly one summary); coverage, leaves, leaf file and RESULT are decided here from the summaries\n"
        "             [--flips N --seed S | --flips-all] [--flip-save DIR] [--mut-arith64] [--mut-unsigned-slack]\n"
        "--raise F : lines 'class_idx lb' replacing the seeded lb of those classes (runs listed in result_dependencies_r1.tsv)\n"
        "--roots F : lines of label vectors (or label indices with --roots-idx); each line is a prefix that must be covered\n"
        "            ('-' = empty prefix); default = the empty prefix.  The line format of production --covers lists is not described.\n"
        "exit status 0 = RESULT PASS, 1 = RESULT FAIL, 2 = usage error\n");
}

static bool parseRunArgs(const std::vector<std::string>& a, RunSpec& rs, Global* G, std::string& err) {
    for (size_t i = 0; i < a.size(); i++) {
        const std::string& s = a[i];
        auto need = [&](std::string& dst) -> bool { if (i + 1 >= a.size()) { err = "missing value after " + s; return false; } dst = a[++i]; return true; };
        long long v;
        std::string t;
        if (s == "--id") { if (!need(rs.id)) return false; }
        else if (s == "--ip") { if (!need(rs.ipPath)) return false; }
        else if (s == "--leaves") { if (!need(rs.leavesPath)) return false; }
        else if (s == "--out-leaves") { if (!need(rs.outLeaves)) return false; }
        else if (s == "--witness-out") { if (!need(rs.witnessOut)) return false; }
        else if (s == "--raise") { if (!need(rs.raisePath)) return false; }
        else if (s == "--roots") { if (!need(rs.rootsPath)) return false; }
        else if (s == "--flip-save") { if (!need(rs.flipSave)) return false; }
        else if (s == "--emit-ip") { if (!need(rs.emitIP)) return false; }
        else if (s == "--emit-blocks") { if (!need(rs.emitBlocks)) return false; }
        else if (s == "--merge") { if (!need(t)) return false; rs.merges.push_back(t); }
        else if (s == "--merge-list") {
            if (!need(t)) return false;
            std::vector<uint8_t> b;
            if (!slurp(t, b)) { err = "cannot read " + t; return false; }
            for (const std::string& x : splitChar(std::string(b.begin(), b.end()), '\n')) {
                std::string y = x;
                while (!y.empty() && (y.back() == '\r' || y.back() == ' ')) y.pop_back();
                if (!y.empty()) rs.merges.push_back(y);
            }
        }
        else if (s == "--class") { if (!need(t) || !parseInt(t, v)) { err = "bad --class"; return false; } rs.cls = (int)v; }
        else if (s == "--R") { if (!need(t) || !parseInt(t, v)) { err = "bad --R"; return false; } rs.Rarg = (int)v; }
        else if (s == "--flips") { if (!need(t) || !parseInt(t, v)) { err = "bad --flips"; return false; } rs.flips = (int)v; }
        else if (s == "--seed") { if (!need(t) || !parseInt(t, v)) { err = "bad --seed"; return false; } rs.seed = (ull)v; }
        else if (s == "--flips-all") rs.flipsAll = true;
        else if (s == "--roots-idx") rs.rootsIdx = true;
        else if (s == "--blocks") rs.verboseBlocks = true;
        else if (s == "--no-recompute") rs.noRecompute = true;
        else if (s == "--lenient") rs.lenient = true;
        else if (s == "--sha") rs.sha = true;
        else if (s == "--dump") g_dump = true;
        else if (s == "--xcheck") g_xcheck = true;
        else if (s == "--mut-arith64") g_mutArith64 = true;
        else if (s == "--mut-unsigned-slack") g_mutUnsignedSlack = true;
        else if (s == "--traces-from") {
            if (!need(t)) return false;
            std::vector<uint8_t> b;
            if (!slurp(t, b)) { err = "cannot read " + t; return false; }
            for (const std::string& x : splitChar(std::string(b.begin(), b.end()), '\n')) {
                std::string y = x;
                while (!y.empty() && (y.back() == '\r' || y.back() == ' ')) y.pop_back();
                if (!y.empty()) rs.traces.push_back(y);
            }
        }
        else if (s == "--table" && G) { if (!need(G->table)) return false; }
        else if (s.size() > 2 && s[0] == '-' && s[1] == '-') { err = "unknown option " + s; return false; }
        else rs.traces.push_back(s);
    }
    return true;
}

static int selftest() {
    int bad = 0;
    auto chk = [&](bool c, const char* what) { if (!c) { printf("SELFTEST FAIL %s\n", what); bad++; } };
    {
        std::vector<uint8_t> e;
        chk(sha256hex(e) == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "sha256 empty");
        std::vector<uint8_t> abc = {'a', 'b', 'c'};
        chk(sha256hex(abc) == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad", "sha256 abc");
        std::string two = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        std::vector<uint8_t> t2(two.begin(), two.end());
        chk(sha256hex(t2) == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1", "sha256 two-block");
    }
    chk(gaussSubspaceCount(9) == 8283458, "gauss 9");
    chk(gaussSubspaceCount(8) == 417199, "gauss 8");   // 417,198 nonzero subspaces of F2^8, plus the zero subspace
    chk(gaussSubspaceCount(7) == 29212, "gauss 7");
    chk(gaussSubspaceCount(6) == 2825, "gauss 6");
    G0Tables g;
    std::string err;
    chk(g.init(err), "GL3 enumeration");
    SubIdx s;
    s.init();
    chk(s.total == 8283458u, "subspace total");
    // encode/decode round trip on a sample
    bool rt = true;
    for (uint32_t i = 0; i < s.total; i += 997) {
        int rows[9];
        int k = s.decode(i, rows);
        if (s.encode(rows, k) != i) { rt = false; break; }
    }
    chk(rt, "subspace index round trip");
    // varint
    {
        const uint8_t b1[] = {0xe5, 0x8e, 0x26};   // 624485
        Reader r;
        r.base = b1; r.pos = 0; r.end = 3;
        chk(r.varint("t") == 624485ULL, "varint 624485");
        const uint8_t b2[] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01};
        Reader r2;
        r2.base = b2; r2.pos = 0; r2.end = 10;
        chk(r2.varint("t") == 0xffffffffffffffffULL, "varint 2^64-1");
        const uint8_t b3[] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02};
        Reader r3;
        r3.base = b3; r3.pos = 0; r3.end = 10;
        bool threw = false;
        try { r3.varint("t"); } catch (BlockFail&) { threw = true; }
        chk(threw, "varint above 64 bits rejected");
        const uint8_t b4[] = {0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00};
        Reader r4;
        r4.base = b4; r4.pos = 0; r4.end = 11;
        threw = false;
        try { r4.varint("t"); } catch (BlockFail&) { threw = true; }
        chk(threw, "11-byte varint rejected");
    }
    chk(i128str((i128)1 << 100) == "1267650600228229401496703205376", "i128str 2^100");
    chk(i128str(-(((i128)1) << 70)) == "-1180591620717411303424", "i128str -2^70");
    printf(bad ? "SELFTEST FAILED\n" : "SELFTEST OK\n");
    return bad ? 1 : 0;
}

int main(int argc, char** argv) {
    std::vector<std::string> args(argv + 1, argv + argc);
    if (args.empty()) { usage(); return 2; }
    Global G;
    std::string manPath, baseDir, batchPath;
    std::vector<std::string> rest;
    for (size_t i = 0; i < args.size(); i++) {
        if (args[i] == "--selftest") return selftest();
        else if (args[i] == "--table" && i + 1 < args.size()) G.table = args[++i];
        else if (args[i] == "--manifest" && i + 1 < args.size()) manPath = args[++i];
        else if (args[i] == "--base" && i + 1 < args.size()) baseDir = args[++i];
        else if (args[i] == "--batch" && i + 1 < args.size()) batchPath = args[++i];
        else rest.push_back(args[i]);
    }
    if (!manPath.empty()) {
        std::string err;
        if (baseDir.empty()) { fprintf(stderr, "--manifest needs --base\n"); return 2; }
        if (!G.man.load(manPath, baseDir, err)) { fprintf(stderr, "%s\n", err.c_str()); return 2; }
        printf("MANIFEST %s entries=%zu base=%s\n", manPath.c_str(), G.man.hashOf.size(), G.man.base.c_str());
    }
    if (!batchPath.empty()) {
        std::vector<uint8_t> b;
        if (!slurp(batchPath, b)) { fprintf(stderr, "cannot read batch file\n"); return 2; }
        int nrun = 0, npass = 0;
        for (const std::string& ln : splitChar(std::string(b.begin(), b.end()), '\n')) {
            std::vector<std::string> tok = splitWS(ln);
            if (tok.empty() || tok[0][0] == '#') continue;
            RunSpec rs;
            std::string err;
            g_mutArith64 = g_mutUnsignedSlack = g_dump = g_xcheck = false;
            if (!parseRunArgs(tok, rs, &G, err)) { printf("=== RUN %s\nBATCH LINE ERROR: %s\nRESULT FAIL [usage]\n", rs.id.c_str(), err.c_str()); nrun++; continue; }
            nrun++;
            if ((rs.emitIP.empty() ? runOne(G, rs) : emitRun(G, rs)) == 0) npass++;
        }
        printf("BATCH runs=%d pass=%d fail=%d\n", nrun, npass, nrun - npass);
        return 0;
    }
    RunSpec rs;
    std::string err;
    if (!parseRunArgs(rest, rs, &G, err)) { fprintf(stderr, "%s\n", err.c_str()); usage(); return 2; }
    if (!rs.emitIP.empty()) { if (G.table.empty()) { usage(); return 2; } return emitRun(G, rs); }
    if (rs.ipPath.empty() || (G.table.empty() && !rs.noRecompute)) { usage(); return 2; }
    return runOne(G, rs);
}
