// symtab334.h: loader and validator for symtab334.tsv, the pair-symmetry tables of <3,3,4> over F2
// (produced by table/s13_gen_symtab.py, equal to the Lean tables of B334/Tables).
//
// Encodings (same as the Python generator and the Lean modules):
//   S   4x4 matrix, entry (r,c) at bit 4r+c, identity 0x8421
//   b   3x4 matrix, entry (j,k) at bit 4j+k      (second factors)
//   c   4x3 matrix, entry (k,i) at bit 3k+i      (third factors)
//   action (b, c) -> (b S, S^-1 c)
// Tables as given in the file (used as they are):
//   ORBM       the 15 orbit minima of the nonzero b under b -> b S
//   CORB[o]    for o in ORBM: the minima of the orbits of the nonzero c under c -> S^-1 c, S in Stab(o)
//   WB[b]      (S, S^-1) with b S in ORBM;   WC[o][c]  (S, S^-1) with S in Stab(o), S^-1 c in CORB[o]
// validate() re-checks every witness pair and the invariance of T334 under the pair action for ALL 20,160 elements of
// GL4(F2) (enumerated here by brute force), so a corrupted or mismatched table file is refused.
// Apache-2.0 (port of the rank333-f2 generator conventions).
#pragma once
#include <bits/stdc++.h>

namespace s334 {

static const int ID44 = 0x8421;

static inline int mul44(int u, int v) {
  int out = 0;
  for (int r = 0; r < 4; r++) {
    int ur = (u >> (4 * r)) & 15, acc = 0;
    for (int l = 0; l < 4; l++) if ((ur >> l) & 1) acc ^= (v >> (4 * l)) & 15;
    out |= acc << (4 * r);
  }
  return out;
}
static inline int mulBS(int b, int S) {   // (3x4) * (4x4)
  int out = 0;
  for (int j = 0; j < 3; j++) {
    int br = (b >> (4 * j)) & 15, acc = 0;
    for (int l = 0; l < 4; l++) if ((br >> l) & 1) acc ^= (S >> (4 * l)) & 15;
    out |= acc << (4 * j);
  }
  return out;
}
static inline int mulSC(int S, int c) {   // (4x4) * (4x3)
  int out = 0;
  for (int r = 0; r < 4; r++) {
    int Sr = (S >> (4 * r)) & 15, acc = 0;
    for (int l = 0; l < 4; l++) if ((Sr >> l) & 1) acc ^= (c >> (3 * l)) & 7;
    out |= acc << (3 * r);
  }
  return out;
}
// inverse of a 4x4 matrix over F2 by Gauss-Jordan; -1 if singular
static inline int inv44(int S) {
  int a[4], e[4];
  for (int r = 0; r < 4; r++) { a[r] = (S >> (4 * r)) & 15; e[r] = 1 << r; }
  for (int col = 0; col < 4; col++) {
    int pv = -1;
    for (int r = col; r < 4; r++) if ((a[r] >> col) & 1) { pv = r; break; }
    if (pv < 0) return -1;
    std::swap(a[col], a[pv]); std::swap(e[col], e[pv]);
    for (int r = 0; r < 4; r++) if (r != col && ((a[r] >> col) & 1)) { a[r] ^= a[col]; e[r] ^= e[col]; }
  }
  int out = 0;
  for (int r = 0; r < 4; r++) out |= e[r] << (4 * r);
  return out;
}

struct SymTab {
  std::string path;
  std::vector<int> orbm;                                   // 15 orbit minima, ascending
  std::map<int, std::vector<int>> corb;                    // o -> c list (ascending)
  std::map<int, int> stab;                                 // o -> |Stab(o)|
  std::vector<std::array<int, 2>> wb;                      // [b] = {S, S^-1}, b in 1..4095
  std::map<int, std::vector<std::array<int, 2>>> wc;       // [o][c] = {S, S^-1}, c in 1..4095
};

static inline std::vector<int> parse_list(const std::string& s) {
  std::vector<int> v; size_t p = 0;
  while (p <= s.size()) {
    size_t q = s.find(',', p); if (q == std::string::npos) q = s.size();
    if (q > p) v.push_back(std::stoi(s.substr(p, q - p)));
    p = q + 1;
  }
  return v;
}

static inline SymTab load(const std::string& path) {
  std::ifstream in(path);
  if (!in) throw std::runtime_error("cannot open symtab file " + path);
  SymTab st; st.path = path; st.wb.assign(4096, {0, 0});
  std::string line;
  while (std::getline(in, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::vector<std::string> f; size_t p = 0;
    while (true) {
      size_t q = line.find('\t', p);
      if (q == std::string::npos) { f.push_back(line.substr(p)); break; }
      f.push_back(line.substr(p, q - p)); p = q + 1;
    }
    if (f.size() != 3) throw std::runtime_error("symtab: bad line: " + line.substr(0, 60));
    if (f[0] == "ORBM") st.orbm = parse_list(f[2]);
    else if (f[0] == "STAB") st.stab[std::stoi(f[1])] = std::stoi(f[2]);
    else if (f[0] == "CORB") st.corb[std::stoi(f[1])] = parse_list(f[2]);
    else if (f[0] == "WB") {
      int b = std::stoi(f[1]); auto v = parse_list(f[2]);
      if (b < 1 || b > 4095 || v.size() != 2) throw std::runtime_error("symtab: bad WB line");
      st.wb[b] = {v[0], v[1]};
    } else if (f[0] == "WC") {
      auto col = f[1].find(':'); if (col == std::string::npos) throw std::runtime_error("symtab: bad WC key");
      int o = std::stoi(f[1].substr(0, col)), c = std::stoi(f[1].substr(col + 1)); auto v = parse_list(f[2]);
      if (c < 1 || c > 4095 || v.size() != 2) throw std::runtime_error("symtab: bad WC line");
      auto& w = st.wc[o]; if (w.empty()) w.assign(4096, {0, 0});
      w[c] = {v[0], v[1]};
    } else throw std::runtime_error("symtab: unknown kind " + f[0]);
  }
  return st;
}

// The target tensor T334 as a list of (x, y, z): x = 3i+j, y = 4j+k, z = 3k+i.
static inline std::vector<std::array<int, 3>> t334_support() {
  std::vector<std::array<int, 3>> t;
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) for (int k = 0; k < 4; k++) t.push_back({3 * i + j, 4 * j + k, 3 * k + i});
  return t;
}

// Returns "" if the tables are consistent, else a description of the first problem.
// Checks: 15 ORBM entries; every nonzero b has (S,S^-1) with S S^-1 = S^-1 S = I and b S in ORBM; for each o in ORBM every
// nonzero c has (S,S^-1) with S S^-1 = I, o S = o and S^-1 c in CORB[o]; and (all 20,160 S in GL4, brute force) the slices of
// T334 are invariant under (b, c) -> (b S, S^-1 c).
static inline std::string validate(const SymTab& st) {
  char buf[200];
  if (st.orbm.size() != 15) return "ORBM does not have 15 entries";
  std::set<int> orbm(st.orbm.begin(), st.orbm.end());
  if (orbm.size() != 15) return "ORBM has repeated entries";
  for (int o : st.orbm) if (o < 1 || o > 4095) return "ORBM entry out of range";
  for (int b = 1; b < 4096; b++) {
    int S = st.wb[b][0], Si = st.wb[b][1];
    if (S < 0 || S > 65535 || Si < 0 || Si > 65535) return "WB entry out of range";
    if (mul44(S, Si) != ID44 || mul44(Si, S) != ID44) { snprintf(buf, sizeof buf, "WB[%d]: S S^-1 != I", b); return buf; }
    if (!orbm.count(mulBS(b, S))) { snprintf(buf, sizeof buf, "WB[%d]: b S not in ORBM", b); return buf; }
  }
  for (int o : st.orbm) {
    auto it = st.corb.find(o); if (it == st.corb.end()) return "CORB missing for an ORBM entry";
    std::set<int> cs(it->second.begin(), it->second.end());
    if (cs.size() != it->second.size() || cs.empty()) return "CORB list empty or repeated";
    for (int c : it->second) if (c < 1 || c > 4095) return "CORB entry out of range";
    auto jt = st.wc.find(o); if (jt == st.wc.end()) return "WC missing for an ORBM entry";
    for (int c = 1; c < 4096; c++) {
      int S = jt->second[c][0], Si = jt->second[c][1];
      if (S < 0 || S > 65535 || Si < 0 || Si > 65535) return "WC entry out of range";
      if (mul44(S, Si) != ID44 || mul44(Si, S) != ID44) { snprintf(buf, sizeof buf, "WC[%d:%d]: S S^-1 != I", o, c); return buf; }
      if (mulBS(o, S) != o) { snprintf(buf, sizeof buf, "WC[%d:%d]: o S != o", o, c); return buf; }
      if (!cs.count(mulSC(Si, c))) { snprintf(buf, sizeof buf, "WC[%d:%d]: S^-1 c not in CORB[o]", o, c); return buf; }
    }
  }
  // invariance of T334 under the pair action, for every S in GL4(F2)
  auto sup = t334_support();
  std::vector<int> T0(9 * 12, 0);   // T0[x*12+y] = row over z
  for (auto& e : sup) T0[e[0] * 12 + e[1]] |= 1 << e[2];
  int ngl = 0;
  for (int S = 0; S < 65536; S++) {
    int Si = inv44(S); if (Si < 0) continue;
    ngl++;
    for (int x = 0; x < 9; x++) {
      int img[12] = {0};
      for (auto& e : sup) if (e[0] == x) {
        int b2 = mulBS(1 << e[1], S), c2 = mulSC(Si, 1 << e[2]);
        for (int y = 0; y < 12; y++) if ((b2 >> y) & 1) img[y] ^= c2;
      }
      for (int y = 0; y < 12; y++) if (img[y] != T0[x * 12 + y]) { snprintf(buf, sizeof buf, "T334 not invariant under S=%d", S); return buf; }
    }
  }
  if (ngl != 20160) return "GL4 enumeration did not give 20160 matrices";
  return "";
}

// Deep check (slow, for tests): recompute ORBM and CORB from scratch (orbits under the full GL4 / Stab(o)) and compare.
static inline std::string validate_deep(const SymTab& st) {
  std::vector<int> gl; for (int S = 0; S < 65536; S++) if (inv44(S) >= 0) gl.push_back(S);
  // orbit minima of b: BFS with the 12 transvections (they generate GL4)
  std::vector<int> trans;
  for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j) trans.push_back(ID44 ^ (1 << (4 * i + j)));
  std::vector<int> orbmin(4096, -1), orbm;
  for (int b0 = 1; b0 < 4096; b0++) {
    if (orbmin[b0] >= 0) continue;
    std::vector<int> q{b0}; orbmin[b0] = b0;
    for (size_t h = 0; h < q.size(); h++) for (int g : trans) { int y = mulBS(q[h], g); if (orbmin[y] < 0) { orbmin[y] = b0; q.push_back(y); } }
    orbm.push_back(b0);   // b0 is the smallest unvisited element of its orbit, hence its minimum
  }
  if (orbm != st.orbm) return "ORBM differs from the brute-force orbit minima";
  for (int o : orbm) {
    std::vector<int> stab; for (int S : gl) if (mulBS(o, S) == o) stab.push_back(S);
    auto its = st.stab.find(o); if (its == st.stab.end() || its->second != (int)stab.size()) return "STAB size differs";
    // Stab(o) is a group, so the orbit of c under c -> S^-1 c is {S c : S in Stab(o)}; the smallest unvisited c is its minimum
    std::vector<char> seen(4096, 0); std::vector<int> mins;
    for (int c0 = 1; c0 < 4096; c0++) {
      if (seen[c0]) continue;
      mins.push_back(c0);
      for (int S : stab) seen[mulSC(S, c0)] = 1;
    }
    if (mins != st.corb.at(o)) return "CORB differs from the brute-force orbit minima for o=" + std::to_string(o);
  }
  return "";
}

}  // namespace s334
