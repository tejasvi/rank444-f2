// mkipS9.cc: a C++ port of mkipS.py.  The output must be
// byte-identical to mkipS.py's.
// Coset-profile IP for <3,3,4> mod S, S = the representative of a G0-class of dimension dS >= 1, in the lineenum9vr format:
//   "R <L> N <ncos>", the coset labels (smallest 9-bit representative of each nonzero coset of A/S, in quotient-coordinate
//   order), one row "C <dim S''> <cap> <size> <labels>" per strict superspace S'' of S (cap = L - lb(class of S'')), rows
//   sorted by (dim, class, label list), then "G <|Stab(S)|>" and the induced label permutations (g in G0 index order).
// Checks (as mkipS.py): the number of distinct strict superspaces equals the number of nonzero subspaces of A/S, each gets
// one class, every row has 2^(d-dS)-1 labels, and every coset lies in the same number of rows.
// Table: seeded334.tsv (columns idx dim basis ... seeded at index 11).  Optional lb overrides (raised rows) with
// --raise CLASS=LB,CLASS=LB,... (mkipS.py has none; mkcand.py lowered caps afterwards; here only for later use).
// usage: mkipS9 TABLE.tsv CLASS L OUT_IP [--raise c=lb,...] [--maxgroup M]     exit 3 = MONOTONE (no IP written), as mkipS.py
// --maxgroup M: if |Stab(S)| > M, list only the subgroup H that also fixes labels l1, l2, ...
// (the smallest label moved by the current H, repeatedly) until |H| <= M.  H is an intersection of stabilizers, hence a
// subgroup (closed, as lechk9vr requires), and every listed element is still induced by an element of Stab_G0(S).
// Without --maxgroup the output is unchanged (byte-identical to mkipS.py).
// --rowcls FILE (v2c, for the row-usage replay): also write the G0-class of every C row, one per line, in output order.
#include <bits/stdc++.h>
typedef unsigned long long u64;

static int det3(const int M[3][3]){
  return (M[0][0]*(M[1][1]*M[2][2]+M[1][2]*M[2][1]) + M[0][1]*(M[1][0]*M[2][2]+M[1][2]*M[2][0])
        + M[0][2]*(M[1][0]*M[2][1]+M[1][1]*M[2][0])) & 1; }
static int topbit(int v){ return 31-__builtin_clz(v); }

int main(int argc,char** argv){
  if(argc<5){ fprintf(stderr,"usage: mkipS9 TABLE.tsv CLASS L OUT_IP [--raise c=lb,...]\n"); return 2; }
  const char* tab=argv[1]; int cS=atoi(argv[2]); int L=atoi(argv[3]); const char* out=argv[4];
  std::map<int,int> raise; long maxgroup=0; std::string rowclsOut;
  for(int i=5;i<argc;i++){ std::string a=argv[i]; if(a=="--raise" && i+1<argc){ std::stringstream ss(argv[++i]); std::string t;
      while(std::getline(ss,t,',')){ auto e=t.find('='); if(e==std::string::npos){ fprintf(stderr,"bad --raise\n"); return 2; } raise[std::stoi(t.substr(0,e))]=std::stoi(t.substr(e+1)); } }
    else if(a=="--maxgroup" && i+1<argc){ maxgroup=atol(argv[++i]); if(maxgroup<1){ fprintf(stderr,"bad --maxgroup\n"); return 2; } }
    else if(a=="--rowcls" && i+1<argc){ rowclsOut=argv[++i]; }
    else { fprintf(stderr,"bad arg %s\n",a.c_str()); return 2; } }
  // ---- table
  std::vector<int> dims, seeded; std::vector<std::vector<int>> bases;
  { std::ifstream f(tab); if(!f){ fprintf(stderr,"cannot read %s\n",tab); return 2; } std::string line; std::getline(f,line);
    while(std::getline(f,line)){ if(line.empty()) continue; std::vector<std::string> c; std::stringstream ss(line); std::string t; while(std::getline(ss,t,'\t')) c.push_back(t);
      if(c.size()<12){ fprintf(stderr,"short table line\n"); return 2; } int idx=std::stoi(c[0]); if(idx!=(int)dims.size()){ fprintf(stderr,"table index order\n"); return 2; }
      dims.push_back(std::stoi(c[1])); std::vector<int> b; std::stringstream bs(c[2]); while(std::getline(bs,t,',')) if(!t.empty()) b.push_back(std::stoi(t));
      if((int)b.size()!=dims.back()){ fprintf(stderr,"basis size != dim at %d\n",idx); return 2; } bases.push_back(b); seeded.push_back(std::stoi(c[11])); } }
  int NC=dims.size(); if(cS<0||cS>=NC){ fprintf(stderr,"bad class\n"); return 2; }
  for(auto& kv:raise){ if(kv.first<0||kv.first>=NC){ fprintf(stderr,"bad raise class\n"); return 2; } seeded[kv.first]=kv.second; }
  int dS=dims[cS]; std::vector<int> Sb=bases[cS];
  std::vector<char> memS(512,0); { std::vector<int> sp={0}; for(int v:Sb){ int n=sp.size(); for(int i=0;i<n;i++) sp.push_back(sp[i]^v); } for(int x:sp) memS[x]=1; }
  // ---- G0 = GL3 x GL3 acting a -> P a Q, g = p*168+q, GL3 listed in increasing 'bits' order (common334.gl3_mats)
  std::vector<std::array<int,3>> GL;   // rows as 3-bit masks: row i bit j = M[i][j] = bit (3i+j) of 'bits'
  for(int bits=0;bits<512;bits++){ int M[3][3]; for(int k=0;k<9;k++) M[k/3][k%3]=(bits>>k)&1; if(det3(M)){ std::array<int,3> r; for(int i=0;i<3;i++) r[i]=(bits>>(3*i))&7; GL.push_back(r); } }
  if(GL.size()!=168){ fprintf(stderr,"GL3 size %zu\n",GL.size()); return 4; }
  const int G=168*168; std::vector<uint16_t> img((size_t)G*512);
  auto mulR=[&](const int* A,const int* B,int* C){ for(int i=0;i<3;i++){ int r=0; for(int k=0;k<3;k++) if((A[i]>>k)&1) r^=B[k]; C[i]=r; } };
  for(int p=0;p<168;p++) for(int v=0;v<512;v++){ int Mv[3]={v&7,(v>>3)&7,(v>>6)&7}, PM[3]; mulR(GL[p].data(),Mv,PM);
    for(int q=0;q<168;q++){ int R[3]; mulR(PM,GL[q].data(),R); img[(size_t)(p*168+q)*512+v]=(uint16_t)(R[0]|(R[1]<<3)|(R[2]<<6)); } }
  // ---- superspaces: every class rep of larger dimension moved by every g, kept when its span contains S (as mkipS.expand)
  struct Key { u64 lo, hi; bool operator==(const Key& o) const { return lo==o.lo && hi==o.hi; } };
  struct KH { size_t operator()(const Key& k) const { return (size_t)(k.lo*0x9E3779B97F4A7C15ULL ^ (k.hi+0x632BE59BD9B4E019ULL)); } };
  std::unordered_map<Key,int,KH> sup; long long nimg=0, incons=0; std::vector<int> rows(9);
  for(int c=0;c<NC;c++){ int d=dims[c]; if(d<=dS) continue;
    for(int g=0;g<G;g++){ const uint16_t* I=&img[(size_t)g*512]; for(int i=0;i<d;i++) rows[i]=I[bases[c][i]];
      int r=0; for(int bit=8;bit>=0;bit--){ int piv=-1; for(int i=r;i<d;i++) if((rows[i]>>bit)&1){ piv=i; break; } if(piv<0) continue;
        std::swap(rows[r],rows[piv]); for(int i=0;i<d;i++) if(i!=r && ((rows[i]>>bit)&1)) rows[i]^=rows[r]; r++; }
      bool ok=true; for(int j=0;j<dS && ok;j++){ int v=Sb[j]; for(int i=0;i<d;i++){ int p=topbit(rows[i]); if((v>>p)&1) v^=rows[i]; } if(v) ok=false; }
      if(!ok) continue; nimg++;
      Key k{0,0}; for(int i=0;i<d;i++){ int sh=9*i; u64 v=(u64)rows[i]; if(sh+9<=64) k.lo|=v<<sh; else if(sh>=64) k.hi|=v<<(sh-64); else { k.lo|=v<<sh; k.hi|=v>>(64-sh); } }
      auto it=sup.find(k); if(it==sup.end()) sup[k]=c; else if(it->second!=c) incons++; } }
  int cod=9-dS; auto gauss=[](int n,int k){ u64 num=1,den=1; for(int i=0;i<k;i++){ num*=((1ULL<<(n-i))-1); den*=((1ULL<<(i+1))-1); } return num/den; };
  u64 expect=0; for(int k=1;k<=cod;k++) expect+=gauss(cod,k);
  printf("class %d: dim %d, seeded lb %d; images %lld, distinct strict superspaces %zu (expected %llu), class inconsistencies %lld\n",cS,dS,seeded[cS],nimg,sup.size(),expect,incons);
  if(sup.size()!=expect || incons){ fprintf(stderr,"superspace check failed\n"); return 4; }
  // ---- quotient map (common334.quotient_map): reduced echelon basis of S, pivots = top bits; labels = compressed non-pivot bits
  std::vector<std::pair<int,int>> basis;
  for(int v0:Sb){ int v=v0; for(auto& pb:basis) if((v>>pb.first)&1) v^=pb.second; if(v){ int p=topbit(v); for(auto& pb:basis) if((pb.second>>p)&1) pb.second^=v; basis.push_back({p,v}); } }
  std::vector<int> comp; { std::set<int> piv; for(auto& pb:basis) piv.insert(pb.first); for(int x=0;x<9;x++) if(!piv.count(x)) comp.push_back(x); }
  int D=comp.size(); auto Lq=[&](int a){ for(auto& pb:basis) if((a>>pb.first)&1) a^=pb.second; int r=0; for(int i=0;i<D;i++) if((a>>comp[i])&1) r|=1<<i; return r; };
  std::vector<int> LS(512); for(int v=0;v<512;v++) LS[v]=Lq(v);
  int ncos=(1<<D)-1; std::vector<int> rep(ncos+1,0); for(int v=511;v>=1;v--) if(LS[v]) rep[LS[v]]=v;
  for(int l=1;l<=ncos;l++) if(rep[l]<=0){ fprintf(stderr,"rep missing\n"); return 4; }
  // ---- rows
  struct RowS { int d, c; std::vector<int> mem; };
  std::vector<RowS> rs; rs.reserve(sup.size());
  for(auto& kv:sup){ int c=kv.second, d=dims[c]; std::vector<int> vec(d);
    for(int i=0;i<d;i++){ int sh=9*i; u64 v; if(sh+9<=64) v=(kv.first.lo>>sh)&511; else if(sh>=64) v=(kv.first.hi>>(sh-64))&511; else v=((kv.first.lo>>sh)|(kv.first.hi<<(64-sh)))&511; vec[i]=(int)v; }
    std::set<int> im={0}; for(int v:vec){ std::set<int> nx=im; for(int x:im) nx.insert(x^LS[v]); im.swap(nx); }
    std::vector<int> mem; for(int x:im) if(x) mem.push_back(x);
    if((int)mem.size()!=(1<<(d-dS))-1){ fprintf(stderr,"row size check failed\n"); return 4; }
    rs.push_back({d,c,mem}); }
  { std::vector<long long> cnt(ncos+1,0); for(auto& r:rs) for(int x:r.mem) cnt[x]++; for(int l=2;l<=ncos;l++) if(cnt[l]!=cnt[1]){ fprintf(stderr,"coset count check failed\n"); return 4; } }
  // ---- stabilizer and label permutations
  std::vector<int> stab; for(int g=0;g<G;g++){ bool ok=true; for(int v:Sb) if(!memS[img[(size_t)g*512+v]]){ ok=false; break; } if(ok) stab.push_back(g); }
  std::vector<std::vector<int>> perms; for(int g:stab){ std::vector<int> P(ncos); std::vector<char> hit(ncos,0);
    for(int l=0;l<ncos;l++){ int x=LS[img[(size_t)g*512+rep[l+1]]]-1; if(x<0||hit[x]){ fprintf(stderr,"perm check failed\n"); return 4; } hit[x]=1; P[l]=x; } perms.push_back(P); }
  // v2: list each distinct label permutation once (first g in index order).  Elements of Stab(S) that act alike on A/S give
  // the same permutation; mkipS.py listed all of them, and lechk9vr rejects repeated elements.  The image of a group is a
  // group, so the deduplicated list is closed.  (No regression class has repeats, so their output is unchanged.)
  size_t gElems=perms.size();
  { std::set<std::vector<int>> seen; std::vector<std::vector<int>> p2; std::vector<int> s2;
    for(size_t i=0;i<perms.size();i++) if(seen.insert(perms[i]).second){ p2.push_back(perms[i]); s2.push_back(stab[i]); }
    perms.swap(p2); stab.swap(s2); }
  size_t fullStab=perms.size(); std::vector<int> fixedLabels;
  if(maxgroup>0 && (long)perms.size()>maxgroup){   // subgroup by successive label stabilizers (see header)
    std::vector<int> H(perms.size()); std::iota(H.begin(),H.end(),0);
    while((long)H.size()>maxgroup){ int lab=-1; for(int l=0;l<ncos && lab<0;l++) for(int h:H) if(perms[h][l]!=l){ lab=l; break; }
      if(lab<0) break; std::vector<int> H2; for(int h:H) if(perms[h][lab]==lab) H2.push_back(h); H.swap(H2); fixedLabels.push_back(lab); }
    std::vector<std::vector<int>> p2; std::vector<int> s2; for(int h:H){ p2.push_back(perms[h]); s2.push_back(stab[h]); } perms.swap(p2); stab.swap(s2); }
  std::sort(rs.begin(),rs.end(),[](const RowS& a,const RowS& b){ if(a.d!=b.d) return a.d<b.d; if(a.c!=b.c) return a.c<b.c; return a.mem<b.mem; });
  int mincap=INT_MAX; for(auto& r:rs) mincap=std::min(mincap,L-seeded[r.c]);
  if(mincap<0){ printf("MONOTONE: a strict superspace has lb %d > L = %d, so R(T mod S) > L already (no IP written)\n",L-mincap,L); return 3; }
  FILE* f=fopen(out,"w"); if(!f){ fprintf(stderr,"cannot write %s\n",out); return 2; }
  fprintf(f,"R %d N %d\n",L,ncos); for(int l=1;l<=ncos;l++) fprintf(f,"%d%s",rep[l],l==ncos?"\n":" ");
  for(auto& r:rs){ fprintf(f,"C %d %d %zu",r.d,L-seeded[r.c],r.mem.size()); for(int x:r.mem) fprintf(f," %d",x-1); fprintf(f,"\n"); }
  fprintf(f,"G %zu\n",stab.size()); for(auto& P:perms){ for(int l=0;l<ncos;l++) fprintf(f,"%d%s",P[l],l+1==ncos?"\n":" "); }
  fclose(f);
  if(!rowclsOut.empty()){ FILE* g=fopen(rowclsOut.c_str(),"w"); if(!g){ fprintf(stderr,"cannot write %s\n",rowclsOut.c_str()); return 2; }
    for(auto& r:rs) fprintf(g,"%d\n",r.c); fclose(g); }
  std::vector<int> single; for(auto& r:rs) if(r.mem.size()==1) single.push_back(L-seeded[r.c]);
  int smin=*std::min_element(single.begin(),single.end()), smax=*std::max_element(single.begin(),single.end());
  printf("class %d (dim %d, lb %d) at L=%d: %d cosets, %zu rows, |Stab|=%zu",cS,dS,seeded[cS],L,ncos,rs.size(),gElems);
  if(fullStab!=gElems) printf(" (%zu distinct label actions)",fullStab);
  if(fullStab!=stab.size()){ printf(" (listed subgroup %zu, fixing labels",stab.size()); for(int l:fixedLabels) printf(" %d",l); printf(")"); }
  printf("; label caps min %d max %d\nwrote %s\n",smin,smax,out);
  return 0; }
