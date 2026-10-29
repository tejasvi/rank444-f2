// lechk9m8: lechk9m4 with label bounds up to 8 (for lineenum9m8).
// lechk9m4: lechk9vr with label bounds up to 4 (for lineenum9m4); the residual counts u[l] were already general.
// lechk: independent checker of the proof traces written by lineenum3 --cert.  Shares no code with lineenum.
//
// The IP (profS --dumpip format): "R r N n", the n label vectors, rows "C k cap m l1..lm" (m = 1 bounds one label's
// multiplicity, m >= 2 is a capped row; rows are numbered in file order), then "G g" and g permutations of the labels.
// A solution is a multiset of R labels, each label at most its bound times, with at most cap labels in every row.
//
// Checked from the IP alone:
//  1. G is a group of label permutations that preserves the bounds and maps every row to a row with cap <= its cap,
//     so G maps solutions to solutions; the lex-min sorted label sequence of an orbit is then canonical (no g makes
//     it lex-smaller) and every prefix of a canonical sequence is canonical.
//  2. Every block of every trace replays: starting from the block's prefix, each node record is justified
//       K  an exact weak-duality bound (integer dual, scale 2^30) shows fewer than R-d labels >= pos fit,
//       O  its fixings follow from its dual, its cut is certified (row bound, total weight or an LP-forced label),
//          and every allowed child label in [pos,cut) is either present (C record) or provably non-canonical,
//       P  after adding the child label l, a row bound or the total weight shows the remaining slots cannot be
//          filled with labels >= l,
//       L  at depth R (the leaf is re-checked against every row), F exactly at the block's frontier depth.
//     Label upper bounds u(l) follow the enumerator's (valid, conservative) rules: u = bound - multiplicity, 0 once
//     a row containing l is full, lowered by LP fixing for the subtree of the fixing node.
//  3. Coverage: the root block's frontier nodes are covered recursively (J block = complete subtree, T block =
//     subtree down to its own frontier).  Hence every canonical solution is a leaf of a covering block.
//  4. Those leaves are all in the given solution files (--sols).
// Usage: lechk IP --order ORD [--threads T] [--sols f1,f2,..] [--leaves-out F] [--cover v1,..,vk] trace1.bin [trace2.bin ...]
// (--cover: check the subtree of that label prefix (vec values) instead of the whole tree.)
// lechk2: --covers FILE checks the subtrees of all prefixes listed in FILE (one per line, comma-separated vec values);
// coverage is COMPLETE when every one of them is covered.  Everything else is lechk.
#include <bits/stdc++.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
typedef unsigned long long u64; typedef __int128 i128;
// lechk9vr: lechk2 widened for point quotients of <3,3,4>: up to 256 labels (4-word masks), any number
// of rows, and row ids read as varints in duals, cut rows and lookahead rows (the trace format of lineenum9vr, magic 'LEB9').
// The checking logic is lechk2's, unchanged.
static int R, N; static std::vector<int> vec; static int ub[256];
struct Row { u64 m[4]; int cap; std::vector<int> labs; };
struct K4 { u64 a,b,c,d; bool operator==(const K4& o) const { return a==o.a&&b==o.b&&c==o.c&&d==o.d; } };
struct K4H { size_t operator()(const K4& k) const { u64 h=k.a*0x9E3779B97F4A7C15ULL; h^=k.b+0x632BE59BD9B4E019ULL+(h<<6)+(h>>2); h^=k.c+0x8CB92BA72F3D8DD7ULL+(h<<6)+(h>>2); h^=k.d+0x52DCE729DA3ED7E5ULL+(h<<6)+(h>>2); return (size_t)h; } };
static std::vector<Row> rows; static std::vector<std::vector<int>> incl; static std::vector<std::vector<int>> G;
static const long long SC = 1LL << 30;
static std::map<int,int> labOfVec; static bool SKIPROWMAP=false;

struct Blk { const uint8_t* p; size_t n; std::string src; };
struct Res { bool ok=false; std::string err; char type=0; std::vector<int> pre; int fd=-1; std::vector<std::vector<int>> F, leaves; long long nodes=0; };

struct Chk {
  const uint8_t* p; const uint8_t* e; std::string err;
  int d=0; int seq[64]; int mult[256]; uint8_t u[256]; uint8_t usave[64][256]; std::vector<int> cnt;
  bool isT=false; int fd=-1; Res* out=nullptr; long long nodes=0;
  Chk(){ cnt.assign(rows.size(),0); }
  void reset(){ d=0; for(int l=0;l<N;l++){ mult[l]=0; u[l]=(uint8_t)ub[l]; } std::fill(cnt.begin(),cnt.end(),0); }
  bool fail(const std::string& s){ if(err.empty()) err=s; return false; }
  bool need(size_t k){ return (size_t)(e-p)>=k; }
  int g8(){ if(!need(1)){ fail("truncated"); return -1; } return *p++; }
  int g16(){ if(!need(2)){ fail("truncated"); return -1; } int x=p[0]|(p[1]<<8); p+=2; return x; }
  bool gv(u64& x){ x=0; int sh=0; while(true){ if(!need(1)) return fail("truncated varint"); int b=*p++; if(sh>=63 && (b>1)) return fail("varint overflow"); x|=(u64)(b&127)<<sh; if(!(b&128)) return true; sh+=7; } }
  bool dual(std::vector<int>& rs,std::vector<u64>& Y){ u64 n; if(!gv(n)) return false; if(n>rows.size()) return fail("dual too long"); rs.resize(n); Y.resize(n);
    for(u64 i=0;i<n;i++){ u64 rr; if(!gv(rr)) return false; if(rr>=rows.size()) return fail("bad row id"); rs[i]=(int)rr; if(!gv(Y[i])) return false; if(Y[i]>(1ULL<<50)) return fail("dual entry too large"); } return true; }
  void add(int l){ memcpy(usave[d],u,N); mult[l]++; seq[d++]=l; int res=ub[l]-mult[l]; if(res<0) res=0; if(u[l]>res) u[l]=(uint8_t)res;
    for(int r:incl[l]) if(++cnt[r]==rows[r].cap) for(int x:rows[r].labs) u[x]=0; }
  void undo(int l){ for(int r:incl[l]) cnt[r]--; mult[l]--; d--; memcpy(u,usave[d],N); }
  // weak-duality value (times SC) of the integer dual over the labels >= pos with u >= 1; T receives sum of Y over rows containing l
  i128 bound(int pos,const std::vector<int>& rs,const std::vector<u64>& Y,i128* T){
    for(int l=0;l<N;l++) T[l]=0; i128 B=0;
    for(size_t i=0;i<rs.size();i++){ const Row& w=rows[rs[i]]; B+=(i128)Y[i]*(w.cap-cnt[rs[i]]); for(int l:w.labs) if(l>=pos && u[l]>=1) T[l]+=Y[i]; }
    for(int l=pos;l<N;l++) if(u[l]>=1 && T[l]<SC) B+=(i128)u[l]*(SC-T[l]);
    return B; }
  long long wt(int from,int row){ long long W=0; for(int l=from;l<N;l++){ if(row>=0 && ((rows[row].m[l>>6]>>(l&63))&1)) continue; W+=u[l]; } return W; }
  // lookahead certificate at the current state: no completion of R-d labels all >= from
  bool look(int from,int kind,int row){ int rem=R-d;
    if(kind==2) return wt(from,-1)<rem;
    if(kind==1){ int needo=rem-(rows[row].cap-cnt[row]); return wt(from,row)<needo; }
    return false; }
  // is seq+[l] non-canonical (some g gives a lex-smaller sorted image)?
  bool nonCanon(int l){ int s[64]; for(int i=0;i<d;i++) s[i]=seq[i]; s[d]=l; int k=d+1; int im[64];
    for(size_t g=0;g<G.size();g++){ const int* P=G[g].data(); int mn=1<<30; for(int i=0;i<k;i++){ im[i]=P[s[i]]; if(im[i]<mn) mn=im[i]; }
      if(mn>s[0]) continue; if(mn<s[0]) return true; std::sort(im,im+k);
      for(int i=0;i<k;i++){ if(im[i]<s[i]) return true; if(im[i]>s[i]) break; } }
    return false; }
  bool leafOK(){ if(d!=R) return false; for(int l=0;l<N;l++) if(mult[l]>ub[l]) return false; for(size_t r=0;r<rows.size();r++) if(cnt[r]>rows[r].cap) return false; return true; }
  bool node(int pos){
    nodes++; int t=g8(); if(t<0) return false;
    if(d==R){ if(t!='L') return fail("depth R without L"); if(!leafOK()) return fail("leaf violates a row or bound"); out->leaves.push_back(std::vector<int>(seq,seq+d)); return true; }
    if(isT && d==fd){ if(t!='F') return fail("frontier depth without F"); out->F.push_back(std::vector<int>(seq,seq+d)); return true; }
    int rem=R-d; std::vector<int> rs; std::vector<u64> Y; i128 T[256];
    if(t=='K'){ if(!dual(rs,Y)) return false; if(!(bound(pos,rs,Y,T)<(i128)rem*SC)) return fail("K: bound not below the remaining slots"); return true; }
    if(t!='O') return fail(std::string("unexpected record ")+(char)t+" at depth "+std::to_string(d));
    int cut=g8(), kind=g8(); if(cut<0||kind<0) return false; int krow=-1; if(kind==1){ u64 kr; if(!gv(kr)) return false; if(kr>=rows.size()) return fail("bad cut row"); krow=(int)kr; }
    int hd=g8(); if(hd<0) return false; uint8_t keep[256]; memcpy(keep,u,N); int lreq=N;
    if(hd){ if(!dual(rs,Y)) return false; i128 B=bound(pos,rs,Y,T); i128 gap=B-(i128)rem*SC; if(gap<0) return fail("O: dual already kills the node");
      int u0[256]; for(int l=0;l<N;l++) u0[l]=u[l];
      for(int l=pos;l<N;l++){ if(u0[l]<1) continue;
        if(T[l]>SC){ i128 km=gap/(T[l]-SC); if(km<u0[l]) u[l]=(uint8_t)km; }          // x_l (T_l-1) <= gap
        else if(T[l]<SC){ i128 kmin=(i128)u0[l]-gap/(SC-T[l]); if(kmin>=1 && l<lreq) lreq=l; } } } // (u_l-x_l)(1-T_l) <= gap
    if(cut<pos || cut>N) return fail("cut out of range");
    if(kind==0){ if(cut!=N) return fail("kind 0 with cut < N"); }
    else if(kind==1||kind==2){ if(!look(cut,kind,krow)) return fail("O: cut certificate fails"); }
    else if(kind==3){ if(!hd || lreq>=N || cut!=lreq+1) return fail("O: forced-label cut not certified"); }
    else return fail("bad cut kind");
    for(int l=pos;l<cut;l++){ if(u[l]<1) continue;
      if(need(2) && p[0]=='C' && p[1]==l){ p+=2; add(l); bool ok;
        if(need(1) && p[0]=='P'){ p++; int k=g8(); int r=-1; if(k==1){ u64 rr; if(!gv(rr)) return false; r=(rr>=rows.size())?-2:(int)rr; } ok=(k==1||k==2) && r!=-2 && (k!=1||r>=0) && look(l,k,r); if(!ok) fail("P: certificate fails"); nodes++; }
        else ok=node(l);
        undo(l); if(!ok) return false; }
      else if(!nonCanon(l)) return fail("missing child "+std::to_string(l)+" at depth "+std::to_string(d)); }
    if(g8()!='E') return fail("expected E at depth "+std::to_string(d));
    memcpy(u,keep,N); return true; }
  void run(const Blk& b,Res& r){ out=&r; err.clear(); p=b.p; e=b.p+b.n; reset(); nodes=0;
    int t=g8(); if(t!='T' && t!='J'){ r.err="bad block tag"; return; } r.type=(char)t; isT=(t=='T');
    int n=g8(); if(n<0||n>R){ r.err="bad prefix length"; return; }
    std::vector<int> pre(n); for(int i=0;i<n;i++){ int v=g16(); auto it=labOfVec.find(v); if(v<0||it==labOfVec.end()){ r.err="bad prefix vec"; return; } pre[i]=it->second; }
    fd=-1; if(isT){ fd=g8(); if(fd==255) fd=-1; else if(fd<=n){ r.err="frontier not below the prefix"; return; } }
    r.pre=pre; r.fd=fd;
    for(int i=0;i<n;i++){ if(i>0 && pre[i]<pre[i-1]){ r.err="prefix not sorted"; return; } if(u[pre[i]]<1){ r.err="prefix label not allowed"; return; } add(pre[i]); }
    bool ok=node(n?pre[n-1]:0);
    if(ok){ if(g8()!='Z') ok=fail("expected Z"); else { u64 nn; if(!gv(nn)) ok=false; else if(p!=e) ok=fail("trailing bytes in block"); } }
    r.nodes=nodes; r.ok=ok; if(!ok) r.err=err; }
};

int main(int argc,char** argv){
  if(argc<2){ fprintf(stderr,"usage: lechk IP --order ORD [--threads T] [--sols f1,f2] [--leaves-out F] traces...\n"); return 1; }
  const char* ipf=argv[1]; const char* ordf=nullptr; int TH=1; std::string solsArg; const char* leavesOut=nullptr; std::vector<std::string> files; std::string coverArg; const char* coversF=nullptr;
  for(int i=2;i<argc;i++){ std::string a=argv[i];
    if(a=="--order") ordf=argv[++i]; else if(a=="--threads") TH=atoi(argv[++i]); else if(a=="--sols") solsArg=argv[++i]; else if(a=="--leaves-out") leavesOut=argv[++i]; else if(a=="--covers") coversF=argv[++i]; else if(a=="--cover") coverArg=argv[++i];
    else if(a=="--skip-row-map-check") SKIPROWMAP=true;   // lechk9vr: only for repeat runs on an IP whose row-map check already passed
    else if(a.size()>2 && a[0]=='-' && a[1]=='-'){ fprintf(stderr,"bad arg %s\n",a.c_str()); return 1; } else files.push_back(a); }
  // ---- IP
  std::vector<int> vecF; std::vector<int> ubF; std::vector<std::pair<int,std::vector<int>>> rowF; std::vector<std::vector<int>> GF;
  { std::ifstream f(ipf); if(!f){ fprintf(stderr,"cannot read %s\n",ipf); return 1; } std::string t1,t2; f>>t1>>R>>t2>>N;
    if(t1!="R"||t2!="N"||N<1||N>256||R<1||R>60){ fprintf(stderr,"bad IP header\n"); return 1; }
    vecF.resize(N); for(int l=0;l<N;l++) f>>vecF[l]; ubF.assign(N,R); std::string line; std::getline(f,line);
    while(std::getline(f,line)){ std::istringstream ss(line); std::string t; if(!(ss>>t)) continue;
      if(t=="C"){ int k,cap,m; ss>>k>>cap>>m; std::vector<int> ls(m); for(int j=0;j<m;j++){ ss>>ls[j]; if(ls[j]<0||ls[j]>=N){ fprintf(stderr,"bad label in row\n"); return 1; } }
        if(!ss){ fprintf(stderr,"bad row line\n"); return 1; }
        if(m==1){ ubF[ls[0]]=std::min(ubF[ls[0]],std::max(0,cap)); continue; } rowF.push_back({cap,ls}); }
      else if(t=="G"){ int ng; ss>>ng; for(int g=0;g<ng;g++){ std::vector<int> P(N); for(int l=0;l<N;l++) f>>P[l]; GF.push_back(P); } break; }
      else { fprintf(stderr,"unknown IP line %s\n",t.c_str()); return 1; } } }
  std::vector<int> ord(N); { if(!ordf){ for(int i=0;i<N;i++) ord[i]=i; } else { std::ifstream f(ordf); for(int i=0;i<N;i++) if(!(f>>ord[i])){ fprintf(stderr,"short order file\n"); return 1; } } }
  std::vector<int> inv(N,-1); for(int i=0;i<N;i++){ if(ord[i]<0||ord[i]>=N||inv[ord[i]]!=-1){ fprintf(stderr,"order is not a permutation\n"); return 1; } inv[ord[i]]=i; }
  vec.resize(N); for(int i=0;i<N;i++){ vec[i]=vecF[ord[i]]; ub[i]=ubF[ord[i]]; if(ub[i]>8){ fprintf(stderr,"bound > 8 (enumerator semantics need <= 8; lechk9m8)\n"); return 1; } labOfVec[vec[i]]=i; }
  if((int)labOfVec.size()!=N){ fprintf(stderr,"duplicate label vectors\n"); return 1; }
  if(rowF.size()>2000000000ULL){ fprintf(stderr,"too many rows\n"); return 1; }
  rows.resize(rowF.size()); incl.assign(N,{});
  for(size_t r=0;r<rowF.size();r++){ Row& w=rows[r]; w.cap=rowF[r].first; w.m[0]=w.m[1]=w.m[2]=w.m[3]=0; std::set<int> seen;
    for(int o:rowF[r].second){ int l=inv[o]; if(!seen.insert(l).second){ fprintf(stderr,"repeated label in row %zu\n",r); return 1; } w.labs.push_back(l); w.m[l>>6]|=1ULL<<(l&63); incl[l].push_back((int)r); }
    std::sort(w.labs.begin(),w.labs.end()); }
  for(auto& P:GF){ std::vector<int> Q(N); for(int i=0;i<N;i++){ int x=P[ord[i]]; if(x<0||x>=N){ fprintf(stderr,"bad group element\n"); return 1; } Q[i]=inv[x]; } G.push_back(Q); }
  // ---- group checks
  { std::set<std::vector<int>> GS(G.begin(),G.end()); if(GS.size()!=G.size()){ fprintf(stderr,"repeated group elements\n"); return 1; }
    std::vector<int> id(N); std::iota(id.begin(),id.end(),0); if(!GS.count(id)){ fprintf(stderr,"identity missing from G\n"); return 1; }
    for(auto& P:G){ std::vector<char> hit(N,0); for(int l=0;l<N;l++){ if(hit[P[l]]){ fprintf(stderr,"group element not a permutation\n"); return 1; } hit[P[l]]=1; if(ub[P[l]]!=ub[l]){ fprintf(stderr,"G does not preserve the bounds\n"); return 1; } } }
    std::vector<int> C(N); for(auto& P:G) for(auto& Q:G){ for(int l=0;l<N;l++) C[l]=P[Q[l]]; if(!GS.count(C)){ fprintf(stderr,"G not closed under composition\n"); return 1; } }
    std::unordered_map<K4,int,K4H> mincap; mincap.reserve(rows.size()*2); for(auto& w:rows){ K4 k{w.m[0],w.m[1],w.m[2],w.m[3]}; auto it=mincap.find(k); if(it==mincap.end()) mincap[k]=w.cap; else it->second=std::min(it->second,w.cap); }
    if(SKIPROWMAP) fprintf(stderr,"WARNING: row-map check of G skipped (--skip-row-map-check)\n");
    if(!SKIPROWMAP) for(auto& P:G) for(auto& w:rows){ u64 m[4]={0,0,0,0}; for(int l:w.labs){ int x=P[l]; m[x>>6]|=1ULL<<(x&63); } auto it=mincap.find(K4{m[0],m[1],m[2],m[3]}); if(it==mincap.end()||it->second>w.cap){ fprintf(stderr,"G does not map the rows to rows with cap <= cap\n"); return 1; } }
    fprintf(stderr,"IP: R %d N %d rows %zu, group %zu checked (closed, bounds and rows preserved)\n",R,N,rows.size(),G.size()); }
  // ---- traces
  std::vector<Blk> blks; long long bytes=0, trunc=0;
  for(auto& fn:files){ int fdsc=open(fn.c_str(),O_RDONLY); if(fdsc<0){ fprintf(stderr,"cannot open %s\n",fn.c_str()); return 1; } struct stat st; fstat(fdsc,&st); size_t sz=st.st_size; if(!sz){ close(fdsc); continue; }
    const uint8_t* m=(const uint8_t*)mmap(nullptr,sz,PROT_READ,MAP_PRIVATE,fdsc,0); close(fdsc); if(m==MAP_FAILED){ fprintf(stderr,"mmap failed %s\n",fn.c_str()); return 1; } bytes+=sz;
    size_t o=0; while(o<sz){ if(sz-o<12){ trunc++; break; } uint32_t mg; uint64_t len; memcpy(&mg,m+o,4); memcpy(&len,m+o+4,8);
      if(mg!=0x3942454C){ fprintf(stderr,"%s: bad block magic at %zu\n",fn.c_str(),o); return 1; } if(len>sz-o-12){ trunc++; break; } blks.push_back({m+o+12,(size_t)len,fn}); o+=12+len; } }
  fprintf(stderr,"traces: %zu files, %.3g bytes, %zu blocks (%lld truncated tails ignored)\n",files.size(),(double)bytes,blks.size(),trunc);
  std::vector<Res> res(blks.size()); std::atomic<size_t> nx{0}; std::atomic<long long> bad{0};
  auto wk=[&](){ Chk c; while(true){ size_t i=nx++; if(i>=blks.size()) break; c.run(blks[i],res[i]); if(!res[i].ok){ bad++; } } };
  { std::vector<std::thread> th; for(int t=0;t<TH;t++) th.emplace_back(wk); for(auto& t:th) t.join(); }
  long long nodes=0; for(auto& r:res) nodes+=r.nodes;
  long long shown=0; for(size_t i=0;i<res.size();i++) if(!res[i].ok && shown++<20){ fprintf(stderr,"BLOCK FAILED (%s, block %zu, prefix",blks[i].src.c_str(),i); for(int l:res[i].pre) fprintf(stderr," %d",vec[l]); fprintf(stderr,"): %s\n",res[i].err.c_str()); }
  fprintf(stderr,"blocks verified %lld of %zu, records %lld\n",(long long)(blks.size()-bad),blks.size(),nodes);
  // ---- coverage
  std::map<std::vector<int>,std::vector<size_t>> byPre; for(size_t i=0;i<res.size();i++) if(res[i].ok) byPre[res[i].pre].push_back(i);
  std::map<std::vector<int>,int> memo; std::set<size_t> used; long long missing=0; std::vector<std::vector<int>> missList;
  std::function<bool(const std::vector<int>&)> cov=[&](const std::vector<int>& P)->bool{
    auto m=memo.find(P); if(m!=memo.end()) return m->second==1; memo[P]=0;
    auto it=byPre.find(P); bool ok=false;
    if(it!=byPre.end()){ for(size_t i:it->second) if(res[i].F.empty()){ used.insert(i); ok=true; break; }
      if(!ok) for(size_t i:it->second){ bool all=true; for(auto& Q:res[i].F) if(!cov(Q)){ all=false; } if(all){ used.insert(i); ok=true; break; } } }
    if(!ok && it==byPre.end()){ missing++; if(missList.size()<20) missList.push_back(P); }
    memo[P]=ok?1:0; return ok; };
  std::vector<int> croot; if(!coverArg.empty()){ std::stringstream cs(coverArg); std::string t; while(std::getline(cs,t,',')){ auto it=labOfVec.find(std::stoi(t)); if(it==labOfVec.end()){ fprintf(stderr,"bad --cover vec %s\n",t.c_str()); return 1; } croot.push_back(it->second); } }
  bool covered;
  if(coversF){ std::ifstream cf(coversF); if(!cf){ fprintf(stderr,"cannot read %s\n",coversF); return 1; } std::string line; long long np=0, nok=0; covered=true;
    while(std::getline(cf,line)){ if(line.empty()) continue; std::vector<int> P; std::stringstream cs(line); std::string t;
      while(std::getline(cs,t,',')){ auto it=labOfVec.find(std::stoi(t)); if(it==labOfVec.end()){ fprintf(stderr,"bad --covers vec %s\n",t.c_str()); return 1; } P.push_back(it->second); }
      np++; if(cov(P)) nok++; else covered=false; }
    fprintf(stderr,"coverage roots: %lld prefixes from %s, %lld covered\n",np,coversF,nok); }
  else { covered=cov(croot);
    if(!croot.empty()) fprintf(stderr,"coverage root: prefix %s\n",coverArg.c_str()); }
  fprintf(stderr,"coverage: %s (blocks used %zu, prefixes without a verified block %lld)\n",covered?"COMPLETE":"INCOMPLETE",used.size(),missing);
  for(auto& P:missList){ fprintf(stderr,"  uncovered prefix:"); for(int l:P) fprintf(stderr," %d",vec[l]); fprintf(stderr,"\n"); }
  std::set<std::vector<int>> leaves; for(size_t i:used) for(auto& L:res[i].leaves){ std::vector<int> v; for(int l:L) v.push_back(vec[l]); std::sort(v.begin(),v.end()); leaves.insert(v); }
  std::set<std::vector<int>> allLeaves; for(auto& r:res) if(r.ok) for(auto& L:r.leaves){ std::vector<int> v; for(int l:L) v.push_back(vec[l]); std::sort(v.begin(),v.end()); allLeaves.insert(v); }
  fprintf(stderr,"leaves: %zu distinct in the covering blocks (%zu in all verified blocks)\n",leaves.size(),allLeaves.size());
  if(leavesOut){ FILE* f=fopen(leavesOut,"w"); for(auto& v:leaves){ for(size_t i=0;i<v.size();i++) fprintf(f,"%d%c",v[i],i+1==v.size()?'\n':' '); } fclose(f); }
  bool solsOK=true;
  if(!solsArg.empty()){ std::set<std::vector<int>> sols; std::stringstream ss(solsArg); std::string fn; long long lines=0;
    while(std::getline(ss,fn,',')){ std::ifstream f(fn); if(!f){ fprintf(stderr,"cannot read %s\n",fn.c_str()); return 1; } std::string line;
      while(std::getline(f,line)){ std::istringstream ls(line); std::vector<int> v; int x; while(ls>>x) v.push_back(x); if(v.empty()) continue; if((int)v.size()==R+1) v.erase(v.begin()); std::sort(v.begin(),v.end()); sols.insert(v); lines++; } }
    long long miss=0, extra=0; for(auto& v:leaves) if(!sols.count(v)){ miss++; if(miss<=5){ fprintf(stderr,"  leaf not in the solution files:"); for(int x:v) fprintf(stderr," %d",x); fprintf(stderr,"\n"); } }
    for(auto& v:sols) if(!allLeaves.count(v)) extra++;
    fprintf(stderr,"solution files: %lld lines, %zu distinct; covering leaves missing from them %lld; solutions not among verified leaves %lld\n",lines,sols.size(),miss,extra);
    solsOK=(miss==0); }
  bool pass=covered && bad==0 && solsOK;
  printf("RESULT %s\n",pass?"PASS":"FAIL"); return pass?0:3;
}
