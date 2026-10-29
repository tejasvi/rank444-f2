// tsolve334: the exact completion search of the 3x3 project (cpp/tsolve/tsolve4.cc of rank333-f2, Apache-2.0,
// doi:10.5281/zenodo.23236154) generalized to <n,m,p> with runtime sizes: B = m x p (bit y = j*p+k), C = p x n (bit z = k*n+i),
// A = n x m (bit x = i*m+j; quotient targets use the first D coordinates).  Changes from tsolve4: rows of Res are NC-bit
// masks (NC = p*n <= 16) instead of 9-bit; the first-branching symmetry is b -> b S, c -> S^-1 c for S in GL_p (GL4 for
// <3,3,4>) instead of GL3; the group key is (b << NC) | c; a wall-clock limit (--timelimit s, result ABORT) was added.
// Everything else (residual-rank pruning over all functionals X of the first-factor space, tight and slack-1 candidate
// generation, symmetry breaking among equal first factors) follows tsolve4.
// Usage: tsolve334 [--nmp n m p] [--maxnodes N] [--timelimit s] [--target tensorfile] file
//   (default n m p = 3 3 4 and target <3,3,4>; target file lines "x y z"; instance lines "v1 .. vR" or "tag: v1 .. vR")
#include <bits/stdc++.h>
typedef uint8_t u8; typedef uint16_t u16; typedef uint32_t u32; typedef uint64_t u64;
static int Nn=3, Mm=3, Pp=4, NA=9, NB=12, NC=12;
static int R; static int A[64]; static int XL=512, XLT=512;
static int GRP[64], GSZ[64];
static u16 TX[512][16];          // T(X), rows y (bits z)
static u16 TXT[512][16];         // transpose, rows z (bits y)
static std::vector<int> XS[64];
static int rankN(const u16* m,int nr){ u16 bas[16]={0}; int rk=0; for(int i=0;i<nr;i++){ u16 v=m[i]; while(v){ int h=31-__builtin_clz(v); if(!bas[h]){ bas[h]=v; rk++; break; } v^=bas[h]; } } return rk; }
static unsigned char Tt[16][16][16];
static std::vector<char> orbitMin; static bool USESYM=true; static bool NOSYM=false;
static std::vector<std::array<int,4>> glp; // GL_p matrices as rows (p bits each)
static int mulB(int b,const int* S){ int r=0; for(int j=0;j<Mm;j++){ int row=(b>>(Pp*j))&((1<<Pp)-1); int o=0; for(int k=0;k<Pp;k++) if((row>>k)&1) o^=S[k]; r|=o<<(Pp*j); } return r; }
static double TLIM=1e30; static std::chrono::steady_clock::time_point TSTART;

struct Info { int rk; int u; u16 cb[16]; u16 cc[16]; int ncb; u16 rker[16]; int nrk; u16 lker[16]; int nlk; };

struct Solver {
  u16 Res[512][16], ResT[512][16]; int u[512]; u32 assigned=0; int B[64], C[64];
  long long nodes=0, maxnodes=LLONG_MAX; bool aborted=false, found=false; int nsol=0;
  Info inf[512];
  void init(){ for(int X=1;X<XL;X++){ memcpy(Res[X],TX[X],sizeof(u16)*NB); memcpy(ResT[X],TXT[X],sizeof(u16)*NC); u[X]=0; } for(int l=0;l<R;l++) for(int X:XS[l]) u[X]++; assigned=0; nodes=0; aborted=false; found=false; }
  inline void apply(int l,int b,int c){ for(int X:XS[l]){ for(int y=0;y<NB;y++) if((b>>y)&1) Res[X][y]^=c; for(int z=0;z<NC;z++) if((c>>z)&1) ResT[X][z]^=b; u[X]--; } }
  inline void unapply(int l,int b,int c){ for(int X:XS[l]){ for(int y=0;y<NB;y++) if((b>>y)&1) Res[X][y]^=c; for(int z=0;z<NC;z++) if((c>>z)&1) ResT[X][z]^=b; u[X]++; } }
  bool checkAfter(int l){ for(int X:XS[l]){ if(rankN(Res[X],NB)>u[X]) return false; } return true; }
  void computeInfo(int X){ Info& I=inf[X]; I.u=u[X];
    u16 v[16], cmb[16]; for(int z=0;z<NC;z++){ v[z]=ResT[X][z]; cmb[z]=1<<z; }
    int rk=0; I.ncb=0; I.nrk=0; u16 bv[16]={0}, bc[16]={0};
    for(int z=0;z<NC;z++){ u16 a=v[z], k=cmb[z]; while(a){ int h=31-__builtin_clz(a); if(!bv[h]){ bv[h]=a; bc[h]=k; rk++; break; } a^=bv[h]; k^=bc[h]; } if(!a) I.rker[I.nrk++]=k; }
    I.rk=rk; for(int h=15;h>=0;h--) if(bv[h]){ I.cb[I.ncb]=bv[h]; I.cc[I.ncb]=bc[h]; I.ncb++; }
    u16 lv[16]={0}, lc[16]={0}; I.nlk=0;
    for(int y=0;y<NB;y++){ u16 a=Res[X][y], k=1<<y; while(a){ int h=31-__builtin_clz(a); if(!lv[h]){ lv[h]=a; lc[h]=k; break; } a^=lv[h]; k^=lc[h]; } if(!a) I.lker[I.nlk++]=k; } }
  bool inCol(const Info& I,int b,int& x){ u16 a=b; x=0; for(int i=0;i<I.ncb;i++){ int h=31-__builtin_clz(I.cb[i]); if((a>>h)&1){ a^=I.cb[i]; x^=I.cc[i]; } } return a==0; }
  struct Sys { u16 m[16]; u8 r[16]; bool bad; int n; void clear(int nn){ memset(m,0,sizeof m); memset(r,0,sizeof r); bad=false; n=nn; }
    void add(u16 mask,int rhs){ if(bad) return; while(mask){ int h=31-__builtin_clz(mask); if(!m[h]){ m[h]=mask; r[h]=(u8)rhs; return; } mask^=m[h]; rhs^=r[h]; } if(rhs) bad=true; }
    int rank() const { int k=0; for(int h=0;h<n;h++) if(m[h]) k++; return k; }
    void solutions(std::vector<int>& out) const { out.clear(); if(bad) return; int fr[16], nf=0; for(int h=0;h<n;h++) if(!m[h]) fr[nf++]=h;
      for(int s=0;s<(1<<nf);s++){ int c=0; for(int i=0;i<nf;i++) if((s>>i)&1) c|=1<<fr[i];
        for(int h=0;h<n;h++) if(m[h]){ int val=r[h]^__builtin_parity(m[h]&c&((1<<h)-1)); if(val) c|=1<<h; }
        out.push_back(c); } } };
  long long candidates(int l,std::vector<std::pair<int,int>>* out,long long cap,bool symFirst){
    std::vector<int> tight, s1; for(int X:XS[l]){ int s=inf[X].u-inf[X].rk; if(s==0) tight.push_back(X); else if(s==1) s1.push_back(X); }
    Sys bs; bs.clear(NB); for(int X:tight){ const Info& I=inf[X]; for(int i=0;i<I.nlk;i++) bs.add(I.lker[i],0); }
    Sys base; base.clear(NC); for(int X:tight){ const Info& I=inf[X]; for(int i=0;i<I.nrk;i++) base.add(I.rker[i],0); }
    std::vector<int> bl; bs.solutions(bl); long long tot=0; std::vector<int> cl;
    for(int b:bl){ if(!b) continue; if(symFirst && !orbitMin[b]) continue; Sys s=base; bool ok=true;
      for(int X:tight){ int x; if(!inCol(inf[X],b,x)){ ok=false; break; } s.add(x,1); if(s.bad){ ok=false; break; } }
      if(!ok) continue;
      for(int X:s1){ int x; if(!inCol(inf[X],b,x)){ const Info& I=inf[X]; for(int i=0;i<I.nrk;i++) s.add(I.rker[i],0); if(s.bad) break; } }
      if(s.bad) continue;
      int nf=NC-s.rank(); long long cnt=(1LL<<nf);
      if(out){ s.solutions(cl); for(int c:cl) if(c) out->push_back({b,c}); }
      tot+=cnt; if(tot>cap) return tot; }
    return tot; }
  void dfs(int depth){
    if(aborted||found) return; if(++nodes>maxnodes){ aborted=true; return; }
    if((nodes&1023)==0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-TSTART).count()>TLIM){ aborted=true; return; }
    if(assigned==((R==32)?0xffffffffu:((1u<<R)-1))){ for(int X=1;X<XL;X++) for(int y=0;y<NB;y++) if(Res[X][y]) return; found=true; nsol++; return; }
    for(int X=1;X<XL;X++) if(u[X]>0) computeInfo(X); else { inf[X].u=0; inf[X].rk=0; }
    int best=-1; long long bc=LLONG_MAX; bool symNow=false;
    if(USESYM && depth==0){
      for(int l=0;l<R;l++) if(GSZ[GRP[l]]==1){ long long c=candidates(l,nullptr,bc,true); if(c<bc){ bc=c; best=l; symNow=true; if(c==0) break; } } }
    if(!symNow){ bc=LLONG_MAX; best=-1;
      for(int l=0;l<R;l++) if(!((assigned>>l)&1)){ long long c=candidates(l,nullptr,bc,false); if(c<bc){ bc=c; best=l; if(c==0) break; } } }
    if(best<0||bc==0) return;
    std::vector<std::pair<int,int>> cand; candidates(best,&cand,LLONG_MAX,symNow);
    int l=best; assigned|=1u<<l;
    for(auto& bc2:cand){ int b=bc2.first, c=bc2.second;
      if(GSZ[GRP[l]]>1){ long long key=((long long)b<<NC)|c; bool bad=false;
        for(int l2=0;l2<R && !bad;l2++) if(l2!=l && GRP[l2]==GRP[l] && ((assigned>>l2)&1)){ long long k2=((long long)B[l2]<<NC)|C[l2]; if((l2<l && key<k2) || (l2>l && key>k2)) bad=true; }
        if(bad) continue; }
      apply(l,b,c);
      if(checkAfter(l)){ B[l]=b; C[l]=c; dfs(depth+1); }
      unapply(l,b,c); if(found||aborted) break; }
    assigned&=~(1u<<l); }
};

int main(int argc,char** argv){
  long long maxnodes=LLONG_MAX; const char* fn=nullptr; const char* tfile=nullptr;
  for(int i=1;i<argc;i++){ std::string a=argv[i]; if(a=="--maxnodes") maxnodes=atoll(argv[++i]); else if(a=="--timelimit") TLIM=atof(argv[++i]);
    else if(a=="--target"){ tfile=argv[++i]; } else if(a=="--nosym"){ USESYM=false; NOSYM=true; }
    else if(a=="--nmp"){ Nn=atoi(argv[++i]); Mm=atoi(argv[++i]); Pp=atoi(argv[++i]); } else fn=argv[i]; }
  if(!fn){ fprintf(stderr,"usage: tsolve334 [--nmp n m p] [--maxnodes N] [--timelimit s] [--target file] file\n"); return 1; }
  NA=Nn*Mm; NB=Mm*Pp; NC=Pp*Nn; if(NA>9||NB>16||NC>16||Pp>4){ fprintf(stderr,"sizes\n"); return 1; }
  memset(Tt,0,sizeof Tt);
  if(tfile){ FILE* f=fopen(tfile,"r"); int x,y,z; while(fscanf(f,"%d %d %d",&x,&y,&z)==3) Tt[x][y][z]^=1; fclose(f); }
  else for(int i=0;i<Nn;i++) for(int j=0;j<Mm;j++) for(int k=0;k<Pp;k++) Tt[i*Mm+j][j*Pp+k][k*Nn+i]=1;
  { int mx=0; for(int x=0;x<NA;x++) for(int y=0;y<NB;y++) for(int z=0;z<NC;z++) if(Tt[x][y][z]) mx=std::max(mx,x); XLT=1<<(mx+1); }
  for(int X=1;X<(1<<NA);X++){ for(int y=0;y<NB;y++){ int row=0; for(int z=0;z<NC;z++){ int v=0; for(int x=0;x<NA;x++) if((X>>x)&1) v^=Tt[x][y][z]; row|=v<<z; } TX[X][y]=row; }
    for(int z=0;z<NC;z++){ int row=0; for(int y=0;y<NB;y++) if((TX[X][y]>>z)&1) row|=1<<y; TXT[X][z]=row; } }
  { // GL_p
    int lim=1<<Pp; std::vector<int> rr(Pp);
    std::function<void(int)> rec=[&](int d){ if(d==Pp){ u16 bas[4]={0}; int rk=0; for(int i=0;i<Pp;i++){ int v=rr[i]; while(v){ int h=31-__builtin_clz(v); if(!bas[h]){ bas[h]=v; rk++; break; } v^=bas[h]; } }
        if(rk==Pp){ std::array<int,4> S={0,0,0,0}; for(int i=0;i<Pp;i++) S[i]=rr[i]; glp.push_back(S); } return; }
      for(int v=1;v<lim;v++){ rr[d]=v; rec(d+1); } };
    rec(0);
    orbitMin.assign(1<<NB,0);
    for(int b=0;b<(1<<NB);b++){ bool mn=true; for(size_t s=0;s<glp.size()&&mn;s++) if(mulB(b,glp[s].data())<b) mn=false; orbitMin[b]=mn; } }
  if(!NOSYM){ // the target must be invariant under (y,z) -> (y S, S^-1 z) for every S in GL_p
    bool inv=true;
    for(size_t si=0;si<glp.size() && inv;si++){ const int* S=glp[si].data();
      // inverse of S by Gauss-Jordan over F2 (row r of S*Si = e_r with the row convention of mulB: row*M = xor of M rows)
      int Si[4]={0,0,0,0}; { int a[4], e[4]; for(int r=0;r<Pp;r++){ a[r]=S[r]; e[r]=1<<r; }
        for(int col=0;col<Pp;col++){ int pv=-1; for(int r=col;r<Pp;r++) if((a[r]>>col)&1){ pv=r; break; } if(pv<0){ inv=false; break; }
          std::swap(a[col],a[pv]); std::swap(e[col],e[pv]); for(int r=0;r<Pp;r++) if(r!=col && ((a[r]>>col)&1)){ a[r]^=a[col]; e[r]^=e[col]; } }
        if(!inv) break;
        // now a = I and e = S^-1 in the row sense (rows of e combine rows of S into unit rows)
        for(int r=0;r<Pp;r++) Si[r]=e[r];
        // self-check: row r of (Si * S) = xor over k in Si[r] of S[k] must be e_r
        for(int r=0;r<Pp;r++){ int row=0; for(int k=0;k<Pp;k++) if((Si[r]>>k)&1) row^=S[k]; if(row!=(1<<r)){ fprintf(stderr,"inverse error\n"); exit(4); } } }
      auto mulC=[&](int c){ int r=0; for(int rr2=0;rr2<Pp;rr2++){ int o=0; for(int k=0;k<Pp;k++) if((Si[rr2]>>k)&1) o^=(c>>(Nn*k))&((1<<Nn)-1); r|=o<<(Nn*rr2); } return r; };
      for(int x=0;x<NA && inv;x++){ static int img[16][16]; for(int a=0;a<16;a++) for(int b2=0;b2<16;b2++) img[a][b2]=0;
        for(int y=0;y<NB;y++) for(int z=0;z<NC;z++) if(Tt[x][y][z]){ int by=mulB(1<<y,S), cz=mulC(1<<z);
          for(int y2=0;y2<NB;y2++) if((by>>y2)&1) for(int z2=0;z2<NC;z2++) if((cz>>z2)&1) img[y2][z2]^=1; }
        for(int y=0;y<NB;y++) for(int z=0;z<NC;z++) if(img[y][z]!=Tt[x][y][z]) inv=false; } }
    USESYM=inv; fprintf(stderr,"GL%d (%zu elements): target %s under b->bS, c->S^-1 c; first-branching symmetry %s\n",Pp,glp.size(),inv?"invariant":"NOT invariant",inv?"on":"off"); }
  std::ifstream in(fn); std::string line;
  while(std::getline(in,line)){ std::string tag; auto p=line.find(':'); std::string body=line; if(p!=std::string::npos){ tag=line.substr(0,p); body=line.substr(p+1); }
    std::stringstream ss(body); std::vector<int> v; int x; while(ss>>x) v.push_back(x); if(v.empty()) continue;
    R=v.size(); if(R>32){ fprintf(stderr,"R too big\n"); return 3; } { int orA=0; for(int a:v) orA|=a; XL=XLT; while(XL<(1<<NA) && (orA>>__builtin_ctz(XL))) XL<<=1; }
    for(int l=0;l<R;l++){ GRP[l]=l; for(int l2=0;l2<l;l2++) if(v[l2]==v[l]){ GRP[l]=GRP[l2]; break; } } for(int l=0;l<R;l++) GSZ[l]=0; for(int l=0;l<R;l++) GSZ[GRP[l]]++;
    for(int l=0;l<R;l++){ A[l]=v[l]; XS[l].clear(); for(int X=1;X<XL;X++) if(__builtin_parity(A[l]&X)) XS[l].push_back(X); }
    Solver* S=new Solver(); S->init(); S->maxnodes=maxnodes; bool pre=true; for(int X=1;X<XL;X++) if(rankN(TX[X],NB)>S->u[X]) pre=false;
    TSTART=std::chrono::steady_clock::now(); if(pre) S->dfs(0); double dt=std::chrono::duration<double>(std::chrono::steady_clock::now()-TSTART).count();
    const char* res= S->found?"SAT":(S->aborted?"ABORT":"UNSAT");
    printf("%s %s| nodes %lld time %.4fs%s", res, line.c_str(), S->nodes, dt, pre?"":" (hyperplane fail)");
    if(S->found){ bool ok=true; for(int x=0;x<NA;x++) for(int y=0;y<NB;y++) for(int z=0;z<NC;z++){ int s=0; for(int l=0;l<R;l++) s^=((A[l]>>x)&1)&((S->B[l]>>y)&1)&((S->C[l]>>z)&1); if(s!=Tt[x][y][z]) ok=false; }
      printf(" | verified %d | B", (int)ok); for(int l=0;l<R;l++) printf(" %d",S->B[l]); printf(" C"); for(int l=0;l<R;l++) printf(" %d",S->C[l]); }
    printf("\n"); fflush(stdout); delete S; }
  return 0; }
