// Derived from lineenum9x, a version of the profile search of the <3,3,3> project (released as cpp/enum/lineenum9qe.cc in
// rank333-f2, Apache-2.0, doi:10.5281/zenodo.23236154). Changed here: row ids in 'O' and 'P' records are varints (magic 'LEB9').
// lineenum9m8: lineenum9m4 with label caps up to 8 (masks r5..r8; derived by mk_m8.py).
// lineenum9m4: lineenum9vr with label caps up to 4 (a fourth residual mask r4; derived by mk_m4.py).
// lineenum9x: lineenum9w + work stealing inside frontier jobs (--donate D, default 0 = off), as lineenum7s: idle workers take
// donated subtrees (depth < D) once the job list is exhausted; a job's state line is written when its root and all pieces end.
// Disabled with --cert, --budget or frontier collection.  Same tree and leaves; only who runs which subtree changes.
// Exhaustive enumeration of the solutions of a line-lemma occupation IP dumped by profS --dumpip.
// A solution is a multiset of R labels (points of V = A/E) with m(U) <= cap(U) for every dumped subspace U.
// Search: labels in nondecreasing order; a label is "allowed" while its multiplicity is below its point cap and
// no saturated subspace contains it, so every cap holds by construction.  Lookahead: for subspaces U of large
// dimension, the remaining slots that cannot go inside U must be fillable by allowed labels >= pos outside U.
// Symmetry: orderly generation under the dumped group G_E (sorted label sequence lex-min in its orbit; prefixes
// of canonical sequences are canonical, so each orbit is produced exactly once).
// LP bound (--lp dmin dmax): at nodes of depth dmin..dmax, prune when the LP relaxation of the remaining slots over
// the label suffix is < rem, certified by an exact integer weak-duality check (see State::lpPrune).
// --roots f K: the jobs are the nodes K levels below each label prefix listed in f (one per line, comma-separated).
// --root v1,..,vk: the jobs are the --frontier nodes of the subtree of that node (replayed with every check).
// --budget B --heavy f: a job visiting more than B nodes is abandoned (not recorded as done) and its prefix appended to f.
// --subroot D IX: the jobs are the --frontier nodes of the subtree of node IX of the depth-D frontier (split a heavy job).
// --cert P (lineenum3): write a proof trace of every completed search block to P_t<thread>.bin (jobs) and P_top.bin (the
// part above the frontier), for the independent checker lechk.  Replays of a subtree root (job, --root, --roots,
// --subroot) add the prefix labels only (no LP fixing along the prefix), so every block is self-contained.
// Record format (all integers little-endian, v = LEB128 varint, labels in search order):
//   block: 'T' n vec16*n frontierD8 | 'J' n vec16*n ;  node records ... ;  'Z' v(nodes)
//   node:  'L' leaf | 'F' frontier node | 'K' dual (LP kill over labels >= pos) |
//          'O' cut8 kind8 [row16 if kind 1] hasDual8 [dual] { 'C' label8 child }* 'E'
//          (no completion uses only labels >= cut: kind 0 cut = N, 1 row bound, 2 total weight, 3 LP-forced label cut)
//   child: node record, or 'P' kind8 [row16]: the child fails the lookahead after it is added (labels >= its label)
//   dual:  v(n) { row16 v(Y) }*n  (exact weak-duality certificate, scale 2^30)
// Usage: lineenum ipfile [--estimate K] [--threads T] [--frontier D] [--state f] [--out f] [--look kmin] [--seed s]
//        [--order f] [--check sols] [--lp dmin dmax] [--lpadd K] [--dumpnodes D] [--maxjobs K] [--skipk k]
#include <bits/stdc++.h>
#include <condition_variable>
#include <thread>
#include <atomic>
#include <mutex>
#include <unistd.h>
#include "packlp.h"
typedef unsigned long long u64;
struct M128 { u64 w[4]; };   // lineenum9: 256-label masks (point quotients have 255 cosets); the type name is kept
static inline M128 AND(M128 x,M128 y){ return {{x.w[0]&y.w[0],x.w[1]&y.w[1],x.w[2]&y.w[2],x.w[3]&y.w[3]}}; }
static inline M128 ANDN(M128 x,M128 y){ return {{x.w[0]&~y.w[0],x.w[1]&~y.w[1],x.w[2]&~y.w[2],x.w[3]&~y.w[3]}}; }
static inline int PC(M128 x){ return __builtin_popcountll(x.w[0])+__builtin_popcountll(x.w[1])+__builtin_popcountll(x.w[2])+__builtin_popcountll(x.w[3]); }
static inline bool TST(M128 x,int l){ return (x.w[l>>6]>>(l&63))&1; }
static inline void CLR(M128& x,int l){ x.w[l>>6]&=~(1ULL<<(l&63)); }
static inline void SET(M128& x,int l){ x.w[l>>6]|=(1ULL<<(l&63)); }
static inline bool NZ(M128 x){ return (x.w[0]|x.w[1]|x.w[2]|x.w[3])!=0; }
#define FORBITS(m,l,BODY) for(int q_=0;q_<4;q_++) for(u64 w_=(m).w[q_]; w_; w_&=w_-1){ int l=64*q_+__builtin_ctzll(w_); BODY; }
static int R,N; static std::vector<int> vecs; static int ub[256]; static std::vector<char> SEPSKIP; static const char* SEPSKIPF=nullptr;   // lineenum9x: rows never separated (dominated: implied for the LP)
struct Row { M128 mask; int cap,size,k; };
static std::vector<Row> rows; static std::vector<std::vector<int>> inc; static std::vector<int> look; static int LOOKK=7;
static std::vector<std::vector<int>> G; static M128 suf[257];
static std::mutex outmu; static FILE* OUT=nullptr; static std::atomic<long long> nleaf{0};
static int DUMPD=-1; static std::vector<int> ORD; static std::mutex dumpmu;
static const char* CERTP=nullptr; static std::mutex certmu;
static int DONATE_D=0; struct Piece { int ix; std::vector<int> seq; M128 a,b,c,e,m5,m6,m7,m8; /* allowed,r2..r8 at the donation point (carry LP fixes) */ }; static std::mutex qmu; static std::condition_variable qcv; static std::deque<Piece> PQ;
static std::atomic<int> idleN{0}; static std::atomic<int>* gOut=nullptr; static std::atomic<long long> donatedN{0}; static long long BUDGET_G=0;
static std::set<int> SKIPK; static int FRONTIER_D=-1; static bool collecting=false; static std::vector<std::vector<int>> frontier;

// HiGHS C API (libhighs.so.1 shipped in the highspy wheel; HighsInt is 32-bit there)
extern "C" {
void* Highs_create(void); void Highs_destroy(void*);
int Highs_passLp(void*,int,int,int,int,int,double,const double*,const double*,const double*,const double*,const double*,const int*,const int*,const double*);
int Highs_run(void*); int Highs_getModelStatus(const void*); double Highs_getObjectiveValue(const void*);
int Highs_getSolution(const void*,double*,double*,double*,double*);
int Highs_setBoolOptionValue(void*,const char*,int); int Highs_setStringOptionValue(void*,const char*,const char*); int Highs_setIntOptionValue(void*,const char*,int);
int Highs_addRows(void*,int,const double*,const double*,int,const int*,const int*,const double*);
double Highs_getInfinity(const void*);
}
static int SEPMODE=1, INHERIT=1; static const char* DONEPF=nullptr; static std::atomic<long long> plSolves{0}, plFails{0}, plPivots{0}, plFallback{0}; static bool USEPL=true;
static int LPMIN=1, LPMAX=-1, LPADD=100; static bool LPFIX=true; static int SIBK=0; static bool SIBSEED=false; static std::atomic<long long> lpSib[64]; static std::atomic<long long> lpCalls[64], lpKills[64], lpReuse[64], lpRounds{0}, lpFails{0}, lpFixed{0};

static std::vector<uint32_t> SID; static std::vector<u64> SW[4]; static std::vector<uint8_t> SCAP; static bool VSEP=true; static const char* FRONTF=nullptr;
static std::vector<uint32_t> incF; static std::vector<int> incO; static std::vector<uint8_t> capv; static std::vector<int> allInc[256];
static std::vector<int> untracked; // rows not tracked during search (checked at leaves)
static inline int topk64(u64 x1,u64 x2,u64 x3,u64 x4,u64 x5,u64 x6,u64 x7,u64 x8,int k){ // max p with popcount(x1>>p)+..+popcount(x8>>p) >= k, or -1
  if(__builtin_popcountll(x1)+__builtin_popcountll(x2)+__builtin_popcountll(x3)+__builtin_popcountll(x4)+__builtin_popcountll(x5)+__builtin_popcountll(x6)+__builtin_popcountll(x7)+__builtin_popcountll(x8)<k) return -1;
  int lo=0,hi=63; while(lo<hi){ int mid=(lo+hi+1)>>1; if(__builtin_popcountll(x1>>mid)+__builtin_popcountll(x2>>mid)+__builtin_popcountll(x3>>mid)+__builtin_popcountll(x4>>mid)+__builtin_popcountll(x5>>mid)+__builtin_popcountll(x6>>mid)+__builtin_popcountll(x7>>mid)+__builtin_popcountll(x8>>mid)>=k) lo=mid; else hi=mid-1; } return lo; }
static inline int topk(M128 B1,M128 B2,M128 B3,M128 B4,M128 B5,M128 B6,M128 B7,M128 B8,int k){ if(k<=0) return 255;
  for(int q=3;q>=0;q--){ int c=__builtin_popcountll(B1.w[q])+__builtin_popcountll(B2.w[q])+__builtin_popcountll(B3.w[q])+__builtin_popcountll(B4.w[q])+__builtin_popcountll(B5.w[q])+__builtin_popcountll(B6.w[q])+__builtin_popcountll(B7.w[q])+__builtin_popcountll(B8.w[q]);
    if(c>=k) return 64*q+topk64(B1.w[q],B2.w[q],B3.w[q],B4.w[q],B5.w[q],B6.w[q],B7.w[q],B8.w[q],k); k-=c; }
  return -1; }
struct State {
  std::vector<uint8_t> cb; bool cert=false; int prepRow=-1, postRow=-1; int curJob=-1;
  inline void c8(int x){ if(cert) cb.push_back((uint8_t)x); }
  inline void c16(int x){ if(cert){ cb.push_back((uint8_t)(x&255)); cb.push_back((uint8_t)((x>>8)&255)); } }
  inline void cv(unsigned long long x){ if(!cert) return; while(x>=128){ cb.push_back((uint8_t)(x&127)|128); x>>=7; } cb.push_back((uint8_t)x); }
  inline void cdual(const std::vector<uint32_t>& rs,const std::vector<long long>& Y){ if(!cert) return; cv(rs.size()); for(size_t i=0;i<rs.size();i++){ cv(rs[i]); cv((unsigned long long)Y[i]); } }   // lineenum9: row ids as varints (lineenum7 wrote 16 bits)
  void cbegin(char tag,const int* pre,int n,int fd){ if(!cert) return; cb.clear(); c8(tag); c8(n); for(int i=0;i<n;i++) c16(vecs[pre[i]]); if(tag=='T') c8(fd); }
  void cend(FILE* f,long long nodes){ if(!cert) return; c8('Z'); cv((unsigned long long)nodes); uint32_t mg=0x3942454C; uint64_t len=cb.size();   // lineenum9t: magic 'LEB9' (row ids in O/P records are varints)
    { std::lock_guard<std::mutex> lk(certmu); fwrite(&mg,4,1,f); fwrite(&len,8,1,f); fwrite(cb.data(),1,cb.size(),f); fflush(f); } cb.clear(); }
  std::vector<uint8_t> cnt; int mult[256]; int seq[64]; int d=0; M128 allowed,r2,r3,r4,r5,r6,r7,r8; M128 stA[64],st2[64],st3[64],st4[64],st5[64],st6[64],st7[64],st8[64];
  int ng; std::vector<int> imgv; // img(depth,g)[j]: sorted image of seq[0..depth-1] under G[g]
  inline int* img(int dd,int g){ return &imgv[((size_t)dd*ng+g)*64]; }
  std::vector<uint32_t> act[64]; long long visited=0, leaves=0; long long depthCnt[64]={0}; long long budgetEnd=LLONG_MAX; bool aborted=false;
  State(){ cnt.assign(rows.size(),0); memset(mult,0,sizeof mult); allowed=M128{}; r2=M128{}; r3=M128{}; r4=M128{}; r5=M128{}; r6=M128{}; r7=M128{}; r8=M128{}; ng=G.size(); imgv.assign((size_t)(R+2)*ng*64,0);
    for(int l=0;l<N;l++){ if(ub[l]>=1) SET(allowed,l); if(ub[l]>=2) SET(r2,l); if(ub[l]>=3) SET(r3,l); if(ub[l]>=4) SET(r4,l); if(ub[l]>=5) SET(r5,l); if(ub[l]>=6) SET(r6,l); if(ub[l]>=7) SET(r7,l); if(ub[l]>=8) SET(r8,l); }
    for(int r:look) if(R-capv[r]>=1) act[0].push_back(r);
    if(LPMAX>=0){ hl=Highs_create(); Highs_setBoolOptionValue(hl,"output_flag",0); Highs_setStringOptionValue(hl,"presolve","off");
      Highs_setIntOptionValue(hl,"threads",1); lact.assign(rows.size(),0.0); inW.assign(rows.size(),0); pcb.assign(SID.size(),0); } }
  ~State(){ if(hl) Highs_destroy(hl); }
  State(const State&)=delete;
  // ---- LP bound.  At a node with remaining slots rem, every completion uses rem labels from S = allowed labels at
  // positions >= pos, so it is a feasible point of  max sum x_l  s.t. 0 <= x_l <= residual multiplicity of l,
  // sum_{l in U} x_l <= cap(U) - m(U) for every tracked subspace U.  Rows are generated lazily (start from the
  // parent's dual support, add the most violated rows of the current optimum).  The node is pruned only when an
  // exact integer check of weak duality proves the optimum < rem: for any y >= 0,
  //   sum x <= sum_U y_U b_U + sum_l u_l max(0, 1 - sum_{U ni l} y_U),
  // evaluated with y = floor(2^30 * dual)/2^30 in 64-bit integers.
  std::vector<uint16_t> pcb; void* hl=nullptr; std::vector<double> lact; std::vector<char> inW; std::vector<uint32_t> dsup[64]; std::vector<long long> dY[64]; bool dvalid[64]={0}; std::vector<uint32_t> kS[64][8]; std::vector<long long> kY[64][8]; int kN[64]={0}, kH[64]={0};
  void sibRec(){ if(SIBK<=0) return; int j=kH[d]; kS[d][j]=dsup[d]; kY[d][j]=dY[d]; kH[d]=(j+1)%SIBK; if(kN[d]<SIBK) kN[d]++; } std::vector<int> Wr; std::vector<int> WrD[64];
  static constexpr long long SC=1LL<<30;
  // exact weak-duality value (times SC) of the integer dual Y on rows rs at the current node
  long long certB(const std::vector<uint32_t>& rs,const std::vector<long long>& Y,M128 S1,M128 S2,M128 S3,M128 S4,M128 S5,M128 S6,M128 S7,M128 S8,int pos){
    long long B=0; long long T[256]; for(int l=pos;l<N;l++) T[l]=0;
    for(size_t i=0;i<rs.size();i++){ int r=rs[i]; B+=Y[i]*(long long)((int)capv[r]-(int)cnt[r]); M128 m=AND(rows[r].mask,S1);
      FORBITS(m,l_,T[l_]+=Y[i]) }
    for(int l=pos;l<N;l++) if(TST(S1,l) && T[l]<SC) B+=(long long)(1+TST(S2,l)+TST(S3,l)+TST(S4,l)+TST(S5,l)+TST(S6,l)+TST(S7,l)+TST(S8,l))*(SC-T[l]);
    return B; }
  // Fixing from the certified dual (valid for any Y >= 0): with t_l = T_l/SC and B the certificate value,
  //   sum x <= B/SC - sum_{t_l>1} x_l (t_l-1) - sum_{t_l<1} (u_l-x_l)(1-t_l),
  // so a completion (sum x = rem) has x_l <= (B-rem*SC)/(T_l-SC) when T_l > SC, and x_l >= u_l - (B-rem*SC)/(SC-T_l)
  // when T_l < SC.  Upper bounds shrink allowed/r2/r3; a label forced to appear caps the next label at it.
  int lpFix(int pos,int rem,bool& fixed){
    M128 S1=AND(allowed,suf[pos]), S2=AND(r2,suf[pos]), S3=AND(r3,suf[pos]), S4=AND(r4,suf[pos]), S5=AND(r5,suf[pos]), S6=AND(r6,suf[pos]), S7=AND(r7,suf[pos]), S8=AND(r8,suf[pos]);
    const auto& rs=dsup[d]; const auto& Y=dY[d];
    long long B=0; long long T[256]; for(int l=pos;l<N;l++) T[l]=0;
    for(size_t i=0;i<rs.size();i++){ int r=rs[i]; B+=Y[i]*(long long)((int)capv[r]-(int)cnt[r]); M128 m=AND(rows[r].mask,S1);
      FORBITS(m,l_,T[l_]+=Y[i]) }
    for(int l=pos;l<N;l++) if(TST(S1,l) && T[l]<SC) B+=(long long)(1+TST(S2,l)+TST(S3,l)+TST(S4,l)+TST(S5,l)+TST(S6,l)+TST(S7,l)+TST(S8,l))*(SC-T[l]);
    long long gap=B-(long long)rem*SC; if(gap<0) return -2; // cannot happen after a failed prune; be safe
    int lreq=N;
    for(int l=pos;l<N;l++){ if(!TST(S1,l)) continue; int u=1+TST(S2,l)+TST(S3,l)+TST(S4,l)+TST(S5,l)+TST(S6,l)+TST(S7,l)+TST(S8,l);
      if(T[l]>SC){ long long km=gap/(T[l]-SC); if(km<u){ fixed=true; lpFixed++;
          if(km<=0) CLR(allowed,l); if(km<=1) CLR(r2,l); if(km<=2) CLR(r3,l); if(km<=3) CLR(r4,l); if(km<=5-1) CLR(r5,l); if(km<=6-1) CLR(r6,l); if(km<=7-1) CLR(r7,l); if(km<=8-1) CLR(r8,l); } }
      else if(T[l]<SC){ long long kmin=u-gap/(SC-T[l]); if(kmin>=1 && l<lreq) lreq=l; } }
    return lreq; }
  // lineenum6: the same LP and separation loop with the dense simplex of packlp.h.  Returns 1 = pruned (K record written),
  // 0 = kept (duals, fixings as in the HiGHS path), -1 = trouble (caller falls back to HiGHS from scratch).
  PackLP pl; std::vector<std::vector<int>> plRows; std::vector<double> plB, plX, plY;
  int lpCustom(int pos,int rem,M128 S1,M128 S2,M128 S3,M128 S4,M128 S5,M128 S6,M128 S7,M128 S8,int nc,const int* colOf,const int* labOf,const double* cu,int& lreq,bool& fixed){
    auto bres=[&](int r)->int{ return (int)capv[r]-(int)cnt[r]; };
    std::vector<std::pair<double,int>> viol;
    for(int round=0; round<200; round++){
      lpRounds++;
      size_t nw=Wr.size(); plRows.resize(nw); plB.resize(nw);
      for(size_t i=0;i<nw;i++){ int r=Wr[i]; auto& rr=plRows[i]; rr.clear(); plB[i]=bres(r); M128 m=AND(rows[r].mask,S1);
        FORBITS(m,l_,rr.push_back(colOf[l_])) }
      plRows.resize(nw); plSolves++;
      if(!pl.solve(nc,plRows,plB,cu)){ plFails++; return -1; }
      plPivots+=pl.iters; double obj=pl.z; pl.primal(plX); pl.duals(plY);
      dsup[d].clear(); dY[d].clear(); bool big=false;
      for(size_t i=0;i<nw;i++){ if(!(plY[i]>0)) continue; double yd=plY[i]*(double)SC; if(!(yd<1e12)){ big=true; continue; }
        long long Y=(long long)floor(yd); if(Y>0){ dsup[d].push_back(Wr[i]); dY[d].push_back(Y); } }
      if(!big) dvalid[d]=true;
      if(obj<rem-1e-7){
        if(!big && certB(dsup[d],dY[d],S1,S2,S3,S4,S5,S6,S7,S8,pos)<(long long)rem*SC){ lpKills[d]++; c8('K'); cdual(dsup[d],dY[d]); sibRec(); return 1; }
        dvalid[d]=false; return -1; }
      viol.clear();
      // lineenum9w: --frontierfile F takes the jobs from a DUMPFRONTIER file (lines "i v1,v2,..."; indices = line order) instead of collecting.
      // lineenum9v: separation sweep over the separable rows only (not --sepskip, tracked), masks stored by word (SoA) so the popcount
//   bound of every row is a branch-free vectorized pass; then one scalar pass over the rows that pass it.  Same rows, same order,
//   same violated list as lineenum9t (--novsep: the old loop).
      // lineenum9t: --sibk K keeps the last K LP-kill duals of each depth (from siblings and cousins) and tries them (certB, valid for any
//   dual Y >= 0) before solving a node's LP; --sibseed adds the latest kill dual's rows to the LP's first working set.
      // lineenum9x: --sepskip FILE lists rows (dominated by a row one dimension up) left out of LP separation; they stay in every other check.
// lineenum9: lineenum7 with 256-label masks (N <= 255, for point quotients).
// lineenum7: activities by value classes of x (bit planes): a(r) = sum_i v_i |U_r n X_i|; falls back to the incidence
      // sweep when x has more than 8 distinct positive values
      { double vals[8]; M128 vm[8]; int k=0; bool okv=true; M128 supp=M128{}; double sx=0;
        for(int j=0;j<nc&&okv;j++){ double x=plX[j]; if(x<=1e-9) continue; int l=labOf[j]; sx+=x; int i=0; while(i<k && std::fabs(vals[i]-x)>1e-9) i++;
          if(i==k){ if(k==8){ okv=false; break; } vals[k]=x; vm[k]=M128{}; k++; } SET(vm[i],l); SET(supp,l); }
        if(SEPMODE==1){ okv=false; double xl[256]; for(int l=0;l<N;l++) xl[l]=0; supp=M128{}; sx=0;
          M128 sup2=M128{}, sup3=M128{}, sup4=M128{}, sup5=M128{}, sup6=M128{}, sup7=M128{}, sup8=M128{};
          for(int j=0;j<nc;j++) if(plX[j]>1e-9){ int l=labOf[j]; xl[l]=plX[j]; SET(supp,l); sx+=plX[j]; if(plX[j]>1+1e-9) SET(sup2,l); if(plX[j]>2+1e-9) SET(sup3,l); if(plX[j]>3+1e-9) SET(sup4,l); if(plX[j]>5-1+1e-9) SET(sup5,l); if(plX[j]>6-1+1e-9) SET(sup6,l); if(plX[j]>7-1+1e-9) SET(sup7,l); if(plX[j]>8-1+1e-9) SET(sup8,l); }
          const int NRW=(int)rows.size(); const double thr=sx-1e-7;
          if(VSEP){ const int NS=(int)SID.size(); uint16_t* pc=pcb.data();
            { const u64 *a0=SW[0].data(), *a1=SW[1].data(), *a2=SW[2].data(), *a3=SW[3].data(); const u64 s0=supp.w[0], s1=supp.w[1], s2=supp.w[2], s3=supp.w[3];
              for(int i=0;i<NS;i++) pc[i]=(uint16_t)(__builtin_popcountll(a0[i]&s0)+__builtin_popcountll(a1[i]&s1)+__builtin_popcountll(a2[i]&s2)+__builtin_popcountll(a3[i]&s3)); }
            for(const M128* sp:{&sup2,&sup3,&sup4,&sup5,&sup6,&sup7,&sup8}) if(NZ(*sp)){ const u64 *a0=SW[0].data(), *a1=SW[1].data(), *a2=SW[2].data(), *a3=SW[3].data(); const u64 s0=sp->w[0], s1=sp->w[1], s2=sp->w[2], s3=sp->w[3];
              for(int i=0;i<NS;i++) pc[i]+=(uint16_t)(__builtin_popcountll(a0[i]&s0)+__builtin_popcountll(a1[i]&s1)+__builtin_popcountll(a2[i]&s2)+__builtin_popcountll(a3[i]&s3)); }
            const uint32_t* sid=SID.data(); const uint8_t* sc=SCAP.data(); const uint8_t* cn=cnt.data();
            for(int i=0;i<NS;i++){ int r=sid[i]; int b=(int)sc[i]-(int)cn[r]; if((int)pc[i]<=b) continue;   // sum of x over the row is at most pc
              if(inW[r] || b>=thr) continue; M128 ms=AND(rows[r].mask,supp);
              double a=0; FORBITS(ms,l_,a+=xl[l_])
              if(a>b+1e-7) viol.push_back({a-b,r}); }
            goto sepdone; }
          for(int r=0;r<NRW;r++){ if(inW[r] || SEPSKIP[r]) continue; int b=bres(r); if(capv[r]==255 || b>=thr) continue; M128 ms=AND(rows[r].mask,supp);
            if(PC(ms)+PC(AND(ms,sup2))+PC(AND(ms,sup3))+PC(AND(ms,sup4))+PC(AND(ms,sup5))+PC(AND(ms,sup6))+PC(AND(ms,sup7))+PC(AND(ms,sup8))<=b) continue;   // sum of x over the row is at most this count
            double a=0; FORBITS(ms,l_,a+=xl[l_])
            if(a>b+1e-7) viol.push_back({a-b,r}); }
          goto sepdone; }
        if(okv){ const int NRW=(int)rows.size(); const double thr=sx-1e-7;
          for(int r=0;r<NRW;r++){ if(inW[r] || SEPSKIP[r]) continue; int b=bres(r); if(capv[r]==255 || b>=thr) continue; const M128& m=rows[r].mask;
            M128 ms=AND(m,supp); if(!NZ(ms)) continue; double a=0; for(int i=0;i<k;i++) a+=vals[i]*PC(AND(ms,vm[i]));
            if(a>b+1e-7) viol.push_back({a-b,r}); } }
        else {
          for(int j=0;j<nc;j++){ double x=plX[j]; if(x<=1e-9) continue; int l=labOf[j]; for(int p=incO[l];p<incO[l+1];p++) lact[incF[p]]+=x; }
          for(int j=0;j<nc;j++){ if(plX[j]<=1e-9) continue; int l=labOf[j];
            for(int p=incO[l];p<incO[l+1];p++){ int r=incF[p]; double a=lact[r]; if(a==0) continue; lact[r]=0;
              if(!inW[r] && !SEPSKIP[r] && a>bres(r)+1e-7) viol.push_back({a-bres(r),r}); } } } }
      sepdone:
      if(viol.empty()){ if(dvalid[d] && LPFIX){ int q=lpFix(pos,rem,fixed); if(q==-2) return 0; lreq=q; } return 0; }
      if((int)viol.size()>LPADD){ std::nth_element(viol.begin(),viol.begin()+LPADD,viol.end(),[](const std::pair<double,int>& x,const std::pair<double,int>& y){ return x.first>y.first; }); viol.resize(LPADD); }
      for(auto& v:viol){ inW[v.second]=1; Wr.push_back(v.second); } }
    return -1; }
  bool lpPrune(int pos){ int lreq; bool fixed; return lpPrune(pos,lreq,fixed); }
  bool lpPrune(int pos,int& lreq,bool& fixed){
    lreq=N; fixed=false;
    int rem=R-d; dvalid[d]=false; if(rem<=0) return false;
    M128 S1=AND(allowed,suf[pos]), S2=AND(r2,suf[pos]), S3=AND(r3,suf[pos]), S4=AND(r4,suf[pos]), S5=AND(r5,suf[pos]), S6=AND(r6,suf[pos]), S7=AND(r7,suf[pos]), S8=AND(r8,suf[pos]);
    if(d>0 && dvalid[d-1] && certB(dsup[d-1],dY[d-1],S1,S2,S3,S4,S5,S6,S7,S8,pos)<(long long)rem*SC){ lpReuse[d]++; c8('K'); cdual(dsup[d-1],dY[d-1]); return true; }
    for(int i=0;i<kN[d];i++){ int j=(kH[d]-1-i+SIBK)%SIBK; if(certB(kS[d][j],kY[d][j],S1,S2,S3,S4,S5,S6,S7,S8,pos)<(long long)rem*SC){ lpSib[d]++; c8('K'); cdual(kS[d][j],kY[d][j]); return true; } }
    int colOf[256], labOf[256], cuI[256]; double cu[256], cost[256], lo[256]; int nc=0;
    for(int l=0;l<N;l++){ colOf[l]=-1; if(l>=pos && TST(S1,l)){ colOf[l]=nc; labOf[nc]=l; cuI[nc]=1+TST(S2,l)+TST(S3,l)+TST(S4,l)+TST(S5,l)+TST(S6,l)+TST(S7,l)+TST(S8,l); cu[nc]=cuI[nc]; cost[nc]=1; lo[nc]=0; nc++; } }
    int tot=0; for(int j=0;j<nc;j++) tot+=cuI[j]; if(tot<rem){ c8('K'); cv(0); return true; }
    lpCalls[d]++;
    auto bres=[&](int r)->int{ return (int)capv[r]-(int)cnt[r]; };
    auto nonred=[&](int r)->bool{ if(capv[r]==255) return false; const M128& m=rows[r].mask; return bres(r) < PC(AND(m,S1))+PC(AND(m,S2))+PC(AND(m,S3))+PC(AND(m,S4))+PC(AND(m,S5))+PC(AND(m,S6))+PC(AND(m,S7))+PC(AND(m,S8)); };
    for(int r:Wr) inW[r]=0; Wr.clear();
    if(d>0) for(int r:dsup[d-1]) if(!inW[r] && nonred(r)){ inW[r]=1; Wr.push_back(r); }
    if(INHERIT && d>0) for(int r:WrD[d-1]) if(!inW[r] && nonred(r)){ inW[r]=1; Wr.push_back(r); }
    if(SIBSEED && kN[d]>0){ int j=(kH[d]-1+SIBK)%SIBK; for(uint32_t r:kS[d][j]) if(!inW[r] && nonred(r)){ inW[r]=1; Wr.push_back(r); } }
    if(USEPL){ int st=lpCustom(pos,rem,S1,S2,S3,S4,S5,S6,S7,S8,nc,colOf,labOf,cu,lreq,fixed); if(st==0) WrD[d]=Wr; if(st>=0) return st==1; plFallback++;
      for(int r:Wr) inW[r]=0; Wr.clear(); if(d>0) for(int r:dsup[d-1]) if(!inW[r] && nonred(r)){ inW[r]=1; Wr.push_back(r); } dvalid[d]=false; lreq=N; fixed=false; }
    double inf=Highs_getInfinity(hl);
    std::vector<double> rl, ru, av; std::vector<int> as, ai;
    auto rowsCSR=[&](const std::vector<int>& rs){ rl.clear(); ru.clear(); av.clear(); as.clear(); ai.clear();
      for(int r:rs){ as.push_back(ai.size()); rl.push_back(-inf); ru.push_back(bres(r)); M128 m=AND(rows[r].mask,S1);
        FORBITS(m,l_,{ ai.push_back(colOf[l_]); av.push_back(1.0); }) } };
    rowsCSR(Wr); as.push_back(ai.size()); ai.push_back(0); av.push_back(0.0); rl.push_back(0); ru.push_back(0); // keep the arrays non-empty
    if(Highs_passLp(hl,nc,(int)Wr.size(),(int)ai.size()-1,2,-1,0.0,cost,lo,cu,rl.data(),ru.data(),as.data(),ai.data(),av.data())<0){ lpFails++; return false; }
    std::vector<double> xv(nc), cd(nc), rv, rd; std::vector<std::pair<double,int>> viol; std::vector<int> addr;
    for(int round=0; round<200; round++){
      lpRounds++;
      if(Highs_run(hl)<0 || Highs_getModelStatus(hl)!=7){ lpFails++; return false; }
      double obj=Highs_getObjectiveValue(hl); size_t nw=Wr.size(); rv.resize(nw); rd.resize(nw);
      Highs_getSolution(hl,xv.data(),cd.data(),rv.data(),rd.data());
      // integer dual Y = floor(SC*dual) on the rows with positive dual (any Y >= 0 gives a valid bound)
      dsup[d].clear(); dY[d].clear(); bool big=false;
      for(size_t i=0;i<nw;i++){ if(!(rd[i]>0)) continue; double yd=rd[i]*(double)SC; if(!(yd<1e12)){ big=true; continue; }
        long long Y=(long long)floor(yd); if(Y>0){ dsup[d].push_back(Wr[i]); dY[d].push_back(Y); } }
      if(!big) dvalid[d]=true;
      if(obj<rem-1e-7){ // exact certificate
        if(!big && certB(dsup[d],dY[d],S1,S2,S3,S4,S5,S6,S7,S8,pos)<(long long)rem*SC){ lpKills[d]++; c8('K'); cdual(dsup[d],dY[d]); sibRec(); return true; }
        lpFails++; return false; }
      // separation: activities of all tracked rows at the current optimum
      viol.clear();
      for(int j=0;j<nc;j++){ double x=xv[j]; if(x<=1e-9) continue; int l=labOf[j]; for(int p=incO[l];p<incO[l+1];p++) lact[incF[p]]+=x; }
      for(int j=0;j<nc;j++){ if(xv[j]<=1e-9) continue; int l=labOf[j];
        for(int p=incO[l];p<incO[l+1];p++){ int r=incF[p]; double a=lact[r]; if(a==0) continue; lact[r]=0;
          if(!inW[r] && a>bres(r)+1e-7) viol.push_back({a-bres(r),r}); } }
      if(viol.empty()){ if(dvalid[d] && LPFIX){ int q=lpFix(pos,rem,fixed); if(q==-2) return false; lreq=q; } return false; }
      if((int)viol.size()>LPADD){ std::nth_element(viol.begin(),viol.begin()+LPADD,viol.end(),[](const std::pair<double,int>& x,const std::pair<double,int>& y){ return x.first>y.first; }); viol.resize(LPADD); }
      addr.clear(); for(auto& v:viol){ inW[v.second]=1; Wr.push_back(v.second); addr.push_back(v.second); }
      rowsCSR(addr);
      if(Highs_addRows(hl,(int)addr.size(),rl.data(),ru.data(),(int)ai.size(),as.data(),ai.data(),av.data())<0){ lpFails++; return false; } }
    lpFails++; return false; }
  // canonicity of seq+[l] (orderly generation); called before add
  inline bool canonAdd(int l){
    for(int g=1;g<ng;g++){ const int* I=img(d,g); int x=G[g][l]; int i=0; bool xu=false;
      for(int j=0;j<=d;j++){ int mj; if(!xu && (i>=d || x<=I[i])){ mj=x; xu=true; } else mj=I[i++]; int sj=(j<d)?seq[j]:l;
        if(mj<sj) return false; if(mj>sj) break; } }
    return true; }
  inline void add(int l){ stA[d]=allowed; st2[d]=r2; st3[d]=r3; st4[d]=r4; st5[d]=r5; st6[d]=r6; st7[d]=r7; st8[d]=r8;
    for(int g=1;g<ng;g++){ const int* I=img(d,g); int* J=img(d+1,g); int x=G[g][l]; int i=0,j=0; while(i<d && I[i]<x) J[j++]=I[i++]; J[j++]=x; while(i<d) J[j++]=I[i++]; }
    mult[l]++; seq[d++]=l; int res=ub[l]-mult[l];
    if(res<=0) CLR(allowed,l); if(res<2) CLR(r2,l); if(res<3) CLR(r3,l); if(res<4) CLR(r4,l); if(res<5) CLR(r5,l); if(res<6) CLR(r6,l); if(res<7) CLR(r7,l); if(res<8) CLR(r8,l);
    const uint32_t* p=&incF[incO[l]]; const uint32_t* e=&incF[incO[l+1]];
    for(;p<e;p++){ int r=*p; if(++cnt[r]==capv[r]) allowed=ANDN(allowed,rows[r].mask); }
    r2=AND(r2,allowed); r3=AND(r3,allowed); r4=AND(r4,allowed); r5=AND(r5,allowed); r6=AND(r6,allowed); r7=AND(r7,allowed); r8=AND(r8,allowed); }
  inline void undo(int l){ const uint32_t* p=&incF[incO[l]]; const uint32_t* e=&incF[incO[l+1]]; for(;p<e;p++) cnt[*p]--;
    mult[l]--; d--; allowed=stA[d]; r2=st2[d]; r3=st3[d]; r4=st4[d]; r5=st5[d]; r6=st6[d]; r7=st7[d]; r8=st8[d]; }
  // Slack bookkeeping.  At a node, prep() computes lmax and, for every active row r, a lower bound s_r on
  // W_r(l)-need_r valid for every candidate l<=lmax (W_r(l) = residual weight of allowed labels >=l outside r).
  // Adding a candidate l can break row r only if the saturation removals sigma it causes (weight of labels >=l
  // removed, besides l's own unit) exceed the row's slack, so post() checks only rows with s_r < sigma.
  static const int SMAX=48;
  std::vector<uint32_t> srow[64]; int sstart[64][SMAX+2]; int hint[64][4]={{0}}; int nh[64]={0};
  std::vector<uint32_t> tmpR; std::vector<uint8_t> tmpS;
  inline int wsuf(int l) const { M128 A=AND(allowed,suf[l]); return PC(A)+PC(AND(r2,suf[l]))+PC(AND(r3,suf[l]))+PC(AND(r4,suf[l]))+PC(AND(r5,suf[l]))+PC(AND(r6,suf[l]))+PC(AND(r7,suf[l]))+PC(AND(r8,suf[l])); }
  // after add(l) (wb = wsuf(l) before the add): can the remaining slots still be filled from allowed labels >= l?
  inline bool post(int l,int wb){ int rem=R-d; if(rem==0) return true;
    M128 A=AND(allowed,suf[l]), A2=AND(r2,suf[l]), A3=AND(r3,suf[l]), A4=AND(r4,suf[l]), A5=AND(r5,suf[l]), A6=AND(r6,suf[l]), A7=AND(r7,suf[l]), A8=AND(r8,suf[l]);
    int wa=PC(A)+PC(A2)+PC(A3)+PC(A4)+PC(A5)+PC(A6)+PC(A7)+PC(A8); int sigma=wb-wa-1; if(sigma<=0) return true;
    if(wa<rem){ postRow=-1; return false; }
    int pd=d-1; int e=sigma>SMAX+1?(int)srow[pd].size():sstart[pd][sigma];
    const uint32_t* rr=srow[pd].data();
    for(int i=0;i<e;i++){ int r=rr[i]; int need=rem-capv[r]+cnt[r]; if(need<=0) continue; const M128& m=rows[r].mask;
      if(PC(ANDN(A,m))+PC(ANDN(A2,m))+PC(ANDN(A3,m))+PC(ANDN(A4,m))+PC(ANDN(A5,m))+PC(ANDN(A6,m))+PC(ANDN(A7,m))+PC(ANDN(A8,m))<need){ postRow=r; return false; } }
    return true; }
  // at a node: build act[d], the largest candidate label worth trying, and the slack buckets
  inline int prep(int pos){ int rem=R-d;
    if(d>0){ act[d].clear(); for(int r:act[d-1]) if(rem-capv[r]+cnt[r]>=1) act[d].push_back(r); }
    M128 A=AND(allowed,suf[pos]), A2=AND(r2,suf[pos]), A3=AND(r3,suf[pos]), A4=AND(r4,suf[pos]), A5=AND(r5,suf[pos]), A6=AND(r6,suf[pos]), A7=AND(r7,suf[pos]), A8=AND(r8,suf[pos]);
    int lmax=topk(A,A2,A3,A4,A5,A6,A7,A8,rem); prepRow=-1; if(lmax<pos) return -1;
    M128 L1=AND(A,suf[lmax]), L2=AND(A2,suf[lmax]), L3=AND(A3,suf[lmax]), L4=AND(A4,suf[lmax]), L5=AND(A5,suf[lmax]), L6=AND(A6,suf[lmax]), L7=AND(A7,suf[lmax]), L8=AND(A8,suf[lmax]);
    auto bind=[&](int r)->bool{ int need=rem-capv[r]+cnt[r]; const M128& m=rows[r].mask;
      int w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m))+PC(ANDN(L5,m))+PC(ANDN(L6,m))+PC(ANDN(L7,m))+PC(ANDN(L8,m)); if(w>=need) return false;
      lmax=topk(ANDN(A,m),ANDN(A2,m),ANDN(A3,m),ANDN(A4,m),ANDN(A5,m),ANDN(A6,m),ANDN(A7,m),ANDN(A8,m),need); prepRow=r; if(lmax>=pos){ L1=AND(A,suf[lmax]); L2=AND(A2,suf[lmax]); L3=AND(A3,suf[lmax]); L4=AND(A4,suf[lmax]); L5=AND(A5,suf[lmax]); L6=AND(A6,suf[lmax]); L7=AND(A7,suf[lmax]); L8=AND(A8,suf[lmax]); }
      return true; };
    for(int i=0;i<nh[d];i++){ int r=hint[d][i]; if(rem-capv[r]+cnt[r]>=1){ bind(r); if(lmax<pos) return -1; } }
    size_t na=act[d].size(); tmpR.resize(na); tmpS.resize(na); int hc[SMAX+2]; memset(hc,0,sizeof hc);
    for(size_t i=0;i<na;i++){ int r=act[d][i]; int need=rem-capv[r]+cnt[r]; const M128& m=rows[r].mask;
      int w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m))+PC(ANDN(L5,m))+PC(ANDN(L6,m))+PC(ANDN(L7,m))+PC(ANDN(L8,m));
      if(w<need){ lmax=topk(ANDN(A,m),ANDN(A2,m),ANDN(A3,m),ANDN(A4,m),ANDN(A5,m),ANDN(A6,m),ANDN(A7,m),ANDN(A8,m),need); prepRow=r; if(lmax<pos) return -1;
        L1=AND(A,suf[lmax]); L2=AND(A2,suf[lmax]); L3=AND(A3,suf[lmax]); L4=AND(A4,suf[lmax]); L5=AND(A5,suf[lmax]); L6=AND(A6,suf[lmax]); L7=AND(A7,suf[lmax]); L8=AND(A8,suf[lmax]); w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m))+PC(ANDN(L5,m))+PC(ANDN(L6,m))+PC(ANDN(L7,m))+PC(ANDN(L8,m));
        hint[d][nh[d]<4?nh[d]++:(int)(visited&3)]=r; }
      int s=w-need; if(s>SMAX) s=SMAX+1; tmpR[i]=r; tmpS[i]=s; hc[s]++; }
    // counting sort by slack bound (bounds taken at a larger lmax stay valid: W_r only grows as l decreases)
    srow[d].resize(na); int acc=0; for(int s=0;s<=SMAX+1;s++){ sstart[d][s]=acc; acc+=hc[s]; } sstart[d][SMAX+1]=acc-hc[SMAX+1];
    int fill[SMAX+2]; for(int s=0;s<=SMAX+1;s++) fill[s]=sstart[d][s]; fill[SMAX+1]=acc-hc[SMAX+1];
    for(size_t i=0;i<na;i++) srow[d][fill[tmpS[i]]++]=tmpR[i];
    return lmax; }
  bool verifyLeaf(bool& tracked){ std::vector<int> c(rows.size(),0); for(int i=0;i<d;i++) for(int r:allInc[seq[i]]) c[r]++;
    tracked=true; bool ok=true;
    for(size_t r=0;r<rows.size();r++) if(c[r]>rows[r].cap){ ok=false; if(capv[r]<255) tracked=false; }
    int m[256]={0}; for(int i=0;i<d;i++) m[seq[i]]++; for(int l=0;l<N;l++) if(m[l]>ub[l]) tracked=false; if(d!=R) tracked=false; return ok&&tracked; }
  void emit(){ bool tr; bool ok=verifyLeaf(tr); if(!tr){ fprintf(stderr,"LEAF VERIFY FAILED\n"); exit(7); } if(!ok) return; nleaf++; leaves++;
    std::lock_guard<std::mutex> lk(outmu); if(OUT){ for(int i=0;i<d;i++) fprintf(OUT,"%d%c",vecs[seq[i]],i+1==d?'\n':' '); fflush(OUT); } }
  void dfs(int pos){
    if(aborted) return; if(visited>=budgetEnd){ aborted=true; return; }
    visited++; depthCnt[d]++;
    if(d==R){ c8('L'); emit(); return; }
    if(collecting && d==FRONTIER_D){ c8('F'); frontier.push_back(std::vector<int>(seq,seq+d)); return; }
    int lmax=prep(pos); int kind=prepRow<0?2:1, krow=prepRow; bool hasDual=false;
    if(lmax>=pos && d>=LPMIN && d<=LPMAX){ int lreq; bool fixed; if(lpPrune(pos,lreq,fixed)) return; // the 'K' record is written by lpPrune
      hasDual=(fixed||lreq<N);
      if(fixed){ lmax=prep(pos); kind=prepRow<0?2:1; krow=prepRow; } if(lreq<lmax){ lmax=lreq; kind=3; } }
    if(cert){ int cut=lmax<pos?pos:lmax+1; if(cut>=N){ cut=N; kind=0; }
      c8('O'); c8(cut); c8(kind); if(kind==1) cv((unsigned long long)krow); c8(hasDual?1:0); if(hasDual) cdual(dsup[d],dY[d]); }   // lineenum9t: varint row (16 bits truncated rows >= 65536)
    for(int l=pos;l<=lmax;l++){ if(!TST(allowed,l)) continue; if(!canonAdd(l)) continue;
      c8('C'); c8(l);
      int wb=wsuf(l); add(l);
      if(post(l,wb)){
        if(DONATE_D>0 && !cert && !collecting && BUDGET_G<=0 && d<DONATE_D && d<R && curJob>=0 && gOut && idleN.load(std::memory_order_relaxed)>0){   
          gOut[curJob]++; { std::lock_guard<std::mutex> lk(qmu); PQ.push_back({curJob,std::vector<int>(seq,seq+d),allowed,r2,r3,r4,r5,r6,r7,r8}); } donatedN++; qcv.notify_one(); }
        else dfs(l); }
      else if(cert){ c8('P'); c8(postRow<0?2:1); if(postRow>=0) cv((unsigned long long)postRow); }   // lineenum9t: varint row
      undo(l); if(aborted) return; }
    c8('E'); }
  double perDepth[64]={0};
  void dive(std::mt19937_64& rng,double& estN,double& estL,int& dr){
    double w=1; estN=1; estL=0; dr=0; int pos=0; std::vector<int> path; perDepth[0]+=1;
    while(true){ if(d==R){ estL=w; break; } std::vector<int> kids; int lmax=prep(pos);
      if(lmax>=pos && d>=LPMIN && d<=LPMAX){ int lreq; bool fixed; if(lpPrune(pos,lreq,fixed)) lmax=-1; else { if(fixed) lmax=prep(pos); if(lreq<lmax) lmax=lreq; } }
      for(int l=pos;l<=lmax;l++){ if(!TST(allowed,l)) continue; if(!canonAdd(l)) continue; int wb=wsuf(l); add(l); if(post(l,wb)) kids.push_back(l); undo(l); }
      if(d==DUMPD){ std::lock_guard<std::mutex> lk(dumpmu); printf("NODE"); for(int i=0;i<d;i++) printf(" %d",ORD.empty()?seq[i]:ORD[seq[i]]); printf(" pos %d\n",ORD.empty()?pos:ORD[pos]); }
      if(kids.empty()) break; w*=kids.size(); estN+=w; perDepth[d+1]+=w; int l=kids[rng()%kids.size()]; add(l); path.push_back(l); pos=l; dr++; }
    for(int i=(int)path.size()-1;i>=0;i--) undo(path[i]); }
  // check mode: is the given sorted canonical sequence accepted step by step?
  std::string walk(const std::vector<int>& best){ int pos=0;
    for(size_t i=0;i<best.size();i++){ int l=best[i]; int lmax=prep(pos);
      if(l>lmax) return "beyond lmax at "+std::to_string(i);
      if(d>=LPMIN && d<=LPMAX){ int lreq; bool fixed; if(lpPrune(pos,lreq,fixed)) return "LP pruned at "+std::to_string(i);
        if(fixed){ lmax=prep(pos); if(l>lmax) return "beyond lmax after LP fixing at "+std::to_string(i); if(!TST(allowed,l)) return "LP-fixed out at "+std::to_string(i); }
        if(l>lreq) return "beyond LP-required label at "+std::to_string(i); } if(!TST(allowed,l)) return "not allowed at "+std::to_string(i);
      if(!canonAdd(l)) return "noncanon at "+std::to_string(i); int wb=wsuf(l); add(l); if(!post(l,wb)) return "post at "+std::to_string(i); pos=l; }
    return ""; }
};

static void lpReport(){ if(LPMAX<0) return; fprintf(stderr,"PACKLP solves %lld pivots %lld fails %lld fallbacks %lld\n",(long long)plSolves,(long long)plPivots,(long long)plFails,(long long)plFallback); fprintf(stderr,"LP calls/kills by depth:");
  for(int d=0;d<64;d++) if(lpCalls[d]||lpReuse[d]||lpSib[d]) fprintf(stderr," d%d %lld/%lld+%lld+s%lld",d,(long long)lpCalls[d],(long long)lpKills[d],(long long)lpReuse[d],(long long)lpSib[d]);
  fprintf(stderr,"  rounds %lld fails %lld fixed %lld\n",(long long)lpRounds,(long long)lpFails,(long long)lpFixed); }
int main(int argc,char** argv){
  const char* ipf=argv[1]; long long EST=0; int TH=1; const char* statep=nullptr; const char* outp="/dev/null"; unsigned long long seed=1; const char* CHECK=nullptr; const char* ORDERF=nullptr; long long MAXJOBS=-1; const char* JOBSF=nullptr; const char* PREFF=nullptr; int PREFD=0; int SUBD=-1; long long SUBIX=-1; const char* ROOTS=nullptr; const char* ROOTSF=nullptr; int REL=3; long long BUDGET=0; const char* HEAVYF=nullptr;
  for(int i=2;i<argc;i++){ std::string a=argv[i];
    if(a=="--estimate") EST=atoll(argv[++i]); else if(a=="--threads") TH=atoi(argv[++i]); else if(a=="--frontier") FRONTIER_D=atoi(argv[++i]);
    else if(a=="--doneprefixes") DONEPF=argv[++i]; else if(a=="--sepmode") SEPMODE=atoi(argv[++i]); else if(a=="--inherit") INHERIT=atoi(argv[++i]); else if(a=="--highs") USEPL=false; else if(a=="--state") statep=argv[++i]; else if(a=="--out") outp=argv[++i]; else if(a=="--look") LOOKK=atoi(argv[++i]); else if(a=="--seed") seed=atoll(argv[++i]); else if(a=="--check") CHECK=argv[++i]; else if(a=="--order") ORDERF=argv[++i]; else if(a=="--skipk") SKIPK.insert(atoi(argv[++i])); else if(a=="--maxjobs") MAXJOBS=atoll(argv[++i]); else if(a=="--dumpnodes") DUMPD=atoi(argv[++i]);
    else if(a=="--sepskip") SEPSKIPF=argv[++i]; else if(a=="--sibk"){ SIBK=atoi(argv[++i]); if(SIBK<0||SIBK>8){ fprintf(stderr,"--sibk 0..8\n"); return 1; } } else if(a=="--sibseed") SIBSEED=true; else if(a=="--novsep") VSEP=false; else if(a=="--frontierfile") FRONTF=argv[++i]; else if(a=="--lp"){ LPMIN=atoi(argv[++i]); LPMAX=atoi(argv[++i]); } else if(a=="--lpadd") LPADD=atoi(argv[++i]); else if(a=="--nolpfix") LPFIX=false; else if(a=="--jobs") JOBSF=argv[++i]; else if(a=="--donate") DONATE_D=atoi(argv[++i]); else if(a=="--prefixes"){ PREFF=argv[++i]; PREFD=atoi(argv[++i]); } else if(a=="--subroot"){ SUBD=atoi(argv[++i]); SUBIX=atoll(argv[++i]); } else if(a=="--root") ROOTS=argv[++i]; else if(a=="--roots"){ ROOTSF=argv[++i]; REL=atoi(argv[++i]); } else if(a=="--budget") BUDGET=atoll(argv[++i]); else if(a=="--heavy") HEAVYF=argv[++i]; else if(a=="--cert") CERTP=argv[++i];
    else { fprintf(stderr,"bad arg %s\n",a.c_str()); return 1; } }
  { std::ifstream f(ipf); std::string tok; f>>tok>>R>>tok>>N; vecs.resize(N); for(int l=0;l<N;l++) f>>vecs[l];
    for(int l=0;l<N;l++) ub[l]=R; std::string line; std::getline(f,line);
    while(std::getline(f,line)){ std::istringstream ss(line); std::string t; ss>>t;
      if(t=="C"){ int k,cap,n; ss>>k>>cap>>n; std::vector<int> ls(n); for(int j=0;j<n;j++) ss>>ls[j];
        if(n==1){ ub[ls[0]]=std::min(ub[ls[0]],std::max(0,cap)); continue; }
        Row w; w.mask=M128{}; for(int l:ls) SET(w.mask,l); w.cap=cap; w.size=n; w.k=k; rows.push_back(w); }
      else if(t=="S"){ fprintf(stderr,"S rows not supported\n"); return 2; }
      else if(t=="G"){ int ng; ss>>ng; for(int g=0;g<ng;g++){ std::getline(f,line); std::istringstream s2(line); std::vector<int> P(N); for(int l=0;l<N;l++) s2>>P[l]; G.push_back(P); } break; } } }
  for(int l=0;l<N;l++) if(ub[l]>8){ fprintf(stderr,"ub[%d]=%d > 8 unsupported\n",l,ub[l]); return 2; }
  if(ORDERF){ std::vector<int> ord; { std::ifstream f(ORDERF); int x; while(f>>x) ord.push_back(x); }
    if((int)ord.size()!=N){ fprintf(stderr,"order file size %zu != %d\n",ord.size(),N); return 2; }
    ORD=ord; std::vector<int> inv(N,-1); for(int i=0;i<N;i++){ if(inv[ord[i]]!=-1){ fprintf(stderr,"order not a permutation\n"); return 2; } inv[ord[i]]=i; }
    std::vector<int> v2(N); int u2[256]; for(int i=0;i<N;i++){ v2[i]=vecs[ord[i]]; u2[i]=ub[ord[i]]; } vecs=v2; for(int i=0;i<N;i++) ub[i]=u2[i];
    for(auto& w:rows){ M128 m=M128{}; for(int l=0;l<N;l++) if(TST(w.mask,l)) SET(m,inv[l]); w.mask=m; }
    for(auto& P:G){ std::vector<int> Q(N); for(int i=0;i<N;i++) Q[i]=inv[P[ord[i]]]; P=Q; } }
  // put the identity first
  for(size_t g=0;g<G.size();g++){ bool id=true; for(int l=0;l<N;l++) if(G[g][l]!=l){id=false;break;} if(id){ std::swap(G[0],G[g]); break; } }
  if(rows.size()>2000000000){ fprintf(stderr,"too many rows\n"); return 2; }
  SEPSKIP.assign(rows.size(),0); if(SEPSKIPF){ std::ifstream f(SEPSKIPF); long long x, n=0; while(f>>x){ if(x<0||x>=(long long)rows.size()){ fprintf(stderr,"bad sepskip row %lld\n",x); return 2; } SEPSKIP[x]=1; n++; } fprintf(stderr,"sepskip: %lld of %zu rows never separated\n",n,rows.size()); }
  inc.assign(N,{}); capv.assign(rows.size(),0);
  for(size_t r=0;r<rows.size();r++){ bool tr=(SKIPK.count(rows[r].k)==0); capv[r]=tr?rows[r].cap:255; if(!tr) untracked.push_back(r);
    for(int l=0;l<N;l++) if(TST(rows[r].mask,l)){ allInc[l].push_back(r); if(tr) inc[l].push_back(r); } }
  incO.assign(N+1,0); for(int l=0;l<N;l++){ incO[l]=incF.size(); for(int r:inc[l]) incF.push_back(r); } incO[N]=incF.size();
  for(size_t r=0;r<rows.size();r++) if(!SEPSKIP[r] && capv[r]!=255){ SID.push_back((uint32_t)r); for(int q=0;q<4;q++) SW[q].push_back(rows[r].mask.w[q]); SCAP.push_back(capv[r]); }
  if(VSEP) fprintf(stderr,"vsep: %zu separable rows\n",SID.size());
  for(size_t r=0;r<rows.size();r++) if(rows[r].k>=LOOKK && capv[r]<255) look.push_back(r);
  if(R>60){ fprintf(stderr,"R too large\n"); return 2; }
  if(CERTP && !SKIPK.empty()){ fprintf(stderr,"--cert does not support --skipk\n"); return 2; }
  auto certOpen=[&](const std::string& sfx)->FILE*{ if(!CERTP) return nullptr; std::string p=std::string(CERTP)+"_"+std::to_string((long long)getpid())+"_"+sfx+".bin";
    FILE* f=fopen(p.c_str(),"wb"); if(!f){ fprintf(stderr,"cannot open %s\n",p.c_str()); exit(2); } return f; };
  FILE* TOPF=nullptr; if(CERTP){ TOPF=certOpen("top"); fprintf(stderr,"cert: writing %s_%lld_*.bin\n",CERTP,(long long)getpid()); }
  suf[N]=M128{}; for(int p=N-1;p>=0;p--){ suf[p]=suf[p+1]; SET(suf[p],p); }
  long long ninc=0; for(int l=0;l<N;l++) ninc+=inc[l].size();
  fprintf(stderr,"R %d N %d rows %zu (avg incidences %.0f) lookahead rows %zu group %zu\n",R,N,rows.size(),(double)ninc/N,look.size(),G.size());
  if(CHECK){ std::map<int,int> lab; for(int l=0;l<N;l++) lab[vecs[l]]=l; std::ifstream f(CHECK); std::string line; int np=0,bad=0;
    while(std::getline(f,line)){ std::istringstream ss(line); std::vector<int> v; int x; while(ss>>x) v.push_back(x); if(v.empty()) continue;
      if((int)v.size()==R+1) v.erase(v.begin());
      std::vector<int> ls; for(int y:v) ls.push_back(lab.at(y)); std::vector<int> best;
      for(auto& P:G){ std::vector<int> im; for(int l:ls) im.push_back(P[l]); std::sort(im.begin(),im.end()); if(best.empty()||im<best) best=im; }
      State s; std::string why=s.walk(best); bool ok=why.empty();
      np++; if(!ok){ bad++; fprintf(stderr,"profile %d REJECTED: %s\n",np,why.c_str()); } }
    printf("checked %d profiles, rejected %d\n",np,bad); return bad?3:0; }
  // subtree test: canonical prefixes of length PREFD of the given profiles, each subtree enumerated completely
  if(PREFF){ std::map<int,int> lab; for(int l=0;l<N;l++) lab[vecs[l]]=l; std::ifstream f(PREFF); std::string line; std::set<std::vector<int>> pre;
    while(std::getline(f,line)){ std::istringstream ss(line); std::vector<int> v; int x; while(ss>>x) v.push_back(x); if(v.empty()) continue;
      if((int)v.size()==R+1) v.erase(v.begin());
      std::vector<int> ls; for(int y:v) ls.push_back(lab.at(y)); std::vector<int> best;
      for(auto& P:G){ std::vector<int> im; for(int l:ls) im.push_back(P[l]); std::sort(im.begin(),im.end()); if(best.empty()||im<best) best=im; }
      pre.insert(std::vector<int>(best.begin(),best.begin()+PREFD)); }
    OUT=fopen(outp,"a"); long long tn=0, tl=0; int k=0; auto t0=std::chrono::steady_clock::now();
    for(const auto& job:pre){ State s; for(size_t i=0;i<job.size();i++){ if(i>0) s.prep(job[i-1]); s.add(job[i]); } s.dfs(job.back());
      fprintf(stderr,"prefix %d nodes %lld leaves %lld\n",k++,s.visited,s.leaves); tn+=s.visited; tl+=s.leaves; }
    double el=std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count();
    fprintf(stderr,"PREFIXES %zu nodes %lld leaves %lld time %.1fs\n",pre.size(),tn,tl,el); lpReport(); if(OUT) fclose(OUT); return 0; }
  if(EST){ std::atomic<long long> done{0}; std::mutex em; double sN=0,sN2=0,sL=0; long long dh[64]={0};
    auto t0=std::chrono::steady_clock::now();
    std::vector<double> pdep(64,0);
    auto wk=[&](int tid){ std::mt19937_64 rng(seed*1000003+tid); State s; while(true){ long long i=done++; if(i>=EST) break; double n,lf; int dr; s.dive(rng,n,lf,dr);
        std::lock_guard<std::mutex> lk(em); sN+=n; sN2+=n*n; sL+=lf; dh[dr]++; }
      std::lock_guard<std::mutex> lk(em); for(int i=0;i<64;i++) pdep[i]+=s.perDepth[i]; };
    std::vector<std::thread> th; for(int i=0;i<TH;i++) th.emplace_back(wk,i); for(auto& t:th) t.join();
    double K=EST, mean=sN/K, sd=sqrt(std::max(0.0,sN2/K-mean*mean)/K);
    double el=std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count();
    printf("estimate nodes %.4g +- %.2g leaves %.4g (%.1fs)\ndepth hist:",mean,sd,sL/K,el); for(int d=0;d<=R;d++) printf(" %lld",dh[d]); printf("\nper-depth est:"); for(int d=0;d<=R;d++) printf(" %.2g",pdep[d]/K); printf("\n"); lpReport(); return 0; }
  OUT=fopen(outp,"a");
  if(FRONTIER_D<0 && !ROOTSF && !FRONTF){ State s; s.cert=(CERTP!=nullptr); auto t0=std::chrono::steady_clock::now(); s.cbegin('T',nullptr,0,255); s.dfs(0); s.cend(TOPF,s.visited); if(TOPF) fclose(TOPF);
    double el=std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count();
    fprintf(stderr,"DONE nodes %lld leaves %lld time %.1fs\n",s.visited,(long long)nleaf,el); for(int d=0;d<=R;d++) fprintf(stderr," %lld",s.depthCnt[d]); fprintf(stderr,"\n"); lpReport(); return 0; }
  auto t0=std::chrono::steady_clock::now();
  if(FRONTF){ std::map<int,int> lab; for(int l=0;l<N;l++) lab[vecs[l]]=l; std::ifstream f(FRONTF); if(!f){ fprintf(stderr,"no frontier file\n"); return 2; } std::string line; size_t nl=0; int mx=0;
    while(std::getline(f,line)){ if(line.empty()) continue; std::stringstream ss(line); long long ix; std::string t; ss>>ix>>t; if(ix!=(long long)nl){ fprintf(stderr,"frontier file: line %zu has index %lld\n",nl,ix); return 2; }
      std::vector<int> job; std::stringstream s2(t); std::string u; while(std::getline(s2,u,',')){ auto it=lab.find(std::stoi(u)); if(it==lab.end()){ fprintf(stderr,"frontier file: bad label %s\n",u.c_str()); return 2; } job.push_back(it->second); }
      if(job.empty()){ fprintf(stderr,"frontier file: empty job\n"); return 2; } mx=std::max(mx,(int)job.size()); frontier.push_back(job); nl++; }
    FRONTIER_D=mx; fprintf(stderr,"frontier loaded from %s: %zu jobs\n",FRONTF,frontier.size()); }
  else if(ROOTSF){ // jobs = union over the listed roots (one label prefix per line, comma-separated vec values) of the frontier REL levels below
    std::map<int,int> lab; for(int l=0;l<N;l++) lab[vecs[l]]=l; std::ifstream f(ROOTSF); std::string line; long long nr=0, npr=0;
    while(std::getline(f,line)){ if(line.empty()) continue; std::vector<int> root; { std::stringstream ss(line); std::string t; while(std::getline(ss,t,',')) root.push_back(lab.at(std::stoi(t))); }
      State s; nr++;
      if(CERTP){ // prefix replay without LP fixing (self-contained block); each label must be allowed where it is added
        for(size_t i=0;i<root.size();i++){ if(i>0) s.prep(root[i-1]); if(!TST(s.allowed,root[i])){ fprintf(stderr,"root %s: label %zu not allowed\n",line.c_str(),i); return 2; } s.add(root[i]); }
        FRONTIER_D=(int)root.size()+REL; s.cert=true; s.cbegin('T',root.data(),(int)root.size(),FRONTIER_D); long long v0=s.visited;
        collecting=true; s.dfs(root.back()); collecting=false; s.cend(TOPF,s.visited-v0); continue; }
      std::string why=s.walk(root);
      if(!why.empty()){ if(why.find("LP")!=std::string::npos){ npr++; continue; } fprintf(stderr,"root %s rejected on replay: %s\n",line.c_str(),why.c_str()); return 2; }
      FRONTIER_D=(int)root.size()+REL; collecting=true; s.dfs(root.back()); collecting=false; }
    fprintf(stderr,"roots %lld (LP-pruned on replay %lld): frontier %zu nodes (%d below each root), leaves above %lld\n",nr,npr,frontier.size(),REL,(long long)nleaf); }
  else if(ROOTS){ // jobs = the depth-FRONTIER_D frontier of the subtree of the node with the given label prefix (vec values)
    std::map<int,int> lab; for(int l=0;l<N;l++) lab[vecs[l]]=l; std::vector<int> root; { std::stringstream ss(ROOTS); std::string t; while(std::getline(ss,t,',')) root.push_back(lab.at(std::stoi(t))); }
    if(root.empty() || FRONTIER_D<=(int)root.size()){ fprintf(stderr,"--root needs --frontier deeper than the root\n"); return 2; }
    State s; std::string why;
    if(CERTP){ for(size_t i=0;i<root.size();i++){ if(i>0) s.prep(root[i-1]); if(!TST(s.allowed,root[i])){ why="label not allowed"; break; } s.add(root[i]); } }
    else why=s.walk(root); // replays the root with every check of dfs
    if(!why.empty()){ if(why.find("LP")!=std::string::npos){ fprintf(stderr,"root pruned on replay (%s): subtree has no solution\nDONE frontier run leaves 0\n",why.c_str()); return 0; }
      fprintf(stderr,"root rejected on replay: %s\n",why.c_str()); return 2; }
    s.cert=(CERTP!=nullptr); s.cbegin('T',root.data(),(int)root.size(),FRONTIER_D); long long v0=s.visited;
    collecting=true; s.dfs(root.back()); collecting=false; s.cend(TOPF,s.visited-v0);
    fprintf(stderr,"root %s: frontier depth %d: %zu nodes, leaves above %lld\n",ROOTS,FRONTIER_D,frontier.size(),(long long)nleaf); }
  else if(SUBD>0){ // jobs = the depth-FRONTIER_D frontier of the subtree of node #SUBIX of the depth-SUBD frontier
    if(FRONTIER_D<=SUBD){ fprintf(stderr,"--subroot needs --frontier deeper than %d\n",SUBD); return 2; }
    int D1=FRONTIER_D; FRONTIER_D=SUBD; { State s; collecting=true; s.dfs(0); collecting=false; }
    if(SUBIX<0 || SUBIX>=(long long)frontier.size()){ fprintf(stderr,"bad subroot index %lld of %zu\n",SUBIX,frontier.size()); return 2; }
    std::vector<int> root=frontier[SUBIX]; size_t nsub=frontier.size(); frontier.clear(); FRONTIER_D=D1; long long l0=nleaf;
    { State s; for(size_t i=0;i<root.size();i++){ if(i>0) s.prep(root[i-1]); s.add(root[i]); }
      s.cert=(CERTP!=nullptr); s.cbegin('T',root.data(),(int)root.size(),FRONTIER_D); long long v0=s.visited;
      collecting=true; s.dfs(root.back()); collecting=false; s.cend(TOPF,s.visited-v0); }
    fprintf(stderr,"subroot %lld of %zu at depth %d (labels",SUBIX,nsub,SUBD); for(int l:root) fprintf(stderr," %d",vecs[l]);
    fprintf(stderr,"): frontier depth %d: %zu nodes, leaves above %lld\n",FRONTIER_D,frontier.size(),(long long)nleaf-l0); }
  else { State s; s.cert=(CERTP!=nullptr); s.cbegin('T',nullptr,0,FRONTIER_D); collecting=true; s.dfs(0); collecting=false; s.cend(TOPF,s.visited); fprintf(stderr,"frontier depth %d: %zu nodes, leaves above %lld\n",FRONTIER_D,frontier.size(),(long long)nleaf); }
  if(TOPF){ fclose(TOPF); TOPF=nullptr; }
  { unsigned long long h=1469598103934665603ULL; for(auto& j:frontier){ for(int l:j){ h^=(unsigned long long)(vecs[l]+1); h*=1099511628211ULL; } h^=0xFFFFULL; h*=1099511628211ULL; } fprintf(stderr,"frontier hash %016llx (%zu nodes)\n",h,frontier.size()); }
  if(getenv("DUMPFRONTIER")){ FILE* df=fopen(getenv("DUMPFRONTIER"),"w"); for(size_t i=0;i<frontier.size();i++){ fprintf(df,"%zu",i); for(size_t k=0;k<frontier[i].size();k++) fprintf(df,"%c%d",k?',':' ',vecs[frontier[i][k]]); fprintf(df,"\n"); } fclose(df);
    if(getenv("DUMPONLY")) return 0; }
  std::vector<int> order(frontier.size()); std::iota(order.begin(),order.end(),0); std::mt19937_64 rng(seed); std::shuffle(order.begin(),order.end(),rng);
  if(JOBSF){ order.clear(); std::ifstream f(JOBSF); long long x; while(f>>x){ if(x<0||x>=(long long)frontier.size()){ fprintf(stderr,"bad job %lld\n",x); return 2; } order.push_back((int)x); } }
  std::vector<char> doneIdx(frontier.size(),0); long long prevDone=0; double prevNodes=0;
  if(statep){ FILE* f=fopen(statep,"r"); if(f){ long long ix,nn,lf; double sec; while(fscanf(f,"%lld %lld %lld %lf",&ix,&nn,&lf,&sec)==4){ if(!doneIdx[ix]){ doneIdx[ix]=1; prevDone++; prevNodes+=nn; } } fclose(f); }
    fprintf(stderr,"resumed %lld done\n",prevDone); }
  if(HEAVYF){ std::ifstream hf(HEAVYF); if(hf){ // jobs already recorded heavy (by an earlier run) are left to the split runs
      std::map<int,int> lab; for(int l=0;l<N;l++) lab[vecs[l]]=l; std::map<std::vector<int>,size_t> idx; for(size_t i=0;i<frontier.size();i++) idx[frontier[i]]=i;
      std::string line; long long nsk=0;
      while(std::getline(hf,line)){ if(line.empty()) continue; std::vector<int> pv; std::stringstream ss(line); std::string t; while(std::getline(ss,t,',')) pv.push_back(lab.at(std::stoi(t)));
        auto it=idx.find(pv); if(it!=idx.end() && !doneIdx[it->second]){ doneIdx[it->second]=2; nsk++; } }
      fprintf(stderr,"skipping %lld jobs already recorded heavy in %s\n",nsk,HEAVYF); } }
  if(DONEPF){ std::ifstream df(DONEPF); if(!df){ fprintf(stderr,"no doneprefixes file\n"); return 2; }   // jobs finished (with traces) by another run
    std::map<int,int> lab; for(int l=0;l<N;l++) lab[vecs[l]]=l; std::map<std::vector<int>,size_t> idx; for(size_t i=0;i<frontier.size();i++) idx[frontier[i]]=i;
    std::string line; long long nsk=0, nl=0;
    while(std::getline(df,line)){ if(line.empty()) continue; nl++; std::vector<int> pv; std::stringstream ss(line); std::string t; while(std::getline(ss,t,',')) pv.push_back(lab.at(std::stoi(t)));
      auto it=idx.find(pv); if(it!=idx.end() && !doneIdx[it->second]){ doneIdx[it->second]=3; nsk++; } }
    fprintf(stderr,"skipping %lld jobs done elsewhere (%lld prefixes in %s)\n",nsk,nl,DONEPF); }
  FILE* HF=HEAVYF?fopen(HEAVYF,"a"):nullptr; long long nheavy=0; // jobs over the node budget: not done, prefix written to HF
  FILE* SF=statep?fopen(statep,"a"):nullptr; std::mutex rm; std::atomic<size_t> nextI{0}; long long ndone=prevDone; double sumN=prevNodes; std::vector<double> sizes; std::atomic<bool> fin{false};
  std::vector<long long> dh(64,0);
  std::vector<FILE*> CF(TH,nullptr); for(int t=0;t<TH;t++) CF[t]=certOpen("t"+std::to_string(t));
  // lineenum9s: per-job bookkeeping for donated pieces
  BUDGET_G=BUDGET; const size_t NF=frontier.size(); std::unique_ptr<std::atomic<int>[]> outst(new std::atomic<int>[NF]); for(size_t i=0;i<NF;i++) outst[i]=0; gOut=outst.get();
  std::vector<char> rootDone(NF,0); std::vector<long long> jnodes(NF,0), jleaves(NF,0); std::vector<std::chrono::steady_clock::time_point> jt0(NF);
  int activeR=0, activeP=0; bool fdone=false;
  auto writeState=[&](int ix){ double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-jt0[ix]).count();   // caller holds rm
    ndone++; sumN+=jnodes[ix]; sizes.push_back(jnodes[ix]); if(SF){ fprintf(SF,"%d %lld %lld %.3f\n",ix,jnodes[ix],jleaves[ix],sec); fflush(SF); } };
  auto checkFin=[&](){ if(nextI.load()>=order.size() && PQ.empty() && activeR==0 && activeP==0 && !fdone){ fdone=true; qcv.notify_all(); } };   // caller holds qmu
  auto worker=[&](int tid){ State s; s.cert=(CERTP!=nullptr); struct Fin{ State& s; std::vector<long long>& dh; std::mutex& m; ~Fin(){ std::lock_guard<std::mutex> lk(m); for(int i=0;i<64;i++) dh[i]+=s.depthCnt[i]; } } fin{s,dh,rm};
    while(true){ size_t k=nextI++;
      if(k<order.size() && !(MAXJOBS>=0 && (long long)k>=MAXJOBS)){ int ix=order[k]; if(doneIdx[ix]) continue;
        { std::lock_guard<std::mutex> lq(qmu); activeR++; }
        { std::lock_guard<std::mutex> lk(rm); jt0[ix]=std::chrono::steady_clock::now(); }
        long long v0=s.visited, l0=s.leaves; const auto& job=frontier[ix]; s.curJob=ix;
        for(size_t i=0;i<job.size();i++){ if(i>0) s.prep(job[i-1]); s.add(job[i]); }
        s.aborted=false; s.budgetEnd=BUDGET>0?s.visited+BUDGET:LLONG_MAX;
        s.cbegin('J',job.data(),(int)job.size(),0);
        s.dfs(job.back()); for(int i=(int)job.size()-1;i>=0;i--) s.undo(job[i]);
        long long nn=s.visited-v0;
        if(s.aborted){ s.aborted=false; s.cb.clear(); { std::lock_guard<std::mutex> lk(rm); nheavy++; if(HF){ for(size_t i=0;i<job.size();i++) fprintf(HF,"%d%c",vecs[job[i]],i+1==job.size()?'\n':','); fflush(HF); } }
          { std::lock_guard<std::mutex> lq(qmu); activeR--; checkFin(); } continue; }
        s.cend(CF[tid],nn);
        { std::lock_guard<std::mutex> lk(rm); jnodes[ix]+=nn; jleaves[ix]+=s.leaves-l0; rootDone[ix]=1; if(outst[ix].load()==0) writeState(ix); }
        { std::lock_guard<std::mutex> lq(qmu); activeR--; checkFin(); }
        continue; }
      // job list exhausted: run donated pieces until every job is finished
      Piece pc;
      { std::unique_lock<std::mutex> lq(qmu); checkFin(); idleN++; qcv.wait(lq,[&]{ return !PQ.empty() || fdone; }); idleN--;
        if(PQ.empty() && fdone) break; pc=std::move(PQ.front()); PQ.pop_front(); activeP++; }
      int ix=pc.ix; s.curJob=ix; long long v0=s.visited, l0=s.leaves; const auto& sq=pc.seq;
      for(size_t i=0;i<sq.size();i++){ if(i>0) s.prep(sq[i-1]); s.add(sq[i]); }
      s.allowed=pc.a; s.r2=pc.b; s.r3=pc.c; s.r4=pc.e; s.r5=pc.m5; s.r6=pc.m6; s.r7=pc.m7; s.r8=pc.m8;   // the donor's state includes LP fixes of its ancestors
      s.aborted=false; s.budgetEnd=LLONG_MAX; s.dfs(sq.back()); for(int i=(int)sq.size()-1;i>=0;i--) s.undo(sq[i]);
      { std::lock_guard<std::mutex> lk(rm); jnodes[ix]+=s.visited-v0; jleaves[ix]+=s.leaves-l0; if(--outst[ix]==0 && rootDone[ix]) writeState(ix); }
      { std::lock_guard<std::mutex> lq(qmu); activeP--; checkFin(); } } };
  auto report=[&](bool f){ std::lock_guard<std::mutex> lk(rm); double el=std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count();
    double F=frontier.size(), S=std::max<long long>(1,ndone), mean=sumN/S; double rate=(sumN-prevNodes)/std::max(1.0,el);
    fprintf(stderr,"%st=%.0fs done %lld/%zu (%.3f%%) nodes %.4g mean %.4g EST %.4g rate %.3g n/s ETA %.3g h leaves %lld heavy %lld\n",f?"FINAL ":"",el,ndone,frontier.size(),100.0*ndone/F,sumN,mean,F*mean,rate,(F-ndone)*mean/std::max(1.0,rate)/3600,(long long)nleaf,nheavy); };
  std::thread mon([&](){ while(!fin){ for(int i=0;i<60&&!fin;i++) std::this_thread::sleep_for(std::chrono::seconds(1)); if(!fin) report(false); } });
  std::vector<std::thread> th; for(int i=0;i<TH;i++) th.emplace_back(worker,i); for(auto& t:th) t.join(); fin=true; mon.join(); report(true);
  if(SF) fclose(SF); if(OUT) fclose(OUT); if(HF) fclose(HF); for(FILE* f:CF) if(f) fclose(f);
  fprintf(stderr,"depth hist:"); for(int i=0;i<=R;i++) fprintf(stderr," %lld",dh[i]); fprintf(stderr,"\n");
  lpReport(); fprintf(stderr,"DONE frontier run leaves %lld heavy %lld\n",(long long)nleaf,nheavy);
}
