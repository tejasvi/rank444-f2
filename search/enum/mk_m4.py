#!/usr/bin/env python3
"""Derive lineenum9m4.cc (label caps up to 4: a fourth residual mask r4) from lineenum9vr.cc by exact, counted text
replacements.  Every replacement must match the expected number of times, else nothing is written.
For IPs whose label caps are all <= 3, r4 stays empty, so search, traces and node counts must equal lineenum9vr's.
usage: mk_m4.py SRC DST
"""
import sys
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
R = [
 ("struct Piece { int ix; std::vector<int> seq; M128 a,b,c; /* allowed,r2,r3 at the donation point (carry LP fixes) */ };",
  "struct Piece { int ix; std::vector<int> seq; M128 a,b,c,e; /* allowed,r2,r3,r4 at the donation point (carry LP fixes) */ };", 1),
 ("static inline int topk64(u64 x1,u64 x2,u64 x3,int k){ // max p with popcount(x1>>p)+popcount(x2>>p)+popcount(x3>>p) >= k, or -1\n"
  "  if(__builtin_popcountll(x1)+__builtin_popcountll(x2)+__builtin_popcountll(x3)<k) return -1;\n"
  "  int lo=0,hi=63; while(lo<hi){ int mid=(lo+hi+1)>>1; if(__builtin_popcountll(x1>>mid)+__builtin_popcountll(x2>>mid)+__builtin_popcountll(x3>>mid)>=k) lo=mid; else hi=mid-1; } return lo; }",
  "static inline int topk64(u64 x1,u64 x2,u64 x3,u64 x4,int k){ // max p with popcount(x1>>p)+..+popcount(x4>>p) >= k, or -1\n"
  "  if(__builtin_popcountll(x1)+__builtin_popcountll(x2)+__builtin_popcountll(x3)+__builtin_popcountll(x4)<k) return -1;\n"
  "  int lo=0,hi=63; while(lo<hi){ int mid=(lo+hi+1)>>1; if(__builtin_popcountll(x1>>mid)+__builtin_popcountll(x2>>mid)+__builtin_popcountll(x3>>mid)+__builtin_popcountll(x4>>mid)>=k) lo=mid; else hi=mid-1; } return lo; }", 1),
 ("static inline int topk(M128 B1,M128 B2,M128 B3,int k){ if(k<=0) return 255;",
  "static inline int topk(M128 B1,M128 B2,M128 B3,M128 B4,int k){ if(k<=0) return 255;", 1),
 ("int c=__builtin_popcountll(B1.w[q])+__builtin_popcountll(B2.w[q])+__builtin_popcountll(B3.w[q]);",
  "int c=__builtin_popcountll(B1.w[q])+__builtin_popcountll(B2.w[q])+__builtin_popcountll(B3.w[q])+__builtin_popcountll(B4.w[q]);", 1),
 ("if(c>=k) return 64*q+topk64(B1.w[q],B2.w[q],B3.w[q],k); k-=c; }",
  "if(c>=k) return 64*q+topk64(B1.w[q],B2.w[q],B3.w[q],B4.w[q],k); k-=c; }", 1),
 ("M128 allowed,r2,r3; M128 stA[64],st2[64],st3[64];", "M128 allowed,r2,r3,r4; M128 stA[64],st2[64],st3[64],st4[64];", 1),
 ("allowed=M128{}; r2=M128{}; r3=M128{};", "allowed=M128{}; r2=M128{}; r3=M128{}; r4=M128{};", 1),
 ("if(ub[l]>=3) SET(r3,l); }", "if(ub[l]>=3) SET(r3,l); if(ub[l]>=4) SET(r4,l); }", 1),
 ("long long certB(const std::vector<uint32_t>& rs,const std::vector<long long>& Y,M128 S1,M128 S2,M128 S3,int pos){",
  "long long certB(const std::vector<uint32_t>& rs,const std::vector<long long>& Y,M128 S1,M128 S2,M128 S3,M128 S4,int pos){", 1),
 ("B+=(long long)(1+TST(S2,l)+TST(S3,l))*(SC-T[l]);", "B+=(long long)(1+TST(S2,l)+TST(S3,l)+TST(S4,l))*(SC-T[l]);", 2),
 ("M128 S1=AND(allowed,suf[pos]), S2=AND(r2,suf[pos]), S3=AND(r3,suf[pos]);",
  "M128 S1=AND(allowed,suf[pos]), S2=AND(r2,suf[pos]), S3=AND(r3,suf[pos]), S4=AND(r4,suf[pos]);", 2),
 ("int u=1+TST(S2,l)+TST(S3,l);", "int u=1+TST(S2,l)+TST(S3,l)+TST(S4,l);", 1),
 ("if(km<=0){ CLR(allowed,l); CLR(r2,l); CLR(r3,l); } else if(km==1){ CLR(r2,l); CLR(r3,l); } else CLR(r3,l); } }",
  "if(km<=0){ CLR(allowed,l); CLR(r2,l); CLR(r3,l); CLR(r4,l); } else if(km==1){ CLR(r2,l); CLR(r3,l); CLR(r4,l); } else if(km==2){ CLR(r3,l); CLR(r4,l); } else CLR(r4,l); } }", 1),
 ("int lpCustom(int pos,int rem,M128 S1,M128 S2,M128 S3,int nc,", "int lpCustom(int pos,int rem,M128 S1,M128 S2,M128 S3,M128 S4,int nc,", 1),
 ("certB(dsup[d],dY[d],S1,S2,S3,pos)", "certB(dsup[d],dY[d],S1,S2,S3,S4,pos)", 2),
 ("M128 sup2=M128{}, sup3=M128{};", "M128 sup2=M128{}, sup3=M128{}, sup4=M128{};", 1),
 ("if(plX[j]>2+1e-9) SET(sup3,l); }", "if(plX[j]>2+1e-9) SET(sup3,l); if(plX[j]>3+1e-9) SET(sup4,l); }", 1),
 ("for(const M128* sp:{&sup2,&sup3}) if(NZ(*sp))", "for(const M128* sp:{&sup2,&sup3,&sup4}) if(NZ(*sp))", 1),
 ("if(PC(ms)+PC(AND(ms,sup2))+PC(AND(ms,sup3))<=b) continue;", "if(PC(ms)+PC(AND(ms,sup2))+PC(AND(ms,sup3))+PC(AND(ms,sup4))<=b) continue;", 1),
 ("certB(dsup[d-1],dY[d-1],S1,S2,S3,pos)", "certB(dsup[d-1],dY[d-1],S1,S2,S3,S4,pos)", 1),
 ("certB(kS[d][j],kY[d][j],S1,S2,S3,pos)", "certB(kS[d][j],kY[d][j],S1,S2,S3,S4,pos)", 1),
 ("cuI[nc]=1+TST(S2,l)+TST(S3,l);", "cuI[nc]=1+TST(S2,l)+TST(S3,l)+TST(S4,l);", 1),
 ("return bres(r) < PC(AND(m,S1))+PC(AND(m,S2))+PC(AND(m,S3)); };", "return bres(r) < PC(AND(m,S1))+PC(AND(m,S2))+PC(AND(m,S3))+PC(AND(m,S4)); };", 1),
 ("int st=lpCustom(pos,rem,S1,S2,S3,nc,", "int st=lpCustom(pos,rem,S1,S2,S3,S4,nc,", 1),
 ("inline void add(int l){ stA[d]=allowed; st2[d]=r2; st3[d]=r3;", "inline void add(int l){ stA[d]=allowed; st2[d]=r2; st3[d]=r3; st4[d]=r4;", 1),
 ("if(res<=0) CLR(allowed,l); if(res<2) CLR(r2,l); if(res<3) CLR(r3,l);", "if(res<=0) CLR(allowed,l); if(res<2) CLR(r2,l); if(res<3) CLR(r3,l); if(res<4) CLR(r4,l);", 1),
 ("r2=AND(r2,allowed); r3=AND(r3,allowed); }", "r2=AND(r2,allowed); r3=AND(r3,allowed); r4=AND(r4,allowed); }", 1),
 ("allowed=stA[d]; r2=st2[d]; r3=st3[d]; }", "allowed=stA[d]; r2=st2[d]; r3=st3[d]; r4=st4[d]; }", 1),
 ("return PC(A)+PC(AND(r2,suf[l]))+PC(AND(r3,suf[l])); }", "return PC(A)+PC(AND(r2,suf[l]))+PC(AND(r3,suf[l]))+PC(AND(r4,suf[l])); }", 1),
 ("M128 A=AND(allowed,suf[l]), A2=AND(r2,suf[l]), A3=AND(r3,suf[l]);\n    int wa=PC(A)+PC(A2)+PC(A3);",
  "M128 A=AND(allowed,suf[l]), A2=AND(r2,suf[l]), A3=AND(r3,suf[l]), A4=AND(r4,suf[l]);\n    int wa=PC(A)+PC(A2)+PC(A3)+PC(A4);", 1),
 ("if(PC(ANDN(A,m))+PC(ANDN(A2,m))+PC(ANDN(A3,m))<need){ postRow=r; return false; } }",
  "if(PC(ANDN(A,m))+PC(ANDN(A2,m))+PC(ANDN(A3,m))+PC(ANDN(A4,m))<need){ postRow=r; return false; } }", 1),
 ("M128 A=AND(allowed,suf[pos]), A2=AND(r2,suf[pos]), A3=AND(r3,suf[pos]);\n    int lmax=topk(A,A2,A3,rem);",
  "M128 A=AND(allowed,suf[pos]), A2=AND(r2,suf[pos]), A3=AND(r3,suf[pos]), A4=AND(r4,suf[pos]);\n    int lmax=topk(A,A2,A3,A4,rem);", 1),
 ("M128 L1=AND(A,suf[lmax]), L2=AND(A2,suf[lmax]), L3=AND(A3,suf[lmax]);", "M128 L1=AND(A,suf[lmax]), L2=AND(A2,suf[lmax]), L3=AND(A3,suf[lmax]), L4=AND(A4,suf[lmax]);", 1),
 ("int w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m)); if(w>=need) return false;", "int w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m)); if(w>=need) return false;", 1),
 ("lmax=topk(ANDN(A,m),ANDN(A2,m),ANDN(A3,m),need); prepRow=r; if(lmax>=pos){ L1=AND(A,suf[lmax]); L2=AND(A2,suf[lmax]); L3=AND(A3,suf[lmax]); }",
  "lmax=topk(ANDN(A,m),ANDN(A2,m),ANDN(A3,m),ANDN(A4,m),need); prepRow=r; if(lmax>=pos){ L1=AND(A,suf[lmax]); L2=AND(A2,suf[lmax]); L3=AND(A3,suf[lmax]); L4=AND(A4,suf[lmax]); }", 1),
 ("int w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m));\n", "int w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m));\n", 1),
 ("if(w<need){ lmax=topk(ANDN(A,m),ANDN(A2,m),ANDN(A3,m),need); prepRow=r; if(lmax<pos) return -1;",
  "if(w<need){ lmax=topk(ANDN(A,m),ANDN(A2,m),ANDN(A3,m),ANDN(A4,m),need); prepRow=r; if(lmax<pos) return -1;", 1),
 ("L1=AND(A,suf[lmax]); L2=AND(A2,suf[lmax]); L3=AND(A3,suf[lmax]); w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m));",
  "L1=AND(A,suf[lmax]); L2=AND(A2,suf[lmax]); L3=AND(A3,suf[lmax]); L4=AND(A4,suf[lmax]); w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m));", 1),
 ("PQ.push_back({curJob,std::vector<int>(seq,seq+d),allowed,r2,r3});", "PQ.push_back({curJob,std::vector<int>(seq,seq+d),allowed,r2,r3,r4});", 1),
 ('if(ub[l]>3){ fprintf(stderr,"ub[%d]=%d > 3 unsupported\\n",l,ub[l]); return 2; }', 'if(ub[l]>4){ fprintf(stderr,"ub[%d]=%d > 4 unsupported\\n",l,ub[l]); return 2; }', 1),
 ("s.allowed=pc.a; s.r2=pc.b; s.r3=pc.c;", "s.allowed=pc.a; s.r2=pc.b; s.r3=pc.c; s.r4=pc.e;", 1),
]
bad = []
for old, new, k in R:
    c = s.count(old)
    if c != k:
        bad.append((c, k, old[:90]))
    s = s.replace(old, new)
if bad:
    for b in bad:
        print("MISMATCH", b)
    sys.exit(1)
s = s.replace("// lineenum9x: lineenum9w + work stealing", "// lineenum9m4: lineenum9vr with label caps up to 4 (a fourth residual mask r4; derived by mk_m4.py).\n// lineenum9x: lineenum9w + work stealing", 1)
open(dst, "w").write(s)
left = [ln for ln in s.split("\n") if ("S3" in ln or "r3" in ln or "A3" in ln or "L3" in ln or "sup3" in ln) and not any(t in ln for t in ("S4", "r4", "A4", "L4", "sup4"))]
print(f"wrote {dst}: {len(R)} replacement kinds; lines with a 3-mask and no 4-mask: {len(left)}")
for ln in left:
    print("  CHECK:", ln.strip()[:160])
