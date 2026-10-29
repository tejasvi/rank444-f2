#!/usr/bin/env python3
"""Derive lineenum9m8.cc (label caps up to 8: residual masks r5..r8) from lineenum9m4.cc by exact, counted text replacements.
Every replacement must match the expected number of times, else nothing is written.  For IPs whose label caps are all <= 4
the masks r5..r8 stay empty, so search, traces and node counts must equal lineenum9m4's (and lineenum9vr's for caps <= 3).
usage: mk_m8.py SRC(lineenum9m4.cc) DST
"""
import sys
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
K = (5, 6, 7, 8)
def seq(fmt, sep=""):
    return sep.join(fmt.format(k=k) for k in K)
R = [
 ("struct Piece { int ix; std::vector<int> seq; M128 a,b,c,e; /* allowed,r2,r3,r4 at the donation point (carry LP fixes) */ };",
  "struct Piece { int ix; std::vector<int> seq; M128 a,b,c,e,m5,m6,m7,m8; /* allowed,r2..r8 at the donation point (carry LP fixes) */ };", 1),
 ("static inline int topk64(u64 x1,u64 x2,u64 x3,u64 x4,int k){ // max p with popcount(x1>>p)+..+popcount(x4>>p) >= k, or -1\n"
  "  if(__builtin_popcountll(x1)+__builtin_popcountll(x2)+__builtin_popcountll(x3)+__builtin_popcountll(x4)<k) return -1;\n"
  "  int lo=0,hi=63; while(lo<hi){ int mid=(lo+hi+1)>>1; if(__builtin_popcountll(x1>>mid)+__builtin_popcountll(x2>>mid)+__builtin_popcountll(x3>>mid)+__builtin_popcountll(x4>>mid)>=k) lo=mid; else hi=mid-1; } return lo; }",
  "static inline int topk64(u64 x1,u64 x2,u64 x3,u64 x4," + seq("u64 x{k},") + "int k){ // max p with popcount(x1>>p)+..+popcount(x8>>p) >= k, or -1\n"
  "  if(__builtin_popcountll(x1)+__builtin_popcountll(x2)+__builtin_popcountll(x3)+__builtin_popcountll(x4)" + seq("+__builtin_popcountll(x{k})") + "<k) return -1;\n"
  "  int lo=0,hi=63; while(lo<hi){ int mid=(lo+hi+1)>>1; if(__builtin_popcountll(x1>>mid)+__builtin_popcountll(x2>>mid)+__builtin_popcountll(x3>>mid)+__builtin_popcountll(x4>>mid)" + seq("+__builtin_popcountll(x{k}>>mid)") + ">=k) lo=mid; else hi=mid-1; } return lo; }", 1),
 ("static inline int topk(M128 B1,M128 B2,M128 B3,M128 B4,int k){ if(k<=0) return 255;",
  "static inline int topk(M128 B1,M128 B2,M128 B3,M128 B4," + seq("M128 B{k},") + "int k){ if(k<=0) return 255;", 1),
 ("int c=__builtin_popcountll(B1.w[q])+__builtin_popcountll(B2.w[q])+__builtin_popcountll(B3.w[q])+__builtin_popcountll(B4.w[q]);",
  "int c=__builtin_popcountll(B1.w[q])+__builtin_popcountll(B2.w[q])+__builtin_popcountll(B3.w[q])+__builtin_popcountll(B4.w[q])" + seq("+__builtin_popcountll(B{k}.w[q])") + ";", 1),
 ("if(c>=k) return 64*q+topk64(B1.w[q],B2.w[q],B3.w[q],B4.w[q],k); k-=c; }",
  "if(c>=k) return 64*q+topk64(B1.w[q],B2.w[q],B3.w[q],B4.w[q]," + seq("B{k}.w[q],") + "k); k-=c; }", 1),
 ("M128 allowed,r2,r3,r4; M128 stA[64],st2[64],st3[64],st4[64];",
  "M128 allowed,r2,r3,r4" + seq(",r{k}") + "; M128 stA[64],st2[64],st3[64],st4[64]" + seq(",st{k}[64]") + ";", 1),
 ("allowed=M128{}; r2=M128{}; r3=M128{}; r4=M128{};", "allowed=M128{}; r2=M128{}; r3=M128{}; r4=M128{};" + seq(" r{k}=M128{{}};"), 1),
 ("if(ub[l]>=4) SET(r4,l); }", "if(ub[l]>=4) SET(r4,l);" + seq(" if(ub[l]>={k}) SET(r{k},l);") + " }", 1),
 ("M128 S1,M128 S2,M128 S3,M128 S4,int pos){", "M128 S1,M128 S2,M128 S3,M128 S4," + seq("M128 S{k},") + "int pos){", 1),
 ("B+=(long long)(1+TST(S2,l)+TST(S3,l)+TST(S4,l))*(SC-T[l]);", "B+=(long long)(1+TST(S2,l)+TST(S3,l)+TST(S4,l)" + seq("+TST(S{k},l)") + ")*(SC-T[l]);", 2),
 ("M128 S1=AND(allowed,suf[pos]), S2=AND(r2,suf[pos]), S3=AND(r3,suf[pos]), S4=AND(r4,suf[pos]);",
  "M128 S1=AND(allowed,suf[pos]), S2=AND(r2,suf[pos]), S3=AND(r3,suf[pos]), S4=AND(r4,suf[pos])" + seq(", S{k}=AND(r{k},suf[pos])") + ";", 2),
 ("int u=1+TST(S2,l)+TST(S3,l)+TST(S4,l);", "int u=1+TST(S2,l)+TST(S3,l)+TST(S4,l)" + seq("+TST(S{k},l)") + ";", 1),
 ("if(km<=0){ CLR(allowed,l); CLR(r2,l); CLR(r3,l); CLR(r4,l); } else if(km==1){ CLR(r2,l); CLR(r3,l); CLR(r4,l); } else if(km==2){ CLR(r3,l); CLR(r4,l); } else CLR(r4,l); } }",
  "if(km<=0) CLR(allowed,l); if(km<=1) CLR(r2,l); if(km<=2) CLR(r3,l); if(km<=3) CLR(r4,l);" + seq(" if(km<={km}) CLR(r{k},l);".replace("{km}", "{k}-1")) + " } }", 1),
 ("int lpCustom(int pos,int rem,M128 S1,M128 S2,M128 S3,M128 S4,int nc,", "int lpCustom(int pos,int rem,M128 S1,M128 S2,M128 S3,M128 S4," + seq("M128 S{k},") + "int nc,", 1),
 ("certB(dsup[d],dY[d],S1,S2,S3,S4,pos)", "certB(dsup[d],dY[d],S1,S2,S3,S4" + seq(",S{k}") + ",pos)", 2),
 ("M128 sup2=M128{}, sup3=M128{}, sup4=M128{};", "M128 sup2=M128{}, sup3=M128{}, sup4=M128{}" + seq(", sup{k}=M128{{}}") + ";", 1),
 ("if(plX[j]>3+1e-9) SET(sup4,l); }", "if(plX[j]>3+1e-9) SET(sup4,l);" + seq(" if(plX[j]>{k}-1+1e-9) SET(sup{k},l);") + " }", 1),
 ("for(const M128* sp:{&sup2,&sup3,&sup4}) if(NZ(*sp))", "for(const M128* sp:{&sup2,&sup3,&sup4" + seq(",&sup{k}") + "}) if(NZ(*sp))", 1),
 ("if(PC(ms)+PC(AND(ms,sup2))+PC(AND(ms,sup3))+PC(AND(ms,sup4))<=b) continue;", "if(PC(ms)+PC(AND(ms,sup2))+PC(AND(ms,sup3))+PC(AND(ms,sup4))" + seq("+PC(AND(ms,sup{k}))") + "<=b) continue;", 1),
 ("certB(dsup[d-1],dY[d-1],S1,S2,S3,S4,pos)", "certB(dsup[d-1],dY[d-1],S1,S2,S3,S4" + seq(",S{k}") + ",pos)", 1),
 ("certB(kS[d][j],kY[d][j],S1,S2,S3,S4,pos)", "certB(kS[d][j],kY[d][j],S1,S2,S3,S4" + seq(",S{k}") + ",pos)", 1),
 ("cuI[nc]=1+TST(S2,l)+TST(S3,l)+TST(S4,l);", "cuI[nc]=1+TST(S2,l)+TST(S3,l)+TST(S4,l)" + seq("+TST(S{k},l)") + ";", 1),
 ("return bres(r) < PC(AND(m,S1))+PC(AND(m,S2))+PC(AND(m,S3))+PC(AND(m,S4)); };", "return bres(r) < PC(AND(m,S1))+PC(AND(m,S2))+PC(AND(m,S3))+PC(AND(m,S4))" + seq("+PC(AND(m,S{k}))") + "; };", 1),
 ("int st=lpCustom(pos,rem,S1,S2,S3,S4,nc,", "int st=lpCustom(pos,rem,S1,S2,S3,S4" + seq(",S{k}") + ",nc,", 1),
 ("inline void add(int l){ stA[d]=allowed; st2[d]=r2; st3[d]=r3; st4[d]=r4;", "inline void add(int l){ stA[d]=allowed; st2[d]=r2; st3[d]=r3; st4[d]=r4;" + seq(" st{k}[d]=r{k};"), 1),
 ("if(res<=0) CLR(allowed,l); if(res<2) CLR(r2,l); if(res<3) CLR(r3,l); if(res<4) CLR(r4,l);", "if(res<=0) CLR(allowed,l); if(res<2) CLR(r2,l); if(res<3) CLR(r3,l); if(res<4) CLR(r4,l);" + seq(" if(res<{k}) CLR(r{k},l);"), 1),
 ("r2=AND(r2,allowed); r3=AND(r3,allowed); r4=AND(r4,allowed); }", "r2=AND(r2,allowed); r3=AND(r3,allowed); r4=AND(r4,allowed);" + seq(" r{k}=AND(r{k},allowed);") + " }", 1),
 ("allowed=stA[d]; r2=st2[d]; r3=st3[d]; r4=st4[d]; }", "allowed=stA[d]; r2=st2[d]; r3=st3[d]; r4=st4[d];" + seq(" r{k}=st{k}[d];") + " }", 1),
 ("return PC(A)+PC(AND(r2,suf[l]))+PC(AND(r3,suf[l]))+PC(AND(r4,suf[l])); }", "return PC(A)+PC(AND(r2,suf[l]))+PC(AND(r3,suf[l]))+PC(AND(r4,suf[l]))" + seq("+PC(AND(r{k},suf[l]))") + "; }", 1),
 ("M128 A=AND(allowed,suf[l]), A2=AND(r2,suf[l]), A3=AND(r3,suf[l]), A4=AND(r4,suf[l]);\n    int wa=PC(A)+PC(A2)+PC(A3)+PC(A4);",
  "M128 A=AND(allowed,suf[l]), A2=AND(r2,suf[l]), A3=AND(r3,suf[l]), A4=AND(r4,suf[l])" + seq(", A{k}=AND(r{k},suf[l])") + ";\n    int wa=PC(A)+PC(A2)+PC(A3)+PC(A4)" + seq("+PC(A{k})") + ";", 1),
 ("if(PC(ANDN(A,m))+PC(ANDN(A2,m))+PC(ANDN(A3,m))+PC(ANDN(A4,m))<need){ postRow=r; return false; } }",
  "if(PC(ANDN(A,m))+PC(ANDN(A2,m))+PC(ANDN(A3,m))+PC(ANDN(A4,m))" + seq("+PC(ANDN(A{k},m))") + "<need){ postRow=r; return false; } }", 1),
 ("M128 A=AND(allowed,suf[pos]), A2=AND(r2,suf[pos]), A3=AND(r3,suf[pos]), A4=AND(r4,suf[pos]);\n    int lmax=topk(A,A2,A3,A4,rem);",
  "M128 A=AND(allowed,suf[pos]), A2=AND(r2,suf[pos]), A3=AND(r3,suf[pos]), A4=AND(r4,suf[pos])" + seq(", A{k}=AND(r{k},suf[pos])") + ";\n    int lmax=topk(A,A2,A3,A4" + seq(",A{k}") + ",rem);", 1),
 ("M128 L1=AND(A,suf[lmax]), L2=AND(A2,suf[lmax]), L3=AND(A3,suf[lmax]), L4=AND(A4,suf[lmax]);",
  "M128 L1=AND(A,suf[lmax]), L2=AND(A2,suf[lmax]), L3=AND(A3,suf[lmax]), L4=AND(A4,suf[lmax])" + seq(", L{k}=AND(A{k},suf[lmax])") + ";", 1),
 ("int w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m)); if(w>=need) return false;",
  "int w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m))" + seq("+PC(ANDN(L{k},m))") + "; if(w>=need) return false;", 1),
 ("lmax=topk(ANDN(A,m),ANDN(A2,m),ANDN(A3,m),ANDN(A4,m),need); prepRow=r; if(lmax>=pos){ L1=AND(A,suf[lmax]); L2=AND(A2,suf[lmax]); L3=AND(A3,suf[lmax]); L4=AND(A4,suf[lmax]); }",
  "lmax=topk(ANDN(A,m),ANDN(A2,m),ANDN(A3,m),ANDN(A4,m)" + seq(",ANDN(A{k},m)") + ",need); prepRow=r; if(lmax>=pos){ L1=AND(A,suf[lmax]); L2=AND(A2,suf[lmax]); L3=AND(A3,suf[lmax]); L4=AND(A4,suf[lmax]);" + seq(" L{k}=AND(A{k},suf[lmax]);") + " }", 1),
 ("int w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m));\n", "int w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m))" + seq("+PC(ANDN(L{k},m))") + ";\n", 1),
 ("if(w<need){ lmax=topk(ANDN(A,m),ANDN(A2,m),ANDN(A3,m),ANDN(A4,m),need); prepRow=r; if(lmax<pos) return -1;",
  "if(w<need){ lmax=topk(ANDN(A,m),ANDN(A2,m),ANDN(A3,m),ANDN(A4,m)" + seq(",ANDN(A{k},m)") + ",need); prepRow=r; if(lmax<pos) return -1;", 1),
 ("L1=AND(A,suf[lmax]); L2=AND(A2,suf[lmax]); L3=AND(A3,suf[lmax]); L4=AND(A4,suf[lmax]); w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m));",
  "L1=AND(A,suf[lmax]); L2=AND(A2,suf[lmax]); L3=AND(A3,suf[lmax]); L4=AND(A4,suf[lmax]);" + seq(" L{k}=AND(A{k},suf[lmax]);") + " w=PC(ANDN(L1,m))+PC(ANDN(L2,m))+PC(ANDN(L3,m))+PC(ANDN(L4,m))" + seq("+PC(ANDN(L{k},m))") + ";", 1),
 ("PQ.push_back({curJob,std::vector<int>(seq,seq+d),allowed,r2,r3,r4});", "PQ.push_back({curJob,std::vector<int>(seq,seq+d),allowed,r2,r3,r4" + seq(",r{k}") + "});", 1),
 ('if(ub[l]>4){ fprintf(stderr,"ub[%d]=%d > 4 unsupported\\n",l,ub[l]); return 2; }', 'if(ub[l]>8){ fprintf(stderr,"ub[%d]=%d > 8 unsupported\\n",l,ub[l]); return 2; }', 1),
 ("s.allowed=pc.a; s.r2=pc.b; s.r3=pc.c; s.r4=pc.e;", "s.allowed=pc.a; s.r2=pc.b; s.r3=pc.c; s.r4=pc.e; s.r5=pc.m5; s.r6=pc.m6; s.r7=pc.m7; s.r8=pc.m8;", 1),
]
bad = []
for old, new, k in R:
    c = s.count(old)
    if c != k:
        bad.append((c, k, old[:100]))
    s = s.replace(old, new)
if bad:
    for b in bad:
        print("MISMATCH", b)
    sys.exit(1)
s = s.replace("// lineenum9m4: lineenum9vr with label caps up to 4", "// lineenum9m8: lineenum9m4 with label caps up to 8 (masks r5..r8; derived by mk_m8.py).\n// lineenum9m4: lineenum9vr with label caps up to 4", 1)
open(dst, "w").write(s)
left = [ln for ln in s.split("\n") if ("S4" in ln or "r4" in ln or "A4" in ln or "L4" in ln or "sup4" in ln) and not any(t in ln for t in ("S8", "r8", "A8", "L8", "sup8", "m8"))]
print(f"wrote {dst}: {len(R)} replacement kinds; lines with a 4-mask and no 8-mask: {len(left)}")
for ln in left:
    print("  CHECK:", ln.strip()[:170])
