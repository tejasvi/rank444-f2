// mkcompS9.cc: a C++ port of mkcompS.py.  The output must
// be byte-identical to mkcompS.py's.
// Completion inputs for quotient raises.  For each class:
//  - T mod S (S = the class representative) as a tsolve334 target in the reduced coordinates of quotient_map(S basis):
//    lines "x y z", sorted;
//  - the leaves of its capacity search as instances: "leaf<k>: c1 .. cL", where c = the coset coordinates of the sorted
//    9-bit labels;
//  - a positive control: the rank-29 scheme moved by the g in G0 that puts the most first factors into S (first maximum
//    in g order), its other first factors mod S, sorted (completion must be SAT).
// usage: mkcompS9 TABLE.tsv SCHEME.exp OUTDIR LEAFDIR CLASS...   (reads LEAFDIR/leaves_c<C>.txt; writes OUTDIR/qS_c<C>.t,
//        OUTDIR/pos_c<C>.a, OUTDIR/inst_c<C>.a)
#include <bits/stdc++.h>

static int det3(const int M[3][3]){
  return (M[0][0]*(M[1][1]*M[2][2]+M[1][2]*M[2][1]) + M[0][1]*(M[1][0]*M[2][2]+M[1][2]*M[2][0])
        + M[0][2]*(M[1][0]*M[2][1]+M[1][1]*M[2][0])) & 1; }
static int topbit(int v){ return 31-__builtin_clz(v); }

// mkcompS.fm: XOR of the bits idx(r-1, c-1) of every occurrence of VAR<r><c> with an odd coefficient; a coefficient is the
// digit run immediately before "*" immediately before VAR (as the regex ([+-]?)\s*(?:(\d+)\*)?VAR(\d)(\d)), else 1.
static int fm(std::string e, char var, int sel){
  // strip, and drop one pair of outer parentheses
  size_t a=e.find_first_not_of(" \t\r\n"), b=e.find_last_not_of(" \t\r\n"); if(a==std::string::npos) return 0; e=e.substr(a,b-a+1);
  if(e.size()>=2 && e.front()=='(' && e.back()==')') e=e.substr(1,e.size()-2);
  int m=0;
  for(size_t i=0;i+2<e.size();i++){ if(e[i]!=var || !isdigit((unsigned char)e[i+1]) || !isdigit((unsigned char)e[i+2])) continue;
    long coef=1; if(i>=2 && e[i-1]=='*' && isdigit((unsigned char)e[i-2])){ size_t k=i-2; while(k>0 && isdigit((unsigned char)e[k-1])) k--; coef=std::stol(e.substr(k,i-1-k)); }
    int r=e[i+1]-'0'-1, c=e[i+2]-'0'-1; int idx = sel==0 ? 3*r+c : sel==1 ? 4*r+c : 3*r+c;   // a: 3i+j; b: 4j+k; c: 3k+i
    if(coef%2) m^=1<<idx; i+=2; }
  return m; }

int main(int argc,char** argv){
  if(argc<6){ fprintf(stderr,"usage: mkcompS9 TABLE.tsv SCHEME.exp OUTDIR LEAFDIR CLASS...\n"); return 2; }
  std::string tab=argv[1], sch=argv[2], out=argv[3], leafdir=argv[4];
  std::vector<int> dims; std::vector<std::vector<int>> bases;
  { std::ifstream f(tab); if(!f){ fprintf(stderr,"cannot read %s\n",tab.c_str()); return 2; } std::string line; std::getline(f,line);
    while(std::getline(f,line)){ if(line.empty()) continue; std::vector<std::string> c; std::stringstream ss(line); std::string t; while(std::getline(ss,t,'\t')) c.push_back(t);
      if(c.size()<12){ fprintf(stderr,"short table line\n"); return 2; } dims.push_back(std::stoi(c[1])); std::vector<int> b; std::stringstream bs(c[2]);
      while(std::getline(bs,t,',')) if(!t.empty()) b.push_back(std::stoi(t)); bases.push_back(b); } }
  // G0 image table (as mkipS9 / common334.build_img0)
  std::vector<std::array<int,3>> GL;
  for(int bits=0;bits<512;bits++){ int M[3][3]; for(int k=0;k<9;k++) M[k/3][k%3]=(bits>>k)&1; if(det3(M)){ std::array<int,3> r; for(int i=0;i<3;i++) r[i]=(bits>>(3*i))&7; GL.push_back(r); } }
  if(GL.size()!=168){ fprintf(stderr,"GL3 size\n"); return 4; }
  const int G=168*168; std::vector<uint16_t> img((size_t)G*512);
  auto mulR=[&](const int* A,const int* B,int* C){ for(int i=0;i<3;i++){ int r=0; for(int k=0;k<3;k++) if((A[i]>>k)&1) r^=B[k]; C[i]=r; } };
  for(int p=0;p<168;p++) for(int v=0;v<512;v++){ int Mv[3]={v&7,(v>>3)&7,(v>>6)&7}, PM[3]; mulR(GL[p].data(),Mv,PM);
    for(int q=0;q<168;q++){ int R[3]; mulR(PM,GL[q].data(),R); img[(size_t)(p*168+q)*512+v]=(uint16_t)(R[0]|(R[1]<<3)|(R[2]<<6)); } }
  // T334
  static unsigned char T[9][12][12]; memset(T,0,sizeof T);
  for(int i=0;i<3;i++) for(int j=0;j<3;j++) for(int k=0;k<4;k++) T[3*i+j][4*j+k][3*k+i]=1;
  // the rank-29 scheme: terms "(A)*(B)*(C)", split at depth-0 '*'
  std::vector<int> firsts;
  { std::ifstream f(sch); if(!f){ fprintf(stderr,"cannot read %s\n",sch.c_str()); return 2; } std::string ln;
    while(std::getline(f,ln)){ size_t a=ln.find_first_not_of(" \t\r\n"); if(a==std::string::npos) continue; size_t b=ln.find_last_not_of(" \t\r\n"); ln=ln.substr(a,b-a+1);
      std::vector<std::string> parts; int d=0; std::string cur; for(char ch:ln){ d+=(ch=='(')-(ch==')'); if(ch=='*' && d==0){ parts.push_back(cur); cur.clear(); } else cur+=ch; } parts.push_back(cur);
      if(parts.size()<3){ fprintf(stderr,"bad scheme line\n"); return 2; }
      int ma=fm(parts[0],'a',0), mb=fm(parts[1],'b',1), mc=fm(parts[2],'c',2); if(ma && mb && mc) firsts.push_back(ma); } }
  if(firsts.size()!=29){ fprintf(stderr,"scheme: %zu terms (expected 29)\n",firsts.size()); return 4; }
  for(int ai=5;ai<argc;ai++){ int c=atoi(argv[ai]); int dS=dims[c]; std::vector<int> Sb=bases[c];
    std::vector<std::pair<int,int>> basis;
    for(int v0:Sb){ int v=v0; for(auto& pb:basis) if((v>>pb.first)&1) v^=pb.second; if(v){ int p=topbit(v); for(auto& pb:basis) if((pb.second>>p)&1) pb.second^=v; basis.push_back({p,v}); } }
    std::vector<int> comp; { std::set<int> piv; for(auto& pb:basis) piv.insert(pb.first); for(int x=0;x<9;x++) if(!piv.count(x)) comp.push_back(x); }
    int D=comp.size(); auto Lq=[&](int a){ for(auto& pb:basis) if((a>>pb.first)&1) a^=pb.second; int r=0; for(int i=0;i<D;i++) if((a>>comp[i])&1) r|=1<<i; return r; };
    std::map<std::tuple<int,int,int>,int> Tp; int LT[9]; for(int x=0;x<9;x++) LT[x]=Lq(1<<x);
    for(int x=0;x<9;x++) for(int y=0;y<12;y++) for(int z=0;z<12;z++) if(T[x][y][z]) for(int xp=0;xp<D;xp++) if((LT[x]>>xp)&1) Tp[{xp,y,z}]^=1;
    int nent=0; { std::string fn=out+"/qS_c"+std::to_string(c)+".t"; FILE* f=fopen(fn.c_str(),"w"); if(!f){ fprintf(stderr,"cannot write %s\n",fn.c_str()); return 2; }
      for(auto& kv:Tp) if(kv.second){ fprintf(f,"%d %d %d\n",std::get<0>(kv.first),std::get<1>(kv.first),std::get<2>(kv.first)); nent++; } fclose(f); }
    std::vector<char> memS(512,0); { std::vector<int> sp={0}; for(int v:Sb){ int n=sp.size(); for(int i=0;i<n;i++) sp.push_back(sp[i]^v); } for(int x:sp) memS[x]=1; }
    int bestg=0, bestc=-1; for(int g=0;g<G;g++){ int cnt=0; for(int a:firsts) cnt+=memS[img[(size_t)g*512+a]]; if(cnt>bestc){ bestc=cnt; bestg=g; } }
    std::vector<int> prof; for(int a:firsts){ int ia=img[(size_t)bestg*512+a]; if(!memS[ia]) prof.push_back(Lq(ia)); } std::sort(prof.begin(),prof.end());
    { std::string fn=out+"/pos_c"+std::to_string(c)+".a"; FILE* f=fopen(fn.c_str(),"w"); fprintf(f,"pos%zu_c%d: ",prof.size(),c); for(size_t i=0;i<prof.size();i++) fprintf(f,"%d%s",prof[i],i+1==prof.size()?"":" "); fprintf(f,"\n"); fclose(f); }
    int n=0; { std::string fn=out+"/inst_c"+std::to_string(c)+".a"; FILE* f=fopen(fn.c_str(),"w"); std::ifstream lf(leafdir+"/leaves_c"+std::to_string(c)+".txt"); std::string ln;
      while(std::getline(lf,ln)){ std::stringstream ss(ln); std::vector<int> v; int x; while(ss>>x) v.push_back(x); if(v.empty()) continue; n++; std::sort(v.begin(),v.end());
        fprintf(f,"leaf%d: ",n); for(size_t i=0;i<v.size();i++) fprintf(f,"%d%s",Lq(v[i]),i+1==v.size()?"":" "); fprintf(f,"\n"); } fclose(f); }
    printf("class %d (dim %d, D=%d): target %d entries; positive control %zu first factors (%d of 29 moved into S); %d leaf instances\n",c,dS,D,nent,prof.size(),bestc,n); }
  return 0; }
