#include <array>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <string>
#include <chrono>
#include <cstdint>
using U=unsigned __int128;using Clock=std::chrono::steady_clock;
struct Mask {std::array<uint64_t,12>w{};bool operator==(const Mask&o)const{return w==o.w;}bool empty()const{for(auto x:w)if(x)return false;return true;}int size()const{int n=0;for(auto x:w)n+=__builtin_popcountll(x);return n;}bool has(int j)const{return(w[j/64]>>(j%64))&1;}};
struct Hash{size_t operator()(const Mask&m)const{uint64_t h=0x9e3779b97f4a7c15ull;for(auto x:m.w){x^=x>>30;x*=0xbf58476d1ce4e5b9ull;x^=x>>27;x*=0x94d049bb133111ebull;x^=x>>31;h^=x+0x9e3779b97f4a7c15ull+(h<<6)+(h>>2);}return h;}};
struct HU{size_t operator()(U x)const{uint64_t a=x,b=x>>64;return (a*0x9e3779b97f4a7c15ull)^(b*0xbf58476d1ce4e5b9ull);}};
Mask meet(const Mask&a,const Mask&b){Mask c;for(int i=0;i<12;i++)c.w[i]=a.w[i]&b.w[i];return c;}
struct Info{uint32_t first,last,left,right,sw[5],old;};
uint64_t rd64(std::ifstream&f){uint64_t x;f.read((char*)&x,8);return x;}
uint32_t rd32(std::ifstream&f){uint32_t x;f.read((char*)&x,4);return x;}
U rdU(std::ifstream&f){U lo=rd64(f),hi=rd64(f);return lo|(hi<<64);}
std::unordered_set<std::string> selected;std::unordered_set<Mask,Hash> selectedDomains;std::vector<Info>info;std::unordered_map<U,int,HU>types;std::unordered_map<std::string,Mask>rows;
void append16(std::string&s,int x){uint16_t z=x;s.push_back(z&255);s.push_back(z>>8);}
int get16(const std::string&s,size_t &i){uint16_t z=(uint8_t)s[i]|((uint16_t)(uint8_t)s[i+1]<<8);i+=2;return (int16_t)z;}
void evaluate(const Mask&d){
 int M=d.size(),A=0,C=0;U starts[6]={},ends[6]={};
 for(int wi=0;wi<12;wi++){uint64_t word=d.w[wi];while(word){int b=__builtin_ctzll(word);word&=word-1;int q=64*wi+b;const Info&I=info[q];ends[I.last]|=U(1)<<I.left;starts[I.first]|=U(1)<<I.right;
  bool e[5];for(int j=0;j<5;j++){e[j]=d.has(I.sw[j]);A+=e[j];}C+=(e[0]&&e[1])-(!e[0]);
  if(!e[2]&&(!e[1]||!d.has(info[I.sw[1]].sw[2]))&&(!e[3]||!d.has(info[I.sw[3]].sw[2])))C++;
  if(e[1]&&e[2]){int a=I.sw[1],b=I.sw[2];if(!d.has(info[a].sw[2])&&!d.has(info[b].sw[1])&&!(d.has(info[a].sw[3])&&d.has(info[info[a].sw[3]].sw[2]))&&!(d.has(info[b].sw[0])&&d.has(info[info[b].sw[0]].sw[1])))C++;}
 }}
 int rb=0,rt=0;std::vector<std::pair<int,int>>f;
 for(int x=0;x<6;x++){if(ends[x]){auto t=types.find(ends[x]);if(t==types.end())throw std::runtime_error("unknown end5type");int count=__builtin_popcountll((uint64_t)ends[x])+__builtin_popcountll((uint64_t)(ends[x]>>64));if(t->second==866)rb++;f.push_back({t->second,count});}if(starts[x]){auto t=types.find(starts[x]);if(t==types.end())throw std::runtime_error("unknown start5type");int count=__builtin_popcountll((uint64_t)starts[x])+__builtin_popcountll((uint64_t)(starts[x]>>64));if(t->second==41)rt++;f.push_back({t->second,-count});}}
 std::sort(f.begin(),f.end());std::vector<std::pair<int,int>>v;for(auto p:f){if(!v.empty()&&v.back().first==p.first)v.back().second+=p.second;else v.push_back(p);}std::string key;append16(key,M);append16(key,A);append16(key,C);append16(key,rb);append16(key,rt);for(auto p:v)if(p.second){append16(key,p.first);append16(key,p.second);}if(selected.count(key))selectedDomains.insert(d);rows.emplace(std::move(key),d);
}
void save(const std::string&prefix){std::vector<std::string>keys;for(auto &kv:rows)keys.push_back(kv.first);std::sort(keys.begin(),keys.end());std::ofstream o(prefix+".rows.txt");std::ofstream w(prefix+".witness.bin",std::ios::binary);uint64_t n=keys.size();w.write((char*)&n,8);for(auto &s:keys){size_t i=0;int M=get16(s,i),A=get16(s,i),C=get16(s,i),rb=get16(s,i),rt=get16(s,i);o<<M<<' '<<A<<' '<<C<<' '<<rb<<' '<<rt;while(i<s.size()){int t=get16(s,i),v=get16(s,i);o<<' '<<t<<':'<<v;}o<<'\n';auto &d=rows.at(s);w.write((char*)d.w.data(),96);}}
int main(int argc,char**argv){if(argc<4)return 2;auto start=Clock::now();{std::ifstream ek("selected_keys.bin",std::ios::binary);uint32_t nn=rd32(ek);for(uint32_t i=0;i<nn;i++){uint32_t n=rd32(ek);std::string s(n,0);ek.read(s.data(),n);selected.insert(s);}}std::ifstream f(argv[1],std::ios::binary),c(argv[2],std::ios::binary);uint64_t n=rd64(f),nr=rd64(f);if(n!=720||nr!=1160)return 3;info.resize(n);for(auto &I:info){I.first=rd32(f);I.last=rd32(f);I.left=rd32(f);I.right=rd32(f);for(auto &z:I.sw)z=rd32(f);I.old=rd32(f);}std::vector<U>reps;for(int i=0;i<nr;i++)reps.push_back(rdU(f));int ng=rd32(f);std::vector<std::vector<Mask>>groups(ng);for(auto &g:groups){int opts=rd32(f);g.resize(opts);for(auto &m:g)f.read((char*)m.w.data(),96);}uint64_t cr=rd64(c),ct=rd64(c);if(cr!=nr||ct!=128400)return 4;for(int i=0;i<cr;i++)rdU(c);for(int i=0;i<ct;i++){U m=rdU(c);int t=rd32(c);types[m]=t;}if(!f||!c)return 5;
 if(argc==5){std::ifstream e(argv[4],std::ios::binary);uint64_t count=rd64(e);for(int j=0;j<count;j++){Mask d;e.read((char*)d.w.data(),96);evaluate(d);}save(argv[3]);std::cout<<"evaluation domains "<<count<<" rows "<<rows.size()<<"\n";return 0;}
 uint64_t total=0;size_t maxfront=0;
 for(int ri=0;ri<nr;ri++){
  Mask lift;for(int q=0;q<720;q++)if((reps[ri]>>info[q].old)&1)lift.w[q/64]|=1ull<<(q%64);
  std::vector<std::vector<Mask>>gg;for(auto &g:groups){std::unordered_set<Mask,Hash>uniq;for(auto &m:g){Mask z=meet(lift,m);if(!z.empty())uniq.insert(z);}gg.emplace_back(uniq.begin(),uniq.end());}
  std::stable_sort(gg.begin(),gg.end(),[](auto&a,auto&b){return a.size()<b.size();});
  std::vector<Mask>front{lift};for(auto &g:gg){std::unordered_set<Mask,Hash>next;next.reserve(front.size()*2);for(auto &d:front)for(auto &m:g){Mask z=meet(d,m);if(!z.empty())next.insert(z);}front.assign(next.begin(),next.end());maxfront=std::max(maxfront,front.size());}
  total+=front.size();for(auto &d:front)evaluate(d);
  if(ri%20==19||ri+1==nr){double sec=std::chrono::duration<double>(Clock::now()-start).count();std::cout<<"seeds "<<ri+1<<" extensions "<<total<<" rows "<<rows.size()<<" maxfront "<<maxfront<<" seconds "<<sec<<std::endl;}
 }
 save(argv[3]);{std::ofstream ee(std::string(argv[3])+".selected.bin",std::ios::binary);uint64_t ne=selectedDomains.size();ee.write((char*)&ne,8);for(auto &d:selectedDomains)ee.write((char*)d.w.data(),96);}double sec=std::chrono::duration<double>(Clock::now()-start).count();std::ofstream j(std::string(argv[3])+".result.json");j<<"{\"result\":\""<<(total==14105084?"COMPLETE_EXPECTED_COUNT":"COMPLETE_COUNT_DIFFERS")<<"\",\"five_classes\":"<<nr<<",\"six_extensions\":"<<total<<",\"feature_rows\":"<<rows.size()<<",\"seconds\":"<<sec<<"}\n";return 0;
}
