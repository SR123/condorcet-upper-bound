"""Recompute all seven-row witnesses with tuple sets, no C++ permutation tables."""
from pathlib import Path
from itertools import permutations
import pickle,struct,json,time
start=time.monotonic();_,cm=pickle.load(open('five_classmap.pickle','rb'));P5=list(permutations(range(5)));ix5={p:i for i,p in enumerate(P5)};P7=list(permutations(range(7)));keymeta=json.load(open('selected_key_index.json'));sids=sorted(x['row'] for x in keymeta if x['kind']=='S');keys={bytes.fromhex(x['key_hex']):sids.index(x['row']) for x in keymeta if x['kind']=='S'};cache={}
def swap(p,j):return p[:j]+(p[j+1],p[j])+p[j+2:]
def feat(F):
 labs=sorted(next(iter(F)));mp={x:i for i,x in enumerate(labs)};G=frozenset(tuple(mp[x] for x in p) for p in F)
 if G in cache:return cache[G]
 A=C=0;left={};right={}
 for p in G:
  ns=[swap(p,j) for j in range(5)];e=[q in G for q in ns];A+=sum(e);C+=int(e[0] and e[1])-int(not e[0]);C+=int(not e[2] and not(e[1] and swap(ns[1],2) in G) and not(e[3] and swap(ns[3],2) in G))
  if e[1] and e[2]:
   aa=ns[1];bb=ns[2]
   if swap(aa,2) not in G and swap(bb,1) not in G and not(swap(aa,3) in G and swap(swap(aa,3),2) in G) and not(swap(bb,0) in G and swap(swap(bb,0),1) in G):C+=1
  left.setdefault(p[-1],set()).add(p[:-1]);right.setdefault(p[0],set()).add(p[1:])
 f={};rb=rt=0
 for side,groups in ((1,left),(-1,right)):
  for F5 in groups.values():
   ls=sorted(next(iter(F5)));mm={x:i for i,x in enumerate(ls)};mask=sum(1<<ix5[tuple(mm[x] for x in p)] for p in F5);c=cm[mask];f[c]=f.get(c,0)+side*len(F5)
   if side==1:rb+=c==866
   else:rt+=c==41
 f={k:v for k,v in f.items() if v};key=struct.pack('<5h',len(G),A,C,rb,rt)+b''.join(struct.pack('<2h',k,v) for k,v in sorted(f.items()));out=(A,C,rb,rt,keys.get(key,-1),f);cache[G]=out;return out
P6=list(permutations(range(6)));sixraw=Path('receiver_complete.witness.bin').read_bytes();sixlines=Path('receiver_complete.rows.txt').read_text().splitlines();assert struct.unpack_from('<Q',sixraw,0)[0]==len(sixlines)
for row,line in enumerate(sixlines):
 t=line.split();M,A,C,rb,rt=map(int,t[:5]);flow={int(k):int(v) for k,v in (z.split(':') for z in t[5:])};words=struct.unpack_from('<12Q',sixraw,8+96*row);inds=[]
 for wi,w in enumerate(words):
  while w:
   b=(w&-w).bit_length()-1;w&=w-1;inds.append(64*wi+b)
 orders={P6[i] for i in inds};aa,cc,bb,tt,pi,ff=feat(orders);assert (len(orders),aa,cc,bb,tt,ff)==(M,A,C,rb,rt,flow),('six feature mismatch',row)
 if row%20000==19999:print('independent six tuple checks',row+1,'seconds',time.monotonic()-start,flush=True)
raw=Path('seven_complete.witness.bin').read_bytes();N=struct.unpack_from('<Q',raw,0)[0];lines=Path('seven_complete.rows.txt').read_text().splitlines();assert N==len(lines)
for j,line in enumerate(lines):
 t=line.split();M,A,flux=map(int,t[:3]);pp={};ff={}
 for z in t[3:]:
  k,v=z[1:].split(':');(pp if z[0]=='p' else ff)[int(k)]=int(v)
 words=struct.unpack_from('<79Q',raw,8+632*j);inds=[]
 for wi,w in enumerate(words):
  while w:
   b=(w&-w).bit_length()-1;w&=w-1;inds.append(64*wi+b)
 orders={P7[i] for i in inds};assert len(orders)==M;left={};right={}
 for p in orders:left.setdefault(p[-1],set()).add(p[:-1]);right.setdefault(p[0],set()).add(p[1:])
 aa=fl=0;ps={};fs={}
 for side,groups in ((1,left),(-1,right)):
  for F6 in groups.values():
   a,cc,rb,rt,pi,f=feat(F6);aa+=a
   if pi<0:fl+=side*(rt-rb)
   else:ps[pi]=ps.get(pi,0)+side
   for k,v in f.items():fs[k]=fs.get(k,0)+v
 ps={k:v for k,v in ps.items() if v};fs={k:v for k,v in fs.items() if v};assert (aa,fl,ps,fs)==(A,flux,pp,ff),j
 if j%4000==3999:print('seven tuple checks',j+1,'seconds',time.monotonic()-start,flush=True)
out={'result':'PASS','independent_seven_tuple_witnesses':N,'independent_six_tuple_witnesses':len(sixlines),'cached_six_slices':len(cache),'seconds':time.monotonic()-start};Path('joint_complete.tuple_replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
