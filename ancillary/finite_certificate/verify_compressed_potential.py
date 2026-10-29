"""Exact replay of the paper's single seven-window potential on all saved rows.
This verifies the new presentation against the audited two-stage certificate;
full coverage is supplied by the complete generators and the receiver proof.
"""
from pathlib import Path
from itertools import permutations
from collections import Counter
import pickle,struct,json,time
H=Path(__file__).resolve().parent;start=time.monotonic();c=json.loads((H/'joint_8_3.certificate.json').read_text());D=c['denominator'];K=c['K_integer'];eta=c['eta_integer'];phi={int(k):v for k,v in c['potential'].items()};psi=c['psi_integer']
meta=json.loads((H/'selected_key_index.json').read_text());sids=sorted(z['row'] for z in meta if z['kind']=='S');special={bytes.fromhex(z['key_hex']):sids.index(z['row']) for z in meta if z['kind']=='S'}
_,cm=pickle.load(open(H/'five_classmap.pickle','rb'));P5=list(permutations(range(5)));ix5={p:i for i,p in enumerate(P5)};P7=list(permutations(range(7)));cache={}
def swap(p,j):return p[:j]+(p[j+1],p[j])+p[j+2:]
def q2(F):
 labs=sorted(next(iter(F)));rel={a:i for i,a in enumerate(labs)};G=frozenset(tuple(rel[a] for a in p) for p in F)
 if G in cache:return cache[G]
 A=C=0;bottom={};top={}
 for p in G:
  ns=[swap(p,j) for j in range(5)];e=[q in G for q in ns];A+=sum(e);C+=int(e[0] and e[1])-int(not e[0]);C+=int(not e[2] and not(e[1] and swap(ns[1],2) in G) and not(e[3] and swap(ns[3],2) in G))
  if e[1] and e[2]:
   aa,bb=ns[1],ns[2]
   if swap(aa,2) not in G and swap(bb,1) not in G and not(swap(aa,3) in G and swap(swap(aa,3),2) in G) and not(swap(bb,0) in G and swap(swap(bb,0),1) in G):C+=1
  bottom.setdefault(p[-1],set()).add(p[:-1]);top.setdefault(p[0],set()).add(p[1:])
 flow=Counter();rb=rt=bs=ts=0
 for sign,groups in ((1,bottom),(-1,top)):
  for L in groups.values():
   rr={a:i for i,a in enumerate(sorted(next(iter(L))))};mask=sum(1<<ix5[tuple(rr[a] for a in p)] for p in L);cl=cm[mask];flow[cl]+=sign*len(L)
   if sign==1:bs+=len(L)*phi.get(cl,0);rb+=cl==866
   else:ts+=len(L)*phi.get(cl,0);rt+=cl==41
 ff=tuple(sorted((cl,v) for cl,v in flow.items() if v));key=struct.pack('<5h',len(G),A,C,rb,rt)+b''.join(struct.pack('<2h',cl,v) for cl,v in ff)
 p=psi[special[key]] if key in special else 2*eta*(rt-rb)
 cache[G]=bs+ts+2*p
 return cache[G]
raw=(H/'seven_complete.witness.bin').read_bytes();lines=(H/'seven_complete.rows.txt').read_text().splitlines();N=struct.unpack_from('<Q',raw)[0];assert N==len(lines);minimum=None
for j,line in enumerate(lines):
 w=struct.unpack_from('<79Q',raw,8+632*j);indices=[]
 for i,word in enumerate(w):
  while word:
   z=word&-word;indices.append(64*i+z.bit_length()-1);word-=z
 J={P7[i] for i in indices};M=len(J);qs=0
 for endpoint,sign in ((-1,1),(0,-1)):
  slices={}
  for p in J:slices.setdefault(p[endpoint],set()).add(p[:-1] if endpoint==-1 else p[1:])
  qs+=sign*sum(q2(F) for F in slices.values())
 cost=sum((1 if k in (0,5) else 2) for p in J for k in range(6) if swap(p,k) in J)
 score=25*D*M+20*qs-4*D*cost
 a=line.split();old=10*K*int(a[0])-D*int(a[1])+20*eta*int(a[2])-10*eta*int(a[0])
 for z in a[3:]:
  k,v=map(int,z[1:].split(':'));old+=(10*psi[k] if z[0]=='p' else 5*phi.get(k,0))*v
 assert score==4*old,('compression identity',j,score,old)
 assert score>=0,('new window inequality',j,score)
 minimum=score if minimum is None else min(minimum,score)
out=dict(result='EXACT PASS',all_seven_witnesses=N,distinct_six_slices=len(cache),minimum_integer_residual=minimum,denominator=40*D,identity='new single-potential residual equals old residual exactly',seconds=time.monotonic()-start,scope='all saved witnesses; complete-family coverage remains the generator/receiver argument')
(H/'compressed_potential_replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
