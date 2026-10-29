from pathlib import Path
from itertools import permutations
import struct,json,pickle,time
start=time.monotonic();P=list(permutations(range(6)));ix={p:i for i,p in enumerate(P)};raw=Path('selected_complete.selected.bin').read_bytes();N=struct.unpack_from('<Q',raw,0)[0];print('selectedlabelledsets',N,flush=True);types={};cache={}
def canon(mask):
 if mask in cache:return cache[mask]
 orders=[P[i] for i in range(720) if mask>>i&1];orb=[]
 for p in orders:
  inv=[p.index(x) for x in range(6)];orb.append(sum(1<<ix[tuple(inv[x] for x in q)] for q in orders))
 c=min(orb)
 for d in orb:cache[d]=c
 return c
for j in range(N):
 d=sum(w<<(64*k) for k,w in enumerate(struct.unpack_from('<12Q',raw,8+96*j)));c=canon(d);types[c]=True
# Classify each canonical domain by its receiver feature key.
rawinfo=Path('full_window_input.bin').read_bytes();info=[]
for j in range(720):
 r=struct.unpack_from('<10I',rawinfo,16+40*j);info.append((*r[:4],r[4:9],r[9]))
_,cm=pickle.load(open('five_classmap.pickle','rb'));keyindex=json.load(open('selected_key_index.json'));kt={bytes.fromhex(r['key_hex']):r for r in keyindex};Sids=sorted(r['row'] for r in keyindex if r['kind']=='S');psi={r:j for j,r in enumerate(Sids)}
def feature(d):
 inds=[i for i in range(720) if d>>i&1];M=len(inds);A=C=0;ends=[0]*6;starts=[0]*6
 def has(q):return bool(d>>q&1)
 for q in inds:
  a,z,l,r,ns,old=info[q];ends[z]|=1<<l;starts[a]|=1<<r;e=[has(u) for u in ns];A+=sum(e);C+=int(e[0] and e[1])-int(not e[0])
  if not e[2] and all(not e[j] or not has(info[ns[j]][4][2]) for j in (1,3)):C+=1
  if e[1] and e[2]:
   aa=ns[1];bb=ns[2]
   if(not has(info[aa][4][2]) and not has(info[bb][4][1]) and not(has(info[aa][4][3]) and has(info[info[aa][4][3]][4][2])) and not(has(info[bb][4][0]) and has(info[info[bb][4][0]][4][1]))):C+=1
 flow={};rb=rt=0
 for m in ends:
  if m:t=cm[m];flow[t]=flow.get(t,0)+m.bit_count();rb+=t==866
 for m in starts:
  if m:t=cm[m];flow[t]=flow.get(t,0)-m.bit_count();rt+=t==41
 key=struct.pack('<5h',M,A,C,rb,rt)+b''.join(struct.pack('<2h',k,v) for k,v in sorted(flow.items()) if v);return M,key
seeds={};items=[]
for d in types:
 M,key=feature(d);meta=kt[key];items.append({'mask':str(d),'M':M,'row':meta['row'],'kind':meta['kind']})
 if meta['kind']=='T' and M==8:continue
 seeds[d]=meta
 revmask=sum(1<<ix[P[i][::-1]] for i in range(720) if d>>i&1);rc=canon(revmask);seeds[rc]=meta
with open('seven_seeds.bin','wb') as f:
 f.write(struct.pack('<I',len(seeds)))
 for d in sorted(seeds):f.write(struct.pack('<12Q',*((d>>(64*j))&((1<<64)-1) for j in range(12))))
with open('seven_exception_keys.bin','wb') as f:
 f.write(struct.pack('<I',len(Sids)))
 for row in Sids:
  key=bytes.fromhex(next(r['key_hex'] for r in keyindex if r['row']==row));f.write(struct.pack('<II',psi[row],len(key)));f.write(key)
out={'selected_labelled_sets':N,'selected_isomorphism_types':len(types),'S_rows':Sids,'seven_seed_count_including_reversals':len(seeds),'classes':sorted(items,key=lambda r:(r['kind'],r['M'],int(r['mask']))),'seconds':time.monotonic()-start};Path('seven_seed_manifest.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='classes'},flush=True)
