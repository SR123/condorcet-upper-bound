from pathlib import Path
from itertools import permutations,combinations
from collections import Counter
from fractions import Fraction as F
import pickle,json,struct,time,sys
here=Path(__file__).resolve().parent;start=time.monotonic();P5=list(permutations(range(5)));i5={p:i for i,p in enumerate(P5)}
family={(1<<120)-1}
for t in combinations(range(5),3):
 laws=[]
 for x in t:
  for rank in (0,2):laws.append(sum((tuple(y for y in p if y in t)[rank]!=x)<<i for i,p in enumerate(P5)))
 family={d&m for d in family for m in laws};family.discard(0)
for a,b in combinations(range(5),2):
 for u,v in [(a,b),(b,a)]:
  m=sum((p.index(u)<p.index(v))<<i for i,p in enumerate(P5));family|={d&m for d in family};family.discard(0)
assert len(family)==128400
acts=[[1<<i5[tuple(r[x] for x in p)] for p in P5] for r in P5]
def bits(d):
 while d:
  z=d&-d;d-=z;yield z.bit_length()-1
remaining=set(family);reps=[]
while remaining:
 d=remaining.pop();inds=list(bits(d));orb={sum(a[i] for i in inds) for a in acts};assert orb<=family
 remaining.difference_update(orb);reps.append(min(orb))
reps.sort();assert len(reps)==1160
classmap={}
for k,d in enumerate(reps):
 inds=list(bits(d))
 for a in acts:classmap[sum(a[i] for i in inds)]=k
assert len(classmap)==128400 and set(classmap)==family
pickle.dump((reps,classmap),open(here/'five_classmap.pickle','wb'),protocol=4)
P6=list(permutations(range(6)));i6={p:i for i,p in enumerate(P6)};N6=720;W=12;MASK=(1<<64)-1;full=(1<<720)-1
with (here/'five_classes.bin').open('wb') as f:
 f.write(struct.pack('<QQ',len(reps),len(classmap)))
 for d in reps:f.write(struct.pack('<QQ',d&MASK,d>>64))
 for d,c in sorted(classmap.items()):f.write(struct.pack('<QQI',d&MASK,d>>64,c))
# Precompute all membership and slice maps; external label normalized by sorted labels.
info=[]
for p in P6:
 a=p[0];z=p[-1];left=tuple(x-(x>z) for x in p[:-1]);right=tuple(x-(x>a) for x in p[1:]);ns=[]
 for j in range(5):ns.append(i6[p[:j]+(p[j+1],p[j])+p[j+2:]])
 info.append((a,z,i5[left],i5[right],ns,i5[tuple(x for x in p if x!=5)]))
with (here/'full_window_input.bin').open('wb') as f:
 f.write(struct.pack('<QQ',len(P6),len(reps)))
 for row in info:f.write(struct.pack('<10I',*row[:4],*row[4],row[5]))
 for d in reps:f.write(struct.pack('<QQ',d&MASK,d>>64))
 groups=[]
 for t in combinations(range(5),2):
  T=(*t,5);group=[]
  for x in T:
   for rank in (0,2):group.append(sum((tuple(y for y in p if y in T)[rank]!=x)<<i for i,p in enumerate(P6)))
  groups.append(group)
 for a in range(5):
  m=sum((p.index(a)<p.index(5))<<i for i,p in enumerate(P6));groups.append([full,m,full^m])
 f.write(struct.pack('<I',len(groups)))
 for group in groups:
  f.write(struct.pack('<I',len(group)))
  for d in group:f.write(struct.pack('<12Q',*((d>>(64*j))&MASK for j in range(W))))
print('PREPARED_FROM_SCRATCH',len(classmap),'five-label sets;',len(reps),'classes; seconds',time.monotonic()-start,flush=True)
