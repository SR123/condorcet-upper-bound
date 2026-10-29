from itertools import permutations,combinations
from pathlib import Path
import struct,time
start=time.monotonic();P=list(permutations(range(7)));Q=list(permutations(range(6)));ix={p:i for i,p in enumerate(Q)};W=79;MASK=(1<<64)-1;full=(1<<5040)-1
with open('seven_window_input.bin','wb') as f:
 f.write(struct.pack('<I',len(P)))
 for p in P:
  a=p[0];z=p[-1];left=tuple(x-(x>z) for x in p[:-1]);right=tuple(x-(x>a) for x in p[1:]);f.write(struct.pack('<4I',a,z,ix[left],ix[right]))
 groups=[]
 for t in combinations(range(7),3):
  g=[]
  for x in t:
   for rank in (0,2):g.append(sum((tuple(y for y in p if y in t)[rank]!=x)<<i for i,p in enumerate(P)))
  groups.append(g)
 for a,b in combinations(range(7),2):
  m=sum((p.index(a)<p.index(b))<<i for i,p in enumerate(P));groups.append([full,m,full^m])
 f.write(struct.pack('<I',len(groups)))
 for g in groups:
  f.write(struct.pack('<I',len(g)))
  for d in g:f.write(struct.pack('<79Q',*((d>>(64*j))&MASK for j in range(W))))
print('7-window input prepared',time.monotonic()-start,'seconds')
