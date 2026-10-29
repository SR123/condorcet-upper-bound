"""Independent bounded exact audit of Moros upper-v10 Sections 2--4/App E.
All nonempty CD subsets on four labels, plus reproducible maximal samples.
No imported previous checker, certificate, optimizer, or audit verdict.
"""
from itertools import permutations, combinations
from collections import defaultdict, Counter
from pathlib import Path
import random,json,time

R=Path(__file__).resolve().parent
def sw(p,j):return p[:j]+(p[j+1],p[j])+p[j+2:]
def ins(p,x,t):
 q=tuple(y for y in p if y!=x);return q[:t]+(x,)+q[t:]

class Universe:
 def __init__(self,n):
  self.n=n;self.P=list(permutations(range(n)));self.ix={p:i for i,p in enumerate(self.P)}
  self.T=list(combinations(range(n),3));self.allowed=[];self.lawmasks=[]
  for T in self.T:
   ids={x:i for i,x in enumerate(T)};am=[];lm=[0]*9
   for k,p in enumerate(self.P):
    tr=tuple(x for x in p if x in ids);m=511
    for j,x in enumerate(tr):m^=1<<(3*ids[x]+j)
    am.append(m)
    for bit in range(9):
     if m>>bit&1:lm[bit]|=1<<k
   self.allowed.append(am);self.lawmasks.append(lm)
 def common(self,D):
  ix=[self.ix[p] for p in D];out={}
  for T,am in zip(self.T,self.allowed):
   m=511
   for k in ix:m&=am[k]
   assert m,'not a Condorcet domain'
   out[T]=m
  return out
 def maximal(self,D):
  co=self.common(D)
  return not any(all(co[T]&am[k] for T,am in zip(self.T,self.allowed))for k,p in enumerate(self.P)if p not in D)
 def greedy(self,seed):
  ids=list(range(len(self.P)));random.Random(seed).shuffle(ids);laws=[511]*len(self.T);D=set()
  for k in ids:
   opts=[m&am[k]for m,am in zip(laws,self.allowed)]
   if all(opts):D.add(self.P[k]);laws=opts
  assert self.maximal(D)
  return D
 def all_full(self):
  F={(1<<len(self.P))-1}
  for laws in self.lawmasks:F={d&m for d in F for m in laws};F.discard(0)
  return F
 def decode(self,d):return {p for k,p in enumerate(self.P)if d>>k&1}

def audit(U,D,check_psi=False):
 n=U.n;co=U.common(D);M=len(D)
 def law(T,x,j):T=tuple(sorted(T));return bool(co[T]>>(3*T.index(x)+j)&1)
 fibres=defaultdict(list)
 for p in D:
  for x in p:fibres[x,tuple(y for y in p if y!=x)].append(p.index(x))
 for f in fibres.values():f.sort()
 def slots(p,x):return fibres[x,tuple(y for y in p if y!=x)]
 def lifts(p,x):return [t for t in slots(p,x)if t<p.index(x)]
 def drops(p,x):return [t for t in slots(p,x)if t>p.index(x)]
 def blocked(p,x):return not lifts(p,x)
 Sigma=len(fibres);G=sum(sum(b>a+1 for a,b in zip(f,f[1:]))for f in fibres.values())
 A=sum(sw(p,j)in D for p in D for j in range(n-1))
 assert Sigma+G==n*M-A
 assert Sigma==sum(blocked(p,x)for p in D for x in p)
 free=[(p,x)for p in D for x in p if lifts(p,x)and drops(p,x)]
 frozen=sum(not lifts(p,x)and not drops(p,x)for p in D for x in p)
 locked={(p,j)for p in D for j in range(n-1)if not drops(p,p[j])and blocked(p,p[j+1])}
 assert 2*Sigma==n*M-len(free)+frozen
 # Local saturation is checked from all common laws, not from a chosen assignment.
 local=all(sw(p,j)in D or not all((co[T]&am[U.ix[sw(p,j)]])==co[T]for T,am in zip(U.T,U.allowed))for p in D for j in range(n-1))
 if local:
  assert 2*Sigma==(n+1)*M-A+len(locked)
  assert 3*Sigma-(n+1)*M-G==frozen+len(locked)-len(free)
 psi=[]
 if check_psi:
  assert U.maximal(D)
  for p,b in free:
   k=p.index(b);assert 0<k<n-1;a,c=p[k-1],p[k+1];T=(a,b,c)
   an3,cn1=law(T,a,2),law(T,c,0)
   assert an3!=cn1,'no-ties lemma'
   t=max(lifts(p,b))if an3 else min(drops(p,b));tau=ins(p,b,t);j=tau.index(a)
   assert tau[j+1]==c and(tau,j)in locked
   psi.append((tau,j))
  assert len(set(psi))==len(psi),'new free charge collision'
  assert G<=3*Sigma-(n+1)*M
 # Appendix E: injection on arbitrary domains; blockedness only when justified.
 phi=[];types=Counter();empty=0
 for p in D:
  w=[int(bool(lifts(p,x)))for x in p]+[0]
  empty+=sum(not w[j]and not w[j+1]for j in range(n))
  for i in range(n-2):
   a,b,c=p[i:i+3]
   if not(lifts(p,b)and lifts(p,c)):continue
   T=(a,b,c)
   if law(T,c,0):typ='C1';tau=sw(p,i+1);q=c
   elif law(T,a,2):typ='A';tau=ins(p,b,max(lifts(p,b)));q=c
   else:
    typ='C2';assert law(T,c,1);tau=ins(p,c,max(lifts(p,c)));q=tau[tau.index(c)+1]
   assert tau in D and tau.index(q)>0
   if typ!='C2' or local:assert blocked(tau,q)
   phi.append((tau,q));types[typ]+=1
 assert len(set(phi))==len(phi),'Appendix E charge collision'
 pp=all(any(m>>(3*k+j)&1 for k in range(3)for j in(0,2))for m in co.values())
 if pp or G==0:
  assert not types['C2'];assert all(blocked(p,x)for p,x in phi)
 Delta=sum(not blocked(p,x)for p,x in phi)
 Lcirc=Sigma-M-sum(blocked(p,x)for p,x in phi)
 assert 3*Sigma-(n+1)*M==Lcirc+empty-Delta
 return dict(n=n,M=M,Sigma=Sigma,G=G,A=A,free=len(free),frozen=frozen,locked=len(locked),local=local,peak_pit=pp,psi=len(psi),phi=len(phi),types=dict(types),Delta=Delta,Lcirc=Lcirc,empty=empty)

def main():
 started=time.monotonic();U=Universe(4);F=U.all_full();maxes=[d for d in F if U.maximal(U.decode(d))]
 all_cd=set()
 for d in maxes:
  s=d
  while s:all_cd.add(s);s=(s-1)&d
 aggregate=Counter();maxrows=[]
 for d in sorted(all_cd):
  z=audit(U,U.decode(d),d in maxes)
  if d in F:assert z['local'],'every full domain is locally saturated'
  aggregate['domains']+=1;aggregate['locally_saturated']+=z['local'];aggregate['peak_pit']+=z['peak_pit'];aggregate['gapless']+=not z['G'];aggregate['nonblocked_marks']+=z['Delta']
  if d in maxes:maxrows.append(z)
 samples=[]
 for n,count in[(5,64),(6,32)]:
  V=Universe(n)
  for s in range(count):samples.append(audit(V,V.greedy(73001+s),True))
 fixture={tuple(int(x)-1 for x in p)for p in ['31542','35241','35421','53124','53142']}
 z=audit(Universe(5),fixture);assert(z['M'],z['Sigma'],z['Delta'],z['Lcirc'],z['empty'])==(5,19,1,14,14)
 out={'status':'PASS','scope':'all nonempty CD subsets on4labels, generated as subsets of all inclusion-maximal full4domains; plus independent greedy maximal5/6samples','full4_count':len(F),'maximal4_count':len(maxes),'all_cd4':dict(aggregate),'maximal4_rows':maxrows,'maximal5_6_samples':samples,'AppendixE10_fixture':z,'seconds':time.monotonic()-started}
 (R/'charges_exact_result.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k not in('maximal4_rows','maximal5_6_samples')},indent=2))
if __name__=='__main__':main()
