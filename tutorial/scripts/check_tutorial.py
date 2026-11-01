"""Reproducible source-correspondence, example and exact-arithmetic checks.
This does not claim a new complete Lean kernel build or native regeneration.
"""
from pathlib import Path
from itertools import permutations,combinations,product
from fractions import Fraction as Q
import hashlib,json,re
p=Path(__file__).resolve().parent.parent
repository=p.parent
old=json.loads((p/'audit/prior_kernel_build/SOURCE_BUILD_RECEIPT.json').read_text())
assert old['result']=='PASS'and old['completed_module_count']==326
for name,record in old['records'].items():
 f=repository/'lean'/Path(*name.split('.')).with_suffix('.lean')
 assert hashlib.sha256(f.read_bytes()).hexdigest()==record['source_sha256'],name
m=json.loads((p/'audit/TUTORIAL_LEAN_MAP.json').read_text())
assert len(m['entrypoints'])==20 and not m['unresolved_names']
for entry in m['entrypoints']:
 lines=(repository/entry['file']).read_text().splitlines()
 assert entry['signature'].splitlines()[0].strip()in lines[entry['line']-1].strip(),entry['name']
assert sum(e['name'].startswith('CDCert.Main.')for e in m['entrypoints'])==7
assert sum(e['name'].startswith('CDCert.TwoInputs.')for e in m['entrypoints'])==3
prior=json.loads((p/'audit/prior_kernel_build/AXIOM_CHECK_RECEIPT.json').read_text())
assert prior['result']=='PASS'and set(prior['axioms'])=={e['name']for e in m['entrypoints']}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'}for a in prior['axioms'].values())

def stats(family):
 family=set(family);n=len(next(iter(family)));labels=set(next(iter(family)))
 sigma=gaps=0
 for x in labels:
  fibres={}
  for row in family:fibres.setdefault(tuple(a for a in row if a!=x),set()).add(row.index(x))
  sigma+=len(fibres)
  for slots in fibres.values():gaps+=sum(b!=a+1 for a,b in zip(sorted(slots),sorted(slots)[1:]))
 edges=[]
 for row in family:
  for j in range(n-1):
   changed=list(row);changed[j],changed[j+1]=changed[j+1],changed[j]
   if tuple(changed)in family:edges.append((row,tuple(changed)))
 assert sigma+gaps+len(edges)==n*len(family)
 return sigma,gaps,len(edges),edges

def laws(family):
 labels=set(next(iter(family)))
 return{(x,pos)for x in labels for pos in range(3)if all(row[pos]!=x for row in family)}
all3=list(permutations((1,2,3)))
for mask in range(1,64):
 fam={all3[i]for i in range(6)if mask>>i&1};stats(fam)
 # Local triple proof: avoid each cyclic triple iff a common never-law exists.
 cycles=[{(1,2,3),(2,3,1),(3,1,2)},{(1,3,2),(3,2,1),(2,1,3)}]
 assert bool(laws(fam))==(not any(c<=fam for c in cycles))
D={tuple(map(int,s))for s in ['123','213','231','321']}
B={tuple(map(int,s))for s in ['123','132','231','321']}
assert stats(D)[:3]==(6,0,6)
assert stats({(1,2,3),(2,3,1)})[:3]==(5,1,0)
assert stats(B)[:3]==(6,2,4)
components=[{(1,2,3),(1,3,2)},{(2,3,1),(3,2,1)}]
assert sum(stats(k)[0]for k in components)==stats(B)[0]+stats(B)[1]==8
K={(1,2),(2,1)}
for t in range(1,5):
 joined={tuple(x+2*i for i,row in enumerate(rows)for x in row)for rows in product(K,repeat=t)}
 s,g,a,_=stats(joined)
 assert len(joined)==2**t and s==t*stats(K)[0]*2**(t-1)and a==t*stats(K)[2]*2**(t-1)and g==0
# Local pattern contradictions used in the injection.
assert laws({('a','b','c'),('b','a','c'),('a','c','b')})=={('a',2),('c',0)}
assert not laws({('u','p','v'),('p','u','v'),('p','v','u'),('u','v','p'),('v','p','u')})
mixed={('b1','q','b2'),('b1','b2','q'),('b2','q','b1')}
assert laws(mixed)=={('b1',1),('q',0)}
assert not laws(mixed|{('q','b1','b2')})
assert laws(mixed|{('q','b2','b1')})=={('b1',1)}
# Exact finite scaling and scalar transfer.
d=8846117280
assert d//5==1769223456 and 12*Q(d,19)==5587021440 and Q(d,152)==58198140
assert Q(5*d,4)==11057646600 and Q(12,19)-Q(1,152)==Q(5,8)
assert 2*d*Q(1,10)==Q(d,5)and 2*d*Q(5,8)==Q(5*d,4)
assert Q(1)+Q(3,8)==Q(11,8)and Q(4)/(1+Q(3,8))==Q(32,11)
Qbound=Q(2**62,d);boundary=Q(5,4)+2*Qbound
assert 8*d*boundary==10*d+2**66
for n in range(7,151):
 weights=[Q(0)for _ in range(n-1)]
 for start in range(n-6):
  for j,w in enumerate([1,2,2,2,2,1]):weights[start+j]+=Q(w,10)
 assert all(0<=x<=1 for x in weights)and sum(1-x for x in weights)==5
tex='\n'.join(f.read_text()for f in(p/'sections').glob('*.tex'))+(p/'main.tex').read_text()
labels=re.findall(r'\\label\{([^}]+)\}',tex)
assert len(labels)==len(set(labels))
assert set(re.findall(r'\\(?:page)?ref\{([^}]+)\}',tex))<=set(labels)
result={'result':'PASS','date':'2026-11-01','source_hashes_matching_prior_full_build':326,'final_exports_mapped':10,'prior_audited_results_mapped':20,'named_original_declarations_mapped':len(m['named_support_and_definitions']),'nonempty_three_alternative_families':63,'copy_counts_up_to_t':4,'window_weight_checks_up_to_n':150,'scope':'Current source identity, declaration locations, mathematical examples, local pattern contradictions and exact scalings. Not a fresh Lean kernel rebuild.'}
(p/'audit/TUTORIAL_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
