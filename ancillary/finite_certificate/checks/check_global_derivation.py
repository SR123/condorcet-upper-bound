"""Exact arithmetic interfaces; the structural hypotheses are proved in the notes.
This file deliberately does NOT pretend arithmetic alone proves a CD theorem.
"""
from fractions import Fraction as F
from pathlib import Path
import json
beta=F(3,8)
general_slope=(1+beta)/4
assert general_slope==F(11,32)
assert 1/general_slope==F(32,11)
assert 1/beta==F(8,3)
assert F(12,19)-F(1,152)==F(5,8)
assert sum([1,2,2,2,2,1])==10
for n in range(3,101):
    assert n/(general_slope*n+F(1,4))==F(32*n,11*n+8)
    assert F(32*n,11*n+8)<F(32,11)
assert F(4)<F(32,11)**3 and F(4)<F(8,3)**3
out={
 'status':'EXACT ARITHMETIC PASS',
 'component_density':'Sigma(K)>=(3/8)n|K|, all nonempty full extreme-law-plus-pairs families',
 'general_hypotheses':'Maximum-size D is full and inclusion-maximal; sum component deletion sums=Sigma(D)+G; G<=3Sigma(D)-(n+1)|D|',
 'general_recurrence':'f(n)<=32n/(11n+8) f(n-1), n>=3',
 'general_exponential':'f(n)<=4(32/11)^(n-3), n>=3',
 'general_polynomial_correction':'O(n^(-8/11)(32/11)^n); from the product of k/(k+8/11)',
 'peak_pit_hypotheses':'A maximum peak-pit family is completed under chosen extreme laws; arbitrary peak-pit subsets need not have interval fibres',
 'peak_pit_recurrence':'h(n)<=(8/3)h(n-1), n>=2',
 'peak_pit_exponential':'h(n)<=4(8/3)^(n-3), n>=3',
 'scope':'Arithmetic verified here. Component structure, complete family coverage, gluing, slicing/telescoping and ordered-copy identities require the supplied mathematical proofs.'}
Path(__file__).with_name('global_derivation_result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
