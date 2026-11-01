"""Exact integer upper-bound tables and independently enumerated small examples.
These calculations do not add external classification results to the Lean proof.
"""
from pathlib import Path
from itertools import product,combinations,permutations
from fractions import Fraction
from math import factorial
import csv,json

ROOT=Path(__file__).resolve().parent.parent
DATA=ROOT/'data';DATA.mkdir(exist_ok=True)
NS=[5,6,7,8,9,10,20,30,100]
CLASSIFIED={3:4,4:9,5:20,6:45,7:100,8:224}
gap={3:4};full={3:4};seed_gap={3:4};seed_full={3:4}
for n in range(4,101):
    gap[n]=3*n*gap[n-1]//(n+1)
    full[n]=min(3*n*full[n-1]//(n+1),32*n*full[n-1]//(11*n+8))
    seed_gap[n]=3*n*seed_gap[n-1]//(n+1)
    seed_full[n]=min(3*n*seed_full[n-1]//(n+1),32*n*seed_full[n-1]//(11*n+8))
    if n in CLASSIFIED:
        assert seed_gap[n]>=CLASSIFIED[n] and seed_full[n]>=CLASSIFIED[n]
        seed_gap[n]=seed_full[n]=CLASSIFIED[n]
    assert seed_gap[n]<=gap[n] and seed_full[n]<=full[n]<=gap[n]
    assert seed_full[n]<=seed_gap[n]
    # Independent exact-rational interpretation of the two integer divisions.
    assert full[n]==int(min(Fraction(3*n,n+1),Fraction(32*n,11*n+8))*full[n-1])

def display(number):
    if number<10**10:return f'{number:,}'.replace(',',r'\,')
    length=len(str(number));unit=10**(length-4)
    rounded=(number+unit-1)//unit
    exponent=length-1
    if rounded==10000:rounded=1000;exponent+=1;unit*=10
    shown=Fraction(rounded,1000)*10**exponent
    assert shown>=number and shown-number<unit
    return str(rounded//1000)+'.'+str(rounded%1000).zfill(3)+r'\times10^{'+str(exponent)+'}'

rows=[]
for n in NS:
    rows.append({'n':n,'deletion_only':4*factorial(n)//factorial(3),
        'gap_only':gap[n],'full_argument':full[n],
        'gap_with_classifications':seed_gap[n],
        'full_with_classifications':seed_full[n]})
with (DATA/'upper_bounds_exact.csv').open('w',newline='') as f:
    writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)

def statistics(family):
    family=set(family);n=len(next(iter(family)));sigma=gaps=adjacency=0
    for x in next(iter(family)):
        fibres={}
        for row in family:
            erased=tuple(y for y in row if y!=x)
            fibres.setdefault(erased,set()).add(row.index(x))
        sigma+=len(fibres)
        for places in fibres.values():
            ordered=sorted(places)
            gaps+=sum(b>a+1 for a,b in zip(ordered,ordered[1:]))
    for row in family:
        for j in range(n-1):
            changed=list(row);changed[j],changed[j+1]=changed[j+1],changed[j]
            adjacency+=tuple(changed)in family
    assert sigma+gaps+adjacency==n*len(family)
    return {'M':len(family),'Sigma':sigma,'G':gaps,'A':adjacency}

def check_extreme_laws(family):
    labels=next(iter(family))
    for triple in combinations(labels,3):
        traces=[tuple(x for x in row if x in triple) for row in family]
        assert any(all(trace[p]!=x for trace in traces)for x in triple for p in [0,2])

base=[(1,2,3),(2,1,3),(2,3,1),(3,2,1)]
constructions=[]
for n in range(5,11):
    t,r=divmod(n,3)
    blocks=[[tuple(x+3*i for x in row)for row in base]for i in range(t)]
    if r==1:blocks.append([(3*t+1,)])
    if r==2:blocks.append([(3*t+1,3*t+2),(3*t+2,3*t+1)])
    family={tuple(x for block in choice for x in block)for choice in product(*blocks)}
    check_extreme_laws(family)
    result=statistics(family)
    expected_M=4**t*(2 if r==2 else 1)
    expected_A=expected_M*Fraction(3*t,2)+(expected_M if r==2 else 0)
    assert result=={'M':expected_M,'Sigma':n*expected_M-int(expected_A),'G':0,'A':int(expected_A)}
    constructions.append({'n':n,'three_label_blocks':t,'remainder':r,**result})

# The seven-label weighted-cost example, generated from its fixed comparisons.
local={tuple(x for pair in choice for x in pair)+(7,)for choice in product(
    [(1,2),(2,1)],[(3,4),(4,3)],[(5,6),(6,5)])}
block={x:i for i,labels in enumerate([(1,2),(3,4),(5,6),(7,)])for x in labels}
full_solution={p for p in permutations(range(1,8))if
    all(p.index(x)<p.index(y)for x in range(1,8)for y in range(1,8)if block[x]<block[y])}
assert local==full_solution
check_extreme_laws(local)
swaps=[]
for j in range(6):
    count=0
    for row in local:
        changed=list(row);changed[j],changed[j+1]=changed[j+1],changed[j]
        count+=tuple(changed)in local
    swaps.append(count)
cost=sum(Fraction(w*a,10)for w,a in zip([1,2,2,2,2,1],swaps))
assert swaps==[8,0,8,0,8,0] and cost==4
weights=[1,2,2,2,2,1]
overlap=[sum(weights[j-i]for i in [0,1]if 0<=j-i<6)for j in range(7)]
assert overlap==[1,3,4,4,4,3,1] and sum(Fraction(10-w,10)for w in overlap)==5

result={'result':'PASS','n_values':NS,'upper_bounds':rows,'small_constructions':constructions,
    'weighted_seven_example':{'M':8,'swap_counts':swaps,'C':'4'},
    'eight_position_window_weight_numerators':overlap,
    'display_rule':'Integers with ten or more digits are rounded upwards to four significant digits.',
    'external_classification_inputs':{str(k):v for k,v in CLASSIFIED.items() if k>=5},
    'external_sources':[
        'https://arxiv.org/html/2306.15993v5#S4.SS1',
        'https://link.springer.com/article/10.1007/s00355-023-01481-3'],
    'formal_scope':'Arithmetic and explicit examples checked by this script; the external classifications are not Lean assumptions of the 32/11 theorem.'}
(DATA/'numerical_examples.json').write_text(json.dumps(result,indent=2)+'\n')
(ROOT/'audit/NUMERICAL_EXAMPLE_CHECKS.json').write_text(json.dumps({k:result[k]for k in ['result','n_values','display_rule','formal_scope']},indent=2)+'\n')

text=r'''\section{What successive ideas achieve at concrete sizes}\label{sec:numerical}
The following tables use exactly the same values of \(n\) throughout.
They count \emph{orders}, not voters. An upper-bound entry need not
be attained by a domain. Our small constructed examples illustrate
the counts; these tables limit \emph{every} domain.

\subsection{First compare the arguments without classification data}
Use only \(f(3)=4\) as the starting value. There are three stages:
\begin{enumerate}[label=\arabic*.]
\item \textbf{Deletion alone.} The weak count \(M\leq\Sigma\)
gives \(f(n)\leq nf(n-1)\), hence \(f(n)\leq4n!/6\).
\item \textbf{The gap argument.} Discarding \(G\geq0\) from
\(G+(n+1)M\leq3\Sigma\) gives
\(f(n)\leq3n f(n-1)/(n+1)\).
\item \textbf{The full argument.} The local estimate and components
also give \(f(n)\leq32n f(n-1)/(11n+8)\). At each step use
the stronger of this and the gap-only step.
\end{enumerate}
Round down after \emph{each} recurrence step, since domain sizes
are integers. Precisely, set \(u_3=v_3=4\) and, for \(n\geq4\),
\[
 u_n=\left\lfloor\frac{3n}{n+1}u_{n-1}\right\rfloor,\qquad
 v_n=\min\!\left\{
 \left\lfloor\frac{3n}{n+1}v_{n-1}\right\rfloor,
 \left\lfloor\frac{32n}{11n+8}v_{n-1}\right\rfloor\right\}.
\]
Induction proves \(f(n)\leq u_n\) and \(f(n)\leq v_n\).
These retain the finite correction in the recurrence, so are sharper
than simply substituting \(n\) into \(4(32/11)^{n-3}\).

\begin{center}\small
\renewcommand{\arraystretch}{1.18}
\begin{tabular}{@{}rrrr@{}}\toprule
\(n\)&Deletion alone&Gap argument&Full argument\\\midrule
'''
for row in rows:
    text+=str(row['n'])+'&'+ '&'.join('$'+display(row[k])+'$'for k in ['deletion_only','gap_only','full_argument'])+r'\\'+'\n'
text+=r'''\bottomrule\end{tabular}
\end{center}
Long entries are rounded \emph{upwards} to four significant digits,
so the displayed numbers are still valid upper bounds. The complete
integers are provided in \texttt{data/upper\_bounds\_exact.csv}.

The two recurrence factors agree at \(n=8\). The gap-only factor
is smaller for \(n<8\); the \(32/11\) factor is smaller for \(n>8\).
This explains why the last two columns agree at small \(n\).
The asymptotic improvement becomes more visible as \(n\) increases.

\subsection{What the separately known small maxima improve}
The published classifications give
\[
 f(5)=20,\qquad f(6)=45,\qquad f(7)=100,\qquad f(8)=224.
\]
The first three values come from the classification through seven
alternatives~\cite{smallcd}; the eight-alternative value is
Theorem~4.1 of~\cite{eightcd}. Use these as additional upper bounds
at their respective steps, then continue the same two recurrences.
This changes the starting information, while the proof steps stay the same.

\begin{center}\small
\renewcommand{\arraystretch}{1.18}
\begin{tabular}{@{}rrr@{}}\toprule
\(n\)&Gap argument, with classifications&Full argument, with classifications\\\midrule
'''
for row in rows:
    text+=str(row['n'])+'&'+ '&'.join('$'+display(row[k])+'$'for k in ['gap_with_classifications','full_with_classifications'])+r'\\'+'\n'
text+=r'''\bottomrule\end{tabular}
\end{center}
The rows through eight now contain exact classified maxima. The
later rows remain upper estimates, and are not claims of exact maxima.
In particular, knowing \(f(8)=224\) helps the finite bounds: for
\(n\geq8\), even the simple geometric consequence becomes
\[
 f(n)\leq224(32/11)^{n-8}.
\]
It improves the leading constant, rather than the exponential base.
Thus the eight-alternative classification is useful additional
information, while the proof of the base \(32/11\) does not require it.

\outside{The recurrences used here are consequences of the formal
gap and transfer results and the deletion upper estimate. These
tables are separate exact-arithmetic calculations, not new exported
Lean theorems. \texttt{scripts/build\_numerical\_examples.py} regenerates
their exact entries, checks the small constructed domains and rounds
long entries upwards. The published classifications in the second
table are external inputs; they have not been added to the assumptions
or dependency chain of the Lean proof.}
'''
(ROOT/'sections/09a_numerical_bounds.tex').write_text(text)
small=r'''\begin{center}\small
\renewcommand{\arraystretch}{1.15}
\begin{tabular}{@{}rrrrrr@{}}\toprule
\(n\)&Three-label blocks&\(M\)&\(\Sigma\)&\(G\)&\(A\)\\\midrule
'''
for row in constructions:
    small+='&'.join(str(row[k])for k in ['n','three_label_blocks','M','Sigma','G','A'])+r'\\'+'\n'
small+=r'\bottomrule\end{tabular}\end{center}'+'\n'
(ROOT/'sections/generated_small_constructions.tex').write_text(small)
print(json.dumps({'result':'PASS','table_rows':rows,'small_examples_checked':len(constructions)},indent=2))
