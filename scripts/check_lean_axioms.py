#!/usr/bin/env python3
"""Run the final statement/axiom check and reject missing or unexpected results."""
from pathlib import Path
import subprocess,re,sys,json

root=Path(__file__).resolve().parents[1]/'lean'
output=root/'build/final-axioms.txt';output.parent.mkdir(exist_ok=True)
run=subprocess.run(['lake','env','lean','receipts/FinalAxioms.lean'],cwd=root,text=True,capture_output=True)
output.write_text(run.stdout+run.stderr)
expected={
 'CDCert.Main.general_recurrence','CDCert.Main.general_geometric','CDCert.Main.peak_recurrence','CDCert.Main.peak_geometric',
 'CDCert.Main.general_limit','CDCert.Main.peak_limit','CDCert.Main.general_polynomial_correction',
 'CDCert.TwoInputs.first_input','CDCert.TwoInputs.second_input','CDCert.TwoInputs.transfer',
 'CDCert.Recurrences.gap_inequality','CDCert.Recurrences.deletion_lower_bound','CDCert.Bridge.InF.density',
 'CDCert.FreeLocked.free_le_locked','CDCert.K6.finite_lemma','CDCert.K6.adj_le','CDCert.Supermult.f_supermul',
 'CDCert.Supermult.h_supermul','CDCert.Recurrences.general_recurrence','CDCert.Bounds.peakPit_recurrence'}
found={name:{a.strip()for a in axioms.split(',')if a.strip()}for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",run.stdout)}
allowed={'propext','Classical.choice','Quot.sound'}
bad={name:sorted(ax-allowed)for name,ax in found.items()if ax-allowed}
receipt={'returncode':run.returncode,'expected_results':len(expected),'observed_results':len(found),
         'missing':sorted(expected-set(found)),'unexpected':sorted(set(found)-expected),
         'unexpected_axioms':bad,'axioms':{name:sorted(ax)for name,ax in found.items()}}
ok=run.returncode==0 and set(found)==expected and not bad
receipt['result']='PASS'if ok else'FAIL'
(output.parent/'AXIOM_CHECK_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k!='axioms'},indent=2))
sys.exit(0 if ok else 1)
