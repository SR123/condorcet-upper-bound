"""Regenerate from definitions in isolation; no supplied rows/witnesses are inputs.
Usage: python3 run_fresh_regeneration.py OUTPUT_DIRECTORY
Requires standard Python3 and a C++17 compiler. No optimizer or network.
"""
from pathlib import Path
import subprocess,sys,shutil,json,hashlib,time
BASE=Path(__file__).resolve().parent
if len(sys.argv)!=2:raise SystemExit(__doc__)
OUT=Path(sys.argv[1]).resolve()
if OUT.exists():raise SystemExit('Choose a new output directory; existing results are preserved.')
OUT.mkdir(parents=True)
scripts=['prepare_full_family.py','prepare_selected_keys.py','prepare_seven_seeds.py','prepare_seven_windows.py','verify_joint_exact.py','verify_joint_tuple_features.py','verify_compressed_potential.py']
for name in scripts+['full_window_selected.cpp','seven_window_oldfirst.cpp','joint_8_3.certificate.json','selected_key_index.json']:
    shutil.copy2(BASE/name,OUT/name)
commands=[];started=time.monotonic()
def run(args,name,timeout=300):
    print('Running',name,flush=True)
    with (OUT/(name+'.log')).open('w')as log:
        result=subprocess.run(args,cwd=OUT,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
    commands.append({'command':args,'log':name+'.log','returncode':result.returncode})
    if result.returncode:raise SystemExit('FAILED: '+name+'; inspect its log. No success receipt written.')
def py(name):run([sys.executable,name],name[:-3])
py('prepare_full_family.py');py('prepare_selected_keys.py')
run(['c++','-O3','-std=c++17','full_window_selected.cpp','-o','full_window_selected'],'compile_six')
run([str(OUT/'full_window_selected'),'full_window_input.bin','five_classes.bin','selected_complete'],'generate_six')
six=json.loads((OUT/'selected_complete.result.json').read_text())
assert six['six_extensions']==14105084 and six['feature_rows']==94830
for suffix in ['rows.txt','witness.bin']:shutil.copyfile(OUT/('selected_complete.'+suffix),OUT/('receiver_complete.'+suffix))
py('prepare_selected_keys.py');py('prepare_seven_seeds.py')
seeds=json.loads((OUT/'seven_seed_manifest.json').read_text())
assert seeds['selected_labelled_sets']==397 and seeds['selected_isomorphism_types']==14 and seeds['seven_seed_count_including_reversals']==18
py('prepare_seven_windows.py')
run(['c++','-O3','-std=c++17','seven_window_oldfirst.cpp','-o','seven_window_oldfirst'],'compile_seven')
run([str(OUT/'seven_window_oldfirst')],'generate_seven')
seven=json.loads((OUT/'seven_complete.result.json').read_text())
assert seven['complete']and seven['seeds']==18 and seven['family_cases']==14248 and seven['feature_rows']==18316
for name in ['verify_joint_exact.py','verify_joint_tuple_features.py','verify_compressed_potential.py']:py(name)
comparisons={}
for name in ['receiver_complete.rows.txt','seven_complete.rows.txt']:
    comparisons[name]=hashlib.sha256((OUT/name).read_bytes()).hexdigest()==hashlib.sha256((BASE/name).read_bytes()).hexdigest()
    assert comparisons[name],('Regenerated rows differ from packaged data',name)
receipt={'result':'COMPLETE FRESH REGENERATION PASS','seconds':time.monotonic()-started,'six':six,'seven':seven,'seeds':seeds,'rows_match_packaged_data':comparisons,'commands':commands,'scope':'Finite families generated from defining laws with no supplied rows or witnesses. Generic seven-window coverage and global theorem require the hand proofs.'}
(OUT/'FULL_REGENERATION_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k not in('commands','seeds')},indent=2))
