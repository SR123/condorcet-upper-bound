#!/usr/bin/env python3
"""Write or verify checksums of the release payload, excluding build outputs."""
from pathlib import Path
import argparse,hashlib,json,os,re,sys

SKIP_DIRS={'.git','.lake','build','__pycache__'}
RUNTIME={
 'ancillary/finite_certificate/joint_exact_replay.json',
 'ancillary/finite_certificate/compressed_potential_replay.json',
 'ancillary/finite_certificate/joint_complete.tuple_replay.json',
 'ancillary/finite_certificate/checks/charges_exact_result.json',
 'ancillary/finite_certificate/checks/global_derivation_result.json'}

def files(root):
    result=[]
    for directory,dirs,names in os.walk(root):
        dirs[:]=[d for d in dirs if d not in SKIP_DIRS]
        for name in names:
            p=Path(directory)/name;rel=p.relative_to(root).as_posix()
            if name in {'MANIFEST.sha256','.DS_Store'}or rel in RUNTIME:continue
            if p.is_symlink():raise RuntimeError('Payload symlink not allowed: '+rel)
            result.append((rel,p))
    return sorted(result)

def digest(p):
    h=hashlib.sha256()
    with p.open('rb')as f:
        while b:=f.read(1024*1024):h.update(b)
    return h.hexdigest()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--write',action='store_true',help='Generate a NEW manifest after reviewing any source changes.')
    args=parser.parse_args();root=args.root.resolve();manifest=root/'MANIFEST.sha256'
    actual={rel:digest(p)for rel,p in files(root)}
    if args.write:
        manifest.write_text(''.join(h+'  '+rel+'\n'for rel,h in actual.items()))
        print('WROTE',manifest,'with',len(actual),'files');return
    expected={}
    for line in manifest.read_text().splitlines():
        m=re.fullmatch(r'([0-9a-f]{64})  (.+)',line)
        if not m:raise RuntimeError('Invalid manifest line')
        h,rel=m.groups()
        if Path(rel).is_absolute()or'..'in Path(rel).parts or rel in expected:raise RuntimeError('Unsafe/duplicate manifest path: '+rel)
        expected[rel]=h
    report={'result':'PASS'if actual==expected else'FAIL','files':len(expected),
            'missing':sorted(set(expected)-set(actual)),'unlisted':sorted(set(actual)-set(expected)),
            'changed':sorted(p for p in actual.keys()&expected.keys()if actual[p]!=expected[p])}
    print(json.dumps(report,indent=2));sys.exit(0 if actual==expected else 1)

if __name__=='__main__':
    try:main()
    except Exception as error:
        print('MANIFEST CHECK FAILED:',error,file=sys.stderr);sys.exit(1)
