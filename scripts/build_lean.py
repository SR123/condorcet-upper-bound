#!/usr/bin/env python3
"""Build the complete project-source import closure with bounded memory use.
Run Mathlib's cache download first. No project .olean is supplied by this
repository. A successful receipt requires every selected module to compile.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys,time

def stripped(s):
    out=[];i=0;depth=0;quoted=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2
            else:
                if s[i]=='\n':out.append('\n')
                i+=1
        elif quoted:
            if s[i]=='\\':i+=2
            elif s[i]=='"':quoted=False;i+=1
            else:i+=1
        elif s.startswith('/-',i):depth=1;i+=2
        elif s.startswith('--',i):
            end=s.find('\n',i);i=len(s)if end<0 else end
        elif s[i]=='"':quoted=True;i+=1
        else:out.append(s[i]);i+=1
    return ''.join(out)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,default=Path(__file__).resolve().parents[1]/'lean')
    parser.add_argument('--jobs',type=int,choices=[1,2],default=1)
    parser.add_argument('--target',action='append',help='Override the two final targets; useful for a small environment check.')
    args=parser.parse_args();root=args.project.resolve()
    targets=args.target or ['CDCert.Main','CDCert.TwoInputs']
    def source(m):return root/(m.replace('.','/')+'.lean')
    graph={}
    def visit(m):
        if m in graph:return
        p=source(m)
        if not p.is_file():raise RuntimeError('Missing project target '+m)
        imports=[]
        for line in stripped(p.read_text()).splitlines():
            match=re.match(r'\s*(?:public\s+)?import\s+(.*)',line)
            if match:imports+=match.group(1).split()
        graph[m]=[d for d in imports if source(d).is_file()]
        for d in graph[m]:visit(d)
    for m in targets:visit(m)
    hashes={m:hashlib.sha256(source(m).read_bytes()).hexdigest()for m in sorted(graph)}
    digest=hashlib.sha256(json.dumps(hashes,sort_keys=True).encode()).hexdigest()
    out=root/'.lake/build/lib/lean';out.mkdir(parents=True,exist_ok=True)
    logs=root/'build/checked-source';logs.mkdir(parents=True,exist_ok=True)
    receipt=logs/'BUILD_RECEIPT.json'
    previous=json.loads(receipt.read_text())if receipt.exists()else{}
    if previous and previous.get('source_digest')!=digest:
        raise RuntimeError('Sources or targets changed. Use a fresh build directory/checkout; old success is not reused.')
    # Ask Lake only for its configured compiler/library paths, not credentials.
    helper='import os,json,shutil;print(json.dumps({"LEAN_PATH":os.environ.get("LEAN_PATH",""),"lean":shutil.which("lean")}))'
    setup=subprocess.run(['lake','env',sys.executable,'-c',helper],cwd=root,text=True,capture_output=True)
    if setup.returncode:
        raise RuntimeError('Lake dependency setup failed:\n'+setup.stdout+setup.stderr)
    config=json.loads(setup.stdout.strip().splitlines()[-1]);lean=config['lean']
    version=subprocess.check_output([lean,'--version'],cwd=root,text=True).strip()
    if not re.search(r'\bversion 4\.26\.0\b',version):raise RuntimeError('Expected pinned Lean4.26.0; got '+version)
    env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(out),config['LEAN_PATH']])
    results=previous.get('results',{});done=set();failed={};running={}
    for m,result in results.items():
        artifact=out/(m.replace('.','/')+'.olean')
        if m in graph and result.get('returncode')==0 and artifact.exists() and hashlib.sha256(artifact.read_bytes()).hexdigest()==result.get('olean_sha256'):
            done.add(m)
    started=time.time()
    def save(status):
        data={'status':status,'targets':targets,'module_count':len(graph),'source_digest':digest,
              'source_sha256':hashes,'compiler':version,'done':sorted(done),'failed':failed,
              'running':sorted(running),'results':results,'elapsed_this_run':time.time()-started}
        tmp=receipt.with_suffix('.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n');tmp.replace(receipt)
    while len(done)<len(graph):
        ready=[m for m in graph if m not in done and m not in failed and m not in running and all(d in done for d in graph[m])]
        if not failed:
            for m in ready:
                if len(running)>=args.jobs:break
                artifact=out/(m.replace('.','/')+'.olean');artifact.parent.mkdir(parents=True,exist_ok=True)
                log=(logs/(m.replace('.','_')+'.txt')).open('w')
                process=subprocess.Popen([lean,'-o',str(artifact),str(source(m))],cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
                running[m]=(process,log,time.time(),artifact)
                print('START',m,flush=True)
        if not running:
            save('FAILED')
            raise RuntimeError('Build did not finish all modules; inspect '+str(receipt))
        time.sleep(0.5)
        for m,(process,log,t0,artifact)in list(running.items()):
            code=process.poll()
            if code is None:continue
            log.close();del running[m]
            results[m]={'returncode':code,'seconds':time.time()-t0,'log':m.replace('.','_')+'.txt'}
            if code==0 and artifact.is_file():
                done.add(m);results[m]['olean_sha256']=hashlib.sha256(artifact.read_bytes()).hexdigest()
            else:failed[m]=code or 'no output artifact'
            print('END',m,'rc',code,'completed',len(done),'/',len(graph),flush=True)
            save('RUNNING'if not failed else'FAILED')
    save('PASS')
    print('SOURCE BUILD PASS:',len(done),'modules;',receipt,flush=True)

if __name__=='__main__':
    try:main()
    except (Exception,KeyboardInterrupt)as error:
        print('BUILD FAILED OR INTERRUPTED:',error,file=sys.stderr)
        sys.exit(1)
