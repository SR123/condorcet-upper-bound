"""Standard-library integer replay of the joint six/seven certificate."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib,time
start=time.monotonic();cp=Path('joint_8_3.certificate.json');c=json.loads(cp.read_text());D=c['denominator'];K=c['K_integer'];E=c['eta_integer'];p={int(k):v for k,v in c['potential'].items()};ps=c['psi_integer'];T=set(c['T_feature_rows']);S=set(c['S_feature_rows']);assert len(ps)==len(S);assert F(K,D)==F(12,19) and F(E,D)==F(1,152);assert not(T&S);six=[];seven=[];Tdata=[]
for row,line in enumerate(open('receiver_complete.rows.txt')):
 t=line.split();M,A,C,rb,rt=map(int,t[:5]);f={int(k):int(v) for k,v in (s.split(':') for s in t[5:])};s=5*(K*M+sum(p.get(k,0)*v for k,v in f.items()))-D*A;r=s-(5*E*(M+4*rb+4*rt) if row not in S|T else 0);assert r>=0,('six',row,r);six.append(r)
 if row in T:assert s==0 and rb==rt;Tdata.append({'row':row,'M':M,'rb':rb,'rt':rt})
for row,line in enumerate(open('seven_complete.rows.txt')):
 t=line.split();M,A,flux=map(int,t[:3]);pp={};ff={}
 for z in t[3:]:
  k,v=z[1:].split(':');(pp if z[0]=='p' else ff)[int(k)]=int(v)
 r=10*K*M+5*sum(p.get(k,0)*v for k,v in ff.items())-D*A+20*E*flux+10*sum(ps[k]*v for k,v in pp.items())-10*E*M;assert r>=0,('seven',row,r);seven.append(r)
assert json.load(open('seven_complete.result.json'))['complete'];assert len(six)==94830;assert len(seven)==18316
out={'result':'PASS','six_rows':len(six),'seven_rows':len(seven),'K':str(F(K,D)),'eta':str(F(E,D)),'min_six_integer_residual':min(six),'min_seven_integer_residual':min(seven),'six_zero_rows':sum(x==0 for x in six),'seven_zero_rows':sum(x==0 for x in seven),'T_data':Tdata,'peakpit_base':str(1/(1-F(K,D)+F(E,D))),'general_base':str(4/(2-F(K,D)+F(E,D))),'certificate_sha256':hashlib.sha256(cp.read_bytes()).hexdigest(),'seconds':time.monotonic()-start};Path('joint_exact_replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
