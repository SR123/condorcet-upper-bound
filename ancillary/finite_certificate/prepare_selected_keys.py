"""Prepare T/S selectors from explicit feature keys; no generated rows needed.
If a rows file is present, also verify every named row matches its feature key.
"""
from pathlib import Path
import json,struct
c=json.load(open('joint_8_3.certificate.json'));T=set(c['T_feature_rows']);S=set(c['S_feature_rows'])
rows=json.load(open('selected_key_index.json'));assert len(rows)==len(T|S)
assert {r['row'] for r in rows}==T|S
for r in rows:
 assert r['kind']==('S' if r['row'] in S else 'T')
 assert len(bytes.fromhex(r['key_hex']))>=10
rp=Path('receiver_complete.rows.txt')
if rp.exists():
 lines=rp.read_text().splitlines()
 for r in rows:
  t=lines[r['row']].split();key=struct.pack('<5h',*map(int,t[:5]))+b''.join(struct.pack('<2h',*map(int,z.split(':'))) for z in t[5:])
  assert key.hex()==r['key_hex'],('feature-key mismatch',r['row'])
with open('selected_keys.bin','wb') as f:
 f.write(struct.pack('<I',len(rows)))
 for r in rows:
  b=bytes.fromhex(r['key_hex']);f.write(struct.pack('<I',len(b)));f.write(b)
print('Explicit T/S feature keys verified:',len(rows),'rows file checked:',rp.exists())
