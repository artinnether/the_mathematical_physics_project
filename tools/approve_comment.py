"""Publish a reviewed comment from a local JSON export; never copies email."""
import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('entry',choices=['soliton','sphere','particles','holonomy']);p.add_argument('submission',type=Path);a=p.parse_args()
source=json.loads(a.submission.read_text());name=str(source['name']).strip();message=str(source['message']).strip()
if not 0<len(name)<=80 or not 0<len(message)<=5000:raise SystemExit('Invalid name or message length')
target=Path(__file__).resolve().parents[1]/'approved-comments.json';data=json.loads(target.read_text());comment={'name':name,'message':message}
if comment in data[a.entry]:raise SystemExit('Already published')
data[a.entry].append(comment);target.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
print('Approved locally. Commit and deploy approved-comments.json to publish.')
