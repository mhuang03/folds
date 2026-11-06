#!/usr/bin/env python3
"""oeis.py "t1,t2,..." [...]: query OEIS (JSON) and print matching A-numbers and names."""
import sys, json, urllib.request, urllib.parse

def query(terms):
    url = 'https://oeis.org/search?' + urllib.parse.urlencode({'q': terms, 'fmt': 'json'})
    import subprocess
    raw = subprocess.run(['curl', '-s', '-m', '30', url], capture_output=True, text=True).stdout
    data = json.loads(raw) if raw.strip() else []
    if isinstance(data, dict):
        data = data.get('results') or []
    return data or []

if __name__ == '__main__':
    for q in sys.argv[1:]:
        res = query(q)
        print('query:', q, '->', len(res), 'results')
        for e in res[:5]:
            print('   A%06d' % e['number'], e['name'][:110])
