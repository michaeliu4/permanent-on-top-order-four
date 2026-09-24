#!/usr/bin/env python3
"""Read-only verification of the STORED Soules certificate.
Python standard library only: arbitrary-precision int and Fraction.
No construction, optimization, sampling, floating point, or input alteration.
Polynomial keys are (r,a,b,c,d,i)-exponents; the last is reduced modulo i^2=-1.
"""
import sys, json, re, hashlib, itertools as it
from fractions import Fraction as F
from functools import reduce
from pathlib import Path

def need(test, message):
    if not test: raise ValueError(message)

def integer(v):
    if type(v) is int: return v
    need(type(v) is str and re.fullmatch(r'-?(0|[1-9][0-9]*)', v),
         'non-integer field')
    return int(v)

def pairs(items):
    d = {}
    for k,v in items:
        need(k not in d, 'duplicate JSON key')
        d[k] = v
    return d

def reject(v): raise ValueError('non-integer JSON number: '+v)

def add(*ps):
    q = {}
    for p in ps:
        for m,c in p.items(): q[m] = q.get(m,0)+c
    return {m:c for m,c in q.items() if c}

def times(c,p): return {m:c*v for m,v in p.items() if c*v}

def mul(p,q):
    ans = {}
    for m,c in p.items():
        for n,d in q.items():
            e = tuple(m[j]+n[j] for j in range(5))+(m[5]^n[5],)
            v = -c*d if m[5] and n[5] else c*d
            ans[e] = ans.get(e,0)+v
    return {m:c for m,c in ans.items() if c}

ONE = {(0,0,0,0,0,0):1}
I = {(0,0,0,0,0,1):1}
prod = lambda seq: reduce(mul,seq,ONE)
star = lambda p: {m:(-c if m[5] else c) for m,c in p.items()}
vars = [{tuple(int(j==k) for j in range(6)):1} for k in range(5)]
r,a,b,c,d = vars
z = [{}, r, add(a,mul(I,b)), add(c,mul(I,d))]
V = [[ONE for _ in range(4)],z]
H = [[add(*(mul(star(V[k][i]),V[k][j]) for k in range(2)))
      for j in range(4)] for i in range(4)]
perms = list(it.permutations(range(4)))
p = add(*(prod(H[i][sigma[i]] for i in range(4)) for sigma in perms))
# A second expression is checked, not assumed.
e = [add(*(prod(z[i] for i in J) for J in it.combinations(range(4),k)))
     for k in range(1,4)]
p2 = add(times(24,ONE),*(times(w,mul(v,star(v)))
         for w,v in zip((6,4,6),e)))
need(p==p2, '24-permutation permanent mismatch')
need(p==star(p), 'permanent not real')
M = [[times((1,2,1)[i],p) if i==j else {} for j in range(3)] for i in range(3)]
for i,j in it.combinations(range(4),2):
    k,l = [t for t in range(4) if t not in (i,j)]
    delta = add(mul(V[0][i],V[1][j]),times(-1,mul(V[1][i],V[0][j])))
    weight = mul(delta,star(delta))
    g = [ONE,add(z[k],z[l]),mul(z[k],z[l])]
    for u in range(3):
        for v in range(3):
            M[u][v] = add(M[u][v],times(-2,prod((weight,g[u],star(g[v])))))
need(all(M[j][i]==star(M[i][j]) for i in range(3) for j in range(3)),
     'M is not Hermitian')
f = {}
for sigma in it.permutations(range(3)):
    sign = (-1)**sum(sigma[i]>sigma[j] for i in range(3) for j in range(i+1,3))
    f = add(f,times(sign,prod(M[i][sigma[i]] for i in range(3))))
need(all(m[5]==0 for m in f), 'determinant has imaginary coefficients')
target = {m[:5]:c for m,c in f.items()}
need(len(target)==1143 and max(map(sum,target))==16, 'target size or degree')
need(set(j for m in target for j in range(5) if m[j])==set(range(5)),
     'a real variable has been lost')
print('DIRECT: permanent (24 permutations), determinant (6 permutations),',
      '1143 monomials, degree 16, all five real variables',flush=True)

path = Path(sys.argv[1])
data = path.read_bytes()
cert = json.loads(data,object_pairs_hook=pairs,parse_float=reject,parse_constant=reject)
need(type(cert) is dict and set(cert)=={'scale','blocks'}, 'root fields')
need(integer(cert['scale'])==207360, 'unexpected scale')
need(type(cert['blocks']) is list and len(cert['blocks'])==4, 'block count')
raw = {}
report = {'certificate_sha256':hashlib.sha256(data).hexdigest(),'blocks':[]}
for h,(block,mcount,n) in enumerate(zip(cert['blocks'],(92,84,91,84),(69,61,66,64))):
    need(set(block)=={'monomials','basis','denominator','numerator','congruence'},
         'block fields')
    mons = block['monomials']
    need(len(mons)==mcount, 'monomial count')
    need(all(type(m) is list and len(m)==5 and
             all(type(v) is int and v>=0 for v in m) for m in mons), 'monomials')
    mons = list(map(tuple,mons))
    need(len(set(mons))==mcount, 'duplicate monomials')
    basis = block['basis']
    need(len(basis)==mcount and all(len(row)==n for row in basis),'basis dimensions')
    P = []
    for row in basis:
        rr = []
        for v in row:
            need(type(v) is list and len(v)==2, 'rational field')
            num,den = map(integer,v)
            need(den>0, 'basis denominator must be positive')
            rr.append(F(num,den))
        P.append(rr)
    den = integer(block['denominator'])
    need(den>0, 'Gram denominator must be positive')
    matrices = []
    for key in ('numerator','congruence'):
        arr = block[key]
        need(len(arr)==n and all(len(row)==n for row in arr),key+' dimensions')
        matrices.append([list(map(integer,row)) for row in arr])
    N,C = matrices
    need(all(N[i][j]==N[j][i] for i in range(n) for j in range(n)), 'N symmetry')
    need(all(C[i][j]==0 for i in range(n) for j in range(i+1,n)), 'C triangularity')
    need(all(C[i][i]!=0 for i in range(n)), 'C invertibility')
    # Entirely arbitrary-precision Python integer matrix products.
    CN = [[sum(C[i][k]*N[k][j] for k in range(i+1))
           for j in range(n)] for i in range(n)]
    W = [[sum(CN[i][k]*C[j][k] for k in range(j+1))
          for j in range(n)] for i in range(n)]
    need(all(W[i][j]==W[j][i] for i in range(n) for j in range(n)), 'W symmetry')
    margins = [W[i][i]-sum(abs(W[i][j]) for j in range(n) if i!=j) for i in range(n)]
    need(all(v>0 for v in margins), 'strict integer diagonal dominance failed')
    polys = [{mons[i]:P[i][j] for i in range(mcount) if P[i][j]} for j in range(n)]
    for i in range(n):
        for j in range(i,n):
            q = F(N[i][j]*(1 if i==j else 2),den)
            if not q: continue
            for m,u in polys[i].items():
                for mm,v in polys[j].items():
                    ee = tuple(x+y for x,y in zip(m,mm))
                    raw[ee] = raw.get(ee,F(0))+q*u*v
    info = {'order':n,'monomials':mcount,'denominator':str(den),
            'min_margin':str(min(margins)),'margins':[str(v) for v in margins],
            'min_abs_C_diagonal':str(min(abs(C[i][i]) for i in range(n))),
            'max_W_bit_length':max(abs(v).bit_length() for row in W for v in row),
            'max_N_bit_length':max(abs(v).bit_length() for row in N for v in row)}
    report['blocks'].append(info)
    print('BLOCK',h,'order',n,'denominator',den,'min_margin',min(margins),
          'max_W_bits',info['max_W_bit_length'],flush=True)
actual = {}
for m,q in raw.items():
    for mm in (m,(m[0],m[3],m[4],m[1],m[2])):
        actual[mm] = actual.get(mm,F(0))+103680*q
need(all(actual.get(m,0)==target.get(m,0) for m in set(actual)|set(target)),
     'full unsymmetrized coefficient identity failed')
report['raw_nonzero_coefficients'] = sum(q!=0 for q in raw.values())
report['coefficient_indices_checked'] = len(set(actual)|set(target))
report['actual_nonzero_coefficients'] = sum(q!=0 for q in actual.values())
report['all_coefficient_residuals_zero'] = True
report['integer_or_rational_acceptance_only'] = True
report['verifier_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
print('COEFFICIENTS:',report['coefficient_indices_checked'],'indices checked;',
      report['actual_nonzero_coefficients'],'nonzero after full swap and scale;',
      'all residuals zero',flush=True)
print('PASS: stored certificate, strict fields, exact positivity, full identity.',flush=True)
if len(sys.argv)>2:
    Path(sys.argv[2]).write_text(json.dumps(report,indent=2)+'\n')
