#!/usr/bin/env python3
"""Exact read-only checks: full complex rank-three (2,2) sector certificates.
Usage: python verify_complex22.py report.json certificate1.json ... certificate6.json
Rebuilds the permanent and the pairing matrix from all 24 permutations.
Only arbitrary-precision integers, rational Fractions and exact SymPy algebra
are acceptance premises. No numerical construction files are loaded.
"""
import hashlib,itertools as it,json,re,sys,time
from fractions import Fraction as F
from pathlib import Path
import sympy as s

def need(test,msg):
    if not test: raise ValueError(msg)
def integer(v):
    if type(v) is int:return v
    need(type(v) is str and re.fullmatch(r'-?(0|[1-9][0-9]*)',v),'integer field')
    return int(v)
def pairs(items):
    out={}
    for k,v in items:
        need(k not in out,'duplicate JSON key');out[k]=v
    return out
def reject(v):raise ValueError('non-integer JSON value: '+v)

start=time.monotonic()
x,a,b,z,c,d,e,f=s.symbols('x a b z c d e f',real=True)
variables=(x,a,b,z,c,d,e,f)
V=s.Matrix([[1,1,1,1],[0,x,a+s.I*b,c+s.I*d],[0,0,z,e+s.I*f]])
A=V.H*V
perms=list(it.permutations(range(4)))
phi={q:s.expand(s.prod(A[i,q[i]] for i in range(4))) for q in perms}
p=s.expand(sum(phi.values()))
parts=[frozenset((frozenset((0,1)),frozenset((2,3)))),
       frozenset((frozenset((0,2)),frozenset((1,3)))),
       frozenset((frozenset((0,3)),frozenset((1,2))))]
H=s.zeros(3)
for q in perms:
    for j,P in enumerate(parts):
        image=frozenset(frozenset(q[i] for i in B) for B in P)
        H[parts.index(image),j]+=phi[q]
H=H.applyfunc(s.expand)
need(H==H.H,'pairing Hermiticity')
need(all(s.expand(sum(H[i,j] for j in range(3))-p)==0 for i in range(3)),
     'pairing row sums')
Q=s.Matrix([[1,0],[0,1],[-1,-1]])
K=(Q.T*(p*s.eye(3)-H)*Q).applyfunc(s.expand)
need(K==K.H,'defect Hermiticity')
P=[[s.Poly(K[i,j],*variables) for j in range(2)] for i in range(2)]
targets={'complex22final':P[0][0]*P[1][1]-P[0][1]*P[1][0],
         'complex22trace':P[0][0]+P[1][1]}
expected={'complex22final':([31,25,27,27,23,24,25,24],3240,1219,12),
          'complex22trace':([6,5,5,4,6,5,5,4],96,67,6)}

Q3=s.Matrix([[1,0,0],[0,1,0],[0,0,1],[-1,-1,-1]])
def permanent(B):
    return s.expand(sum(s.prod(B[i,q[i]] for i in range(B.rows))
                        for q in it.permutations(range(B.rows))))
def determinant(B):
    return s.expand(sum((-1)**sum(q[i]>q[j] for i in range(B.rows)
                                  for j in range(i+1,B.rows))
                        *s.prod(B[i,q[i]] for i in range(B.rows))
                        for q in it.permutations(range(B.rows))))
for sec in ['31','211']:
    Fm=s.Matrix(4,4,lambda i,j:s.expand(A[i,j]*(permanent(A.minor_submatrix(i,j))
       if sec=='31' else (-1)**(i+j)*determinant(A.minor_submatrix(i,j)))))
    need(Fm==Fm.H,'hook Hermiticity')
    B=(Q3.T*(p*s.eye(4)-Fm)*Q3).applyfunc(s.expand)
    PP=[[s.Poly(B[i,j],*variables) for j in range(3)] for i in range(3)]
    targets['complex'+sec+'e1']=sum(PP[i][i] for i in range(3))
    name='complex31e2proved' if sec=='31' else 'complex211e2'
    targets[name]=sum(PP[i][i]*PP[j][j]-PP[i][j]*PP[j][i]
                      for i,j in it.combinations(range(3),2))
expected.update({
 'complex31e1':([6,5,5,4,6,5,5,4],144,67,6),
 'complex211e1':([6,5,5,4,6,5,5,4],144,67,6),
 'complex211e2':([74,56,52,46,61,52,56,53],9072,1377,12),
 'complex31e2proved':([50,40,47,46,51,49,37,34],7968,1346,12)})
print('DIRECT: actual conjugation, 24-permutation permanent and pairing matrix, eight real variables',flush=True)
report={'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'certificates':[]}
seen=set()
for filename in sys.argv[2:]:
    data=Path(filename).read_bytes()
    J=json.loads(data,object_pairs_hook=pairs,parse_float=reject,parse_constant=reject)
    need(set(J)=={'name','multiplier','scale','blocks','coefficient_count'},'root fields')
    name=J['name'];need(name in expected and name not in seen,'certificate name')
    seen.add(name);orders,scale,nterms,degree=expected[name]
    need(integer(J['multiplier'])==0,'unexpected multiplier')
    need(integer(J['scale'])==scale,'scale')
    need(integer(J['coefficient_count'])>0,'coefficient count')
    poly=targets[name]
    need(poly.total_degree()==degree,'target degree')
    target={m:F(int(v)) for m,v in poly.terms() if v}
    need(all(v.is_Integer for m,v in poly.terms()),'non-real or noninteger target coefficient')
    need(len(target)==nterms,'target support')
    need(all(any(m[j]>0 for m in target) for j in range(8)),'variable dropped')
    need(len(J['blocks'])==len(orders),'block count')
    actual={};records=[]
    for h,(block,n) in enumerate(zip(J['blocks'],orders)):
        need(set(block)=={'basis','denominator','numerator'},'block fields')
        need(len(block['basis'])==n,'basis length')
        beta=[]
        for terms in block['basis']:
            B={}
            for mon,rat in terms:
                need(type(mon) is list and len(mon)==8 and
                     all(type(v) is int and v>=0 for v in mon),'monomial')
                need(type(rat) is list and len(rat)==2,'rational pair')
                nu,de=map(integer,rat);need(de>0,'basis denominator')
                mon=tuple(mon);need(mon not in B,'duplicate basis monomial')
                B[mon]=F(nu,de)
            beta.append(B)
        den=integer(block['denominator']);need(den>0,'Gram denominator')
        N=block['numerator'];need(len(N)==n and all(len(row)==n for row in N),'Gram dimensions')
        G=[[F(integer(v),den) for v in row] for row in N]
        need(all(G[i][j]==G[j][i] for i in range(n) for j in range(n)),'Gram symmetry')
        M=[row[:] for row in G];piv=[]
        for k in range(n):
            dd=M[k][k];need(dd>0,'nonpositive rational LDL pivot');piv.append(str(dd))
            for i in range(k+1,n):
                aa=M[i][k]/dd
                for j in range(k+1,n):M[i][j]-=aa*M[k][j]
        for i in range(n):
            for j in range(i,n):
                coef=scale*G[i][j]*(1 if i==j else 2)
                for mon,u in beta[i].items():
                    for other,v in beta[j].items():
                        index=tuple(q+r for q,r in zip(mon,other))
                        actual[index]=actual.get(index,F(0))+coef*u*v
        records.append({'order':n,'denominator':str(den),'positive_exact_pivots':piv})
        print('BLOCK',name,h,'order',n,'all exact rational LDL pivots positive',flush=True)
    keys=set(actual)|set(target)
    need(all(actual.get(m,F(0))==target.get(m,F(0)) for m in keys),
         'full unsymmetrized coefficient identity')
    need(len(keys)==integer(J['coefficient_count']),'reported coefficient-space count')
    record={'name':name,'sha256':hashlib.sha256(data).hexdigest(),
            'scale':scale,'degree':degree,'nonzero_target_terms':len(target),
            'coefficient_positions_checked':len(keys),'blocks':records}
    report['certificates'].append(record)
    print('PASS',name,'full identity',len(keys),'positions;',nterms,'nonzero terms;',record['sha256'],flush=True)
need(seen==set(expected),'all six stated certificates required')
report['elapsed_seconds']=time.monotonic()-start
report['acceptance_arithmetic']='exact integers, Fraction, SymPy; no floating-point acceptance premise'
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n')
print('ALL SIX EXACT COMPLEX CERTIFICATES PASSED',flush=True)
