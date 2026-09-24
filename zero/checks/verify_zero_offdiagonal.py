#!/usr/bin/env python3
"""Read-only exact certificate checker. No numerical construction is imported."""
import itertools as it,json,sys,re,hashlib
from pathlib import Path
from fractions import Fraction as F
import sympy as s

def need(b,m):
 if not b:raise ValueError(m)
def integer(v):
 if type(v)is int:return v
 need(type(v)is str and re.fullmatch(r'-?(0|[1-9][0-9]*)',v),'integer field');return int(v)
def unique(xs):
 d={}
 for k,v in xs:need(k not in d,'duplicate key');d[k]=v
 return d
def reject(v):raise ValueError('noninteger JSON number '+v)
def per(A):return s.expand(sum(s.prod(A[i,p[i]]for i in range(A.rows))for p in it.permutations(range(A.rows))))
def det(A):return s.expand(sum((-1)**sum(p[i]>p[j]for i in range(A.rows)for j in range(i+1,A.rows))*s.prod(A[i,p[i]]for i in range(A.rows))for p in it.permutations(range(A.rows))))
a,b,c,d,e,f=s.symbols('a b c d e f',real=True);vs=(a,b,c,d,e,f)
V=s.Matrix([[1,0,a,c+s.I*d],[0,1,b,e+s.I*f],[0,0,1,1]]);A=V.H*V;p=per(A)
H=s.Matrix(4,4,lambda i,j:s.expand(A[i,j]*per(A.minor_submatrix(i,j))))
need(A[0,1]==0 and H==H.H,'zero entry or Hermiticity')
need(all(s.expand(sum(H[i,j]for j in range(4))-p)==0 for i in range(4)),'row sums')
Q=s.Matrix([[1,0,0],[0,1,0],[0,0,1],[-1,-1,-1]])
K=(Q.T*(p*s.eye(4)-H)*Q).applyfunc(s.expand);pol=s.Poly(det(K),*vs)
need(pol.total_degree()==12,'degree');need(all(v.is_Integer for m,v in pol.terms()),'integer target')
target={m:F(int(v))for m,v in pol.terms()if v};need(len(target)==567,'target support');need(all(any(m[i]for m in target)for i in range(6)),'lost variable')
print('RECONSTRUCTED: 24-permutation permanent; 6-permutation determinant; degree12,567 terms,all6 real variables.',flush=True)
data=Path(sys.argv[1]).read_bytes();J=json.loads(data,object_pairs_hook=unique,parse_float=reject,parse_constant=reject)
need(set(J)=={'name','multiplier','scale','variables','blocks','coefficient_count'},'fields')
need(J['name']=='hook_zero_offdiagonal' and integer(J['multiplier'])==0,'name or multiplier');need(J['variables']==list(map(str,vs)),'variables')
scale=integer(J['scale']);need(scale==10240,'scale');orders=[24,26,20,21,20,22,22,21];need(len(J['blocks'])==8,'block count');actual={};reports=[]
for h,(block,n)in enumerate(zip(J['blocks'],orders)):
 need(set(block)=={'basis','denominator','numerator'},'block fields');need(len(block['basis'])==n,'basis length');beta=[]
 for terms in block['basis']:
  pp={}
  for m,rat in terms:
   need(type(m)is list and len(m)==6 and all(type(j)is int and j>=0 for j in m),'monomial');need(type(rat)is list and len(rat)==2,'rational pair')
   nu,de=map(integer,rat);need(de>0 and tuple(m)not in pp,'basis denominator/duplicate');pp[tuple(m)]=F(nu,de)
  beta.append(pp)
 den=integer(block['denominator']);N=block['numerator'];need(den>0 and len(N)==n and all(len(row)==n for row in N),'Gram data');G=[[F(integer(v),den)for v in row]for row in N];need(all(G[i][j]==G[j][i]for i in range(n)for j in range(n)),'symmetry')
 M=[row[:]for row in G];piv=[]
 for k in range(n):
  a=M[k][k];need(a>0,'nonpositive exact LDL pivot');piv.append(str(a))
  for i in range(k+1,n):
   r=M[i][k]/a
   for j in range(k+1,n):M[i][j]-=r*M[k][j]
 for i in range(n):
  for j in range(i,n):
   v=scale*G[i][j]*(1 if i==j else 2)
   for m,a in beta[i].items():
    for mm,b in beta[j].items():
     exp=tuple(c+d for c,d in zip(m,mm));actual[exp]=actual.get(exp,F(0))+v*a*b
 reports.append({'order':n,'denominator':str(den),'exact_LDL_pivots':piv});print('PD block',h,'order',n,'all exact pivots positive.',flush=True)
keys=set(actual)|set(target);need(len(keys)==integer(J['coefficient_count'])==625,'coefficient count');need(all(actual.get(m,F(0))==target.get(m,F(0))for m in keys),'full coefficient identity')
print('PASS: full unsymmetrized identity at625 positions;176 positive rational pivots. This certificate alone is a zero-entry hook determinant result, not unrestricted POT.',flush=True)
if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps({'certificate_sha256':hashlib.sha256(data).hexdigest(),'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'degree':12,'nonzero_terms':567,'positions_checked':625,'blocks':reports,'all_residuals_zero':True},indent=2))
