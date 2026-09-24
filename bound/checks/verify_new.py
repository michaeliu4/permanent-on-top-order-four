#!/usr/bin/env python3
"""Read-only exact check of new hook certificates; no numerical constructor.
Usage: python verify_new.py certificate.json [report.json]
Uses CPython arbitrary-precision int/Fraction and SymPy exact polynomials.
"""
import itertools as it,json,re,hashlib,sys
from fractions import Fraction as Rat
from pathlib import Path
import sympy as s

def need(test,message):
 if not test:raise ValueError(message)
def integer(v):
 if type(v) is int:return v
 need(type(v) is str and re.fullmatch(r'-?(0|[1-9][0-9]*)',v),'integer field')
 return int(v)
def unique(items):
 d={}
 for k,v in items:
  need(k not in d,'duplicate JSON key');d[k]=v
 return d
def reject(v):raise ValueError('noninteger JSON number '+v)
def permanent(A):
 return s.expand(sum(s.prod(A[i,p[i]]for i in range(A.rows))for p in it.permutations(range(A.rows))))

path=Path(sys.argv[1]);raw=path.read_bytes();J=json.loads(raw,object_pairs_hook=unique,parse_float=reject,parse_constant=reject)
need(set(J)=={'name','multiplier','scale','blocks','coefficient_count'},'root fields')
name=J['name'];need(integer(J['multiplier'])==0,'no multiplier allowed')
t=s.symbols('x a b z c d e f',real=True);x,a,b,z,c,d,e,f=t
V=s.Matrix([[1,1,1,1],[0,x,a+s.I*b,c+s.I*d],[0,0,z,e+s.I*f]])
A=V.H*V;p=permanent(A)
F=s.Matrix(4,4,lambda i,j:s.expand(A[i,j]*permanent(A.minor_submatrix(i,j))))
need(F==F.H,'Hermiticity')
need(all(s.expand(sum(F[i,j]for j in range(4))-p)==0 for i in range(4)),'row sum')
Q=s.Matrix([[1,0,0],[0,1,0],[0,0,1],[-1,-1,-1]])
if name=='hook_bound_19_18':
 scale=912;orders=[33,27]*4;count=930;degree=8
 K=(Q.T*(19*p*s.eye(4)-18*F)*Q).applyfunc(s.expand)
 q=s.symbols('q0:6',real=True);y=s.Matrix([q[i]+s.I*q[i+3]for i in range(3)])
 targetpoly=s.Poly(s.expand((y.H*K*y)[0]),*(t+q));nv=14
elif name=='hook_moment_reduced':
 scale=13584;orders=[50,61,52,40,52,48,45,46];count=1346;degree=12;nv=8
 pp=s.Poly(p,*t);FF=[[s.Poly(F[i,j],*t)for j in range(4)]for i in range(4)]
 T=sum(FF[i][i]for i in range(4))-pp
 E=sum(FF[i][i]*FF[j][j]-FF[i][j]*FF[j][i]for i,j in it.combinations(range(4),2))-pp*T
 targetpoly=16*pp**2-8*pp*T-3*T**2+12*E
else:raise ValueError('unknown target')
need(integer(J['scale'])==scale,'scale')
need(targetpoly.total_degree()==degree,'degree')
need(all(c.is_Integer for m,c in targetpoly.terms()),'real integer coefficients')
exact={m:Rat(int(c))for m,c in targetpoly.terms()if c}
need(len(exact)==count,'support count')
need(all(any(m[j]for m in exact)for j in range(nv)),'variable lost')
print('RECONSTRUCTED',name,'degree',degree,'terms',count,'variables',nv,flush=True)
actual={};report={'name':name,'certificate_sha256':hashlib.sha256(raw).hexdigest(),'blocks':[]}
need(len(J['blocks'])==len(orders),'block count')
for h,(bl,n)in enumerate(zip(J['blocks'],orders)):
 need(set(bl)=={'basis','denominator','numerator'},'block fields')
 need(len(bl['basis'])==n,'basis dimension');beta=[]
 for pp in bl['basis']:
  b={}
  for m,c in pp:
   need(type(m) is list and len(m)==nv and all(type(i)is int and i>=0 for i in m),'monomial')
   need(type(c)is list and len(c)==2,'rational pair');nu,de=map(integer,c)
   need(de>0 and tuple(m)not in b,'basis denominator or duplicate');b[tuple(m)]=Rat(nu,de)
  beta.append(b)
 den=integer(bl['denominator']);N=bl['numerator'];need(den>0,'positive denominator')
 need(len(N)==n and all(len(r)==n for r in N),'Gram dimensions')
 G=[[Rat(integer(c),den)for c in row]for row in N]
 need(all(G[i][j]==G[j][i]for i in range(n)for j in range(n)),'Gram symmetry')
 W=[r[:]for r in G];piv=[]
 for k in range(n):
  d=W[k][k];need(d>0,'nonpositive exact LDL pivot');piv.append(str(d))
  for i in range(k+1,n):
   a=W[i][k]/d
   for j in range(k+1,n):W[i][j]-=a*W[k][j]
 for i in range(n):
  for j in range(i,n):
   c=scale*G[i][j]*(1 if i==j else 2)
   for m,a in beta[i].items():
    for mm,b in beta[j].items():
     e=tuple(i+j for i,j in zip(m,mm));actual[e]=actual.get(e,Rat(0))+c*a*b
 report['blocks'].append({'order':n,'denominator':str(den),'positive_LDL_pivots':piv})
 print('BLOCK',h,'order',n,'all exact rational pivots positive',flush=True)
keys=set(actual)|set(exact)
need(len(keys)==integer(J['coefficient_count']),'coefficient positions')
need(all(actual.get(m,Rat(0))==exact.get(m,Rat(0))for m in keys),'full coefficient identity')
report.update({'degree':degree,'nonzero_terms':count,'coefficient_positions':len(keys),'all_residuals_zero':True,'positive_pivots':sum(orders),'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()})
print('PASS',name,'full unsymmetrized identity;',len(keys),'coefficient positions;',sum(orders),'positive pivots',flush=True)
if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps(report,indent=2)+'\n')
