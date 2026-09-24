"""Exact verifier. No floating-point arithmetic or optimization is used."""
import sys, json, itertools as it, math
from pathlib import Path
from fractions import Fraction as F
import sympy as s
import numpy as np
path=sys.argv[1] if len(sys.argv)>1 else str(Path(__file__).with_name('soules_order4_rank2_certificate.json'))
with open(path) as fh: cert=json.load(fh)
r,a,b,c,d=s.symbols('r a b c d',real=True);xs=(r,a,b,c,d)
z=[s.Integer(0),r,a+s.I*b,c+s.I*d]
H=s.Matrix(4,4,lambda i,j:1+s.conjugate(z[i])*z[j])
p=s.expand(sum(s.prod(H[i,perm[i]]for i in range(4))for perm in it.permutations(range(4))))
M=p*s.diag(1,2,1)
for i,j in it.combinations(range(4),2):
 k,l=[t for t in range(4)if t not in(i,j)]
 g=s.Matrix([1,z[k]+z[l],z[k]*z[l]])
 M-=2*(z[i]-z[j])*s.conjugate(z[i]-z[j])*g*g.H
M=M.applyfunc(s.expand)
f=s.expand(M[0,0]*(M[1,1]*M[2,2]-M[1,2]*M[2,1])-M[0,1]*(M[1,0]*M[2,2]-M[1,2]*M[2,0])+M[0,2]*(M[1,0]*M[2,1]-M[1,1]*M[2,0]))
target={m:F(int(co))for m,co in s.Poly(f,*xs).terms()}
print('determinant reconstructed:',len(target),'monomials',flush=True)
raw={}
for bi,block in enumerate(cert['blocks']):
 mons=[tuple(m)for m in block['monomials']];P=[[F(*x)for x in row]for row in block['basis']]
 n=len(P[0]);den=int(block['denominator']);N=np.array([[int(x)for x in row]for row in block['numerator']],dtype=object)
 C=np.array(block['congruence'],dtype=object)
 assert N.shape==C.shape==(n,n)
 assert np.array_equal(N,N.T)
 assert all(C[i,j]==0 for i in range(n)for j in range(i+1,n))
 assert all(C[i,i]!=0 for i in range(n))
 W=C@N@C.T
 assert all(W[i,i]>sum(abs(W[i,j])for j in range(n)if j!=i)for i in range(n))
 polys=[{mons[i]:P[i][j]for i in range(len(mons))if P[i][j]}for j in range(n)]
 for i in range(n):
  for j in range(i,n):
   q=F(int(N[i,j])*(1 if i==j else 2),den)
   for m,u in polys[i].items():
    for mm,v in polys[j].items():
     ee=tuple(x+y for x,y in zip(m,mm));raw[ee]=raw.get(ee,F(0))+q*u*v
 print('block',bi,'exact positivity passed;',n,'by',n,flush=True)
actual={};scale=F(cert['scale'],2)
for m,co in raw.items():
 sw=(m[0],m[3],m[4],m[1],m[2])
 actual[m]=actual.get(m,F(0))+scale*co
 actual[sw]=actual.get(sw,F(0))+scale*co
assert all(actual.get(m,F(0))==target.get(m,F(0))for m in set(actual)|set(target))
print('PASS: exact SOS identity and four exact positive-definiteness certificates.')
