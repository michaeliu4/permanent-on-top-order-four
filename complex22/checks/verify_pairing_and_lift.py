"""Exact universal pairing-sector bridge and an exact indefinite lift fixture."""
import itertools as it,sympy as s,json
from pathlib import Path
S=list(it.permutations(range(4)));index={q:i for i,q in enumerate(S)}
parts=[frozenset((frozenset((0,1)),frozenset((2,3)))),frozenset((frozenset((0,2)),frozenset((1,3)))),frozenset((frozenset((0,3)),frozenset((1,2))))]
def action(q,P):return frozenset(frozenset(q[i] for i in B) for B in P)
def rho(q):return s.Matrix(3,3,lambda i,j:int(action(q,parts[j])==parts[i]))
E=[s.Matrix(24,3,lambda i,j:int(action(S[i],parts[k])==parts[j])) for k in range(2)]
Q=s.Matrix([[1/s.sqrt(2),1/s.sqrt(6)],[-1/s.sqrt(2),1/s.sqrt(6)],[0,-2/s.sqrt(6)]])
C1=E[0]*Q/s.sqrt(8);C2=(2*E[1]+E[0])*Q/s.sqrt(24)
assert s.simplify(C1.T*C1)==s.eye(2) and s.simplify(C2.T*C2)==s.eye(2)
assert s.simplify(C1.T*C2)==s.zeros(2)
P=s.zeros(24);chars=[]
for g in S:
    G=s.zeros(24)
    for i,q in enumerate(S):G[i,index[tuple(g[q[k]] for k in range(4))]]=1
    R=rho(g);B=Q.T*R.T*Q;chi=s.trace(R)-1;chars.append(chi)
    assert s.simplify(G*C1-C1*B)==s.zeros(24,2)
    assert s.simplify(G*C2-C2*B)==s.zeros(24,2)
    assert E[0].T*G*E[0]==8*R.T
    P+=chi*G/12
assert sum(c*c for c in chars)==24
assert s.simplify(P-C1*C1.T-C2*C2.T)==s.zeros(24)
assert P*P==P and s.trace(P)==4
print('PASS: all 24 universal pairing coefficients; correct transpose; two complete (2,2) copies.',flush=True)

# Direct actual-conjugation reconstruction of the polarized lift.
a,b,c,d=s.symbols('a b c d',real=True)
r=s.symbols('r0:3',real=True);t=s.symbols('t0:3',real=True);xi=s.Matrix([r[i]+s.I*t[i] for i in range(3)])
V=s.Matrix([[xi[0],1,a,b],[xi[1],0,1,c+s.I*d],[xi[2],0,0,1]])
A=V.H*V;p=0;H=s.zeros(3)
for g in S:
    phi=s.prod(A[i,g[i]] for i in range(4));p+=phi;H+=phi*rho(g)
Q0=s.Matrix([[1,0],[0,1],[-1,-1]])
K=(Q0.T*(p*s.eye(3)-H)*Q0).applyfunc(s.expand)
W=s.zeros(6)
for i in range(3):
 for j in range(3):
  for u in range(2):
   for v in range(2):W[2*i+u,2*j+v]=s.expand((s.diff(K[u,v],r[i],r[j])-s.I*s.diff(K[u,v],r[i],t[j]))/2)
assert W==W.H
for u in range(2):
 for v in range(2):assert s.expand(sum(s.conjugate(xi[i])*xi[j]*W[2*i+u,2*j+v] for i in range(3) for j in range(3))-K[u,v])==0
W0=W.subs({a:0,b:1,c:0,d:1});q=s.Matrix([5,-4,-4*s.I,5*s.I,-2,-2])
assert s.expand((q.H*W0*q)[0])==-18
assert (q.H*q)[0]==90
assert s.det(s.Matrix([[q[0],q[1]],[q[2],q[3]]]))==9*s.I
print('PASS: universal six-dimensional lift, actual conjugates; exact non-PSD numerator -18, norm 90, product-rank obstruction 9i.',flush=True)
print('The universal block-positivity conclusion uses the separately certified pairing-sector theorem, not the negative fixture.',flush=True)
