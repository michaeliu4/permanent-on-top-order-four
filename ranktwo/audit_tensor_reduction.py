#!/usr/bin/env python3
"""Exact finite tensor-map identities and algebraic checks, no fixtures or sampling."""
import itertools as it
from collections import Counter
import sympy as s

def need(v,msg):
    if not v: raise ValueError(msg)

def zero(A,msg):
    need(all(s.simplify(v)==0 for v in A),msg)

bits=list(it.product((0,1),repeat=4)); loc={b:i for i,b in enumerate(bits)}
perms=list(it.permutations(range(4))); pairs=list(it.combinations(range(4),2))
I3=s.eye(3); I16=s.eye(16)
F={}
for i,j in pairs:
    k,l=[t for t in range(4) if t not in (i,j)]
    A=s.zeros(3,16)
    for col,b in enumerate(bits):
        sig={(0,1):1,(1,0):-1}.get((b[i],b[j]),0)
        if sig:
            row=b[k]+b[l]
            A[row,col]=sig/s.sqrt(2)/(s.sqrt(2) if row==1 else 1)
    F[i,j]=A
E=[F[0,1].T,F[2,3].T]
zero(E[0].T*E[1],'disjoint singlet maps not orthogonal')
D=F[0,2].T
cs=[]
for A in E:
    cc=s.simplify((A.T*D)[0,0]); zero(A.T*D-cc*I3,'map overlap not scalar'); cs.append(cc)
T=s.simplify(D-sum((A*cc for A,cc in zip(E,cs)),s.zeros(16,3)))
norm=s.simplify((T.T*T)[0,0]); zero(T.T*T-norm*I3,'third map norm')
E.append(s.simplify(T/s.sqrt(norm)))
for i in range(3):
    for j in range(3): zero(E[i].T*E[j]-(I3 if i==j else s.zeros(3)),'E orthogonality')
Psym=s.zeros(16)
Es=s.zeros(16,5)
for col,b in enumerate(bits): Es[col,sum(b)]=1/s.sqrt(s.binomial(4,sum(b)))
Psym=Es*Es.T
P31=sum((A*A.T for A in E),s.zeros(16))
hs=[]
for (i,j),(k,l) in [((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))]:
    h=s.zeros(16,1)
    for col,b in enumerate(bits):
        x={(0,1):1,(1,0):-1}.get((b[i],b[j]),0)
        y={(0,1):1,(1,0):-1}.get((b[k],b[l]),0)
        h[col]=s.Rational(x*y,2)
    hs.append(h)
T1=hs[0]; T2=hs[1]-T1*(T1.T*hs[1])[0]
T2=s.simplify(T2/s.sqrt((T2.T*T2)[0])); J=T1.row_join(T2); P22=s.simplify(J*J.T)
Uall=Es.row_join(E[0]).row_join(E[1]).row_join(E[2]).row_join(J)
zero(Uall.T*Uall-I16,'orthonormal completeness')
zero(Psym+P31+P22-I16,'projector completeness')
zero(sum((h*h.T for h in hs),s.zeros(16))-s.Rational(3,2)*P22,'double-singlet tight frame')
need([s.trace(P) for P in (Psym,P31,P22)]==[5,9,2],'sector dimensions')
print('SECTORS: exact orthonormal decomposition 5+9+2; singlet overlaps',cs,'norm',norm,flush=True)
Us=[]; Rs=[]; Ts=[]; contracted=Counter(); chars=[]
for perm in perms:
    inv=[perm.index(i) for i in range(4)]
    U=s.zeros(16)
    for col,b in enumerate(bits): U[loc[tuple(b[inv[i]] for i in range(4))],col]=1
    Us.append(U)
    R=s.Matrix(3,3,lambda i,j:s.simplify((E[i].T*U*E[j])[0,0]))
    for i in range(3):
        for j in range(3): zero(E[i].T*U*E[j]-R[i,j]*I3,'S4 spin-1 action not scalar')
    T=s.simplify(J.T*U*J)
    zero(U*Es-Es,'symmetric sector action')
    for j in range(3): zero(U*E[j]-sum((E[i]*R[i,j] for i in range(3)),s.zeros(16,3)),'spin-1 invariance')
    zero(U*J-J*T,'spin-0 invariance')
    Rs.append(R); Ts.append(T)
    fixed=sum(perm[i]==i for i in range(4))
    fixedpairs=sum(set((perm[i],perm[j]))==set((i,j)) for i,j in pairs)
    need(s.simplify(s.trace(R)-(fixed-1))==0,'standard character')
    need(s.simplify(s.trace(T)-(fixedpairs-fixed))==0,'22 character')
    chars.append((fixed-1,fixedpairs-fixed))
    A=F[0,1]*U
    matches=[ij for ij in pairs if A==F[ij] or A==-F[ij]]
    need(len(matches)==1,'singlet orbit convention')
    contracted[matches[0]]+=1
need(all(contracted[p]==4 for p in pairs),'singlet orbit multiplicities')
zero(sum(Us,s.zeros(16))-24*Psym,'symmetric averaging')
zero(sum((3*s.Rational(c1,24)*U for U,(c1,c2) in zip(Us,chars)),s.zeros(16))-P31,'central 31 projector')
zero(sum((2*s.Rational(c2,24)*U for U,(c1,c2) in zip(Us,chars)),s.zeros(16))-P22,'central 22 projector')
for rr,d,n in ((Rs,3,8),(Ts,2,12)):
    for a,b in it.product(range(d),repeat=2):
        need(s.simplify(sum(R[a,b] for R in rr))==0,'nontrivial average')
    for a,b,c,d1 in it.product(range(d),repeat=4):
        need(s.simplify(sum(R[a,b]*R[c,d1] for R in rr))==n*int(a==c and b==d1),'matrix-coefficient orthogonality')
for a,b in it.product(range(3),repeat=2):
    for c,d in it.product(range(2),repeat=2):
        need(s.simplify(sum(R[a,b]*T[c,d] for R,T in zip(Rs,Ts)))==0,'cross-sector orthogonality')
print('UNIVERSAL TWIRL: all matrix-coefficient identities; constants 24,8,12;',
      'each F_ij occurs four times (sign cancels)',flush=True)
# All these checks are of fixed matrices or polynomial identities, not evaluated spinors.
u=s.symbols('u0:4'); v=s.symbols('v0:4')
w=s.Matrix([s.prod((u[i],v[i])[b[i]] for i in range(4)) for b in bits])
for i,j in pairs:
    k,l=[t for t in range(4) if t not in (i,j)]
    det=u[i]*v[j]-v[i]*u[j]
    sym=s.Matrix([u[k]*u[l],(u[k]*v[l]+v[k]*u[l])/s.sqrt(2),v[k]*v[l]])
    zero(F[i,j]*w-det*sym/s.sqrt(2),'universal F_ij product-vector formula')
for h,((i,j),(k,l)) in zip(hs,[((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))]):
    need(s.expand((h.T*w)[0]-(u[i]*v[j]-v[i]*u[j])*(u[k]*v[l]-v[k]*u[l])/2)==0,'double-singlet product formula')
print('PRODUCT VECTORS: all six F_ij formulas; all three double-singlet formulas',flush=True)
# Cycle expansion with actual Pauli i; no assumption that phases are real.
n=[s.symbols('n%d_0:3'%i,real=True) for i in range(4)]
pauli=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]
rho=[(s.eye(2)+sum((nn[j]*pauli[j] for j in range(3)),s.zeros(2)))/2 for nn in n]
per=0
for perm in perms:
    unseen=set(range(4)); term=1
    while unseen:
        i=min(unseen); cyc=[]
        while i in unseen:
            unseen.remove(i); cyc.append(i); i=perm[i]
        T=s.eye(2)
        for i in cyc: T=T*rho[i]
        term*=s.trace(T)
    per+=s.expand(term)
dot=lambda i,j:sum(n[i][h]*n[j][h] for h in range(3))
ss=sum(dot(i,j) for i,j in pairs)
tt=dot(0,1)*dot(2,3)+dot(0,2)*dot(1,3)+dot(0,3)*dot(1,2)
need(s.expand(per-(15+5*ss+tt)/2)==0,'Bloch permanent cycle expansion')
print('BLOCH: 24-cycle permanent identity with all 12 real components and actual conjugation',flush=True)
# Exact remainder behind the stated trace estimate, with trace(G)=4.
a,b,c,x,y,z=s.symbols('a b c x y z',real=True); k=4-a-b-c
EE=((b+c)**2+(a+c)**2+(a+b)**2-4*(x*x+y*y+z*z))/16
lhs=14*k+6*EE-8
rhs=2*k*(k+2)+((a-b)**2+(a-c)**2+(b-c)**2)/8+s.Rational(3,2)*(k*a-x*x+k*b-y*y+k*c-z*z)
need(s.expand(lhs-rhs)==0,'trace-bound remainder')
print('TRACE: exact remainder = 2k(k+2) + squared differences/8 + 3/2*(three PSD minors)',flush=True)
print('PASS: universal spectral constants, sector completeness, complex conventions, scalar/trace algebra.',flush=True)
