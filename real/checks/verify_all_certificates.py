#!/usr/bin/env python3
"""Exact, read-only verifier for all nine real order-four POT certificates.
Usage: python verify_all_certificates.py ../certificates/*.json
The input certificate data are necessary; numerical search is never invoked.
"""
import itertools as it
import json, sys, re, hashlib
from fractions import Fraction as F
from pathlib import Path
import sympy as s

def need(b,msg):
    if not b: raise ValueError(msg)
def integer(a):
    if type(a) is int: return a
    need(type(a) is str and re.fullmatch(r'-?(0|[1-9][0-9]*)',a), 'integer field')
    return int(a)
def distinct(items):
    out={}
    for k,v in items:
        need(k not in out,'duplicate JSON key'); out[k]=v
    return out
def reject(v): raise ValueError('non-integer JSON number '+v)
def per(A):
    return s.expand(sum(s.prod(A[i,q[i]] for i in range(A.rows))
                        for q in it.permutations(range(A.rows))))
def det(A):
    return s.expand(sum((-1)**sum(q[i]>q[j] for i in range(A.rows)
                                  for j in range(i+1,A.rows))
                        *s.prod(A[i,q[i]] for i in range(A.rows))
                        for q in it.permutations(range(A.rows))))
x,y,z,u,v=s.symbols('x y z u v',real=True); variables=(x,y,z,u,v)
Q=s.Matrix([[1,0,0],[0,1,0],[0,0,1],[-1,-1,-1]])
R=s.Matrix([[1,1],[-1,0],[0,-1],[0,-1],[-1,0],[1,1]])
subsets=list(it.combinations(range(4),2))
comp=lambda I:[i for i in range(4) if i not in I]
cache={}
def sectors(chart):
    if chart in cache: return cache[chart]
    V=(s.Matrix([[1,1,1,1],[0,x,y,u],[0,0,z,v]]) if chart=='new'
       else s.Matrix([[1,x,y,u],[0,1,z,v],[0,0,1,1]]))
    A=V.T*V; p=per(A)
    P=s.Matrix(4,4,lambda i,j:A[i,j]*per(A.minor_submatrix(i,j)))
    G=s.Matrix(4,4,lambda i,j:A[i,j]*(-1)**(i+j)*det(A.minor_submatrix(i,j)))
    C=s.Matrix(6,6,lambda i,j:per(A.extract(subsets[i],subsets[j]))
        *per(A.extract(comp(subsets[i]),comp(subsets[j]))))
    out={'31':Q.T*(p*s.eye(4)-P)*Q,
         '211':Q.T*(p*s.eye(4)-G)*Q,
         '22':R.T*(p*s.eye(6)-C)*R}
    out={k:B.applyfunc(s.expand) for k,B in out.items()}
    need(all(B==B.T for B in out.values()),'sector symmetry')
    cache[chart]=out; return out
orders={'last':[45,40,42,39], '31_e1':[5,4,4,5], '31_e2':[19,19,21,24],
        '211_e1':[5,4,4,5], '211_e2':[32,24,24,28], '211_012':[87,96,87,101],
        '22_0':[4,4,4,4], '22_1':[4,4,4,4], '22_01':[12,11,11,17]}
seen=set()
for fn in sys.argv[1:]:
    data=Path(fn).read_bytes()
    J=json.loads(data,object_pairs_hook=distinct,parse_float=reject,parse_constant=reject)
    need(set(J)=={'name','multiplier','scale','blocks','coefficient_count'},'root fields')
    name=J['name']; need(name in orders and name not in seen,'unknown/duplicate target')
    seen.add(name); need(integer(J['multiplier'])==0,'unexpected multiplier')
    scale=integer(J['scale']); need(scale>0,'positive scale')
    if name=='last':
        B=sectors('new')['31']; polynomial=det(B)
    else:
        sector,label=name.split('_'); B=sectors('old')[sector]
        if label.startswith('e'):
            k=int(label[1:]); polynomial=sum(det(B.extract(I,I))
                for I in it.combinations(range(B.rows),k))
        else:
            I=tuple(map(int,label)); polynomial=det(B.extract(I,I))
    target={m:F(int(c)) for m,c in s.Poly(polynomial,*variables).terms() if c}
    if name=='last':
        need(len(target)==1240 and max(map(sum,target))==16,'new target degree/support')
    need(len(J['blocks'])==len(orders[name]),'block count'); actual={}
    for h,(block,n) in enumerate(zip(J['blocks'],orders[name])):
        need(set(block)=={'basis','denominator','numerator'},'block fields')
        need(len(block['basis'])==n,'basis dimension'); beta=[]
        for terms in block['basis']:
            pp={}
            for m,rat in terms:
                need(type(m) is list and len(m)==5 and
                     all(type(a) is int and a>=0 for a in m),'monomial')
                need(type(rat) is list and len(rat)==2,'rational pair')
                a,b=map(integer,rat); need(b>0,'positive basis denominator')
                m=tuple(m); need(m not in pp,'duplicate basis monomial'); pp[m]=F(a,b)
            beta.append(pp)
        denominator=integer(block['denominator']); need(denominator>0,'positive Gram denominator')
        N=block['numerator']; need(len(N)==n and all(len(row)==n for row in N),'Gram dimensions')
        G=[[F(integer(q),denominator) for q in row] for row in N]
        need(all(G[i][j]==G[j][i] for i in range(n) for j in range(n)),'Gram symmetry')
        M=[row[:] for row in G]
        for k in range(n):
            pivot=M[k][k]; need(pivot>0,'nonpositive exact rational LDL pivot')
            for i in range(k+1,n):
                a=M[i][k]/pivot
                for j in range(k+1,n): M[i][j]-=a*M[k][j]
        for i in range(n):
            for j in range(i,n):
                a=scale*G[i][j]*(1 if i==j else 2)
                for m,c in beta[i].items():
                    for mm,d in beta[j].items():
                        e=tuple(q+r for q,r in zip(m,mm))
                        actual[e]=actual.get(e,F(0))+a*c*d
    need(all(actual.get(m,F(0))==target.get(m,F(0))
             for m in set(actual)|set(target)),'full unsymmetrized coefficient identity')
    print('PASS',name,'orders',orders[name],'target terms',len(target),
          'sha256',hashlib.sha256(data).hexdigest(),flush=True)
need(seen==set(orders),'the complete proof requires all nine certificates')
print('ALL NINE EXACT IDENTITIES AND RATIONAL POSITIVITY CHECKS PASSED')
