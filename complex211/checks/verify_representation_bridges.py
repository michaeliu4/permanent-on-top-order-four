"""Exact finite coefficient/group audit, valid for arbitrary complex entries."""
import itertools as it,sympy as s
S=list(it.permutations(range(4)));subs=list(it.combinations(range(4),2));one=s.ones(4,1)
Q=s.Matrix([[1,0,0],[0,1,0],[0,0,1],[-1,-1,-1]])
R=s.Matrix([[1,1],[-1,0],[0,-1],[0,-1],[-1,0],[1,1]])
inc=s.Matrix(4,6,lambda i,j:int(i in subs[j]));assert inc*R==s.zeros(4,2)
Qleft=(Q.T*Q).inv()*Q.T;Rleft=(R.T*R).inv()*R.T
chars=[]
for q in S:
 sg=(-1)**sum(q[i]>q[j] for i in range(4) for j in range(i+1,4))
 P=s.Matrix(4,4,lambda i,j:int(q[i]==j));B=s.Matrix(6,6,lambda i,j:int(tuple(sorted(q[k] for k in subs[i]))==subs[j]))
 assert P*one==one
 X=Qleft*P*Q;Y=Rleft*B*R
 assert P*Q==Q*X and B*R==R*Y
 c=[1,s.trace(X),s.trace(Y),sg*s.trace(X),sg];chars.append(c)
 # The coefficient of prod_i a[i,q(i)] in each compound is precisely P,sg*P,B.
 for i in range(4):
  for j in range(4):
   if q[i]!=j:continue
   rows=[k for k in range(4) if k!=i];cols=[k for k in range(4) if k!=j]
   perm=[cols.index(q[k]) for k in rows]
   sg3=(-1)**sum(perm[a]>perm[b] for a in range(3) for b in range(a+1,3))
   assert sg3*(-1)**(i+j)==sg
G=s.Matrix(chars).T*s.Matrix(chars)
assert G==24*s.eye(5)
assert [int(c) for c in chars[0]]==[1,3,2,3,1]
# Check universal derivative block indices, no sample matrix values.
for sigma in S:
 for tau in S:
  k=sigma.index(0);l=tau.index(0)
  factors=[(sigma[j],tau[j]) for j in range(4)]
  if k!=l:assert (0,0) not in factors
  else:
   remaining=[p for p in factors if p!=(0,0)]
   sr=[sigma[j]-1 for j in range(4) if j!=k];tr=[tau[j]-1 for j in range(4) if j!=k]
   assert remaining==[(a+1,b+1) for a,b in zip(sr,tr)]
print('PASS: standard, (2,2), sign-standard compounds; irreducible characters; dimensions 1,3,2,3,1.')
print('PASS: cofactor signs and all 576 universal diagonal-decrement block indices.')
