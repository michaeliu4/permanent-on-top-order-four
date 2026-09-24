"""Read-only exact verification of the complex (2,1,1) certificates.
Usage: python verify_cofactor.py ../certificates/*.json --report report.json
Requires SymPy; all acceptance arithmetic is integer/rational/symbolic.
No numerical constructor, optimizer, numpy, or pickle is imported.
"""
import argparse, hashlib, itertools as it, json, re
from fractions import Fraction as F
from pathlib import Path
import sympy as s

def need(b, message):
    if not b:
        raise ValueError(message)

def integer(v):
    if type(v) is int:
        return v
    need(type(v) is str and re.fullmatch(r'-?(0|[1-9][0-9]*)', v),
         'invalid integer field')
    return int(v)

def unique(items):
    out = {}
    for k, v in items:
        need(k not in out, 'duplicate JSON key')
        out[k] = v
    return out

def reject(v):
    raise ValueError('noninteger JSON number: ' + v)

def matrix_function(A, alternating=False):
    out = 0
    for q in it.permutations(range(A.rows)):
        sign = (-1)**sum(q[i] > q[j] for i in range(A.rows)
                         for j in range(i+1, A.rows)) if alternating else 1
        out += sign*s.prod(A[i, q[i]] for i in range(A.rows))
    return s.expand(out)

parser = argparse.ArgumentParser()
parser.add_argument('certificates', nargs='+')
parser.add_argument('--report')
args = parser.parse_args()
x,a,b,z,c,d,e,f = s.symbols('x a b z c d e f', real=True)
variables = (x,a,b,z,c,d,e,f)
V = s.Matrix([[1,1,1,1], [0,x,a+s.I*b,c+s.I*d], [0,0,z,e+s.I*f]])
A = V.H*V
p = matrix_function(A)
G = s.Matrix(4,4,lambda i,j: s.expand(
    A[i,j]*(-1)**(i+j)*matrix_function(A.minor_submatrix(i,j), True)))
k = s.Matrix([(-1)**i*matrix_function(
    V[:, [j for j in range(4) if j != i]], True) for i in range(4)])
need(all(s.expand(v) == 0 for v in V*k), 'signed null-vector identity')
need(G == G.H, 'cofactor Hermiticity')
need(all(s.expand(sum(G[i,j] for j in range(4))) == 0 for i in range(4)),
     'cofactor row sums')
need(all(s.expand(G[i,j]-s.conjugate(k[i])*A[i,j]*k[j]) == 0
         for i in range(4) for j in range(4)), 'cofactor Gram factorization')
P = s.Poly(p, *variables)
GP = [[s.Poly(G[i,j], *variables) for j in range(4)] for i in range(4)]
T = sum(GP[i][i] for i in range(4))
E = sum(GP[i][i]*GP[j][j]-GP[i][j]*GP[j][i]
        for i,j in it.combinations(range(4), 2))
targets = {'moment211final': 3*P**2-2*P*T-T**2+4*E,
           'trace211two': 2*P-T, 'trace211sharpexact': 8*P-5*T}
expected = {
    'moment211final': (3024, [41,35,47,46,51,49,37,34], 1346, 12),
    'trace211two': (48, [6,5,5,4,6,5,5,4], 67, 6),
    'trace211sharpexact': (192, [5,5,4,4,5,5,4,4], 67, 6)}
seen, reports = set(), []
for filename in args.certificates:
    data = Path(filename).read_bytes()
    J = json.loads(data, object_pairs_hook=unique,
                   parse_float=reject, parse_constant=reject)
    need(set(J) == {'name','multiplier','scale','blocks','coefficient_count'},
         'root fields')
    name = J['name']
    need(name in targets and name not in seen, 'unknown/duplicate target')
    seen.add(name)
    scale, orders, terms, degree = expected[name]
    need(integer(J['multiplier']) == 0 and integer(J['scale']) == scale,
         'unexpected multiplier/scale')
    need(len(J['blocks']) == 8, 'block count')
    target = targets[name]
    need(target.total_degree() == degree, 'target degree')
    need(all(v.is_Integer for m,v in target.terms()), 'noninteger target')
    exact = {m:F(int(v)) for m,v in target.terms() if v}
    need(len(exact) == terms and all(any(m[i] for m in exact) for i in range(8)),
         'target support or missing variable')
    actual, blocks = {}, []
    for block, n in zip(J['blocks'], orders):
        need(set(block) == {'basis','denominator','numerator'}, 'block fields')
        need(len(block['basis']) == n, 'basis dimension')
        beta = []
        for terms0 in block['basis']:
            q = {}
            for m, rat in terms0:
                need(type(m) is list and len(m) == 8 and
                     all(type(t) is int and t >= 0 for t in m), 'monomial')
                need(type(rat) is list and len(rat) == 2, 'rational pair')
                num, den = map(integer, rat)
                need(den > 0 and tuple(m) not in q, 'denominator/duplicate')
                q[tuple(m)] = F(num, den)
            beta.append(q)
        den = integer(block['denominator'])
        N = block['numerator']
        need(den > 0 and len(N) == n and all(len(row) == n for row in N),
             'Gram denominator/dimensions')
        Q = [[F(integer(v), den) for v in row] for row in N]
        need(all(Q[i][j] == Q[j][i] for i in range(n) for j in range(n)),
             'Gram symmetry')
        M, pivots = [row[:] for row in Q], []
        for j in range(n):
            pivot = M[j][j]
            need(pivot > 0, 'nonpositive exact rational LDL pivot')
            pivots.append(pivot)
            for i in range(j+1, n):
                r = M[i][j]/pivot
                for l in range(j+1, n):
                    M[i][l] -= r*M[j][l]
        for i in range(n):
            for j in range(i, n):
                q = scale*Q[i][j]*(1 if i == j else 2)
                for m,u in beta[i].items():
                    for mm,v in beta[j].items():
                        exponent = tuple(a+b for a,b in zip(m,mm))
                        actual[exponent] = actual.get(exponent,F(0))+q*u*v
        blocks.append({'denominator': str(den), 'order': n,
                       'positive_LDL_pivots': [[str(v.numerator),str(v.denominator)]
                                               for v in pivots]})
    keys = set(actual) | set(exact)
    need(len(keys) == integer(J['coefficient_count']), 'coefficient count')
    need(all(actual.get(m,0) == exact.get(m,0) for m in keys),
         'full unsymmetrized coefficient identity')
    report = {'name': name, 'sha256': hashlib.sha256(data).hexdigest(),
              'degree': degree, 'nonzero_terms': len(exact), 'orders': orders,
              'coefficient_positions_checked': len(keys),
              'all_residuals_zero': True, 'blocks': blocks}
    reports.append(report)
    print('PASS',name,'degree',degree,'nonzero',len(exact),'positions',len(keys),
          'orders',orders,'sha256',report['sha256'],flush=True)
need(seen == set(targets), 'all three certificates required')
print('PASS: three exact complex identities; 416 positive rational pivots;',
      'null-vector/cofactor identities; no numerical acceptance premise.')
if args.report:
    out = Path(args.report)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({'reports': reports, 'verifier_sha256':
        hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}, indent=2)+'\n')
