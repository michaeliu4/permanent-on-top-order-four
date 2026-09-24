# Permanent-on-top bounds in order four

Exact rational certificates and verification programs accompanying the paper
*Permanent-on-top bounds in order four*.

The programs verify the polynomial identities, Gram-matrix positivity, and
finite tensor and representation identities used in the proofs. The paper
supplies the arguments that extend these identities to the stated matrix
classes. The unrestricted complex order-four permanent-on-top problem remains
open.

## Requirements

Python 3.12, SymPy 1.14.0, and NumPy 2.3.3. From the repository root:

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python run_checks.py
```

On Windows, activate the environment with `.venv\Scripts\activate`.
Run Python with assertions enabled, without `-O` or `PYTHONOPTIMIZE`.

The driver checks the input hashes and runs eleven verification programs.
A successful run ends with:

```text
PASS: all selected exact certificates and representation checks.
```

Detailed logs and machine-readable reports are written to `run/`. They are
generated outputs and are not needed to start a fresh verification.

## Contents

| Directory | Mathematical content |
| --- | --- |
| `ranktwo/` | Complex order-four rank-two determinant certificate and tensor reduction, Section 3 |
| `real/` | Nine certificates for the real order-four theorem and representation identities, Section 4 |
| `complex22/` | Complex Fourier-block identities and the pairing representation, Section 5 |
| `complex211/` | Cofactor-sector trace and moment inequalities, Section 5 |
| `zero/` | Hook determinant when an off-diagonal entry is zero, Section 5 |
| `bound/` | The universal factor `19/18`, Section 5 |

The package contains twenty-one certificates: eighteen correspond to the
displayed arguments and tables, and three additional identities are used by
the verification programs. `MANIFEST.json` identifies all certificate and
checker inputs by their SHA-256 hashes. The verifiers reconstruct the target
polynomials and check their coefficients with exact rational arithmetic;
certificate generation and numerical optimization are not required.

For the rank-two determinant identity, the stored scale is `207360`. The
verifier symmetrizes the stored sum with its image under
`(r,a,b,c,d) -> (r,c,d,a,b)`, using the multiplier `207360/2 = 103680` for
each half, as in the paper.

## Manuscript and citation

The [V1 final manuscript](manuscript/permanent-on-top-order-four-V1-final.pdf)
and its [LaTeX source](manuscript/permanent-on-top-order-four-V1-source.zip)
are preserved in `manuscript/`.

The exact verification package is preserved as
[companion release v1](https://github.com/michaeliu4/permanent-on-top-order-four/releases/tag/v1).
Use that tagged release to reproduce the computations. Citation metadata for
the software is supplied in `CITATION.cff`.
