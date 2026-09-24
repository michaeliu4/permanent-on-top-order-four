"""Verify the exact certificates for Permanent-on-top bounds in order four."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path


if not __debug__:
    raise SystemExit("Verification requires Python assertions; run without -O or PYTHONOPTIMIZE.")


ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / "MANIFEST.json").read_text())
for rel, entry in manifest.items():
    path = ROOT / rel
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != entry["sha256"]:
        raise SystemExit(f"Hash mismatch: {rel}")

reports = ROOT / "run"
reports.mkdir(exist_ok=True)


def run(label: str, directory: str, script: str, *args: str) -> None:
    print(f"Checking {label}", flush=True)
    command = [sys.executable, "-E", script, *args]
    with (reports / f"{label}.log").open("w") as output:
        subprocess.run(command, cwd=ROOT / directory, stdout=output,
                       stderr=subprocess.STDOUT, check=True)
    print(f"PASS {label}", flush=True)


run("ranktwo", "ranktwo", "verify_certificate.py")
run("ranktwo-strict", "ranktwo", "strict_exact_verify.py",
    "soules_order4_rank2_certificate.json", str(reports / "ranktwo-strict.json"))
run("ranktwo-tensor", "ranktwo", "audit_tensor_reduction.py")
run("real", "real", "checks/verify_all_certificates.py",
    *[str(p.relative_to(ROOT / "real")) for p in sorted((ROOT / "real/certificates").glob("*.json"))])
run("real-bridge", "real", "checks/verify_representation_bridges.py")
run("complex22", "complex22", "checks/verify_complex_progress.py",
    str(reports / "complex22.json"),
    *[str(p.relative_to(ROOT / "complex22")) for p in sorted((ROOT / "complex22/certificates").glob("*.json"))])
run("complex22-bridge", "complex22", "checks/verify_pairing_and_lift.py")
run("complex211", "complex211", "checks/verify_cofactor.py",
    *[str(p.relative_to(ROOT / "complex211")) for p in sorted((ROOT / "complex211/certificates").glob("*.json"))],
    "--report", str(reports / "complex211.json"))
run("complex211-bridge", "complex211", "checks/verify_representation_bridges.py")
run("bound", "bound", "checks/verify_new.py",
    "certificates/certificate_hook_bound_19_18_m0.json",
    str(reports / "bound.json"))
run("zero", "zero", "checks/verify_zero_offdiagonal.py",
    "certificates/certificate_hook_zero_offdiagonal.json",
    str(reports / "zero.json"))
print("PASS: all selected exact certificates and representation checks.")
