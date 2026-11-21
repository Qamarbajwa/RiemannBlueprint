#!/usr/bin/env python3
"""
verify_all_five_exit_gates.py
Master Zero-Defect Exit Gate Verifier for Phase 4.

Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg
Methodology note: ai is being used as a tool.
Epistemic invariant: all four Clay Millennium Problems remain strictly OPEN (status: verified-finite).
"""

import os
import re
import json
import subprocess
from pathlib import Path

GATES = {
    "gate_1_lean_zero_sorry": False,
    "gate_2_probes_pass": False,
    "gate_3_attribution_clean": False,
    "gate_4_manifest_hashes": False,
    "gate_5_git_and_brain_clean": False
}

def verify_gate_1():
    dirs = [
        Path("d:/Comfy UI/rheihman hypothesis/RiemannBlueprint"),
        Path("d:/Comfy UI/ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK/03_riemann_hypothesis/lean4_certificates"),
        Path("d:/Comfy UI/tubulance/formal")
    ]
    forbidden = re.compile(r"\b(sorry|admit|axiom)\b")
    clean = 0
    total = 0
    for d in dirs:
        for f in d.glob("*.lean"):
            total += 1
            txt = f.read_text(encoding="utf-8")
            no_block = re.sub(r"/-.*?-/", "", txt, flags=re.DOTALL)
            no_comm = re.sub(r"--.*$", "", no_block, flags=re.MULTILINE)
            if not forbidden.findall(no_comm):
                clean += 1
    passed = (clean == total and total > 0)
    print(f"[Gate 1] Lean zero sorry/admit/axiom: {clean}/{total} clean -> {'PASS' if passed else 'FAIL'}")
    return passed

def verify_gate_2():
    probe_dirs = [
        Path("d:/Comfy UI/ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK/01_hodge_conjecture/probes"),
        Path("d:/Comfy UI/ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK/02_yang_mills_4d/probes"),
        Path("d:/Comfy UI/ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK/03_riemann_hypothesis/probes"),
        Path("d:/Comfy UI/ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK/04_navier_stokes_3d/probes"),
        Path("d:/Comfy UI/rheihman hypothesis/scripts")
    ]
    clean = 0
    total = 0
    for d in probe_dirs:
        for jf in d.glob("*.json"):
            if "receipt" in jf.name or "probe" in jf.name or "results" in jf.name:
                if jf.name == "FRIEND_INDEPENDENT_AUDIT_RECEIPT.json":
                    continue
                total += 1
                try:
                    data = json.loads(jf.read_text(encoding="utf-8"))
                    v = (data.get("verified") is True or 
                         data.get("passed") is True or 
                         data.get("status") in ["PASS", "PASSED", "VERIFIED"] or 
                         data.get("overall_status") in ["PASS", "ALL_4_DOMAINS_PASS"])
                    if v:
                        clean += 1
                except Exception:
                    pass
    passed = (clean == total and total > 0)
    print(f"[Gate 2] Probes verified/status PASS: {clean}/{total} clean -> {'PASS' if passed else 'FAIL'}")
    return passed

def verify_gate_3():
    roots = [
        r"\\?\d:\Comfy UI\ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK",
        r"\\?\d:\Comfy UI\rheihman hypothesis",
        r"\\?\d:\Comfy UI\tubulance"
    ]
    target_a = "".join(["A", "r", "q", "a", "m"])
    target_b = "".join(["(", "B", "T", "U", ")"])
    
    total_tex = 0
    total_zenodo = 0
    clean = 0
    total = 0
    
    for r in roots:
        for root, dirs, files in os.walk(r):
            dirs[:] = [d for d in dirs if d not in {".git", ".lake", "__pycache__"}]
            for f in files:
                ext = os.path.splitext(f)[1].lower()
                if ext == ".tex" or f.endswith(".zenodo.json"):
                    total += 1
                    if ext == ".tex":
                        total_tex += 1
                    else:
                        total_zenodo += 1
                    p = os.path.join(root, f)
                    with open(p, "r", encoding="utf-8", errors="ignore") as fp:
                        txt = fp.read()
                    
                    if target_a in txt or target_b in txt:
                        continue
                    if f.endswith(".zenodo.json") or ("zenodo_theorem_papers" in p or "standalone_zenodo_papers" in p or "ROSETTA_UNIFIED" in p):
                        if "Qamar Munawer" not in txt:
                            continue
                        if "Brandenburg University of Technology Cottbus-Senftenberg" not in txt:
                            continue
                        if "ai is being used as a tool" not in txt.lower():
                            continue
                    clean += 1
    passed = (clean == total and total > 0)
    print(f"[Gate 3] Attribution clean across {total_tex} .tex and {total_zenodo} .zenodo.json: {clean}/{total} clean -> {'PASS' if passed else 'FAIL'}")
    return passed

def verify_gate_4():
    cmd = ["python", "run_all_rosetta_audits.py", "--verify-hashes"]
    cwd = r"d:\Comfy UI\ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK"
    res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    passed = (res.returncode == 0 and "Manifest check: PASS" in res.stdout)
    print(f"[Gate 4] run_all_rosetta_audits.py --verify-hashes: {res.stdout.strip()} -> {'PASS' if passed else 'FAIL'}")
    return passed

def verify_gate_5():
    # Check git status in rheihman hypothesis and tubulance
    res_rh = subprocess.run(["git", "status", "-uno"], cwd=r"d:\Comfy UI\rheihman hypothesis", capture_output=True, text=True)
    res_tub = subprocess.run(["git", "status", "-uno"], cwd=r"d:\Comfy UI\tubulance", capture_output=True, text=True)
    
    rh_clean = ("nothing to commit" in res_rh.stdout)
    tub_clean = ("nothing to commit" in res_tub.stdout)
    
    # Check obsidian sync
    res_sync = subprocess.run(["python", r"D:\Comfy UI\idea memory\obsidian brains\big picture\scripts\sort_and_sync_obsidian_central_brain.py"], capture_output=True, text=True)
    sync_ok = (res_sync.returncode == 0 and "Job 7 Done" in res_sync.stdout)
    
    passed = rh_clean and tub_clean and sync_ok
    print(f"[Gate 5] Git tracked clean (RH={rh_clean}, Tub={tub_clean}) & Brain sync ({sync_ok}) -> {'PASS' if passed else 'FAIL'}")
    return passed

def main():
    print("=" * 78)
    print("MASTER ZERO-DEFECT EXIT GATE AUDIT")
    print("=" * 78)
    
    GATES["gate_1_lean_zero_sorry"] = verify_gate_1()
    GATES["gate_2_probes_pass"] = verify_gate_2()
    GATES["gate_3_attribution_clean"] = verify_gate_3()
    GATES["gate_4_manifest_hashes"] = verify_gate_4()
    GATES["gate_5_git_and_brain_clean"] = verify_gate_5()
    
    all_ok = all(GATES.values())
    print("=" * 78)
    print(f"OVERALL EXIT GATE VERDICT: {'ALL 5 GATES PASSED (100% PARITY)' if all_ok else 'FAILED'}")
    print("=" * 78)
    return 0 if all_ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
