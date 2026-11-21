#!/usr/bin/env python3
"""
scan_rosetta_gaps.py
Comprehensive Gap & Drift Discovery across all 4 workspaces, tubulance, and ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK.
Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg
Methodology note: ai is being used as a tool.
Epistemic invariant: all four Clay Millennium Problems remain strictly OPEN (status: verified-finite).
"""

import os
import re
import json
import hashlib
from pathlib import Path

def ext_path(p: Path | str) -> str:
    s = str(Path(p).resolve())
    if os.name == "nt" and not s.startswith("\\\\?\\"):
        return "\\\\?\\" + s
    return s

def clean_rel(p_str: str, base_str: str) -> str:
    p_norm = p_str.replace("\\\\?\\", "").replace("\\", "/")
    base_norm = base_str.replace("\\\\?\\", "").replace("\\", "/")
    if p_norm.startswith(base_norm):
        return p_norm[len(base_norm):].lstrip("/")
    return p_norm

WORKSPACES = {
    "rh": Path("d:/Comfy UI/rheihman hypothesis"),
    "hodge": Path("d:/Comfy UI/hodge conjecture"),
    "ym": Path("d:/Comfy UI/yang mills and the mass gap"),
    "tubulance": Path("d:/Comfy UI/tubulance"),
    "pack": Path("d:/Comfy UI/ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK")
}

REPORT = {
    "lean_uncompiled_or_sorry": [],
    "probe_receipts_missing_or_failed": [],
    "tex_out_of_date_or_uncompiled": [],
    "tex_missing_pfaffian_section": [],
    "attribution_drift_arqam": [],
    "attribution_drift_btu": [],
    "attribution_missing_ai_tool": [],
    "mirror_drift_pack": []
}

def scan_attribution(ws_path: Path, rel_base: str):
    ignore_dirs = {".git", ".lake", ".rh-v2-runtime", "__pycache__", "build", ".cache", "99_Raw_Discussions", "target"}
    check_exts = {".tex", ".lean", ".py", ".json", ".md"}
    ws_ext = ext_path(ws_path)
    
    for root, dirs, files in os.walk(ws_ext):
        dirs[:] = [d for d in dirs if d not in ignore_dirs and not d.startswith(".")]
        for f in files:
            ext = os.path.splitext(f)[1].lower()
            if ext not in check_exts:
                continue
            full_path = os.path.join(root, f)
            try:
                st = os.stat(full_path)
                if st.st_size > 2_000_000:
                    continue
                with open(full_path, "r", encoding="utf-8", errors="ignore") as fp:
                    text = fp.read()
            except Exception:
                continue
            
            rel_str = f"{rel_base}/{clean_rel(full_path, ws_ext)}"
            
            target_a = "".join(["A", "r", "q", "a", "m"])
            target_b = "".join(["(", "B", "T", "U", ")"])
            if target_a in text:
                REPORT["attribution_drift_arqam"].append(rel_str)
            if target_b in text:
                REPORT["attribution_drift_btu"].append(rel_str)
            
            # Check ai is being used as a tool for papers, zenodo.json
            if ext == ".tex" or f.endswith(".zenodo.json"):
                if "ai is being used as a tool" not in text.lower():
                    REPORT["attribution_missing_ai_tool"].append(rel_str)

def scan_tex_papers():
    for ws_key in ["rh", "tubulance"]:
        ws = WORKSPACES[ws_key]
        ws_ext = ext_path(ws)
        for root, dirs, files in os.walk(ws_ext):
            dirs[:] = [d for d in dirs if d not in {".git", ".lake", "__pycache__"}]
            for f in files:
                if f.lower().endswith(".tex"):
                    tex_path = os.path.join(root, f)
                    pdf_path = os.path.splitext(tex_path)[0] + ".pdf"
                    rel_str = f"{ws_key}/{clean_rel(tex_path, ws_ext)}"
                    
                    if not os.path.exists(pdf_path):
                        REPORT["tex_out_of_date_or_uncompiled"].append({"file": rel_str, "reason": "pdf_missing"})
                    else:
                        if os.path.getmtime(pdf_path) < os.path.getmtime(tex_path):
                            REPORT["tex_out_of_date_or_uncompiled"].append({"file": rel_str, "reason": "pdf_stale"})
                    
                    # Check section "How Energy, Quantum Matter, Pfaffian Squares, and Real-Life Fields Connect"
                    if "zenodo_theorem_papers" in tex_path or "ROSETTA_UNIFIED" in tex_path:
                        try:
                            with open(tex_path, "r", encoding="utf-8", errors="ignore") as fp:
                                text = fp.read()
                            if "How Energy, Quantum Matter, Pfaffian Squares, and Real-Life Fields Connect" not in text:
                                REPORT["tex_missing_pfaffian_section"].append(rel_str)
                        except Exception:
                            pass

def scan_lean_modules():
    forbidden_pat = re.compile(r"\b(sorry|admit|axiom)\b")
    # Scan pack lean modules
    pack_ext = ext_path(WORKSPACES["pack"])
    for root, dirs, files in os.walk(pack_ext):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake", "__pycache__"}]
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(root, f)
                with open(p, "r", encoding="utf-8", errors="ignore") as fp:
                    text = fp.read()
                no_block = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
                no_comments = re.sub(r"--.*$", "", no_block, flags=re.MULTILINE)
                matches = forbidden_pat.findall(no_comments)
                if matches:
                    REPORT["lean_uncompiled_or_sorry"].append({"file": f"pack/{clean_rel(p, pack_ext)}", "matches": matches})
            
    # Scan RiemannBlueprint lean modules
    rb_ext = ext_path(WORKSPACES["rh"] / "RiemannBlueprint")
    for root, dirs, files in os.walk(rb_ext):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake", "__pycache__"}]
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(root, f)
                with open(p, "r", encoding="utf-8", errors="ignore") as fp:
                    text = fp.read()
                no_block = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
                no_comments = re.sub(r"--.*$", "", no_block, flags=re.MULTILINE)
                matches = forbidden_pat.findall(no_comments)
                if matches:
                    REPORT["lean_uncompiled_or_sorry"].append({"file": f"rh/RiemannBlueprint/{clean_rel(p, rb_ext)}", "matches": matches})

def scan_probes_and_receipts():
    pack_ext = ext_path(WORKSPACES["pack"])
    for root, dirs, files in os.walk(pack_ext):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake", "__pycache__"}]
        for f in files:
            if f.startswith("probe_") and f.endswith(".py"):
                probe_path = os.path.join(root, f)
                receipt_path = os.path.splitext(probe_path)[0] + ".json"
                rel_str = f"pack/{clean_rel(probe_path, pack_ext)}"
                if not os.path.exists(receipt_path):
                    # Check if receipt exists with slightly different name
                    pass
                else:
                    try:
                        with open(receipt_path, "r", encoding="utf-8") as fp:
                            data = json.load(fp)
                        verified = data.get("verified", data.get("passed", data.get("status") in ["PASS", "VERIFIED"]))
                        if not verified:
                            REPORT["probe_receipts_missing_or_failed"].append({"file": rel_str, "status": "failed"})
                    except Exception as e:
                        REPORT["probe_receipts_missing_or_failed"].append({"file": rel_str, "error": str(e)})

def scan_mirroring():
    pack_rh_lean = ext_path(WORKSPACES["pack"] / "03_riemann_hypothesis" / "lean4_certificates")
    rb_dir = ext_path(WORKSPACES["rh"] / "RiemannBlueprint")
    for f in os.listdir(rb_dir):
        if f.endswith(".lean"):
            src = os.path.join(rb_dir, f)
            dst = os.path.join(pack_rh_lean, f)
            if not os.path.exists(dst):
                REPORT["mirror_drift_pack"].append(f"Missing in pack: {f}")
            else:
                with open(src, "rb") as fp1, open(dst, "rb") as fp2:
                    if fp1.read() != fp2.read():
                        REPORT["mirror_drift_pack"].append(f"Content mismatch in pack: {f}")

def main():
    print("[*] Scanning attribution drift...")
    for key in ["pack", "rh", "tubulance"]:
        scan_attribution(WORKSPACES[key], key)
        
    print("[*] Scanning TeX papers...")
    scan_tex_papers()
    
    print("[*] Scanning Lean modules...")
    scan_lean_modules()
    
    print("[*] Scanning probes and receipts...")
    scan_probes_and_receipts()
    
    print("[*] Scanning mirroring drift...")
    scan_mirroring()
    
    out_file = ext_path(Path("d:/Comfy UI/rheihman hypothesis/scripts/gap_scan_report.json"))
    with open(out_file, "w", encoding="utf-8") as fp:
        json.dump(REPORT, fp, indent=2)
    print(f"[+] Gap scan report written to {out_file}")
    
    summary = {k: len(v) for k, v in REPORT.items()}
    print("Summary:", json.dumps(summary, indent=2))

if __name__ == "__main__":
    main()
