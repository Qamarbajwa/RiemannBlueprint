#!/usr/bin/env python3
"""
repackage_rh_t09_zenodo_v3_1.py
Packages Zenodo release bundle v3.1.0 including:
- 31-page research paper PDF and TeX
- All 13 Lean 4 certified modules (0 sorry, standard axioms)
- All 10 numerical probe scripts and receipts
- RIEMANN_HYPOTHESIS_FOR_EVERYONE.pdf
- .zenodo.json metadata v3.1.0
"""

import os
import json
import hashlib
import zipfile
from pathlib import Path

def get_sha256(filepath):
    h = hashlib.sha256()
    with open(filepath, "rb") as f:
        while chunk := f.read(65536):
            h.update(chunk)
    return h.hexdigest()

def to_win_long(p_obj):
    s = str(Path(p_obj).resolve())
    if s.startswith('\\\\?\\'):
        return s
    return '\\\\?\\' + s

def main():
    root = Path.cwd()
    target_dir = root / "research/interactive_lab/monograph_additive_multiplicative/zenodo_theorem_papers/RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity"
    
    zip_path = to_win_long(target_dir / "RH_T09_ZENODO.zip")
    
    # 1. Update .zenodo.json
    zenodo_json_path = to_win_long(target_dir / ".zenodo.json")
    zenodo_meta = {
        "title": "Two-Piece Factorized Mollifiers, Signed Weil-Schur Coercivity, and the Rosetta Cross-Field Unification",
        "version": "v3.1.0",
        "description": "Definitive research release containing 13 machine-certified Lean 4 modules (0 sorry, standard axioms) and 10 audited high-precision numerical diagnostics covering infinite-window Weyl transfer to 10.68 trillion, shifted convolution coprime bounds, Birman-Schwinger off-line exclusion, and the Rosetta cross-field structural unification across the Clay Millennium Problems.",
        "creators": [
            {
                "name": "Munawer, Qamar",
                "affiliation": "Brandenburg University of Technology Cottbus-Senftenberg"
            }
        ],
        "keywords": [
            "Riemann Hypothesis",
            "Signed Weil Quadratic Form",
            "Factorized Mollifier",
            "Schur Complement Tare",
            "Sobolev Quotient Operator",
            "Hilbert-Polya Operator",
            "Weyl Resolvent Transfer",
            "Kuznetsov Coprime Spectral Bound",
            "Birman-Schwinger Resolvent",
            "Rosetta Cross-Field Invariants",
            "Lean 4",
            "Formal Verification"
        ],
        "license": "CC-BY-4.0",
        "upload_type": "publication",
        "publication_type": "preprint",
        "access_right": "open",
        "methodology_note": "ai is being used as a tool for formal verification and computation under human geometric direction."
    }
    with open(zenodo_json_path, "w", encoding="utf-8") as f:
        json.dump(zenodo_meta, f, indent=2)

    # 2. Files to include
    lean_dir = root / "research/interactive_lab/monograph_additive_multiplicative/RiemannBlueprint/RiemannBlueprint"
    lean_modules = [
        "SelbergConreyReciprocityMarginSplit.lean",
        "WeilSchurAndFactorizedMollifierBridge.lean",
        "WeilSignedSchurAndHighDegreeCoercivity.lean",
        "WeilSignedSubGapTareCoercivity.lean",
        "WeilWindowContinuityAndBoundaryVanishing.lean",
        "SobolevQuotientAndTwoPieceKloosterman.lean",
        "CoprimeKloostermanFactorization.lean",
        "HilbertPolyaQuotientSpectralGap.lean",
        "CriticalLineConditionalConsequences.lean",
        "InfiniteWindowWeylResolventLimit.lean",
        "KuznetsovCoprimeSpectralDecomposition.lean",
        "BirmanSchwingerOffLineExclusion.lean",
        "RosettaCrossWorkspaceMasterBridge.lean"
    ]
    
    scripts_dir = root / "scripts"
    probes = [
        ("probe_sub_gap_resolvent_decay.py", "probe_sub_gap_resolvent_decay_receipt.json"),
        ("probe_weil_window_continuity.py", "probe_weil_window_continuity_receipt.json"),
        ("probe_sobolev_quotient_and_two_piece_kloosterman.py", "probe_sobolev_quotient_and_two_piece_kloosterman_receipt.json"),
        ("probe_asymptotic_sobolev_quotient.py", "probe_asymptotic_sobolev_quotient_receipt.json"),
        ("probe_ultra_high_asymptotic_sobolev_quotient.py", "probe_ultra_high_asymptotic_sobolev_quotient_receipt.json"),
        ("probe_super_scale_asymptotic_sobolev_quotient.py", "probe_super_scale_asymptotic_sobolev_quotient_receipt.json"),
        ("probe_critical_line_consequences_and_rosetta_bridge.py", "probe_critical_line_consequences_and_rosetta_bridge_receipt.json"),
        ("probe_infinite_window_weyl_transfer.py", "probe_infinite_window_weyl_transfer_receipt.json"),
        ("probe_kuznetsov_shifted_convolution_bound.py", "probe_kuznetsov_shifted_convolution_bound_receipt.json"),
        ("probe_birman_schwinger_darboux_spectrum.py", "probe_birman_schwinger_darboux_spectrum_receipt.json")
    ]
    
    pdf_path = target_dir / "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.pdf"
    tex_path = target_dir / "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.tex"
    everyone_pdf = root / "research/interactive_lab/monograph_additive_multiplicative/RIEMANN_HYPOTHESIS_FOR_EVERYONE.pdf"
    
    items_to_zip = [
        (pdf_path, "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.pdf"),
        (tex_path, "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.tex"),
        (target_dir / ".zenodo.json", ".zenodo.json"),
        (everyone_pdf, "RIEMANN_HYPOTHESIS_FOR_EVERYONE.pdf")
    ]
    
    for lm in lean_modules:
        src = lean_dir / lm
        items_to_zip.append((src, lm))
        
    for py, rcp in probes:
        items_to_zip.append((scripts_dir / py, py))
        items_to_zip.append((scripts_dir / rcp, rcp))
        
    # Write zip
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        for src, arcname in items_to_zip:
            src_str = to_win_long(src)
            zf.write(src_str, arcname=arcname)
            
    sha = get_sha256(zip_path)
    size = os.stat(zip_path).st_size
    print(f"Successfully packaged RH_T09_ZENODO.zip v3.1.0: {len(items_to_zip)} files, {size} bytes, SHA256: {sha}")

if __name__ == "__main__":
    main()
