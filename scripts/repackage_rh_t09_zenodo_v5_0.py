#!/usr/bin/env python3
"""
repackage_rh_t09_zenodo_v5_0.py
Packages Zenodo release bundle v5.0.0 including:
- 41-page definitive research monograph PDF and TeX
- All 21 Lean 4 certified modules (0 sorry, standard axioms)
- All 16 numerical probe scripts and receipts
- Standalone interactive HTML visualizer
- RIEMANN_HYPOTHESIS_FOR_EVERYONE.pdf
- .zenodo.json metadata v5.0.0

Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg
Methodology note: ai is being used as a tool.
Epistemic invariant: all four Clay Millennium Problems remain strictly OPEN.
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
        "version": "v5.0.0",
        "description": "Comprehensive release containing 21 machine-certified Lean 4 modules (0 sorry, standard axioms), 16 audited high-precision numerical diagnostics, a 41-page definitive monograph, and a standalone interactive visualizer covering the Chiral Virial Commutator Engine, Dilation Sobolev Domain Core, Non-Archimedean Quantum Graph Measure, 100-Zero Multi-Scale Virial Landscape Audit, positive prime-measure rigidity, discrete prime Euler-Maclaurin dispersion, Maass cusp form coprime projection, continuous norm-resolvent convergence, Sobolev compact resolvents, Polya kernel Fourier-sine positivity, and the Rosetta cross-field structural unification across the Clay Millennium Problems.",
        "creators": [
            {
                "name": "Munawer, Qamar",
                "affiliation": "Brandenburg University of Technology Cottbus-Senftenberg"
            }
        ],
        "keywords": [
            "Riemann Hypothesis",
            "Chiral Virial Commutator Engine",
            "Dilation Sobolev Domain",
            "Non-Archimedean Quantum Graph",
            "100-Zero Virial Landscape",
            "Positive Prime-Measure Rigidity",
            "Signed Weil Quadratic Form",
            "Factorized Mollifier",
            "Schur Complement Tare",
            "Sobolev Quotient Operator",
            "Hilbert-Polya Operator",
            "Euler-Maclaurin Dispersion",
            "Maass Cusp Form",
            "Norm-Resolvent Convergence",
            "Sobolev Compact Resolvent",
            "Polya Kernel Sine Positivity",
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
        "RosettaCrossWorkspaceMasterBridge.lean",
        "SobolevCompactResolventEmbedding.lean",
        "PolyaKernelUniversalSinePositivity.lean",
        "DiscretePrimeEulerMaclaurinDispersion.lean",
        "MaassCuspFormCoprimeProjection.lean",
        "ContinuousNormResolventConvergence.lean",
        "ChiralVirialCommutatorEngine.lean",
        "DilationSobolevDomainCore.lean",
        "NonArchimedeanPrimeGraphMeasure.lean"
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
        ("probe_birman_schwinger_darboux_spectrum.py", "probe_birman_schwinger_darboux_spectrum_receipt.json"),
        ("probe_polya_convex_sine_transform.py", "probe_polya_convex_sine_transform_receipt.json"),
        ("probe_discrete_prime_dispersion.py", "probe_discrete_prime_dispersion_receipt.json"),
        ("probe_maass_coprime_projection.py", "probe_maass_coprime_projection_receipt.json"),
        ("probe_continuous_norm_resolvent.py", "probe_continuous_norm_resolvent_receipt.json"),
        ("probe_chiral_virial_engine.py", "probe_chiral_virial_engine_receipt.json"),
        ("probe_multi_zero_virial_landscape.py", "probe_multi_zero_virial_landscape_receipt.json")
    ]
    
    paper_pdf = target_dir / "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.pdf"
    paper_tex = target_dir / "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.tex"
    visualizer = root / "research/interactive_lab/critical_line_and_rosetta_unification_visualizer.html"
    everyone_pdf = root / "research/interactive_lab/monograph_additive_multiplicative/RIEMANN_HYPOTHESIS_FOR_EVERYONE.pdf"
    
    print(f"Creating Zenodo Bundle v5.0.0 at: {zip_path}")
    if os.path.exists(zip_path):
        os.remove(zip_path)
        
    total_files = 0
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as z:
        # 1. Monograph & Metadata
        z.write(to_win_long(paper_pdf), arcname="RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.pdf")
        z.write(to_win_long(paper_tex), arcname="RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.tex")
        z.write(to_win_long(zenodo_json_path), arcname=".zenodo.json")
        z.write(to_win_long(visualizer), arcname="critical_line_and_rosetta_unification_visualizer.html")
        z.write(to_win_long(everyone_pdf), arcname="RIEMANN_HYPOTHESIS_FOR_EVERYONE.pdf")
        total_files += 5
        
        # 2. Lean 4 modules
        for mod in lean_modules:
            p_mod = to_win_long(lean_dir / mod)
            if os.path.exists(p_mod):
                z.write(p_mod, arcname=f"lean_blueprint/{mod}")
                total_files += 1
            else:
                print(f"WARNING: Missing lean module {mod}")
                
        # 3. Probes and receipts
        for py_file, receipt_file in probes:
            p_py = to_win_long(scripts_dir / py_file)
            p_rec = to_win_long(scripts_dir / receipt_file)
            if os.path.exists(p_py):
                z.write(p_py, arcname=f"diagnostics/{py_file}")
                total_files += 1
            else:
                print(f"WARNING: Missing script {py_file}")
            if os.path.exists(p_rec):
                z.write(p_rec, arcname=f"diagnostics/{receipt_file}")
                total_files += 1
            else:
                print(f"WARNING: Missing receipt {receipt_file}")

    zip_size = os.path.getsize(zip_path)
    zip_sha = get_sha256(zip_path)
    
    print("\n======================================================================")
    print("ZENODO BUNDLE v5.0.0 CREATION SUMMARY:")
    print(f"  Zip Path:      {zip_path}")
    print(f"  Total Files:   {total_files}")
    print(f"  Total Bytes:   {zip_size:,} bytes ({zip_size / (1024*1024):.2f} MB)")
    print(f"  SHA-256:       {zip_sha}")
    print("======================================================================")

if __name__ == "__main__":
    main()
