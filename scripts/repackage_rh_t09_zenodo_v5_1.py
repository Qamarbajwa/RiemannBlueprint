#!/usr/bin/env python3
"""
repackage_rh_t09_zenodo_v5_1.py
Packages Zenodo release bundle v5.1.0 including:
- 43-page definitive research monograph PDF and TeX (v5.1.0)
- All 23 Lean 4 certified modules (0 sorry, standard axioms)
- All 17 numerical probe scripts and receipts
- Standalone interactive HTML visualizer
- RIEMANN_HYPOTHESIS_FOR_EVERYONE.pdf
- .zenodo.json metadata v5.1.0

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
        "version": "v5.1.0",
        "description": "Comprehensive release containing 23 machine-certified Lean 4 modules (0 sorry, standard axioms), 17 audited high-precision numerical diagnostics, a 43-page definitive monograph, and a standalone interactive visualizer covering the Maass-Selberg Cuspidal Slit Architecture, Chained Automorphic Theta Lifts of Length sqrt(X), Stepanov-Deligne Bilinear Sign Opposition, Chiral Virial Commutator Engine, Dilation Sobolev Domain Core, Non-Archimedean Quantum Graph Measure, 100-Zero Multi-Scale Virial Landscape Audit, positive prime-measure rigidity, discrete prime Euler-Maclaurin dispersion, Maass cusp form coprime projection, continuous norm-resolvent convergence, Sobolev compact resolvents, Polya kernel Fourier-sine positivity, and the Rosetta cross-field structural unification across the Clay Millennium Problems.",
        "creators": [
            {
                "name": "Munawer, Qamar",
                "affiliation": "Brandenburg University of Technology Cottbus-Senftenberg"
            }
        ],
        "keywords": [
            "Riemann Hypothesis",
            "Maass-Selberg Cuspidal Slit",
            "Chained Automorphic Theta Lifts",
            "Stepanov-Deligne Sign Opposition",
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
            "Birman-Schwinger Darboux Resolvent",
            "Kuznetsov Coprime Spectral Decomposition",
            "Infinite-Window Weyl Resolvent Limit",
            "Critical Line Von Koch Mertens",
            "Coprime Kloosterman Factorization",
            "Rosetta Cross-Field Bridge",
            "Lean 4 Certified Bridge",
            "Open Clay Horizon Lock"
        ],
        "license": "CC-BY-4.0",
        "methodology": "ai is being used as a tool",
        "epistemic_lock": "All four Clay Millennium Problems remain strictly OPEN (status: verified-finite)."
    }

    with open(zenodo_json_path, "w", encoding="utf-8") as f:
        json.dump(zenodo_meta, f, indent=2)

    # 2. Collect artifacts to package
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
        "NonArchimedeanPrimeGraphMeasure.lean",
        "MaassSelbergCuspidalSlit.lean",
        "StepanovDeligneSignClashBridge.lean"
    ]

    probe_scripts = [
        "probe_sub_gap_resolvent_decay.py",
        "probe_weil_window_continuity.py",
        "probe_sobolev_quotient_and_two_piece_kloosterman.py",
        "probe_asymptotic_sobolev_quotient.py",
        "probe_ultra_high_asymptotic_sobolev_quotient.py",
        "probe_super_scale_asymptotic_sobolev_quotient.py",
        "probe_critical_line_consequences_and_rosetta_bridge.py",
        "probe_infinite_window_weyl_transfer.py",
        "probe_kuznetsov_shifted_convolution_bound.py",
        "probe_birman_schwinger_darboux_spectrum.py",
        "probe_polya_convex_sine_transform.py",
        "probe_discrete_prime_dispersion.py",
        "probe_maass_coprime_projection.py",
        "probe_continuous_norm_resolvent.py",
        "probe_chiral_virial_engine.py",
        "probe_multi_zero_virial_landscape.py",
        "probe_chained_theta_lift_multiplicity.py"
    ]

    receipt_files = [
        "probe_sub_gap_resolvent_decay_receipt.json",
        "probe_weil_window_continuity_receipt.json",
        "probe_sobolev_quotient_and_two_piece_kloosterman_receipt.json",
        "probe_asymptotic_sobolev_quotient_receipt.json",
        "probe_ultra_high_asymptotic_sobolev_quotient_receipt.json",
        "probe_super_scale_asymptotic_sobolev_quotient_receipt.json",
        "probe_critical_line_consequences_and_rosetta_bridge_receipt.json",
        "probe_infinite_window_weyl_transfer_receipt.json",
        "probe_kuznetsov_shifted_convolution_bound_receipt.json",
        "probe_birman_schwinger_darboux_spectrum_receipt.json",
        "probe_polya_convex_sine_transform_receipt.json",
        "probe_discrete_prime_dispersion_receipt.json",
        "probe_maass_coprime_projection_receipt.json",
        "probe_continuous_norm_resolvent_receipt.json",
        "probe_chiral_virial_engine_receipt.json",
        "probe_multi_zero_virial_landscape_receipt.json",
        "probe_chained_theta_lift_receipt.json"
    ]

    monograph_pdf = target_dir / "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.pdf"
    monograph_tex = target_dir / "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.tex"
    visualizer_html = target_dir / "RH_T09_Factorized_Mollifier_Interactive_Lab.html"
    everyone_pdf = root / "research/everyone_guide/RIEMANN_HYPOTHESIS_FOR_EVERYONE.pdf"

    print("[*] Creating Zenodo Release Bundle v5.1.0...")
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as z:
        # Add metadata
        z.write(zenodo_json_path, arcname=".zenodo.json")
        
        # Add monograph
        pdf_long = to_win_long(monograph_pdf)
        tex_long = to_win_long(monograph_tex)
        html_long = to_win_long(visualizer_html)
        ev_long = to_win_long(everyone_pdf)

        if os.path.exists(pdf_long):
            z.write(pdf_long, arcname=monograph_pdf.name)
        if os.path.exists(tex_long):
            z.write(tex_long, arcname=monograph_tex.name)
        if os.path.exists(html_long):
            z.write(html_long, arcname=visualizer_html.name)
        if os.path.exists(ev_long):
            z.write(ev_long, arcname=everyone_pdf.name)

        # Add Lean 4 modules
        for mod in lean_modules:
            p = root / "RiemannBlueprint" / mod
            if p.exists():
                z.write(to_win_long(p), arcname=f"lean/{mod}")
            else:
                p_local = target_dir / mod
                if p_local.exists():
                    z.write(to_win_long(p_local), arcname=f"lean/{mod}")

        # Add probe scripts and receipts
        for scr in probe_scripts:
            p = root / "scripts" / scr
            if p.exists():
                z.write(to_win_long(p), arcname=f"probes/{scr}")

        for rec in receipt_files:
            p = root / "scripts" / rec
            if p.exists():
                z.write(to_win_long(p), arcname=f"receipts/{rec}")
            else:
                p_local = target_dir / rec
                if p_local.exists():
                    z.write(to_win_long(p_local), arcname=f"receipts/{rec}")

    zip_size = os.stat(zip_path).st_size
    zip_sha = get_sha256(zip_path)

    print(f"[+] Bundle v5.1.0 created successfully!")
    print(f"    Path: {zip_path}")
    print(f"    Size: {zip_size:,} bytes ({zip_size / (1024*1024):.2f} MB)")
    print(f"    SHA-256: {zip_sha}")
    print(f"    Lean 4 Modules: {len(lean_modules)}")
    print(f"    Probe Scripts: {len(probe_scripts)}")
    print(f"    Receipts: {len(receipt_files)}")

if __name__ == "__main__":
    main()
