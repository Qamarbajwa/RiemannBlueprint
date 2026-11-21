#!/usr/bin/env python3
"""
inject_pfaffian_and_recompile_standalone.py
Injects the section 'How Energy, Quantum Matter, Pfaffian Squares, and Real-Life Fields Connect'
into all 27 standalone papers in ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK/standalone_zenodo_papers,
recompiles their PDFs via pdflatex, cleans temp files, and updates zip packages.

Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg
Methodology note: ai is being used as a tool.
Epistemic invariant: all four Clay Millennium Problems remain strictly OPEN (status: verified-finite).
"""

import os
import re
import subprocess
import zipfile
from pathlib import Path

BASE_DIR = Path(r"\\?\d:\Comfy UI\ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK\standalone_zenodo_papers")

SECTION_TEXT = r"""
\section{How Energy, Quantum Matter, Pfaffian Squares, and Real-Life Fields Connect}

Across all four workspaces and seven worldwide domains, the same three-line geometric architecture appears consistently, connecting finite matrix identities to physical energy, quantum states, and engineering systems:

\begin{enumerate}
  \item \textbf{Pythagorean Schur Energy Partition ($E_{\mathrm{total}} = E_{\mathrm{tare}} + E_{\mathrm{core}}$):} Whenever a physical system is partitioned into a positive baseline $A$ and an active core $D$, the Schur complement $S = D - B^T A^{-1} B$ isolates the true residual dynamics. Normalizing by $D$ produces $\cos^2\Theta + \sin^2\Theta = 1$, where $\cos^2\Theta$ represents the energy absorbed by the quiescent baseline, and $\sin^2\Theta$ represents the genuine active energy fraction.
  \item \textbf{Quantum Matter and Chiral Halves ($P_+ + P_- = I$, $P_+ P_- = 0$):} In quantum physics, Pauli spinors, Majorana zero modes, and topological insulators decompose states into orthogonal left-handed and right-handed chiral sectors via projectors $P_\pm$. Probing a single half-domain ($K_{\mathrm{half}} + K_{\mathrm{half}}^T = 4 T_{\mathrm{ch}}$) resolves the parity blindness of full-domain quadratic forms and recovers topological invariants.
  \item \textbf{Block-Pfaffian Squares ($\det M = \mathrm{Pf}(M)^2$):} For any skew-symmetric $2n \times 2n$ pairing matrix $M = -M^T$, the determinant is identically the square of its Pfaffian, governing non-vanishing energy gaps, planar dimer partition functions in statistical mechanics, and finite Cassels-Tate pairings in arithmetic geometry.
  \item \textbf{Real-Life Physical and Engineering Systems:} This Schur-tared stability arch governs boundary-layer drag depletion in fluid dynamics, power-grid frequency stabilization, acoustic noise cancellation, structural vibration attenuation, high-homogeneity magnetic resonance imaging shimming, and fault-tolerant topological quantum error correction.
\end{enumerate}

"""

def process_paper(tex_path: Path):
    with open(tex_path, "r", encoding="utf-8", errors="ignore") as fp:
        txt = fp.read()
    
    if "How Energy, Quantum Matter, Pfaffian Squares, and Real-Life Fields Connect" in txt:
        print(f"[-] Already has Pfaffian section: {tex_path.name}")
        return True
    
    # Target insertion points
    targets = [
        r"\section{Methodology and Epistemic Boundary}",
        r"\section{Epistemic Candour: Exact Boundaries}",
        r"\section{Formal Lean 4 Certification}",
        r"\section{Osterwalder-Schrader Reconstruction and Lean 4 Certification}",
        r"\section{Conclusion and Epistemic Integrity}",
        r"\section{Conclusion}",
        r"\end{document}"
    ]
    
    inserted = False
    for t in targets:
        if t in txt:
            txt = txt.replace(t, SECTION_TEXT + "\n" + t, 1)
            inserted = True
            break
            
    if not inserted:
        print(f"[!] Could not find target insertion point in {tex_path.name}")
        return False
        
    with open(tex_path, "w", encoding="utf-8") as fp:
        fp.write(txt)
    print(f"[+] Injected Pfaffian section into {tex_path.name}")
    
    # Compile with pdflatex (2 passes)
    parent_dir = str(tex_path.parent).replace("\\\\?\\", "")
    tex_filename = tex_path.name
    
    cmd = ["pdflatex", "-interaction=nonstopmode", tex_filename]
    res1 = subprocess.run(cmd, cwd=parent_dir, capture_output=True, text=True)
    res2 = subprocess.run(cmd, cwd=parent_dir, capture_output=True, text=True)
    
    if res2.returncode != 0:
        print(f"[FAIL] Compilation failed for {tex_filename}: returncode={res2.returncode}")
        # print tail of log
        print("\n".join(res2.stdout.splitlines()[-15:]))
        return False
    else:
        print(f"[PASS] Successfully compiled {tex_filename}")
        
    # Clean up temp files
    stem = tex_path.stem
    for ext in [".aux", ".log", ".out", ".toc"]:
        temp_file = Path(parent_dir) / f"{stem}{ext}"
        if temp_file.exists():
            try:
                temp_file.unlink()
            except Exception:
                pass
                
    # Update zip files in the folder if they exist
    pdf_path = Path(parent_dir) / f"{stem}.pdf"
    for zip_file in Path(parent_dir).glob("*.zip"):
        print(f"[*] Updating archive {zip_file.name} with updated PDF/TEX...")
        with zipfile.ZipFile(zip_file, "a") as zf:
            zf.write(tex_path, arcname=tex_filename)
            if pdf_path.exists():
                zf.write(pdf_path, arcname=pdf_path.name)
                
    return True

def main():
    tex_files = sorted(BASE_DIR.rglob("*.tex"))
    print(f"[*] Found {len(tex_files)} tex files in {BASE_DIR}")
    success_count = 0
    fail_count = 0
    for tf in tex_files:
        ok = process_paper(tf)
        if ok:
            success_count += 1
        else:
            fail_count += 1
            
    print(f"[*] Finished processing: {success_count} succeeded, {fail_count} failed.")

if __name__ == "__main__":
    main()
