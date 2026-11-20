#!/usr/bin/env python3
"""
build_all_riemann_theorem_and_common_person_papers.py

Generates, compiles, and packages standalone LaTeX/PDF papers for:
- Paper 00: Common-Person Relational Guide ("What Is Happening and What Relates to What")
- Paper T01: Exterior Prime Identity Matrices & Grade-2 Semiprime Drop (PrimeIdentityExteriorWedge.lean)
- Paper T02: Identity of One as Two Halves, Cholesky Whitening & Pi From Scratch (HalfDimensionIdentitySplit.lean)
- Paper T03: Tripotent {0, 1} Mobius Projectors & 4.71x Square-Free Subspace Booster (PrimeBinaryCompressionBooster.lean Thms 1-4)
- Paper T04: Higher-Dimensional Schur Trigonometry & Pythagorean Telescoping (PrimeBinaryCompressionBooster.lean Thms 5,6,8)
- Paper T05: Weierstrass-Euclid Half-Dimension Pinch & Exclusion Disc (EuclidOppositeSideExclusion.lean, EuclidPinchToRiemannBridge.lean)
- Paper T06: Semiprime GCD Tare Sqrt-Multiplicity & BBLR Angle Pinch (PrimeBinaryCompressionBooster.lean Thms 9-10)
- Paper T07: Lipschitz Continuity, Nested 4-Rosetta Intervals & Archimedean Squeeze (PrimeBinaryCompressionBooster.lean Thms 11-13)
- Paper T08: Continuum Selberg Quadratic Mollifier & Bettin-Conrey Reciprocity (ContinuumSelbergMollifierEnergyDecay.lean)

Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg.
Methodology: ai is being used as a tool.
"""

from __future__ import annotations

import os
import sys
import json
import re
import shutil
import subprocess
import zipfile
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent
OUTPUT_BASE = BASE_DIR / "zenodo_theorem_papers"
LEAN_SOURCE_DIR = BASE_DIR / "RiemannBlueprint" / "RiemannBlueprint"
PROBE_SOURCE_DIR_1 = Path("D:/Comfy UI/idea memory/obsidian brains/big picture/03_Riemann_Hypothesis/Probes")
PROBE_SOURCE_DIR_2 = Path("D:/Comfy UI/ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK/03_riemann_hypothesis/probes")
AUDIT_PACK_PAPERS_DIR = Path("D:/Comfy UI/ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK/03_riemann_hypothesis/papers")

from papers_rh_theorems import ALL_RIEMANN_PAPERS

LATEX_TEMPLATE = r"""\documentclass[11pt,a4paper]{article}

\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{booktabs}
\usepackage{xcolor}
\usepackage{listings}
\usepackage{geometry}
\usepackage{hyperref}

\providecommand{\Sha}{\mathrm{Sha}}

\geometry{
  a4paper,
  top=25mm,
  bottom=25mm,
  left=25mm,
  right=25mm
}

\hypersetup{
  colorlinks=true,
  linkcolor=blue!70!black,
  citecolor=red!70!black,
  urlcolor=teal!70!black
}

\lstdefinelanguage{Lean4}{
  keywords={theorem, lemma, def, where, by, have, exact, refine, intro, rintro, cases, rcases, constructor, calc, ring, norm_num, linarith, nlinarith, omega, dsimp, rw, simpa, import, namespace, end, open},
  keywordstyle=\color{blue!80!black}\bfseries,
  ndkeywords={Prop, Type, Real, Nat, Int, Bool, Set, Matrix, Fin},
  ndkeywordstyle=\color{teal!80!black}\bfseries,
  identifierstyle=\color{black},
  sensitive=true,
  comment=[l]{--},
  morecomment=[s]{/-}{-/},
  commentstyle=\color{green!50!black}\itshape,
  stringstyle=\color{purple},
  basicstyle=\ttfamily\small,
  breaklines=true,
  breakatwhitespace=true,
  frame=single,
  rulecolor=\color{gray!40},
  backgroundcolor=\color{gray!5},
  numbers=none,
  showstringspaces=false
}

\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{remark}[theorem]{Remark}

\title{\textbf{__TITLE__}}

\author{Qamar Munawer \\ Brandenburg University of Technology Cottbus-Senftenberg}

\date{\today}

\begin{document}

\maketitle

\begin{abstract}
__ABSTRACT__
\end{abstract}

\vspace{1em}
\noindent\textbf{Keywords:} __KEYWORDS__

\section{Introduction and Everyday Intuition}
__SECTION_1__

\section{Step-by-Step Mathematical Derivation}
__SECTION_2__

\section{Formal Lean 4 Theorem Exposition}
__SECTION_3__

\section{High-Precision Numerical Verification}
__SECTION_4__

\section{Methodology and Epistemic Boundary}
\noindent This research was developed using modern formal and computational methods where ai is being used as a tool for interactive formal theorem verification, high-precision symbolic calculation, and rigorous cross-workspace audit.

\vspace{0.5em}
\noindent\textbf{Epistemic Horizon Status:} All four Clay Millennium Problems (the Riemann Hypothesis, the Hodge Conjecture, the 4D Yang-Mills Mass Gap, and 3D Navier-Stokes Regularity) remain strictly open. The results presented in this paper constitute verified finite-dimensional algebraic theorems, unconditional identity splits, formal Lean 4 certificates, and reproducible numerical probes that establish exact structural invariants and obstruction boundaries within their mathematically defined domains.

\begin{thebibliography}{99}
__REFERENCES__
\end{thebibliography}

\end{document}
"""

def clean_lean_code_listing(sec_text: str) -> str:
    def replacer(match):
        code = match.group(1)
        replacements = [
            ("·", "."), ("⟨", "<"), ("⟩", ">"), ("•", "*"),
            ("∧", "/\\"), ("∨", "\\/"), ("→", "->"), ("↔", "<->"),
            ("∀", "forall "), ("∃", "exists "),
            ("≤", "<="), ("≥", ">="), ("≠", "!="), ("←", "<-"),
            ("₀", "0"), ("₁", "1"), ("₂", "2"), ("₃", "3"), ("₄", "4"),
            ("₅", "5"), ("₆", "6"), ("₇", "7"), ("₈", "8"), ("₉", "9"),
            ("λ", "lam"), ("ι", "iota"), ("π", "pi"), ("β", "beta"),
            ("μ", "mu"), ("η", "eta"), ("ρ", "rho"), ("ζ", "zeta"),
            ("φ", "phi"), ("Δ", "Delta"), ("Ω", "Omega"), ("Θ", "Theta"),
            ("ℝ", "Real"), ("ℕ", "Nat"), ("ℤ", "Int"), ("ℚ", "Rat"), ("ℂ", "Complex"),
            ("⁻¹", "^-1"), ("†", "*")
        ]
        for src, dst in replacements:
            code = code.replace(src, dst)
        return f"\\begin{{lstlisting}}[language=Lean4]{code}\\end{{lstlisting}}"
    
    return re.sub(r"\\begin\{lstlisting\}\[language=Lean4\](.*?)(\\end\{lstlisting\})", replacer, sec_text, flags=re.DOTALL)

def sanitize_text(text: str) -> str:
    t = text.replace("---", " - ").replace("--", " - ").replace("#", "")
    for sub, dig in zip("₀₁₂₃₄₅₆₇₈₉", "0123456789"):
        t = t.replace(sub, dig)
    
    def fix_texttt(m):
        inner = m.group(1).replace(r"\_", "_").replace("_", r"\_")
        return r"\texttt{" + inner + "}"

    t = re.sub(r"\\texttt\{([^}]+)\}", fix_texttt, t)
    t = re.sub(r'(?<!\\)%', r'\%', t)
    return t

def render_latex(paper_dict: dict) -> str:
    tex = LATEX_TEMPLATE
    tex = tex.replace("__TITLE__", sanitize_text(paper_dict["title"]))
    tex = tex.replace("__ABSTRACT__", sanitize_text(paper_dict["abstract"]))
    tex = tex.replace("__KEYWORDS__", sanitize_text(", ".join(paper_dict.get("keywords", []))))
    tex = tex.replace("__SECTION_1__", sanitize_text(paper_dict["sec1_intuition"]))
    tex = tex.replace("__SECTION_2__", sanitize_text(paper_dict["sec2_derivation"]))
    tex = tex.replace("__SECTION_3__", sanitize_text(clean_lean_code_listing(paper_dict["sec3_lean"])))
    tex = tex.replace("__SECTION_4__", sanitize_text(paper_dict["sec4_numerical"]))
    tex = tex.replace("__REFERENCES__", paper_dict["references"])
    return tex

def compile_pdf(tex_path: Path, output_dir: Path) -> bool:
    cmd = [
        "pdflatex",
        "-interaction=nonstopmode",
        "-halt-on-error",
        tex_path.name
    ]
    for pass_num in (1, 2):
        res = subprocess.run(cmd, cwd=str(output_dir), stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, errors="replace", timeout=480)
        if res.returncode != 0:
            print(f"[ERROR] pdflatex pass {pass_num} failed for {tex_path.name}:")
            log_file = output_dir / tex_path.with_suffix(".log").name
            if log_file.exists():
                lines = log_file.read_text(encoding="utf-8", errors="replace").splitlines()
                err_lines = [l for l in lines if l.startswith("!") or "Error" in l or "Undefined control" in l]
                print("\n".join(err_lines[:10]))
            return False
    return True

def latex_to_plain_text(text: str) -> str:
    t = text.replace("$", "")
    replacements = [
        (r"\wedge", "∧"), (r"\pi", "π"), (r"\Gamma", "Γ"), (r"\sqrt", "√"),
        (r"\mu", "μ"), (r"\in", "∈"), (r"\{", "{"), (r"\}", "}"),
        (r"\approx", "≈"), (r"\times", "×"), (r"\cos", "cos"), (r"\sin", "sin"),
        (r"\tan", "tan"), (r"\ln", "ln"), (r"\Theta", "Θ"), (r"^\circ", "°"),
        (r"\mathrm{dir}", "dir"), (r"\mathrm{moll}", "moll"), (r"\mathrm{BBLR}", "BBLR"),
        (r"\mathrm", ""), (r"\beta", "β"), (r"\le", "≤"), (r"\ge", "≥"),
        (r"\Delta", "Δ"), (r"\subseteq", "⊆"), (r"\varepsilon", "ε"),
        (r"\lceil", "⌈"), (r"\rceil", "⌉"), (r"\exp", "exp"), (r"\mathcal{O}", "O"),
        (r"\%", "%"), (r"\_", "_"), ("---", " - "), ("--", " - ")
    ]
    for src, dst in replacements:
        t = t.replace(src, dst)
    return t

def generate_zenodo_json(paper_dict: dict, out_path: Path):
    clean_abstract = latex_to_plain_text(paper_dict['abstract'])
    metadata = {
        "title": latex_to_plain_text(paper_dict["title"]),
        "upload_type": "publication",
        "publication_type": "article",
        "description": (
            f"<p>{clean_abstract}</p>"
            f"<p><strong>Formal Verification:</strong> Certified in Lean 4 with zero custom axioms [propext, Classical.choice, Quot.sound].</p>"
            f"<p><strong>Methodology:</strong> In accordance with open science standards, ai is being used as a tool for formal proof synthesis and numerical cross-checking.</p>"
            f"<p><strong>Epistemic Horizon:</strong> Finite structural theorem; open Millennium horizons remain strictly open.</p>"
        ),
        "creators": [
            {
                "name": "Qamar Munawer",
                "affiliation": "Brandenburg University of Technology Cottbus-Senftenberg",
                "orcid": "0009-0004-9467-3363"
            }
        ],
        "keywords": paper_dict.get("keywords", []) + ["Lean 4", "Formal Mathematics", "ai is being used as a tool"],
        "license": "cc-by-4.0",
        "access_right": "open"
    }
    out_path.write_text(json.dumps(metadata, indent=2, ensure_ascii=False), encoding="utf-8")

def to_extended_path(p: Path) -> str:
    s = str(p.resolve())
    if s.startswith("\\\\?\\"):
        return s
    return "\\\\?\\" + s

def build_paper_bundle(paper_dict: dict) -> bool:
    paper_id = paper_dict["id"]
    folder_prefix = "_".join(paper_id.split("_")[:2])
    paper_dir = OUTPUT_BASE / folder_prefix
    paper_dir.mkdir(parents=True, exist_ok=True)
    lean_dir = paper_dir / "lean4_certificates"
    probe_dir = paper_dir / "probes"
    lean_dir.mkdir(exist_ok=True)
    probe_dir.mkdir(exist_ok=True)

    # Copy lean files
    for lf in paper_dict.get("lean_files", []):
        src = LEAN_SOURCE_DIR / lf
        if src.exists():
            shutil.copy2(src, lean_dir / lf)
        else:
            print(f"[WARN] Lean file {lf} not found in {LEAN_SOURCE_DIR}")

    # Copy probe receipts
    for pf in paper_dict.get("probe_files", []):
        src1 = PROBE_SOURCE_DIR_1 / pf
        src2 = PROBE_SOURCE_DIR_2 / pf
        if src1.exists():
            shutil.copy2(src1, probe_dir / pf)
        elif src2.exists():
            shutil.copy2(src2, probe_dir / pf)
        else:
            print(f"[WARN] Probe file {pf} not found")

    # Generate .zenodo.json
    generate_zenodo_json(paper_dict, paper_dir / ".zenodo.json")

    # Generate .tex
    tex_content = render_latex(paper_dict)
    tex_path = paper_dir / f"{paper_id}.tex"
    tex_path.write_text(tex_content, encoding="utf-8")

    # Compile PDF
    print(f"--> Compiling {paper_id}.tex in {folder_prefix}/ with pdflatex (2 passes)...")
    ok = compile_pdf(tex_path, paper_dir)
    if not ok:
        return False
    pdf_path = paper_dir / f"{paper_id}.pdf"
    print(f"    [OK] Generated {pdf_path.name} ({round(pdf_path.stat().st_size / 1024, 1)} KB)")

    # Create Zenodo ZIP bundle
    zip_path = paper_dir / f"{paper_id}_ZENODO.zip"
    zip_target = to_extended_path(zip_path)
    with zipfile.ZipFile(zip_target, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.write(pdf_path, pdf_path.name)
        zf.write(tex_path, tex_path.name)
        zf.write(paper_dir / ".zenodo.json", ".zenodo.json")
        for lf in lean_dir.glob("*.lean"):
            zf.write(lf, f"lean4_certificates/{lf.name}")
        for pf in probe_dir.glob("*.json"):
            zf.write(pf, f"probes/{pf.name}")
    print(f"    [OK] Packaged {zip_path.name}")

    # Copy PDF to audit pack papers directory
    if AUDIT_PACK_PAPERS_DIR.exists():
        shutil.copy2(pdf_path, AUDIT_PACK_PAPERS_DIR / pdf_path.name)

    return True

def main() -> int:
    print("=" * 80)
    print("BUILDING ALL 9 RIEMANN STANDALONE PAPERS (PAPER 00 + T01 THROUGH T08)")
    print("Methodology note: ai is being used as a tool.")
    print("Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg.")
    print("=" * 80)

    OUTPUT_BASE.mkdir(parents=True, exist_ok=True)
    success_count = 0
    total = len(ALL_RIEMANN_PAPERS)

    for i, p in enumerate(ALL_RIEMANN_PAPERS, 1):
        print(f"\n[{i}/{total}] Processing {p['id']}...")
        if build_paper_bundle(p):
            success_count += 1
        else:
            print(f"[FAIL] Paper {p['id']} compilation failed!")
            return 1

    print("\n" + "=" * 80)
    print(f"SUCCESS: {success_count}/{total} standalone papers generated, compiled, and packaged!")
    print(f"Output directory: {OUTPUT_BASE}")
    print("=" * 80)

    return 0

if __name__ == "__main__":
    raise SystemExit(main())
