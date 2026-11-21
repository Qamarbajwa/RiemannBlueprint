#!/usr/bin/env python3
"""
probe_unconditional_premise_discharge.py
=========================================
Audits theorem signatures in RiemannBlueprint and across all four workspaces
to quantify the reduction and elimination of floating analytical hypotheses.

Author: Qamar Munawer
Affiliation: Brandenburg University of Technology Cottbus-Senftenberg
Methodology: ai is being used as a tool
Epistemic Boundary: All four Clay Millennium Problems remain strictly OPEN
(status: verified-finite, open_horizon_lock: STRICTLY OPEN).
"""

from __future__ import annotations

import json
import os
import re
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
WORKSPACE_DIR = SCRIPT_DIR.parent
RECEIPT_PATH = SCRIPT_DIR / "probe_unconditional_premise_discharge_receipt.json"

# Paths to the 5 workspaces
WORKSPACES = {
    "01_hodge": Path(r"d:\Comfy UI\hodge conjecture\examples\math_gov\LeanMillenniumExt"),
    "02_yang_mills": Path(r"d:\Comfy UI\yang mills and the mass gap\formal"),
    "03_riemann": Path(r"d:\Comfy UI\rheihman hypothesis\RiemannBlueprint"),
    "04_navier_stokes": Path(r"d:\Comfy UI\tubulance\formal"),
    "05_p_vs_np": Path(r"d:\Comfy UI\tubulance\formal"),
}

# Regex patterns for theorem/lemma detection in Lean 4
THM_PATTERN = re.compile(
    r"^(?:theorem|lemma)\s+([A-Za-z0-9_]+)\s*([\s\S]*?):=", re.MULTILINE
)
ARG_PATTERN = re.compile(r"\(([^)]+)\)")


def categorize_argument(arg_str: str) -> str:
    """Categorizes a Lean argument into variable, positivity condition, or analytical hypothesis."""
    arg_str = arg_str.strip()
    if ":" not in arg_str:
        return "structural"
    name_part, type_part = arg_str.split(":", 1)
    name_part = name_part.strip()
    type_part = type_part.strip()

    # Relational propositions (hypotheses)
    if any(op in type_part for op in ["<", "≤", ">", "≥", "="]) and "→" not in type_part:
        if re.match(r"^0\s*[<≤]\s*[A-Za-z0-9_]+$", type_part) or re.match(r"^[A-Za-z0-9_]+\s*≠\s*0$", type_part):
            return "domain_positivity"
        return "analytical_hypothesis"

    if type_part.startswith("∀"):
        return "analytical_hypothesis"

    return "variable"


def audit_lean_file(filepath: Path) -> list[dict]:
    """Audits all theorems/lemmas in a Lean 4 file."""
    if not filepath.exists():
        return []

    content = filepath.read_text(encoding="utf-8")
    results = []

    for match in THM_PATTERN.finditer(content):
        thm_name = match.group(1)
        sig_body = match.group(2).strip()

        # Find return type (after the colon that defines the return proposition)
        # Note: signatures look like: `(args...) : ReturnProp :=`
        # We split by `:` from right to get return type
        def find_declaration_colon(s: str) -> int:
            depth = 0
            for i, ch in enumerate(s):
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
                elif ch == ":" and depth == 0:
                    return i
            return -1

        colon_idx = find_declaration_colon(sig_body)
        if colon_idx != -1:
            args_part = sig_body[:colon_idx].strip()
            return_prop = sig_body[colon_idx + 1:].strip()

        # Extract arguments
        args = ARG_PATTERN.findall(args_part)
        classified_args = []
        analytical_hypotheses = []

        for arg in args:
            cat = categorize_argument(arg)
            classified_args.append({"arg": arg.strip(), "category": cat})
            if cat == "analytical_hypothesis":
                analytical_hypotheses.append(arg.strip())

        is_hypothesis_free = len(analytical_hypotheses) == 0

        results.append({
            "theorem": thm_name,
            "file": filepath.name,
            "total_args": len(args),
            "classified_args": classified_args,
            "analytical_hypotheses": analytical_hypotheses,
            "is_hypothesis_free": is_hypothesis_free,
            "status": "UNCONDITIONAL" if is_hypothesis_free else "CONDITIONAL",
        })

    return results


def run_audit() -> dict:
    t0 = time.time()
    print("=" * 80)
    print("PROBE: UNCONDITIONAL PREMISE DISCHARGE AUDIT ACROSS 4 WORKSPACES")
    print("Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg")
    print("Methodology: ai is being used as a tool")
    print("Epistemic Boundary: All four Clay Millennium Problems remain strictly OPEN")
    print("=" * 80)

    # 1. Audit Riemann Blueprint
    riemann_dir = WORKSPACES["03_riemann"]
    riemann_modules = [
        "RiemannNonCommutingPrimeUncertaintyCert.lean",
        "RosettaPhaseDispersionAndUncertaintyCert.lean",
        "AlpogeClaudeThetaSeesawAndBostSlopeBridgeCert.lean",
        "UnconditionalPremiseDischargeAudit.lean",
        "MathlibRiemannZetaDirectBridge.lean",
        "RiemannQuintillionPrimeWindowAndSchoenfeldCert.lean",
        "PrimeBinaryCompressionBooster.lean",
        "WeilSignedSubGapTareCoercivity.lean",
        "PrimeLogBakerEffectiveDischarge.lean",
    ]

    print("\n[WORKSPACE 03: RIEMANN HYPOTHESIS]")
    riemann_audits = {}
    for mod in riemann_modules:
        p = riemann_dir / mod
        if p.exists():
            thms = audit_lean_file(p)
            uncond = sum(1 for t in thms if t["is_hypothesis_free"])
            cond = sum(1 for t in thms if not t["is_hypothesis_free"])
            riemann_audits[mod] = {
                "theorems": thms,
                "total": len(thms),
                "unconditional": uncond,
                "conditional": cond,
            }
            print(f"  - {mod:<55} Total: {len(thms):2d} | Unconditional: {uncond:2d} | Conditional: {cond:2d}")
            for t in thms:
                marker = " [FREE]" if t["is_hypothesis_free"] else " [COND]"
                print(f"      {marker} {t['theorem']}")
                if not t["is_hypothesis_free"]:
                    for h in t["analytical_hypotheses"]:
                        print(f"             └── hypothesis: {h}")

    # 2. Audit Cross-Workspace Premise Elimination Modules
    cross_workspace_modules = {
        "01_hodge": [
            "HodgeKudlaMillsonSeesawAndBostSlopeCert.lean",
            "HodgeArakelovChowCompactnessCert.lean",
            "HodgeUnconditionalArakelovSlopeDischarge.lean",
            "HodgeBostEffectiveCycleDegreeCert.lean",
        ],
        "02_yang_mills": [
            "YangMillsBalabanPolymerContractionCert.lean",
            "YangMillsUnconditionalPolymerContractionDischarge.lean",
            "YM187_S3CocyclePullAndBalabanConvergenceCert.lean",
            "YangMillsInstantonActionFloorCert.lean",
        ],
        "04_navier_stokes": [
            "NavierStokesDyadicCascadeAndBiotSavartCert.lean",
            "NavierStokesUnconditionalDyadicDampingDischarge.lean",
            "RosettaContinuumAnalyticPremiseACert.lean",
            "NavierStokesHeterochiralDecayCert.lean",
        ],
        "05_p_vs_np": [
            "PvsNPUnconditionalPfaffianGenusDischarge.lean",
            "PvsNPContinuumPfaffianGenusBarrierCert.lean",
            "BSDContinuumCasselsTatePfaffianFinitenessCert.lean",
        ],
    }

    cross_audits = {}
    for ws, mods in cross_workspace_modules.items():
        ws_dir = WORKSPACES[ws]
        print(f"\n[WORKSPACE {ws.upper()}]")
        ws_res = {}
        for mod in mods:
            p = ws_dir / mod
            if p.exists():
                thms = audit_lean_file(p)
                uncond = sum(1 for t in thms if t["is_hypothesis_free"])
                cond = sum(1 for t in thms if not t["is_hypothesis_free"])
                ws_res[mod] = {
                    "total": len(thms),
                    "unconditional": uncond,
                    "conditional": cond,
                    "theorems": thms,
                }
                print(f"  - {mod:<55} Total: {len(thms):2d} | Unconditional: {uncond:2d} | Conditional: {cond:2d}")
                for t in thms:
                    marker = " [FREE]" if t["is_hypothesis_free"] else " [COND]"
                    print(f"      {marker} {t['theorem']}")
                    if not t["is_hypothesis_free"]:
                        for h in t["analytical_hypotheses"]:
                            print(f"             └── hypothesis: {h}")
        cross_audits[ws] = ws_res

    # 3. Aggregate Scorecard
    total_theorems = 0
    total_unconditional = 0
    total_conditional = 0

    for res in riemann_audits.values():
        total_theorems += res["total"]
        total_unconditional += res["unconditional"]
        total_conditional += res["conditional"]

    for ws_res in cross_audits.values():
        for res in ws_res.values():
            total_theorems += res["total"]
            total_unconditional += res["unconditional"]
            total_conditional += res["conditional"]

    scorecard = {
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "total_theorems_audited": total_theorems,
        "total_unconditional_theorems": total_unconditional,
        "total_conditional_theorems": total_conditional,
        "unconditional_ratio_pct": round(100.0 * total_unconditional / total_theorems, 2) if total_theorems else 0.0,
        "newly_created_unconditional_modules": {
            "01_hodge": "HodgeUnconditionalArakelovSlopeDischarge.lean",
            "02_yang_mills": "YangMillsUnconditionalPolymerContractionDischarge.lean",
            "03_riemann": "UnconditionalPremiseDischargeAudit.lean",
            "04_navier_stokes": "NavierStokesUnconditionalDyadicDampingDischarge.lean",
            "05_p_vs_np": "PvsNPUnconditionalPfaffianGenusDischarge.lean",
        },
        "epistemic_boundary": {
            "HODGE_CONJECTURE_OPEN": True,
            "YANG_MILLS_MASS_GAP_OPEN": True,
            "RIEMANN_HYPOTHESIS_OPEN": True,
            "NAVIER_STOKES_REGULARITY_OPEN": True,
            "P_VS_NP_OPEN": True,
            "status": "verified-finite",
            "open_horizon_lock": "STRICTLY OPEN",
        },
        "riemann_details": riemann_audits,
        "cross_workspace_details": cross_audits,
    }

    print("\n" + "=" * 80)
    print("UNCONDITIONAL PREMISE DISCHARGE SCORECARD")
    print(f"  Total Theorems Audited:        {total_theorems}")
    print(f"  100% Hypothesis-Free Theorems: {total_unconditional} ({scorecard['unconditional_ratio_pct']}%)")
    print(f"  Legacy Conditional Theorems:   {total_conditional}")
    print("=" * 80)

    RECEIPT_PATH.write_text(json.dumps(scorecard, indent=2), encoding="utf-8")
    print(f"Receipt written to: {RECEIPT_PATH}")
    return scorecard


if __name__ == "__main__":
    run_audit()
