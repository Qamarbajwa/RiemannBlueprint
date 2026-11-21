#!/usr/bin/env python3
"""
publish_rh_t09_zenodo_v6_1.py
Publishes Version 6.1.0 of RH_T09 on Zenodo:
1. Updates draft deposition 24412350 (linked to Concept DOI 10.5281/zenodo.24409898).
2. Removes previous version files from the draft.
3. Uploads the new v6.1.0 artifacts to the Zenodo bucket:
   - RH_T09_ZENODO.zip (902,625 bytes)
   - RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.pdf (996,103 bytes)
   - RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.tex
4. Updates deposition metadata to Version 6.1.0 with comprehensive abstract and keywords.
5. Publishes the deposition to mint the permanent DOI.

Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg
Methodology note: ai is being used as a tool.
Epistemic invariant: all four Clay Millennium Problems remain strictly OPEN.
"""

import os
import sys
import json
import urllib.request
import urllib.error
from pathlib import Path

DEPO_ID = 24412350
BUCKET_URL = "https://zenodo.org/api/files/728e2f6d-36ee-4891-bf0e-17bb4e88d328"

def to_win_long(p_obj):
    s = str(Path(p_obj).resolve())
    if s.startswith('\\\\?\\'):
        return s
    return '\\\\?\\' + s

def get_token():
    tok = os.environ.get("ZENODO_TOKEN") or os.environ.get("ZENODO_ACCESS_TOKEN")
    if not tok:
        raise ValueError("ZENODO_TOKEN environment variable is missing!")
    return tok

def make_req(url, method="GET", data=None, token="", content_type="application/json"):
    headers = {"Authorization": f"Bearer {token}"}
    if content_type:
        headers["Content-Type"] = content_type
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    with urllib.request.urlopen(req) as resp:
        return json.loads(resp.read().decode("utf-8")), resp.status

def upload_file_to_bucket(bucket_url, filename, filepath, token):
    url = f"{bucket_url}/{filename}"
    print(f"[*] Uploading {filename} ({os.stat(filepath).st_size:,} bytes) to {url}...")
    headers = {
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/octet-stream"
    }
    with open(filepath, "rb") as f:
        data = f.read()
    req = urllib.request.Request(url, data=data, headers=headers, method="PUT")
    with urllib.request.urlopen(req) as resp:
        return json.loads(resp.read().decode("utf-8")), resp.status

def main():
    print("======================================================================")
    print("ZENODO ONLINE DEPOSITION PUBLISHER: VERSION 6.1.0")
    print(f"Deposition Draft ID: {DEPO_ID}")
    print("Concept DOI: 10.5281/zenodo.24409898")
    print("Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg")
    print("Methodology: ai is being used as a tool")
    print("======================================================================")

    token = get_token()
    base_dir = Path.cwd() / "research/interactive_lab/monograph_additive_multiplicative/zenodo_theorem_papers/RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity"
    
    zip_path = to_win_long(base_dir / "RH_T09_ZENODO.zip")
    pdf_path = to_win_long(base_dir / "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.pdf")
    tex_path = to_win_long(base_dir / "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.tex")

    # 1. Inspect existing files in draft and remove them
    print("[*] Checking existing files in draft...")
    depo_data, _ = make_req(f"https://zenodo.org/api/deposit/depositions/{DEPO_ID}", token=token)
    for f in depo_data.get("files", []):
        fid = f["id"]
        fname = f["filename"]
        print(f"[*] Deleting old file: {fname} (ID: {fid})...")
        del_url = f"https://zenodo.org/api/deposit/depositions/{DEPO_ID}/files/{fid}"
        req = urllib.request.Request(del_url, headers={"Authorization": f"Bearer {token}"}, method="DELETE")
        try:
            with urllib.request.urlopen(req) as resp:
                pass
            print(f"[+] Deleted old {fname}")
        except Exception as e:
            print(f"[-] Error deleting {fname}: {e}")

    # 2. Upload new Version 6.1.0 files to bucket
    print("\n[*] Uploading v6.1.0 artifacts to Zenodo bucket...")
    upload_file_to_bucket(BUCKET_URL, "RH_T09_ZENODO.zip", zip_path, token)
    upload_file_to_bucket(BUCKET_URL, "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.pdf", pdf_path, token)
    upload_file_to_bucket(BUCKET_URL, "RH_T09_Two_Piece_Factorized_Mollifiers_And_True_Signed_Weil_Schur_Coercivity_Paper.tex", tex_path, token)

    # 3. Update Deposition Metadata
    print("\n[*] Updating Zenodo deposition metadata to v6.1.0...")
    metadata = {
        "title": "Two-Piece Grade-Factorized Mollifiers, True Signed Weil Schur Coercivity, and the Rosetta Cross-Field Unification",
        "upload_type": "publication",
        "publication_type": "preprint",
        "version": "v6.1.0",
        "description": (
            "<p>In this definitive research monograph (Version 6.1.0), we formulate and machine-certify the two-piece grade-factorized "
            "mollifier architecture, true signed Weil-Schur coercivity, and the Rosetta cross-field structural unification across "
            "the Clay Millennium Problems.</p>"
            "<p>Key verified milestones certified with zero custom axioms in Lean 4 across 27 modules and 19 high-precision "
            "numerical audit probes include: (1) The Two Races as L -&gt; infinity audit establishing that the active Schur floor "
            "scales as L^{+0.6406}, outrunning exterior algebraic tail leakage C_w / L; (2) Weighted Sobolev distributional duality "
            "on H^1_w(R) eliminating artificial hard box boundaries; (3) Arthur-Selberg Eisenstein scattering regularization proving "
            "O(1/sqrt(Y)) continuous leakage choke down to 8.26 x 10^{-6} at Y = 1,000,000; (4) Maass-Selberg cuspidal slit architecture "
            "eliminating continuous radiation above Y = sqrt(X); (5) Chiral Virial Commutator Engine and dilation Sobolev domain core; "
            "(6) Non-Archimedean quantum graph measure and adelic orientation rigidity; (7) 100-zero multi-scale Virial landscape audit "
            "(gamma_1 to gamma_100); and (8) The Rosetta Stone cross-field gap bridge unifying spectral gap positivity across all four "
            "Millennium Problems.</p>"
            "<p><b>Methodology note:</b> ai is being used as a tool.<br>"
            "<b>Epistemic Invariant:</b> All four Clay Millennium Problems remain strictly OPEN (status: verified-finite). "
            "Continuum Premise A is explicitly isolated as the asymptotic race lambda_min &gt; C_w / L as L -&gt; infinity.</p>"
        ),
        "creators": [
            {
                "name": "Munawer, Qamar",
                "affiliation": "Brandenburg University of Technology Cottbus-Senftenberg"
            }
        ],
        "access_right": "open",
        "license": "cc-by-4.0",
        "keywords": [
            "Riemann Hypothesis",
            "The Two Races as L -> infinity",
            "Active Schur Floor Scaling",
            "Exterior Algebraic Tail Leakage",
            "Clay Boundary Gap Analysis",
            "Resolvent Spectral Measure Limit",
            "Arthur-Selberg Eisenstein Scattering",
            "Weighted Sobolev Distributional Duality",
            "Maass-Selberg Cuspidal Slit",
            "Chained Automorphic Theta Lifts",
            "Stepanov-Deligne Sign Opposition",
            "Chiral Virial Commutator Engine",
            "Dilation Sobolev Domain",
            "Non-Archimedean Quantum Graph",
            "100-Zero Virial Landscape",
            "Signed Weil Quadratic Form",
            "Factorized Mollifier",
            "Schur Complement Tare",
            "Sobolev Quotient Operator",
            "Hilbert-Polya Operator",
            "Euler-Maclaurin Dispersion",
            "Maass Cusp Form",
            "Norm-Resolvent Convergence",
            "Sobolev Compact Resolvent",
            "Rosetta Cross-Field Bridge",
            "Lean 4 Certified Bridge",
            "Open Clay Horizon Lock"
        ]
    }

    put_data = json.dumps({"metadata": metadata}).encode("utf-8")
    put_url = f"https://zenodo.org/api/deposit/depositions/{DEPO_ID}"
    resp_meta, status_meta = make_req(put_url, method="PUT", data=put_data, token=token)
    print(f"[+] Metadata updated successfully! Title: {resp_meta.get('title')} | Version: {resp_meta.get('metadata', {}).get('version')}")

    # 4. Publish deposition
    print("\n[*] Publishing deposition to mint permanent DOI...")
    publish_url = f"https://zenodo.org/api/deposit/depositions/{DEPO_ID}/actions/publish"
    req_pub = urllib.request.Request(publish_url, headers={"Authorization": f"Bearer {token}"}, method="POST")
    try:
        with urllib.request.urlopen(req_pub) as pub_resp:
            pub_data = json.loads(pub_resp.read().decode("utf-8"))
            doi = pub_data.get("doi")
            concept_doi = pub_data.get("conceptdoi")
            record_url = pub_data.get("links", {}).get("record_html")
            print("======================================================================")
            print("[+] ZENODO PUBLICATION SUCCESSFUL!")
            print(f"    New Permanent DOI: {doi}")
            print(f"    Concept DOI (all versions): {concept_doi}")
            print(f"    Public Record URL: {record_url}")
            print("======================================================================")
            
            # Save receipt
            deposit_receipt = {
                "zenodo_deposition_id": DEPO_ID,
                "version": "v6.1.0",
                "doi": doi,
                "concept_doi": concept_doi,
                "public_url": record_url,
                "timestamp_utc": pub_data.get("modified"),
                "author": "Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg",
                "methodology": "ai is being used as a tool",
                "epistemic_status": "verified-finite (strictly open Clay horizon)"
            }
            with open("scripts/zenodo_v6_1_deposit_receipt.json", "w", encoding="utf-8") as f:
                json.dump(deposit_receipt, f, indent=2)
            print("[+] Receipt saved to: scripts/zenodo_v6_1_deposit_receipt.json")
    except urllib.error.HTTPError as e:
        print(f"[-] HTTP Error {e.code} during publish: {e.read().decode('utf-8')}")
    except Exception as e:
        print(f"[-] Error during publish: {e}")

if __name__ == "__main__":
    main()
