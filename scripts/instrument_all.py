with open('d:/Comfy UI/rheihman hypothesis/research/interactive_lab/monograph_additive_multiplicative/main.tex', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Map starting line number (1-based) to the instrumentation lines to insert
instrumentation = {
    131: "\\label{def:primes_units}\n\\lean{RiemannBlueprint.Section2_PrimeAtoms.Primes}\n\\leanok",
    141: "\\lean{RiemannBlueprint.Section2_PrimeAtoms.bezout_identity}\n\\leanok",
    163: "\\lean{RiemannBlueprint.Section2_PrimeAtoms.euclid_lemma}\n\\uses{lem:bezout}\n\\leanok",
    180: "\\lean{RiemannBlueprint.Section2_PrimeAtoms.fundamental_theorem_of_arithmetic}\n\\uses{lem:euclid}\n\\leanok",
    210: "\\lean{RiemannBlueprint.Section2_PrimeAtoms.modulo_6_sieve_confinement}\n\\uses{thm:fta}\n\\leanok",
    235: "\\lean{RiemannBlueprint.Section2_PrimeAtoms.fermats_little_theorem}\n\\leanok",
    257: "\\lean{RiemannBlueprint.Section2_PrimeAtoms.wilsons_theorem}\n\\leanok",
    290: "\\label{def:ord10}\n\\lean{RiemannBlueprint.Section2_PrimeAtoms.ord10}\n\\leanok",
    298: "\\lean{RiemannBlueprint.Section2_PrimeAtoms.base10_radix_periodicity}\n\\uses{thm:flt, def:ord10}\n\\leanok",

    367: "\\label{def:omega_Omega}\n\\lean{RiemannBlueprint.Section3_CompositeTaxonomy.omega}\n\\leanok",
    376: "\\label{prop:arithmetic_classification}\n\\lean{RiemannBlueprint.Section3_CompositeTaxonomy.arithmetic_classification_partition}\n\\leanok",
    391: "\\label{def:pure_mixed_composites}\n\\lean{RiemannBlueprint.Section3_CompositeTaxonomy.PureComposites}\n\\uses{def:omega_Omega}\n\\leanok",
    410: "\\lean{RiemannBlueprint.Section3_CompositeTaxonomy.von_mangoldt_isolation}\n\\uses{def:pure_mixed_composites}\n\\leanok",
    438: "\\label{def:divisor_functions}\n\\leanok",
    446: "\\uses{thm:fta}\n\\leanok",
    466: "\\lean{RiemannBlueprint.Section3_CompositeTaxonomy.divisor_count_composite}\n\\leanok",
    487: "\\label{def:totient_function}\n\\leanok",
    495: "\\lean{RiemannBlueprint.Section3_CompositeTaxonomy.prime_vs_composite_totient_gap}\n\\uses{cor:divisor_bounds}\n\\leanok",
    517: "\\uses{prop:totient_gap}\n\\leanok",
    579: "\\lean{RiemannBlueprint.Section3_CompositeTaxonomy.coprime_composite_lattice}\n\\leanok",

    607: "\\label{def:P_and_zetaC}\n\\lean{RiemannBlueprint.Section4_CompositeZeta.PrimeZeta}\n\\leanok",
    615: "\\lean{RiemannBlueprint.Section4_CompositeZeta.additive_identity_relation}\n\\uses{def:P_and_zetaC}\n\\leanok",
    648: "\\label{def:local_euler}\n\\leanok",
    662: "\\uses{thm:additive_identity}\n\\leanok",
    687: "\\lean{RiemannBlueprint.Section4_CompositeZeta.divisor_weight_primes_and_composites}\n\\uses{cor:divisor_bounds}\n\\leanok",
    737: "\\lean{RiemannBlueprint.Section4_CompositeZeta.analytic_discrepancy_theorem}\n\\uses{thm:divisor_weighted}\n\\leanok",

    803: "\\lean{RiemannBlueprint.Section5_MobiusMertens.ReciprocalZeta}\n\\leanok",
    848: "\\lean{RiemannBlueprint.Section5_MobiusMertens.reciprocal_partition_identity}\n\\uses{thm:reciprocal_euler_product}\n\\leanok",
    893: "\\lean{RiemannBlueprint.Section5_MobiusMertens.mertens}\n\\leanok",
    902: "\\uses{def:mertens_function}\n\\leanok",
    938: "\\lean{RiemannBlueprint.Section5_MobiusMertens.mertens_riemann_equivalence}\n\\uses{lem:mellin_reciprocal_zeta}\n\\leanok",

    1028: "\\lean{RiemannBlueprint.Section6_CriticalStripAudit.zero_free_half_plane}\n\\leanok",
    1060: "\\lean{RiemannBlueprint.Section6_CriticalStripAudit.additive_partition_firewall}\n\\leanok",
    1092: "\\lean{RiemannBlueprint.Section6_CriticalStripAudit.dirichletEta}\n\\leanok",
    1101: "\\lean{RiemannBlueprint.Section6_CriticalStripAudit.dirichlet_eta_relation}\n\\uses{def:dirichlet_eta}\n\\leanok",
    1147: "\\uses{thm:eta_continuation}\n\\leanok",
    1164: "\\lean{RiemannBlueprint.Section6_CriticalStripAudit.chi_critical_line_modulus}\n\\uses{thm:approx_functional_equation}\n\\leanok",

    1204: "\\lean{RiemannBlueprint.Section7_SpectralBridge.chebyshevPsi}\n\\leanok",
    1219: "\\uses{def:chebyshev_functions}\n\\leanok",
    1247: "\\label{def:normalized_chebyshev}\n\\leanok",
    1257: "\\uses{lem:log_derivative_zeta}\n\\leanok",
    1335: "\\lean{RiemannBlueprint.Section7_SpectralBridge.spectral_stability_theorem}\n\\uses{thm:riemann_explicit_formula}\n\\leanok"
}

out_lines = []
start_collecting = False

for idx, line in enumerate(lines, 1):
    if line.strip().startswith('\\begin{abstract}'):
        start_collecting = True
    if line.strip().startswith('\\end{document}'):
        start_collecting = False
        break
    
    if not start_collecting:
        continue
    
    # Add proof leanok
    if line.strip() == '\\begin{proof}':
        out_lines.append(line)
        out_lines.append('\\leanok\n')
        continue
    
    out_lines.append(line)
    
    # Check if this line is an environment definition
    if idx in instrumentation:
        # If the next line is a \label, we insert AFTER the label; otherwise immediately after
        next_line = lines[idx] if idx < len(lines) else ""
        if '\\label{' in next_line:
            pass # we will insert after the next line
        else:
            out_lines.append(instrumentation[idx] + '\n')
    
    if (idx - 1) in instrumentation:
        prev_line = lines[idx - 2]
        if '\\label{' in line:
            out_lines.append(instrumentation[idx - 1] + '\n')

with open('d:/Comfy UI/rheihman hypothesis/research/interactive_lab/monograph_additive_multiplicative/RiemannBlueprint/blueprint/src/content.tex', 'w', encoding='utf-8') as f:
    f.writelines(out_lines)

print(f"content.tex written successfully ({len(out_lines)} lines).")
