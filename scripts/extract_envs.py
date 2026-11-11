import re

with open('d:/Comfy UI/rheihman hypothesis/research/interactive_lab/monograph_additive_multiplicative/main.tex', 'r', encoding='utf-8') as f:
    lines = f.readlines()

env_pattern = re.compile(r'\\begin\{(definition|lemma|proposition|theorem|corollary)\}')
label_pattern = re.compile(r'\\label\{([^}]+)\}')

results = []
current_env = None
current_line = 0

for idx, line in enumerate(lines, 1):
    m = env_pattern.search(line)
    if m:
        current_env = m.group(1)
        current_line = idx
        # look ahead for label
        lbl = ""
        for j in range(idx - 1, min(idx + 5, len(lines))):
            lm = label_pattern.search(lines[j])
            if lm:
                lbl = lm.group(1)
                break
        results.append(f"Line {current_line}: \\begin{{{current_env}}} [label: {lbl}]")

with open('d:/Comfy UI/rheihman hypothesis/research/interactive_lab/monograph_additive_multiplicative/RiemannBlueprint/math_envs.txt', 'w', encoding='utf-8') as f:
    f.write('\n'.join(results))

print(f"Extracted {len(results)} mathematical environments.")
