import os
from pathlib import Path
from jinja2 import Environment, FileSystemLoader
import leanblueprint

pkg_dir = Path(leanblueprint.__file__).parent
loader = FileSystemLoader(pkg_dir / "templates")
env = Environment(
    loader=loader,
    variable_start_string='{|',
    variable_end_string='|}',
    comment_start_string='{--',
    comment_end_string='--}'
)

config = {
    'master_branch': 'main',
    'github_username': 'qamar-munawer',
    'github_projectname': 'additive-multiplicative-zeta-blueprint',
    'title': 'Additive-Multiplicative Completeness of Prime and Composite Dirichlet Systems: Structural Partitions, Natural Boundaries, and Spectral Equivalences of the Riemann Hypothesis',
    'lib_name': 'RiemannBlueprint',
    'author': 'Qamar Munawer',
    'github': 'https://github.com/qamar-munawer/additive-multiplicative-zeta-blueprint',
    'home': 'https://qamar-munawer.github.io/additive-multiplicative-zeta-blueprint',
    'dochome': 'https://qamar-munawer.github.io/additive-multiplicative-zeta-blueprint/docs',
    'documentclass': 'report',
    'paper': 'a4paper',
    'showmore': True,
    'toc_depth': 3,
    'split_level': 1,
    'localtoc_level': 0
}

repo_dir = Path("d:/Comfy UI/rheihman hypothesis/research/interactive_lab/monograph_additive_multiplicative/RiemannBlueprint")
out_dir = repo_dir / "blueprint"
(out_dir / "src").mkdir(parents=True, exist_ok=True)

for tpl_name in env.list_templates():
    if tpl_name.endswith("blueprint.yml"):
        continue
    tpl = env.get_template(tpl_name)
    path = out_dir / "src" / tpl_name
    path.parent.mkdir(parents=True, exist_ok=True)
    tpl.stream(config).dump(str(path))
    print(f"Generated {path}")

print("Blueprint files successfully initialized.")
