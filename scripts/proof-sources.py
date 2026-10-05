#!/usr/bin/env python3
"""List the complete audited local source set in import order.

Challenge/Expected.lean is an intentionally untrusted comparator specification;
its placeholder proofs are never imported by the proof-backed solution.
"""
from __future__ import annotations
import argparse
import pathlib
import re
import runpy


def discover(root: pathlib.Path) -> list[tuple[str, pathlib.Path]]:
    code_only = runpy.run_path(str(root / 'scripts/scan-proof-sources.py'))['code_only']
    paths = [root / 'ExactHillShares.lean', root / 'Tests.lean',
             root / 'Challenge/Definitions.lean']
    for directory in ('ExactHillShares', 'Tests', 'Solution'):
        paths.extend(sorted((root / directory).rglob('*.lean')))
    if (root / 'Solution.lean').is_file():
        paths.append(root / 'Solution.lean')
    files = {}
    for path in paths:
        relative = path.relative_to(root)
        if not path.is_file() or path.is_symlink():
            raise ValueError(f'Missing or symlinked proof source: {relative}')
        name = relative.with_suffix('').as_posix().replace('/', '.')
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', name):
            raise ValueError(f'Unsupported local module name: {relative}')
        files[name] = path
    if not any(name.startswith('Solution.') for name in files):
        raise ValueError('No proof-backed Solution modules; refusing incomplete inventory')
    deps = {}
    for name, path in files.items():
        imports = []
        for line in code_only(path.read_text()).splitlines():
            line = line.strip()
            if line.startswith('import '):
                for imported in line[7:].split():
                    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', imported):
                        raise ValueError(f'Unsupported import syntax in {path.relative_to(root)}: {imported}')
                    local = root.joinpath(*imported.split('.')).with_suffix('.lean')
                    if local.is_file():
                        if imported not in files:
                            raise ValueError(f'Unaudited local import in {name}: {imported}')
                        imports.append(imported)
        deps[name] = imports
    ordered, active, done = [], set(), set()
    def visit(name: str) -> None:
        if name in done:
            return
        if name in active:
            raise ValueError(f'Cyclic local module imports at {name}')
        active.add(name)
        for dependency in deps[name]:
            visit(dependency)
        active.remove(name)
        done.add(name)
        ordered.append((name, files[name].relative_to(root)))
    for name in sorted(files):
        visit(name)
    return ordered


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=pathlib.Path, default=pathlib.Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    try:
        for name, path in discover(args.root.resolve()):
            print(f'{name}\t{path.as_posix()}')
    except (OSError, ValueError) as error:
        parser.exit(1, f'PROOF_INVENTORY_REJECT: {error}\n')


if __name__ == '__main__':
    main()
