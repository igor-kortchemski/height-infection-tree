#!/usr/bin/env python3
"""Structural and source-identity checks for the publication copy; not full preflight."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = ["HeightPaper.mainTheorem", "HeightPaper.strongProfileTheorem",
            "HeightPaper.uniformStrongProfileTheorem"]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def code_only(text):
    """Remove Lean nested comments and strings while retaining line boundaries."""
    result = []
    pos = depth = 0
    string = False
    while pos < len(text):
        if depth:
            if text.startswith('/-', pos):
                depth += 1; pos += 2
            elif text.startswith('-/', pos):
                depth -= 1; pos += 2
            else:
                result.append('\n' if text[pos] == '\n' else ' '); pos += 1
        elif string:
            if text[pos] == '\\':
                pos += 2
            elif text[pos] == '"':
                string = False; result.append(' '); pos += 1
            else:
                result.append('\n' if text[pos] == '\n' else ' '); pos += 1
        elif text.startswith('/-', pos):
            depth = 1; result.append(' '); pos += 2
        elif text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end == -1 else end
        elif text[pos] == '"':
            string = True; result.append(' '); pos += 1
        else:
            result.append(text[pos]); pos += 1
    assert depth == 0 and not string, 'Unterminated Lean comment or string'
    return ''.join(result)


def main():
    config = json.loads((ROOT / 'comparator.json').read_text())
    assert config['challenge_module'] == 'Challenge'
    assert config['solution_module'] == 'Solution'
    assert config['theorem_names'] == EXPECTED
    assert config.get('definition_names', []) == []
    assert set(config['permitted_axioms']) == ALLOWED
    assert set(config) <= {'challenge_module', 'solution_module', 'theorem_names',
                           'definition_names', 'permitted_axioms', 'enable_nanoda'}
    challenge = (ROOT / 'Challenge.lean').read_text()
    assert len(challenge.encode()) <= 100 * 1024 and len(challenge.splitlines()) <= 1000
    cc = code_only(challenge)
    imports = re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)', cc, re.M)
    assert imports and all(m.startswith(('Mathlib.', 'Lean.')) for row in imports for m in row.split())
    assert re.findall(r'\b(?:sorry|admit|axiom)\b', cc) == ['sorry'] * 3
    assert re.findall(r'theorem\s+(mainTheorem|strongProfileTheorem|uniformStrongProfileTheorem)\s*:', cc) == [n.rsplit('.', 1)[1] for n in EXPECTED]
    filenames = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others',
                                         '--exclude-standard'], cwd=ROOT).split(b'\0')
    files = {Path(name.decode()) for name in filenames if name}
    lean_files = sorted(p for p in files if p.suffix == '.lean')
    for relative in lean_files:
        path = ROOT / relative
        assert not path.is_symlink(), f'Lean symlink: {relative}'
        text = path.read_text()
        assert len(text.splitlines()) <= 10000, f'Oversized Lean file: {relative}'
        code = code_only(text)
        assert re.match(r'\s*module\b', code), f'Missing module header: {relative}'
        if relative != Path('Challenge.lean'):
            forbidden = re.search(r'\b(?:sorry|admit|axiom|native_decide|bv_decide)\b', code)
            assert not forbidden, f'Forbidden code token in {relative}: {forbidden[0]}'
            assert not re.search(r'^\s*(?:public\s+)?import\s+Challenge\b', code, re.M), f'Challenge imported by {relative}'
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0'
    for package in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']:
        assert package['type'] == 'git'
        assert re.fullmatch(r'[0-9a-f]{40}', package['rev']), package['name']
        assert re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?', package['url']), package['name']
    metadata = json.loads((ROOT / 'formalization.yaml').read_text())
    assert metadata['version'] == 'v0.4'
    project = metadata['project']
    assert project['name'] and project['description']
    assert project['authors'] and project['responsible_maintainers']
    assert project['license'] == 'Apache-2.0'
    assert 'Apache License' in (ROOT / 'LICENSE').read_text()
    assert metadata['sources'] and metadata['automation']['methods']
    assert metadata['status']['sorry_count'] == metadata['status']['sorry_in_definitions'] == 0
    assert set(metadata['status']['axioms']) == ALLOWED
    assert [s['lean'] for s in metadata['alignment']['statements']] == EXPECTED
    assert metadata['classification']['arxiv'] == ['math.PR']
    assert all(re.fullmatch(r'\d{2}[A-Z]\d{2}', c) for c in metadata['classification']['msc2020'])
    provenance = json.loads((ROOT / 'publication/source-provenance.json').read_text())
    assert provenance['source_commit'] == '7f56d1daf0ba8d2d621b6da715f1fdb7c44e4961'
    assert provenance['reviewed_manuscript_sha256'] == 'c247d8b4479bf300e3529ed35701a07b00277584d2d66d4587f39a0e8d2c1626'
    manifest = (ROOT / 'publication/source-files.sha256').read_text().splitlines()
    protected = set()
    for line in manifest:
        digest, name = line.split('  ', 1)
        assert re.fullmatch(r'[0-9a-f]{64}', digest), name
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts, name
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, name
        assert name not in protected, name
        protected.add(name)
    assert protected == {p.as_posix() for p in lean_files} | {
        'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'comparator.json'}
    assert not any(p.suffix.lower() in {'.tex', '.pdf', '.bib'} for p in files)
    assert not any(p.parts[0] in {'.agents', 'output'} for p in files)
    assert not any('ROADMAP' in p.name or p.name == 'MANUSCRIPT_RECOMMENDATIONS.md' for p in files)
    print(f'PASS: {len(lean_files)} module sources; concrete Lean core and Mathlib Challenge '
          f'({len(challenge.splitlines())} lines, {len(challenge.encode())} bytes); '
          'three isolated theorem holes; implementation source scan; pins; metadata shape; '
          'complete source identity; manuscript and draft exclusions.')
    print('Local structural check only. Full Palomar policy, canonical dependency verification, '
          'and registry intake remain separate.')


if __name__ == '__main__':
    main()
