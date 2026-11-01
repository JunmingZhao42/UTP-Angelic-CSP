#!/usr/bin/env python3
"""Run ./scripts/check-doc-links.py [FILE.md ...] to check Markdown links.

Reports relative links to missing files, and `#Lnnn` anchors into theory files
whose label names an Isabelle result that is not on that line. Without
arguments, checks every Markdown file outside deps/ and audits/. Exits 1 if
anything is reported.
"""
import os
import re
import sys

repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
skip_dirs = {'.git', '.codex', '.claude', '.isabelle', 'audits', 'deps', 'heaps',
             'browser_info', 'generated'}
link = re.compile(r'\[([^\]]*)\]\(([^)\s]+)\)')
label_name = re.compile(r'^`?([A-Za-z_][A-Za-z0-9_\'.]*)`?$')
declaration = (r'^\s*(?:lemma|theorem|corollary|proposition|definition|abbreviation|'
               r'lemmas|fun|primrec)\s+(?:\(in \S+\)\s+)?{}(?![A-Za-z0-9_\'])')


def markdown_files():
    for dirpath, dirs, files in os.walk(repo):
        dirs[:] = sorted(d for d in dirs if d not in skip_dirs)
        yield from (os.path.join(dirpath, f) for f in sorted(files) if f.endswith('.md'))


def result_name(label):
    """The Isabelle name a link label refers to, or None for prose labels."""
    m = label_name.match(label.strip())
    if not m:
        return None
    name = m.group(1).split('.')[-1]
    if label.strip().startswith('`') or re.search(r'[_0-9]|[A-Z].*[A-Z]', name):
        return name
    return None


def check(doc, theory_lines):
    with open(doc, encoding='utf-8') as fh:
        lines = fh.read().split('\n')
    in_code = False
    for lineno, line in enumerate(lines, 1):
        if line.lstrip().startswith(('```', '~~~')):
            in_code = not in_code
        if in_code:
            continue
        for label, target in link.findall(line):
            if re.match(r'(https?:|mailto:|#)', target):
                continue
            path, _, anchor = target.partition('#')
            full = os.path.normpath(os.path.join(os.path.dirname(doc), path))
            if not os.path.exists(full):
                yield f'{lineno}: missing file {target}'
                continue
            name = result_name(label)
            if name is None or not full.endswith('.thy') or not re.fullmatch(r'L\d+', anchor):
                continue
            theory = theory_lines(full)
            n = int(anchor[1:])
            if name in '\n'.join(theory[max(0, n - 1):n + 1]).replace('\\<^sub>', '_'):
                continue
            found = [i for i, l in enumerate(theory, 1)
                     if re.match(declaration.format(re.escape(name)), l)]
            where = 'declared at ' + ', '.join(f'L{i}' for i in found) if found else 'no declaration found'
            yield f'{lineno}: {label} is not at #{anchor} ({where})'


def main(args):
    docs = [os.path.abspath(a) for a in args] or list(markdown_files())
    cache = {}

    def theory_lines(path):
        if path not in cache:
            with open(path, encoding='utf-8', errors='replace') as fh:
                cache[path] = fh.read().split('\n')
        return cache[path]

    count = 0
    for doc in docs:
        for problem in check(doc, theory_lines):
            print(f'{os.path.relpath(doc, repo)}:{problem}')
            count += 1
    print(f'{count} problem(s) in {len(docs)} file(s)')
    return 1 if count else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
