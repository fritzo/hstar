#!/usr/bin/env python

import os
import re
import subprocess
import multiprocessing
import parsable

BADGE = '![Proof Status](https://img.shields.io/badge/{}.svg?style=flat)'


def re_count(patt, text, flags=0):
    return sum(1 for _ in re.finditer(patt, text, re.MULTILINE | re.DOTALL))


def count_holes(coq_files):
    hole_counts = []
    for filename in coq_files:
        with open(filename) as f:
            text = f.read()
            hole_count = re_count(r'\bAdmitted\.', text)
            hole_count += re_count(r'\badmit\..*?(Qed|Defined)\.', text)
        if hole_count:
            hole_counts.append({'count': hole_count, 'name': filename})
    hole_counts.sort(key=(lambda item: (-item['count'], item['name'])))
    return hole_counts


def get_metrics(coq_files):
    hole_counts = count_holes(coq_files)
    if hole_counts:
        total = sum(item['count'] for item in hole_counts)
        lines = [BADGE.format('proofs-{}_holes-red'.format(total))]
        lines.append('')
        lines.append(' Holes | File')
        lines.append(' -----:|:' + '-' * 70)
        for item in hole_counts:
            item['stem'] = os.path.split(item['name'])[-1]
            lines.append(
                ' {count: >5d} | [{stem}]({name})'.format(**item))
        lines.append('')
    else:
        lines = [BADGE.format('proofs-complete-green')]
        lines.append('')
    return (line + '\n' for line in lines)


@parsable.command
def update_readme(*coq_files):
    '''
    Update README.md by replacing the line matching
    'img.shields.io/badge/proofs'.
    '''
    filename = 'README.md'
    tempname = '{}.tmp'.format(filename)
    with open(filename) as infile:
        with open(tempname, 'w') as outfile:
            state = 'PRE'
            for line in infile:

                if state == 'PRE':
                    if not re.search(r'img.shields.io/badge/proofs', line):
                        outfile.write(line)
                    else:
                        state = 'REPLACE'
                        for line in get_metrics(coq_files):
                            outfile.write(line)

                elif state == 'REPLACE':
                    if re.search(r'^\S', line):
                        state = 'POST'
                        outfile.write(line)

                elif state == 'POST':
                    outfile.write(line)

    os.rename(tempname, filename)


re_lemma = re.compile(
    r'\b(Lemma|Theorem|Corollary|Instance)\s+([A-Za-z0-9_\']+)\b')
re_qed = re.compile(r'\b(Qed|Defined|Admitted)\.')


def read_theorem_names(thms, fin, fout):
    proc = subprocess.Popen(
        ['coqtop'],
        stdin=subprocess.PIPE,
        stdout=fout,
        stderr=fout)
    thm = None
    for line in fin:
        if thm is None:
            match = re_lemma.search(line)
            if match:
                thm = {
                    'type': match.group(1),
                    'name': match.group(2),
                    'holes': 0,
                    'words': set(),
                }
        else:
            thm['holes'] += re_count(r'\badmit\.', line)
            match = re_qed.search(line)
            if match:
                if match.group(1) == 'Admitted':
                    thm['holes'] += 1
                proc.stdin.write('Show Proof.\n'.format(**thm))
                thms[thm['name']] = thm
                thm = None
        proc.stdin.write(line)
    proc.stdin.write('Quit.\n')
    proc.wait()


def get_words(text):
    matches = re.finditer('[A-Za-z_\']+', text, re.MULTILINE)
    return set(match.group() for match in matches)


def read_theorem_bodies(thms, fin):
    thm = None
    for line in fin:
        if thm is None:
            match = re.search(r'^([A-Za-z0-9_\']+) < ', line)
            if match:
                name = match.group(1)
                if name in thms:
                    thm = {'name': name, 'words': set()}
        elif not line.isspace():
            thms[name]['words'] |= get_words(line)
        else:
            thm = None


def add_dependency_graph(thms):
    for name, thm in thms.iteritems():
        deps = set()
        for word in thm['words']:
            if word in thms and word != name:
                deps.add(word)
        thm['deps'] = ' '.join(sorted(deps))


def collect_thms_file(filename):
    thms = {}
    defsname = '{}.defs'.format(filename)
    with open(filename) as fin:
        with open(defsname, 'w') as fout:
            read_theorem_names(thms, fin, fout)
    with open(defsname) as fin:
        read_theorem_bodies(thms, fin)
    os.remove(defsname)
    return thms


def collect_thms(coq_files):
    thms = {}
    for part in multiprocessing.Pool().map(collect_thms_file, coq_files):
        thms.update(part)
    add_dependency_graph(thms)
    return thms


@parsable.command
def print_thms(*coq_files):
    '''
    Print all theorems from coq files.
    '''
    thms = collect_thms(coq_files)
    for thm in thms.itervalues():
        print '{type} {name} {holes}: {deps}'.format(**thm)


if __name__ == '__main__':
    parsable.dispatch()
