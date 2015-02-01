#!/usr/bin/env python

import os
import re
import glob
import subprocess
import parsable


BADGE = '![Proof Status](https://img.shields.io/badge/{}.svg?style=flat)'

DEVNULL = open(os.devnull, 'w')


def re_count(patt, text, flags=0):
    return sum(1 for _ in re.finditer(patt, text, re.MULTILINE | re.DOTALL))


def count_holes():
    hole_counts = []
    for filename in glob.glob('src/*.v'):
        with open(filename) as f:
            text = f.read()
            hole_count = re_count(r'\bAdmitted\.', text)
            hole_count += re_count(r'\badmit\..*?(Qed|Defined)\.', text)
        if hole_count:
            stem = filename[4:-2]
            hole_counts.append({'count': hole_count, 'name': stem})
    hole_counts.sort(key=(lambda item: (-item['count'], item['name'])))
    return hole_counts


def get_metrics():
    hole_counts = count_holes()
    if hole_counts:
        total = sum(item['count'] for item in hole_counts)
        lines = [BADGE.format('proofs-{}_holes-red'.format(total))]
        lines.append('')
        lines.append('Holes | File')
        lines.append('-----:|:' + '-' * 60)
        for item in hole_counts:
            lines.append(
                '{count: >5d} | [{name}](src/{name}.v)'.format(**item))
        lines.append('')
    else:
        lines = [BADGE.format('proofs-complete-green')]
        lines.append('')
    return (line + '\n' for line in lines)


@parsable.command
def update_readme(filename='README.md'):
    '''
    Update readme by replacing the line matching 'img.shields.io/badge/proofs'.
    '''
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
                        for line in get_metrics():
                            outfile.write(line)

                elif state == 'REPLACE':
                    if re.search(r'^# \b', line):
                        state = 'POST'
                        outfile.write(line)

                elif state == 'POST':
                    outfile.write(line)

    os.rename(tempname, filename)


def read_theorem_names(thms, fin, fout):
    proc = subprocess.Popen(
        ['coqtop'],
        stdin=subprocess.PIPE,
        stdout=fout,
        stderr=DEVNULL)
    thm = None
    for line in fin:
        proc.stdin.write(line)
        if thm is None:
            match = re.search(
                r'\b(Lemma|Theorem|Corollary|Instance)\s+([A-Za-z0-9_\']+)\b',
                line)
            if match:
                thm = {
                    'type': match.group(1),
                    'name': match.group(2),
                    'holes': 0,
                    'body': '',
                }
        else:
            thm['holes'] += re_count(r'\badmit\.', line)
            match = re.search(r'\b(Qed|Defined|Admitted)\.', line)
            if match:
                if match.group(1) == 'Admitted':
                    thm['holes'] += 1
                proc.stdin.write('Print {name}.\n'.format(**thm))
                thms[thm['name']] = thm
                thm = None
    proc.stdin.write('Quit.\n')
    proc.wait()


def read_theorem_bodies(thms, fin):
    thm = None
    for line in fin:
        if thm is None:
            match = re.search(r'^([A-Za-z0-9_\']+) = ', line)
            if match:
                thm = {'name': match.group(1), 'body': line}
        else:
            if re.match(r'^\s+$', line):
                if thm['name'] in thms:
                    thms[thm['name']].update(thm)
                thm = None
            else:
                thm['body'] += line


def add_dependency_graph(thms):
    for name, thm in thms.iteritems():
        deps = set()
        for match in re.finditer('[A-Za-z_\']+', thm['body'], re.MULTILINE):
            word = match.group()
            if word in thms and word != name:
                deps.add(word)
        thm['deps'] = sorted(deps)


def collect_thms(*filenames):
    thms = {}
    for filename in filenames:
        defsname = '{}.defs'.format(filename)
        with open(filename) as fin:
            with open(defsname, 'w') as fout:
                read_theorem_names(thms, fin, fout)
        with open(defsname) as fin:
            read_theorem_bodies(thms, fin)
        os.remove(defsname)
    add_dependency_graph(thms)
    return thms


@parsable.command
def print_thms(*filenames):
    '''
    Print all theorems from coq files.
    '''
    thms = collect_thms(*filenames)
    for thm in thms.itervalues():
        print '{type} {name} {holes} depends on:\n  {deps}'.format(**thm)


if __name__ == '__main__':
    parsable.dispatch()
