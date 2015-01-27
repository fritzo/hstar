#!/usr/bin/env python

import os
import re
import glob


BADGE = '![Proof Status](https://img.shields.io/badge/{}.svg?style=flat)'


def count_holes():
    hole_counts = []
    for filename in glob.glob('src/*.v'):
        with open(filename) as f:
            hole_count = sum(
                1
                for line in f
                if re.search(r'\b(admit|Admitted)\.', line))
        if hole_count:
            stem = filename[4:-2]
            hole_counts.append({'count': hole_count, 'name': stem})
    hole_counts.sort(key=(lambda item: item['count']), reverse=True)
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
            lines.append('{count: >5d} | [{name}](src/{name}.v)'.format(**item))
        lines.append('')
    else:
        lines = [BADGE.format('proofs-complete-green')]
        lines.append('')
    return (line + '\n' for line in lines)


def update_readme(filename='README.md'):
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


if __name__ == '__main__':
    update_readme()
