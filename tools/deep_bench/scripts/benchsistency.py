#!/usr/bin/env python
from __future__ import print_function
import os
from tabulate import tabulate


STD_SMT2_BENCH_DIR = "bench_horn"
STD_ICE_BENCH_DIR = "bench_horn_ice"
STD_MCMC_BENCH_DIR = "bench_horn_mcmc"
STD_ALL = [STD_SMT2_BENCH_DIR, STD_ICE_BENCH_DIR, STD_MCMC_BENCH_DIR]


class MissingRootException(Exception):
    pass


def plausible_root(path):
    for dirname in STD_ALL:
        if os.path.isdir(os.path.join(path, dirname)):
            return True
    return False


def list_benchmarks(path):
    tail = os.path.split(path)[1].lower()
    for entry in os.listdir(path):
        if tail == STD_SMT2_BENCH_DIR:
            name, ext = os.path.splitext(entry)
            if ext == '.smt2':
                yield name
        elif tail == STD_ICE_BENCH_DIR:
            name, ext = os.path.splitext(entry)
            if ext == '.bpl':
                yield name
        elif tail == STD_MCMC_BENCH_DIR:
            if os.path.isdir(path):
                yield entry
        else:
            raise ValueError("%s is of unrecognized typed" % tail)


def main():
    root = os.getcwd()
    while not plausible_root(root):
        new_root = os.path.split(root)[0]
        if new_root == root:
            raise MissingRootException("didn't find benchmarks dirs above cwd")
        root = new_root

    found = dict((dirname, set(list_benchmarks(os.path.join(root, dirname))))
                 for dirname in STD_ALL)
    all_benchs = set.union(*found.values())
    
    sorted_keys = list(sorted(found.keys()))
    table = [[b] + [u'\u2713' if b in found[a] else '' for a in sorted_keys]
             for b in all_benchs]
    print(tabulate(table, headers=[]+sorted_keys))


if __name__ == '__main__':
    main()