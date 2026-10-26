#!/usr/bin/env python3
"""Search for exact rational invariant-observable certificates.

Input JSON: square row-major ``operators`` (a label-to-matrix dictionary),
``seeds`` (a list of column vectors), and optional signed row ``comparison``.
All entries are integers or rational strings. Output gives basis columns,
closure coordinates, seed coordinates, and either zero initial moments or a
distinguishing label word. This search is untrusted: consumers must check the
matrix identities, as in GameTheoryExtensions.Math.InvariantObservables.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path


def coordinates(columns, vector):
    """Solve B x = vector for independent columns; return None off their span."""
    width = len(columns)
    rows = [[column[i] for column in columns] + [value]
            for i, value in enumerate(vector)]
    pivots = []
    for column in range(width):
        pivot = next((i for i in range(len(pivots), len(rows)) if rows[i][column]), None)
        if pivot is None:
            raise ValueError("dependent basis columns")
        row_index = len(pivots)
        rows[row_index], rows[pivot] = rows[pivot], rows[row_index]
        scale = rows[row_index][column]
        rows[row_index] = [entry / scale for entry in rows[row_index]]
        for i, row in enumerate(rows):
            if i != row_index:
                scale = row[column]
                rows[i] = [entry - scale * source
                           for entry, source in zip(row, rows[row_index])]
        pivots.append(row_index)
    if any(not any(row[:width]) and row[-1] for row in rows):
        return None
    return [rows[pivot][-1] for pivot in pivots]


def apply(matrix, vector):
    return [sum((a * b for a, b in zip(row, vector)), Fraction(0)) for row in matrix]


def construct(data):
    operators = {label: [[Fraction(x) for x in row] for row in matrix]
                 for label, matrix in data["operators"].items()}
    seeds = [[Fraction(x) for x in vector] for vector in data["seeds"]]
    comparison = [Fraction(x) for x in data.get("comparison", [])]
    sizes = [len(vector) for vector in seeds] + [len(matrix) for matrix in operators.values()]
    if comparison:
        sizes.append(len(comparison))
    if not sizes or len(set(sizes)) != 1:
        raise ValueError("a common ambient dimension is required")
    size = sizes[0]
    if any(len(row) != size for matrix in operators.values() for row in matrix):
        raise ValueError("operators must be square")
    basis = []
    provenance = []

    def include(vector, word, seed):
        if coordinates(basis, vector) is None:
            basis.append(vector)
            provenance.append((word, seed))

    for seed, vector in enumerate(seeds):
        include(vector, [], seed)
    current = 0
    while current < len(basis):
        word, seed = provenance[current]
        for label, matrix in operators.items():
            include(apply(matrix, basis[current]), [label] + word, seed)
        current += 1
    closure = {label: [coordinates(basis, apply(matrix, vector)) for vector in basis]
               for label, matrix in operators.items()}
    result = {
        "ambient_dimension": size,
        "dimension": len(basis),
        "basis_columns": basis,
        "closure_columns": closure,
        "seed_columns": [coordinates(basis, seed) for seed in seeds],
        "basis_words": [{"word": word, "seed": seed} for word, seed in provenance],
    }
    if comparison:
        moments = [sum((a * b for a, b in zip(comparison, vector)), Fraction(0))
                   for vector in basis]
        result["initial_moments"] = moments
        first = next((i for i, value in enumerate(moments) if value), None)
        if first is not None:
            word, seed = provenance[first]
            result["distinguishing_trace"] = {"word": word, "seed": seed, "value": moments[first]}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = construct(json.loads(args.input.read_text(encoding="utf-8")))
    encoded = json.dumps(result, default=str, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded, encoding="utf-8")
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
