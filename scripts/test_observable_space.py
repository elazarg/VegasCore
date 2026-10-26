#!/usr/bin/env python3
"""Independent matrix identities and distinguishing traces for exact search."""

from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("observable_space", ROOT / "experiments/observable_space.py")
SEARCH = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SEARCH)


class ObservableSpaceTests(unittest.TestCase):
    def assert_certificate(self, data, result):
        columns = result["basis_columns"]

        def reconstruct(coefficient):
            return [sum((x * column[i] for x, column in zip(coefficient, columns)), F(0))
                    for i in range(result["ambient_dimension"])]

        for seed, coefficient in zip(data["seeds"], result["seed_columns"]):
            self.assertEqual(reconstruct(coefficient), list(map(F, seed)))
        for label, matrix in data["operators"].items():
            matrix = [[F(x) for x in row] for row in matrix]
            for column, coefficient in zip(columns, result["closure_columns"][label]):
                direct = [sum((a * b for a, b in zip(row, column)), F(0)) for row in matrix]
                self.assertEqual(reconstruct(coefficient), direct)

    def test_observation_filtered_hidden_bit(self):
        data = json.loads((ROOT / "experiments/observable_space_example.json").read_text())
        result = SEARCH.construct(data)
        self.assertEqual(result["dimension"], 2)
        self.assertEqual(result["ambient_dimension"], 4)
        self.assertEqual(result["initial_moments"], [0, 0])
        self.assertNotIn("distinguishing_trace", result)
        self.assert_certificate(data, result)

    def test_terminal_moment_is_not_closed(self):
        data = {"operators": {"next": [[0, 0, 1], [0, 1, 0], [0, 1, 0]]},
                "seeds": [[0, 0, 1]], "comparison": [1, -1, 0]}
        result = SEARCH.construct(data)
        self.assertEqual(result["distinguishing_trace"],
                         {"word": ["next"], "seed": 0, "value": 1})
        self.assert_certificate(data, result)

    def test_rational_and_dependent_seeds(self):
        data = {"operators": {"mix": [["1/3", "2/3"], ["1/2", "1/2"]]},
                "seeds": [[1, 0], [2, 0], [0, 0]], "comparison": [0, 1]}
        result = SEARCH.construct(data)
        self.assertEqual(result["dimension"], 2)
        self.assert_certificate(data, result)
        witness = result["distinguishing_trace"]
        value = list(map(F, data["seeds"][witness["seed"]]))
        for label in reversed(witness["word"]):
            value = SEARCH.apply([[F(x) for x in row] for row in data["operators"][label]], value)
        self.assertEqual(sum(a * b for a, b in zip(data["comparison"], value)), witness["value"])

    def test_zero_space(self):
        data = {"operators": {"id": [[1, 0], [0, 1]]},
                "seeds": [[0, 0]], "comparison": [1, -1]}
        result = SEARCH.construct(data)
        self.assertEqual(result["dimension"], 0)
        self.assert_certificate(data, result)

    def test_nonsquare_rejected(self):
        with self.assertRaises(ValueError):
            SEARCH.construct({"operators": {"bad": [[1, 0]]}, "seeds": [[1]]})


if __name__ == "__main__":
    unittest.main()
