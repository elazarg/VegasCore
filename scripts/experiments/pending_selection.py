#!/usr/bin/env python3
"""Exact local incentive comparisons for pending commitment selection.

Every selector reads only envelope identifiers and multiplicities. Meanings
are fixed when an envelope is created and used only to evaluate outcomes.
No scheduler history, self-delivery, or private observation record is present.
These one-response games are NOT witnesses of proper native subgames or a
compiler SPE theorem. Their purpose is to test proposed inclusion contracts.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import json
from typing import Callable


@dataclass(frozen=True)
class Envelope:
    serial: int
    meaning: int


Law = dict[int, Fraction]
Pool = tuple[Envelope, ...]
Selector = Callable[[Pool], Law]


def lottery(pool: Pool, *, distinct: bool, weighted: bool) -> Law:
    if distinct:
        by_id = {envelope.serial: envelope for envelope in pool}
        assert all(by_id[envelope.serial] == envelope for envelope in pool)
        pool = tuple(by_id.values())
    # A fixed age preference: the two retained identifiers have weight five;
    # the fresh identifier has weight one, irrespective of its hidden meaning.
    weights = tuple(5 if weighted and envelope.serial < 2 else 1 for envelope in pool)
    total = sum(weights)
    result: Law = defaultdict(Fraction)
    for envelope, weight in zip(pool, weights):
        result[envelope.meaning] += Fraction(weight, total)
    assert sum(result.values()) == 1
    return dict(result)


def selectors() -> dict[str, Selector]:
    return {
        "first_identifier": lambda pool: {min(pool, key=lambda e: e.serial).meaning: Fraction(1)},
        "latest_identifier": lambda pool: {max(pool, key=lambda e: e.serial).meaning: Fraction(1)},
        "uniform_identifiers": lambda pool: lottery(pool, distinct=True, weighted=False),
        "uniform_copies": lambda pool: lottery(pool, distinct=False, weighted=False),
        "weighted_identifiers": lambda pool: lottery(pool, distinct=True, weighted=True),
        "weighted_copies": lambda pool: lottery(pool, distinct=False, weighted=True),
    }


def responses(pool: Pool) -> dict[str, Pool]:
    return {
        **{f"submit_{value}": pool + (Envelope(2, value),) for value in range(3)},
        "silent": pool,
        **{f"replay_{envelope.serial}": pool + (envelope,) for envelope in pool},
    }


def expected(law: Law, utility: tuple[int, ...]) -> Fraction:
    return sum((mass * utility[result] for result, mass in law.items()), Fraction())


def report() -> dict[str, object]:
    pool = (Envelope(0, 1), Envelope(1, 2))
    opposing = ((3, 2, 1), (3, 1, 2))
    result = {}
    for name, select in selectors().items():
        laws = {response: select(pending) for response, pending in responses(pool).items()}
        payoffs = {response: tuple(expected(law, u) for u in opposing)
                   for response, law in laws.items()}
        best = tuple(max(values[i] for values in payoffs.values()) for i in range(2))
        common = [response for response, values in payoffs.items() if values == best]
        tested = failures = 0
        for retained in product(range(3), repeat=2):
            old = tuple(Envelope(serial, value) for serial, value in enumerate(retained))
            outcomes = {response: select(pending) for response, pending in responses(old).items()}
            for utility in product(range(-2, 4), repeat=3):
                tested += 1
                values = {response: expected(law, utility) for response, law in outcomes.items()}
                maximum = max(values.values())
                failures += any(values[f"submit_{action}"] < maximum
                                for action in range(3) if utility[action] == max(utility))
        result[name] = {
            "payoffs_for_opposing_utilities": {r: [str(v) for v in values]
                                               for r, values in payoffs.items()},
            "common_optimal_responses": common,
            "menus_and_utilities_checked": tested,
            "source_optimal_submission_failures": failures,
        }
        if name == "weighted_copies":
            assert not common and failures > 0
            assert payoffs["submit_0"] == (Fraction(18, 11), Fraction(18, 11))
            assert best == (Fraction(5, 3), Fraction(5, 3))
        else:
            assert "submit_0" in common and failures == 0
    return result


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
