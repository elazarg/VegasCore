#!/usr/bin/env python3
"""Exhaustive pure-SPE experiments for action coalescing.

These finite games use information-set closure and whole-policy deviations.
They are design probes, not a Vegas compiler or a general equilibrium checker.
The interleaved game has turns Alice, Bob, Alice; Bob cannot see Alice's first
choice and Alice sees Bob's reply. No two consecutive player moves coalesce.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
import json
from typing import Callable


History = tuple[int, ...]
Info = tuple[int, ...]
Plan = tuple[int, ...]
Profile = tuple[Plan, ...]
ALICE, BOB = 0, 1


@dataclass(frozen=True)
class Game:
    players: int
    actions: Callable[[History], tuple[int, ...]]
    actor: Callable[[History], int]
    info: Callable[[int, History], Info]
    outcome: Callable[[History], tuple[int, int | None]]

    def histories(self) -> tuple[History, ...]:
        def visit(history: History):
            yield history
            for action in self.actions(history):
                yield from visit(history + (action,))
        return tuple(visit(()))


def value(prefer_one: bool, result: int | None) -> int:
    if result is None:
        return 0
    if result == 0:
        return 3
    return 2 if (result == 1) == prefer_one else 1


def selected(reply: int, response: int) -> int:
    return 1 if response == reply else 2


def interleaved(target: bool) -> Game:
    def actions(history):
        if len(history) == 3:
            return ()
        if len(history) == 1:
            return (0, 1)
        if not history and target:
            return (0, 1)  # zero, or the restricted family {1, 2}
        return (0, 1, 2)  # source value, or final response/withholding

    def outcome(history):
        first, reply, response = history
        if response == 2:
            return reply, None
        if not target or first == 0:
            return reply, first
        return reply, selected(reply, response)

    return Game(
        2, actions, lambda h: BOB if len(h) == 1 else ALICE,
        lambda who, h: (len(h),) if who == BOB else h, outcome,
    )


def simple(split: bool) -> Game:
    def actions(history):
        if not history:
            return (0, 1) if split else (0, 1, 2)
        if split and history == (1,):
            return (1, 2)
        return ()

    return Game(1, actions, lambda _: ALICE, lambda _, h: h, lambda h: (0, h[-1]))


def analyze(game: Game) -> dict[str, object]:
    histories = game.histories()
    decisions = tuple(h for h in histories if game.actions(h))
    menus: list[dict[Info, tuple[int, ...]]] = [{} for _ in range(game.players)]
    cells: dict[tuple[int, Info], set[History]] = {}
    for h in decisions:
        who = game.actor(h)
        info = game.info(who, h)
        assert menus[who].setdefault(info, game.actions(h)) == game.actions(h)
        cells.setdefault((who, info), set()).add(h)

    def below(root, h):
        return h[:len(root)] == root

    roots = tuple(root for root in histories if all(
        not any(below(root, h) for h in cell) or all(below(root, h) for h in cell)
        for cell in cells.values()
    ))
    plans = [tuple(product(*menu.values())) for menu in menus]
    profiles: tuple[Profile, ...] = tuple(product(*plans))
    indices = [{info: j for j, info in enumerate(menu)} for menu in menus]

    def play(profile, root):
        h = root
        while game.actions(h):
            who = game.actor(h)
            h += (profile[who][indices[who][game.info(who, h)]],)
        return game.outcome(h)

    def utility(prefer_one, who, result):
        # Bob has a genuine strict preference between the two public replies.
        return value(prefer_one, result[1]) if who == ALICE else int(result[0] == 0)

    # Maximize over every replacement policy at each proper root, holding all
    # opponents' complete policies fixed. No single-deviation assumption is used.
    results = {(p, root): play(p, root) for p in profiles for root in roots}
    best: dict[tuple, int] = {}
    for p in profiles:
        for root in roots:
            result = results[p, root]
            for prefer_one in (False, True):
                for who in range(game.players):
                    key = prefer_one, who, root, p[:who] + p[who + 1:]
                    best[key] = max(best.get(key, -1), utility(prefer_one, who, result))

    equilibria = []
    for prefer_one in (False, True):
        equilibria.append({p for p in profiles if all(
            utility(prefer_one, who, results[p, root]) ==
            best[prefer_one, who, root, p[:who] + p[who + 1:]]
            for root in roots for who in range(game.players)
        )})

    return {
        "profiles": len(profiles),
        "decision_information_sets": [len(menu) for menu in menus],
        "proper_nonterminal_roots": [list(h) for h in roots if game.actions(h)],
        "spe_counts_prefer_2_then_1": [len(eq) for eq in equilibria],
        "common_spe": len(equilibria[0] & equilibria[1]),
        "spe_public_outcomes": [sorted({results[p, ()] for p in eq}) for eq in equilibria],
        "adjacent_same_player_decisions": sum(
            game.actor(h) == game.actor(h + (a,))
            for h in decisions for a in game.actions(h) if game.actions(h + (a,))
        ),
    }


def report() -> dict[str, object]:
    cases = {
        "split_single_player": analyze(simple(True)),
        "coalesced_single_player": analyze(simple(False)),
        "interleaved_source": analyze(interleaved(False)),
        "interleaved_target": analyze(interleaved(True)),
    }
    assert cases["split_single_player"]["common_spe"] == 0
    assert cases["coalesced_single_player"]["common_spe"] == 1
    assert cases["interleaved_source"]["common_spe"] > 0
    assert cases["interleaved_target"]["common_spe"] == 0
    assert cases["interleaved_target"]["adjacent_same_player_decisions"] == 0
    assert [1] not in cases["interleaved_target"]["proper_nonterminal_roots"]
    assert [1, 0] in cases["interleaved_target"]["proper_nonterminal_roots"]
    assert cases["interleaved_source"]["spe_public_outcomes"] == [[(0, 0)], [(0, 0)]]
    assert cases["interleaved_target"]["spe_public_outcomes"] == [[(0, 0)], [(0, 0)]]
    # Moving Alice's last packet before Bob's reply loses adaptive responses.
    adaptive = [selected(bit, bit) for bit in (0, 1)]
    fixed = [[selected(bit, response) for bit in (0, 1)] for response in (0, 1)]
    assert adaptive == [1, 1] and adaptive not in fixed
    cases["response_to_new_information"] = {"adaptive": adaptive, "fixed_packets": fixed}
    return cases


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
