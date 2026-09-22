#!/usr/bin/env python3
"""Finite design experiment for failure elision and preservation contracts.

Exhaustive over pure strategies of a deterministic, one-player, perfect-
information four-decision game. Every history starts a proper subgame. This
is an executable design probe, not a verified Vegas adapter or a general SPE
checker. The canonical Lean counterexample is IrreversibleFailure.lean.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from itertools import product
import json
from typing import Callable


History = tuple[int, ...]
Plan = dict[History, int]
Outcome = tuple[bool, int | None]
Utility = Callable[[Outcome], int]


class Admission(Enum):
    VALUES = "values"
    FORFEITURE = "values-or-forfeiture"


@dataclass(frozen=True)
class CommitmentInterface:
    """The two actual sites in this program, independent of analysis requests."""

    a: Admission
    b: Admission


VALUE_INTERFACE = CommitmentInterface(Admission.VALUES, Admission.VALUES)
EXPANDED_INTERFACE = CommitmentInterface(Admission.FORFEITURE, Admission.VALUES)


@dataclass(frozen=True)
class Arena:
    """Admission changes legal histories; encoding changes representation."""

    interface: CommitmentInterface
    invert_b: bool = False

    def actions(self, history: History) -> tuple[int, ...]:
        if len(history) == 4:
            return ()
        if not history:
            return (0, 1) if self.interface.a is Admission.FORFEITURE else (1,)
        if len(history) == 1 and self.interface.b is Admission.FORFEITURE:
            return (-1, 0, 1)
        return (0, 1)

    def histories(self) -> tuple[History, ...]:
        def visit(history: History):
            yield history
            for action in self.actions(history):
                yield from visit(history + (action,))

        return tuple(visit(()))

    def outcome(self, history: History) -> Outcome:
        valid, encoded_b, open_a, open_b = history
        value = encoded_b ^ int(self.invert_b)
        return bool(valid and open_a), value if open_b and encoded_b != -1 else None

    def public_view(self, history: History) -> tuple[object, ...]:
        """Fixed commit events reveal no value/forfeiture bit before opening."""
        view: list[object] = []
        if history:
            view.append("A committed")
        if len(history) >= 2:
            view.append("B committed")
        if len(history) >= 3:
            view.append(bool(history[0] and history[2]))
        if len(history) == 4:
            view.append(self.outcome(history)[1])
        return tuple(view)


def plans(arena: Arena):
    decisions = tuple(h for h in arena.histories() if arena.actions(h))
    for choices in product(*(arena.actions(h) for h in decisions)):
        yield dict(zip(decisions, choices))


def key(plan: Plan) -> tuple[int, ...]:
    return tuple(plan[h] for h in sorted(plan))


def prefer(bit: int) -> Utility:
    def utility(outcome: Outcome) -> int:
        success, value = outcome
        if value is None:
            return 0
        return 3 if success else 2 if value == bit else 1

    return utility


def optimal_values(arena: Arena, utility: Utility) -> dict[History, int]:
    values: dict[History, int] = {}
    for history in reversed(arena.histories()):
        actions = arena.actions(history)
        values[history] = (
            max(values[history + (a,)] for a in actions)
            if actions else utility(arena.outcome(history))
        )
    return values


def outcomes(arena: Arena, plan: Plan) -> dict[History, Outcome]:
    result: dict[History, Outcome] = {}
    for history in reversed(arena.histories()):
        result[history] = (
            result[history + (plan[history],)]
            if arena.actions(history) else arena.outcome(history)
        )
    return result


def spe(plan_outcomes, optimal, utility: Utility) -> bool:
    # Whole-continuation best replies are enumerated by backward induction;
    # this is exact for this finite one-player perfect-information arena.
    return all(utility(result) == optimal[h] for h, result in plan_outcomes.items())


def extend(plan: Plan, failure_choice: int | None = None) -> Plan:
    """Copy source continuations; optionally supply a utility-specific repair."""
    result = {}
    for history in Arena(EXPANDED_INTERFACE).histories():
        if len(history) == 4:
            continue
        source_history = (1,) + history[1:] if history else ()
        action = plan[source_history]
        if history and history[0] == 0 and failure_choice is not None:
            action = failure_choice if len(history) == 1 else 1
        result[history] = action
    return result


def rename_b(plan: Plan) -> Plan:
    """A second pass: invert B's representation, including its later recall."""
    result = {}
    for history in Arena(EXPANDED_INTERFACE, invert_b=True).histories():
        if len(history) == 4:
            continue
        original = history
        if len(history) >= 2:
            original = (history[0], history[1] ^ 1) + history[2:]
        result[history] = plan[original] ^ int(len(history) == 1)
    return result


def validate(source: Arena, target: Arena, compiler, utilities: tuple[Utility, ...],
             observe=lambda outcome: outcome) -> dict[str, object]:
    source_best = [optimal_values(source, u) for u in utilities]
    target_best = [optimal_values(target, u) for u in utilities]
    result: dict[str, object] = {"outcome": True, "nash": True, "spe": True,
                                "source_plans": 0, "spe_witness": None}
    for plan in plans(source):
        result["source_plans"] += 1
        source_results = outcomes(source, plan)
        target_results = outcomes(target, compiler(plan))
        result["outcome"] &= observe(source_results[()]) == observe(target_results[()])
        for index, utility in enumerate(utilities):
            if utility(source_results[()]) == source_best[index][()]:
                result["nash"] &= utility(target_results[()]) == target_best[index][()]
            if spe(source_results, source_best[index], utility):
                preserved = spe(target_results, target_best[index], utility)
                result["spe"] &= preserved
                if not preserved and result["spe_witness"] is None:
                    history = next(h for h, value in target_results.items()
                                   if utility(value) < target_best[index][h])
                    result["spe_witness"] = {
                        "utility_index": index, "target_prefix": history,
                        "compiled_payoff": utility(target_results[history]),
                        "attainable_payoff": target_best[index][history],
                    }
    return result


def main() -> None:
    source, target = Arena(VALUE_INTERFACE), Arena(EXPANDED_INTERFACE)
    utilities = (prefer(0), prefer(1))
    source_spe = [set(), set()]
    target_spe = [set(), set()]
    counts = []
    for arena, collection in ((source, source_spe), (target, target_spe)):
        best = [optimal_values(arena, utility) for utility in utilities]
        count = 0
        for plan in plans(arena):
            count += 1
            realized = outcomes(arena, plan)
            for index, utility in enumerate(utilities):
                if spe(realized, best[index], utility):
                    collection[index].add(key(plan))
        counts.append(count)
    assert source_spe[0] & source_spe[1]
    assert not target_spe[0] & target_spe[1]

    ordinary = validate(source, target, extend, utilities)
    scoped = [validate(source, target, lambda p, b=b: extend(p, b), (utilities[b],))
              for b in (0, 1)]
    wrong_scope = validate(source, target, lambda p: extend(p, 0), (utilities[1],))
    assert ordinary["outcome"] and ordinary["nash"] and not ordinary["spe"]
    assert all(result["spe"] for result in scoped)
    assert not wrong_scope["spe"]

    # If analysis observes only A, every real utility on its two outcomes has
    # one of these three weak orders. For deterministic play this exhausts
    # utility comparisons, not just three arbitrarily selected examples.
    only_a = (lambda o: int(o[0]), lambda o: -int(o[0]), lambda _o: 0)
    safe = validate(source, target, extend, only_a, observe=lambda o: o[0])
    composed = validate(source, Arena(EXPANDED_INTERFACE, invert_b=True),
                        lambda p: rename_b(extend(p)), only_a, observe=lambda o: o[0])
    renaming = validate(target, Arena(EXPANDED_INTERFACE, invert_b=True), rename_b, utilities)
    assert all(safe[p] and composed[p] and renaming[p] for p in ("outcome", "nash", "spe"))

    # Restricting the compiled strategy does not remove off-path target roots.
    source_decisions = sum(bool(source.actions(h)) for h in source.histories())
    target_decisions = sum(bool(target.actions(h)) for h in target.histories())
    assert (0,) not in source.histories() and (0,) in target.histories()

    # Exercise all semantic interfaces of the same two-site instruction tree.
    # No equilibrium request is an input to the arena or its observations.
    admission_cases = []
    for a, b in product(Admission, repeat=2):
        arena = Arena(CommitmentInterface(a, b))
        histories = arena.histories()
        assert ((0,) in histories) == (a is Admission.FORFEITURE)
        assert ((1, -1) in histories) == (b is Admission.FORFEITURE)
        for history in histories:
            if history and a is Admission.VALUES:
                assert history[0] == 1
            if len(history) >= 2 and b is Admission.VALUES:
                assert history[1] != -1
            if len(history) == 2:
                assert arena.public_view(history) == ("A committed", "B committed")
            if len(history) == 4 and history[1] == -1:
                assert arena.outcome(history)[1] is None
        admission_cases.append({
            "A": a.value, "B": b.value,
            "decision_histories": sum(bool(arena.actions(h)) for h in histories),
            "early_failure_hidden": True,
        })

    report = {
        "scope": "pure deterministic one-player perfect-information experiment",
        "strategy_counts": {"source": counts[0], "target": counts[1]},
        "decision_history_counts": {"source": source_decisions, "target": target_decisions},
        "source_spe_counts": list(map(len, source_spe)),
        "target_spe_counts": list(map(len, target_spe)),
        "common_source_spe": len(source_spe[0] & source_spe[1]),
        "common_target_spe": len(target_spe[0] & target_spe[1]),
        "copy_completion": ordinary,
        "utility_specific_completions": scoped,
        "reuse_outside_utility_scope": wrong_scope,
        "only_a_observed": safe,
        "second_pass_b_encoding": renaming,
        "only_a_then_encoding": composed,
        "mixed_site_interfaces": admission_cases,
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
