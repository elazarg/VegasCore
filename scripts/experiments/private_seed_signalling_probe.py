"""Exact finite timing calculation; not a native SE counterexample certificate.

The corresponding builder, raw-action reduction and reset argument are in
docs/se-private-seed-signalling.md. This checks the observation distinction
and all reduced pure late-policy pairs, including B observing A's outcome.
"""

from fractions import Fraction
from itertools import product


W = Fraction(3)
EPSILON = Fraction(1)
DEPOSIT = Fraction(5)
NEVER = None
CHOICES = (0, 1, NEVER)


def callback_view(seed: int, helper: bool) -> tuple[bool, bool]:
    """Pending-helper and accepted-helper flags at the fixed-block callback."""
    pending = helper
    accepted = False
    observed = None
    if seed == 0:
        observed = pending, accepted
    if pending:  # Fixed middle slot, independent of the seed.
        pending, accepted = False, True
    if seed == 1:
        observed = pending, accepted
    assert observed is not None
    return observed


def delivered(choice: int | None, seed: int) -> int:
    return int(choice is not None and choice == seed)


def payoff(own: int, other: int) -> Fraction:
    if not own:
        return -EPSILON
    return W if not other else Fraction(0)


def late_law(a: int | None, b: tuple[int | None, int | None]):
    """B's choice is indexed by A's observed delivery bit."""
    result = {(da, db): Fraction(0) for da, db in product((0, 1), repeat=2)}
    for xa, xb in product((0, 1), repeat=2):
        da = delivered(a, xa)
        db = delivered(b[da], xb)
        result[da, db] += Fraction(1, 4)
    return result


def value(law, player: int) -> Fraction:
    return sum(
        (mass * payoff(bits[player], bits[1 - player]) for bits, mass in law.items()),
        Fraction(0),
    )


def main() -> None:
    assert W > 2 * EPSILON > 0
    assert DEPOSIT > W + EPSILON
    assert W - DEPOSIT < -EPSILON
    assert callback_view(0, False) == callback_view(1, False)
    assert callback_view(0, True) != callback_view(1, True)

    b_policies = tuple(product(CHOICES, repeat=2))
    laws = {(a, b): late_law(a, b) for a, b in product(CHOICES, b_policies)}
    expected = W / 4 - EPSILON / 2
    uniform = {bits: Fraction(1, 4) for bits in product((0, 1), repeat=2)}

    # Enumerate every pure late pair, including intentional nontransmission.
    equilibria = []
    for (a, b), law in laws.items():
        a_best = max(value(laws[other_a, b], 0) for other_a in CHOICES)
        b_best = max(value(laws[a, other_b], 1) for other_b in b_policies)
        if value(law, 0) == a_best and value(law, 1) == b_best:
            equilibria.append((a, b))
            assert law == uniform
            assert value(law, 0) == value(law, 1) == expected
    assert len(equilibria) == 8

    # B can strictly improve on an EARLY value of zero after A WAIT,
    # even if A's continuation is not optimal (including A never sending).
    for a in CHOICES:
        best_b = max(value(laws[a, b], 1) for b in b_policies)
        assert best_b >= expected > 0

    # The contradiction needs fixed whole-policy deviations, not a complete
    # classification of late equilibria. Their lower bounds hold against
    # every opposing late policy, including deliberate nontransmission.
    fixed_b = (0, 0)
    assert min(value(laws[a, fixed_b], 1) for a in CHOICES) == expected
    assert min(value(laws[0, b], 0) for b in b_policies) == expected

    # Each continuation-optimal B policy sends at an eligible late slot
    # for every positive-probability A history. A's maximum is then expected.
    for b in product((0, 1), repeat=2):
        assert max(value(laws[a, b], 0) for a in CHOICES) == expected

    # A helper permits seed-specific timing; it yields certain delivery.
    for seed in (0, 1):
        pending, accepted = callback_view(seed, True)
        selected_slot = 0 if pending else 1
        assert pending != accepted
        assert delivered(selected_slot, seed) == 1

    print(f"Checked {len(laws)} pure late-policy pairs with exact fractions.")
    print(f"All {len(equilibria)} late equilibrium pairs have the uniform delivery law.")
    print(f"Strict initial WAIT value: {expected}; honest value: 0.")
    print(f"Both fixed WAIT deviations have worst-case value {expected}.")
    print("Original co-delivery: 1/4; exclusion probability: 3/4.")
    print("Scope: reduced timing game only; native embedding remains unverified.")


if __name__ == "__main__":
    main()
