"""Exact normalized-rule falsifier; NOT Lean execution or QualifiedBindingLaw verification.

Reimplements the first two-owner Bool BIND block of CommitTimingInformation,
compiled in .concurrent mode, plus its ordered PUB finish. Native and source
runners are independent. Small candidate capacities replace the contract's
200970 candidates. Focal raw alias weights/noncomputable canonical aliases are
EXCLUDED: information retains the entire NORMALIZED own recall/before-views.
No numerical success proves raw SE preservation. Stop on the first mismatch.
The optional two-input variant adds Alice private input100 beside Bob input0,
keeping commitment names1/2 and the four-event syntax. Its original joint prior
has diagonal3/8 and off-diagonal1/8; the negative control uses its product law.
The observation code is specialized, not a generic serializer: a retired block
before a later active site necessarily closes at clock7, with survivor admission
before the missing event's expiry. Its omitted raw clock/order/activation fields
are therefore determined by the recorded masks, handles and receipt chronology.

Crosswalk: ReservedEpochScheduler.command; EventApplication.handle/expire;
PhaseApplication.restore/settle; PhaseProposalReference.BasePolicy;
CommitRecoveryValueTremble; CommitRecoveryStep; ProposalRecoveryNoMissQuery.
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from dataclasses import dataclass, replace
from fractions import Fraction as F
from functools import lru_cache

SCALE, N_BAD, S_BAD = F(1, 4), F(1, 5), F(1, 6)
DEADLINE, PACKETS, WIDTH, HORIZON = 7, 630, 638, 200970
FAIL = -1
TWO_INPUTS = False


def owned_input(theta, owner):
    """Only immutable owned cells, never the opposite player's private bit."""
    if TWO_INPUTS:
        return (theta >> owner) & 1
    return theta if owner else None


def ordinary(owner, own_input, generation):
    """A declared full-support table on SEMANTIC query features, not raw I.

    This particular table ignores archive/own-prefix arguments. Generation and
    immutable own input survive the actual NoMiss/Erase normalization. The
    primary program has no further focal BIND in one block.
    """
    if owner == 0:
        p = F(2, 3) if TWO_INPUTS and own_input else F(1, 3)
    else:
        p = F(3, 4) if own_input else F(1, 4)
    if generation % 2:
        p = 1 - p
    return ((0, 1 - p), (1, p))


def total(law):
    return sum(law.values(), F(0))


def source_terminal(bit, values, excluded):
    # Independent source PUB interpreter, guards constantly true.
    pubs, mask = [], excluded
    for owner in (0, 1):
        value = FAIL if mask & (1 << owner) else values[owner]
        pubs.append(value)
        if value == FAIL:
            mask |= 1 << owner
    return (bit, tuple(values), tuple(pubs), mask)


@dataclass(frozen=True)
class Source:
    bit: int
    gen: int = 0
    excluded: int = 0
    entry: int = 0
    row: int = 0
    values: tuple = (None, None)
    moves: tuple = ()          # (automatic / omission / admitted, value)
    retired: tuple = ()        # complete original attempted words, including BAD
    bad: int = 0


def source_information(s, owner):
    # Full observation/own-action code specialized to this source syntax.
    past = []
    for gen, entry, moves in s.retired:
        mask = entry
        signals, own = [], None
        for actor, (kind, value) in enumerate(moves):
            if kind == "M":
                mask |= 1 << actor
            signals.append((kind != "A", mask))
            if actor == owner and kind != "A":
                own = (kind, value)
        past.append((gen, entry, tuple(signals), own))
    return (owner, owned_input(s.bit, owner), tuple(past), s.gen,
            s.entry, tuple((k != "A", s.entry | sum(
                1 << i for i, (kind, _) in enumerate(s.moves[:j + 1]) if kind == "M"))
                for j, (k, _) in enumerate(s.moves)))


def source_step(s, kind, value):
    actor = s.row
    values = list(s.values)
    values[actor] = value
    excluded = s.excluded | ((1 << actor) if kind == "M" else 0)
    bad = s.bad | ((1 << actor) if kind == "D" and value == FAIL else 0)
    nxt = replace(s, row=actor + 1, values=tuple(values), excluded=excluded,
                  moves=s.moves + ((kind, value),), bad=bad)
    if nxt.row < 2:
        return nxt
    if excluded != s.entry:
        archive = s.retired + ((s.gen, s.entry, nxt.moves),)
        if excluded != 3:
            return Source(s.bit, s.gen + 1, excluded, excluded,
                          retired=archive, bad=bad)
        return replace(nxt, values=(FAIL, FAIL), retired=archive)
    return nxt


@lru_cache(None)
def source_q0(s):
    if s.row == 2:
        return {source_terminal(s.bit, s.values, s.excluded): F(1)}
    if s.excluded & (1 << s.row):
        return source_q0(source_step(s, "A", FAIL))
    law = defaultdict(F)
    for value, weight in ordinary(s.row, owned_input(s.bit, s.row), s.gen):
        for terminal, probability in source_q0(source_step(s, "D", value)).items():
            law[terminal] += weight * probability
    return dict(law)


def enumerate_source(prior):
    """No native state, schedule, receipts, or native-derived posterior enters."""
    mass, forced = defaultdict(F), defaultdict(lambda: defaultdict(F))
    nodes, terminal_mass = 0, F(0)

    def visit(s, weight):
        nonlocal nodes, terminal_mass
        nodes += 1
        if s.row == 2:
            terminal_mass += weight
            return
        actor = s.row
        if s.excluded & (1 << actor):
            visit(source_step(s, "A", FAIL), weight)
            return
        site = source_information(s, actor)
        if not s.bad & (1 << (1 - actor)):
            mass[site] += weight
            for value in (0, 1):
                for terminal, probability in source_q0(source_step(s, "D", value)).items():
                    forced[site, value][terminal] += weight * probability
        visit(source_step(s, "M", FAIL), weight * SCALE)
        visit(source_step(s, "D", FAIL), weight * (1 - SCALE) * S_BAD)
        for value, probability in ordinary(actor, owned_input(s.bit, actor), s.gen):
            visit(source_step(s, "D", value), weight * (1 - SCALE) * (1 - S_BAD) * probability)

    for bit, weight in prior:
        visit(Source(bit), weight)
    assert terminal_mass == 1, ("source total", terminal_mass)
    return mass, forced, nodes


@dataclass(frozen=True)
class Native:
    bit: int
    tape: int
    phase: int = 0           # BIND [0,2), ordered PUB [2,4), terminal 4
    gen: int = 0
    excluded: int = 0
    entry: int = 0
    clock: int = 0
    cursor: int = 0
    values: tuple = (None, None, None, None)
    order: tuple = ()
    started: tuple = (0, 0, None, None)
    accepted: tuple = (None, None)
    catalogue: tuple = ((), ())
    pending: tuple = ()
    ledger: tuple = ()
    inputs: tuple = ()
    receipts: tuple = ()
    leaked: tuple = ((), ())
    next_id: tuple = (0, 0)
    sent: tuple = ()
    recall: tuple = ((), ())
    retired: tuple = ()
    closed: tuple = ()
    bad: int = 0


def ready(n, event):
    if n.values[event] is not None or event // 2 != n.phase // 2:
        return False
    if event < 2:
        return True
    return all(n.values[e] is not None for e in ((0, 1) if event == 2 else (0, 1, 2)))


def refresh(n):
    return replace(n, started=tuple(
        (n.started[e] if n.started[e] is not None else n.clock) if ready(n, e)
        else None for e in range(4)))


def complete(n, event, value, handle=None):
    values, accepted = list(n.values), list(n.accepted)
    values[event] = value
    if event < 2 and handle is not None:
        accepted[event] = handle
    return refresh(replace(n, values=tuple(values), accepted=tuple(accepted),
                           order=n.order + (event,)))


def settle(n):
    while n.phase < 4:
        changed = True
        while changed:
            changed = False
            for e in range(n.phase, n.phase + 2):
                if ready(n, e) and n.excluded & (1 << (e % 2)):
                    n = complete(n, e, FAIL)
                    changed = True
        if any(n.values[e] is None for e in range(n.phase, n.phase + 2)):
            return n
        if n.phase == 0:
            record = (n.gen, n.entry, n.values[:2], n.accepted, n.excluded)
            n = replace(n, closed=n.closed + (record,))
            if n.excluded != n.entry:
                # Copy saved config/accepted; retain physical catalogue/clock/E.
                n = replace(n, gen=n.gen + (n.excluded != 3), entry=n.excluded,
                            values=(None,) * 4, accepted=(None, None), order=(),
                            started=(n.clock, n.clock, None, None),
                            retired=n.retired + (record,))
                if n.excluded != 3:
                    continue
                for e in (0, 1):
                    n = complete(n, e, FAIL)
            n = refresh(replace(n, phase=2, entry=n.excluded))
        else:
            n = replace(n, phase=4, entry=n.excluded)
    return n


def catalogue(n, owner, serial):
    return dict(n.catalogue[owner]).get(serial)


def public(n):
    # Hidden BIND means absent; ordered completion and accepted handles present.
    return (n.phase, n.gen, n.excluded, n.clock, n.started, n.order,
            tuple(v is not None for v in n.values[:2]), n.values[2:], n.accepted,
            tuple((r[0], r[1], tuple(v is not None for v in r[2]), r[3], r[4])
                  for r in n.retired))


def observe(n, owner):
    return (owned_input(n.bit, owner), n.values[owner], n.values[2:], public(n),
            n.catalogue[owner], n.leaked[owner], n.ledger, n.receipts)


def information(n, owner):
    return (owner, n.recall[owner], observe(n, owner))


def native_source_site(n, owner):
    """Structural retrospective readout, never fitted using source weights.

    Current unissued static-earlier foreign values are NOT inserted here. At
    qualified beta all entry-active current rows are admitted; their private
    means are absent from the owner's full source information.
    """
    past = []
    for gen, entry, values, accepted, _ in n.retired:
        mask, signals = entry, []
        for actor in (0, 1):
            automatic = bool(entry & (1 << actor))
            if not automatic and accepted[actor] is None:
                mask |= 1 << actor
            signals.append((not automatic, mask))
        own = None if entry & (1 << owner) else (
            "M" if accepted[owner] is None else "D", values[owner])
        past.append((gen, entry, tuple(signals), own))
    prefix = tuple((not bool(n.entry & (1 << actor)), n.entry) for actor in range(owner))
    return (owner, owned_input(n.bit, owner), tuple(past), n.gen, n.entry, prefix)


def response(n, owner, action, record=True):
    before = observe(n, owner)
    emitted = None
    if action is not None:
        event, serial, value = action
        cats = list(n.catalogue)
        if event < 2:
            assert catalogue(n, owner, serial) is None, "fresh counted preparation"
            cats[owner] = tuple(sorted(cats[owner] + ((serial, value),)))
        # Wire commitment omits its private preparation. Opening exposes value.
        emitted = (owner, n.next_id[owner], n.phase, n.gen, event, serial,
                   value if event >= 2 else None)
        ids = list(n.next_id)
        ids[owner] += 1
        n = replace(n, catalogue=tuple(cats), next_id=tuple(ids),
                    pending=n.pending + (emitted,), inputs=n.inputs + (emitted,),
                    sent=n.sent + ((n.phase, n.gen, event),),
                    bad=n.bad | ((1 << owner) if event < 2 and value == FAIL else 0))
    if record:
        recalls = list(n.recall)
        recalls[owner] += ((before, action, emitted),)
        n = replace(n, recall=tuple(recalls))
    return n


def process(n):
    if not n.pending:
        return n
    packet = n.pending[0]
    owner, serial_id, phase, gen, event, serial, plaintext = packet
    accepted = False
    if (phase, gen) == (n.phase, n.gen) and not n.excluded & (1 << owner) and ready(n, event):
        entered = n.started[event]
        if entered is not None and n.clock - entered < DEADLINE:
            if event < 2 and event == owner:
                value = catalogue(n, owner, serial)
                assert value is not None
                n = complete(n, event, value, serial)
                accepted = True
            elif event >= 2 and event % 2 == owner and n.accepted[owner] == serial:
                if catalogue(n, owner, serial) == plaintext == n.values[owner] and plaintext != FAIL:
                    n = complete(n, event, plaintext)
                    accepted = True
    n = replace(n, pending=n.pending[1:], ledger=n.ledger + (packet,),
                receipts=n.receipts + (((owner, serial_id), accepted),))
    return settle(n)


def advance(n):
    """Return next actual activation. Deterministic empty processing is skipped.

    Exact command cursor remains; owned stochastic WAITs and before-views do not
    disappear. The original fixed tape is never resampled or inferred from I.
    """
    while n.phase < 4:
        assert n.cursor < HORIZON and n.clock < 45, ("finite runtime bound", n)
        cycle, slot = divmod(n.cursor, WIDTH)
        if slot < PACKETS:
            if not (n.tape and cycle % 3 == 1) and n.pending:
                n = process(n)
                n = replace(n, cursor=n.cursor + 1)
            else:
                n = replace(n, cursor=cycle * WIDTH + PACKETS)
            continue
        n = replace(n, cursor=n.cursor + 1)
        if slot < PACKETS + 2:
            owner = (slot - PACKETS) ^ n.tape
            leaks = list(n.leaked)
            known = {p[:2] for p in n.inputs if p[0] == owner}
            known |= {p[:2] for p in n.leaked[owner] + n.ledger}
            leaks[owner] += tuple(p for p in n.pending if p[0] != owner and p[:2] not in known)
            return owner, replace(n, leaked=tuple(leaks))
        if PACKETS + 3 <= slot < PACKETS + 7:
            event = slot - PACKETS - 3
            if ready(n, event) and n.started[event] is not None and n.clock - n.started[event] >= DEADLINE:
                n = complete(n, event, FAIL)
                n = settle(replace(n, excluded=n.excluded | (1 << (event % 2))))
        elif slot == WIDTH - 1:
            n = replace(n, clock=n.clock + 1)
    return None, n


def request(n, owner):
    for event in range(n.phase, min(4, n.phase + 2)):
        if event % 2 == owner and ready(n, event) and not n.excluded & (1 << owner):
            if (n.phase, n.gen, event) not in n.sent:
                return event
    return None


def action_law(n, owner, cap, noisy):
    event = request(n, owner)
    if event is None:
        return ((None, F(1)),)
    wait = SCALE if noisy else F(0)
    if event >= 2:
        value, serial = n.values[owner], n.accepted[owner]
        if value == FAIL or serial is None:
            return ((None, F(1)),)
        return ((None, wait), ((event, serial, value), 1 - wait))
    fresh = [i for i in range(cap) if catalogue(n, owner, i) is None]
    assert fresh, ("candidate capacity", n)
    slots = [(serial, ((SCALE / len(fresh)) if noisy else F(0)) +
              ((1 - SCALE) if noisy else F(1)) * (serial == fresh[0])) for serial in fresh]
    meanings = [(FAIL, N_BAD)] if noisy else []
    meanings += [(v, p * (1 - N_BAD if noisy else 1))
                 for v, p in ordinary(owner, owned_input(n.bit, owner), n.gen)]
    law = [(None, wait)]
    law += [((event, serial, value), (1 - wait) * sp * vp)
            for serial, sp in slots for value, vp in meanings]
    assert sum(p for _, p in law) == 1
    return tuple((a, p) for a, p in law if p)


def terminal(n):
    assert n.phase == 4
    return (n.bit, n.values[:2], n.values[2:], n.excluded)


@lru_cache(None)
def native_q0(n, cap, close_count, qualified=False):
    if not qualified and len(n.closed) > close_count:
        _, entry, _, accepted, final_e = n.closed[close_count]
        if final_e != entry or any(accepted[o] is None for o in (0, 1) if not entry & (1 << o)):
            return {None: F(1)}
        qualified = True
    if n.phase == 4:
        return {terminal(n) if qualified else None: F(1)}
    owner, n = advance(n)
    if owner is None:
        return native_q0(n, cap, close_count, qualified)
    law = defaultdict(F)
    for action, weight in action_law(n, owner, cap, False):
        child = response(n, owner, action, False)
        for result, probability in native_q0(child, cap, close_count, qualified).items():
            law[result] += weight * probability
    assert total(law) == 1
    return dict(law)


def enumerate_native(cap, prior, source_mass, source_forced, mutation):
    reach, outgoing, sites, witnesses = defaultdict(F), defaultdict(lambda: defaultdict(F)), {}, defaultdict(int)
    counts = defaultdict(int)
    final_mass = F(0)

    def visit(n, weight):
        nonlocal final_mass
        counts["prefixes"] += 1
        if n.phase != 0:
            final_mass += weight
            return
        owner, n = advance(n)
        if n.phase != 0:
            final_mass += weight
            return
        event = request(n, owner)
        if event is not None and n.excluded == n.entry:
            info = information(n, owner)
            j = native_source_site(n, owner)
            if info in sites:
                assert sites[info] == j, "one structural J for every hidden native state at I"
            sites[info] = j
            reach[info] += weight
            if n.gen and any(r[2][owner] == FAIL and r[3][owner] is not None for r in n.retired):
                witnesses["canceled_focal_BAD_clean_I"] += 1
            if n.gen and any(r[3][1 - owner] is None for r in n.retired):
                lost = any(p[4] == 1 - owner and p[3] < n.gen for p in n.inputs)
                witnesses["retry_after_lost_foreign_SEND" if lost else "retry_no_foreign_SEND"] += 1
            if owner == 1 and n.gen == 0 and not any(p[4] == 0 for p in n.inputs):
                witnesses["static_earlier_unissued_I"] += 1
            for serial in range(cap):
                if catalogue(n, owner, serial) is not None:
                    continue
                for value in (0, 1):
                    choice = (value, serial)
                    outgoing[info, choice]  # preserve zero-qualified choices
                    if n.bad & (1 << (1 - owner)):
                        continue
                    start = replace(n, recall=((), ()))
                    after = response(start, owner, (event, serial, value), False)
                    for result, probability in native_q0(after, cap, len(n.closed)).items():
                        if result is not None:
                            outgoing[info, choice][result] += weight * probability
        for action, probability in action_law(n, owner, cap, True):
            visit(response(n, owner, action), weight * probability)

    for bit, bp in prior:
        for tape in (0, 1):
            visit(Native(bit, tape), bp / 2)
    assert final_mass == 1, ("native first-block exit mass", final_mass)
    for scenario in ("static_earlier_unissued_I", "canceled_focal_BAD_clean_I",
                     "retry_after_lost_foreign_SEND", "retry_no_foreign_SEND"):
        assert witnesses[scenario] > 0, ("required scenario absent", scenario)
    counts.update({"information_sites": len(sites), "proper_choices": len(outgoing),
                   "q0_cache": native_q0.cache_info().currsize})
    common = {}
    zero = 0
    for (info, choice), law in outgoing.items():
        j, value = sites[info], choice[0]
        t = total(law)
        assert t <= reach[info], ("qualified mass exceeds native reach", t, reach[info])
        if info in common and common[info] != t:
            return {"mismatch": "qualification mass depends on proper encoding", "I": repr(info),
                    "choice": choice, "T": str(t), "previous_T": str(common[info])}
        common[info] = t
        if not t:
            zero += 1
            continue
        s = source_mass.get(j, F(0))
        v = source_forced.get((j, value), {})
        if not s:
            return {"mismatch": "positive native qualification has no structural source J",
                    "I": repr(info), "J": repr(j), "choice": choice, "T": str(t)}
        for forced_value in (0, 1):
            assert total(source_forced[j, forced_value]) == s, (
                "source forced continuation mass", j, forced_value, s)
        for atom in set(law) | set(v):
            lhs, rhs = s * law.get(atom, F(0)), t * v.get(atom, F(0))
            if lhs != rhs:
                return {"mismatch": "S*U != T*V", "mutation": mutation,
                        "I": repr(info), "J": repr(j), "choice": choice, "terminal": atom,
                        "S": str(s), "T": str(t), "U": str(law.get(atom, F(0))),
                        "V": str(v.get(atom, F(0))), "S_U": str(lhs), "T_V": str(rhs),
                        "counts": dict(counts)}
    assert 0 < zero < len(outgoing), "both positive and zero qualification must occur"
    return {"status": "all tested normalized sites passed", "counts": dict(counts),
            "zero_qualified_choices": zero, "native_exit_mass": str(final_mass),
            "witness_counts": dict(witnesses), "native_information_occupation": str(total(reach))}


def main():
    global TWO_INPUTS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capacity", type=int, default=2)
    parser.add_argument("--correlated-inputs", action="store_true")
    parser.add_argument("--negative-control", choices=("none", "wrong-source-prior"), default="none")
    args = parser.parse_args()
    TWO_INPUTS = args.correlated_inputs
    assert args.capacity >= 2, "two fresh registrations per owner must be available"
    native_prior = (((0, F(3, 8)), (1, F(1, 8)), (2, F(1, 8)), (3, F(3, 8)))
                    if TWO_INPUTS else ((0, F(1, 2)), (1, F(1, 2))))
    wrong_prior = (tuple((theta, F(1, 4)) for theta in range(4)) if TWO_INPUTS
                   else ((0, F(1, 3)), (1, F(2, 3))))
    source_prior = native_prior if args.negative_control == "none" else wrong_prior
    if TWO_INPUTS:
        # Same individual marginals: the mutation changes CORRELATION only.
        for owner in (0, 1):
            assert sum(p for theta, p in native_prior if owned_input(theta, owner)) == F(1, 2)
            assert sum(p for theta, p in wrong_prior if owned_input(theta, owner)) == F(1, 2)
    source_mass, source_forced, source_nodes = enumerate_source(source_prior)
    result = enumerate_native(args.capacity, native_prior, source_mass, source_forced,
                              args.negative_control)
    result.update({"scope": "normalized-rule Python reimplementation; NOT Lean/raw-alias verification",
                   "candidate_capacity": args.capacity, "source_prefixes": source_nodes,
                   "initial_inputs": "two correlated owned bits" if TWO_INPUTS else "Bob private bit",
                   "source_information_sites": len(source_mass), "negative_control": args.negative_control})
    print(json.dumps(result, indent=2, default=str))
    if "mismatch" in result:
        raise SystemExit(2)
    if args.negative_control != "none":
        raise SystemExit("negative control failed to detect a mismatch")


if __name__ == "__main__":
    main()
