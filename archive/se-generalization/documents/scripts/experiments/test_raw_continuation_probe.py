"""Regression checks for finite RAW continuation and one-time escrow saturation."""

from fractions import Fraction
import unittest

from adaptive_schedules import HALF, Chance, End, Move, consistent_beliefs, law, pure
from deferral_miss_probe import violations
from raw_continuation_probe import (
    BITS, ONE, OwnerOpportunity, ReportBackend, assert_perfect_recall, collection_mass,
    due_profile, due_unexpired_target,
    first_late_content_profile, first_late_content_target,
    late_canonical_target, late_profile, protected_profile, protected_retry,
    rationality, risk_seen, source, source_profile, target, target_profile, trembles,
)


class RawContinuationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.backend = ReportBackend(HALF, HALF)
        self.deposit = Fraction(2)
        self.root = target(self.deposit, self.backend)
        self.raw = target_profile(self.root, True)

    def test_raw_completion_preserves_the_protected_source_law(self) -> None:
        assert_perfect_recall(self.root)
        self.assertEqual(rationality(self.root, self.raw), {})
        self.assertEqual(law(self.root, self.raw), law(source(), source_profile()))
        self.assertTrue(all(not outcome[-1] for outcome in law(self.root, self.raw)))

    def test_canonical_post_miss_and_attempt_play_is_not_rational(self) -> None:
        failures = rationality(self.root, target_profile(self.root, False))
        expected = {f"miss:{v}" for v in BITS} | {
            f"attempt:{v}:{attempted}" for v in BITS for attempted in BITS}
        self.assertEqual(set(failures), expected)
        self.assertTrue(all(failure["gain"] == HALF for failure in failures.values()))

    def test_coverage_holds_without_any_incremental_retry_charge(self) -> None:
        for v in BITS:
            first = self.root.branches[v][1]
            miss = dict(first.children)["miss"]
            self.assertEqual(collection_mass(miss, self.raw), ONE)
            for attempted in BITS:
                continuation = dict(first.children)[f"attempt{attempted}"]
                for _, response in continuation.children:
                    self.assertEqual(collection_mass(response, self.raw), Fraction(1, 4))

    def test_private_attempted_choice_is_preserved_in_consistent_beliefs(self) -> None:
        beliefs = consistent_beliefs(self.root, self.raw, trembles(self.root))
        for v in BITS:
            for attempted in BITS:
                members = beliefs[f"attempt:{v}:{attempted}"]
                self.assertEqual(sum(mu for _, mu in members), ONE)
                self.assertTrue(all(node.infoset == f"attempt:{v}:{attempted}"
                                    for node, mu in members if mu))
                self.assertEqual(self.raw[f"attempt:{v}:{attempted}"]
                                 [f"retry{attempted}:certificate"], ONE)

        def first_end(node):
            if isinstance(node, End):
                return node
            if isinstance(node, Chance):
                return first_end(node.branches[0][1])
            self.assertIsInstance(node, Move)
            return first_end(node.children[0][1])

        # The certificate proves the attempted a, not the accepted retry r.
        # Bob's correct limit belief r=a follows from the completed strategy.
        for attempted in BITS:
            for node, mu in beliefs[f"retry:cert{attempted}"]:
                if mu:
                    self.assertEqual(first_end(node).outcome[1], attempted)

    def test_forgetting_the_attempted_choice_breaks_raw_rationality(self) -> None:
        forgot = dict(self.raw)
        for v in BITS:
            for attempted in BITS:
                name = f"attempt:{v}:{attempted}"
                forgot[name] = pure(f"retry{v}:certificate", *forgot[name])
        failures = rationality(self.root, forgot)
        self.assertEqual(set(failures), {"attempt:0:1", "attempt:1:0"})
        self.assertTrue(all(failure["gain"] == ONE for failure in failures.values()))

    def test_second_fresh_retry_is_deterred_only_while_escrow_is_clear(self) -> None:
        clear = protected_retry(self.deposit, self.backend, False)
        sunk = protected_retry(self.deposit, self.backend, True)
        self.assertEqual(rationality(clear, protected_profile(clear, False)), {})
        failures = rationality(sunk, protected_profile(sunk, False))
        self.assertEqual(set(failures), {f"after_protected:{bit}" for bit in BITS})
        self.assertTrue(all(failure["gain"] == HALF for failure in failures.values()))
        self.assertEqual(rationality(sunk, protected_profile(sunk, True)), {})

    def test_whole_policy_checker_agrees_with_exhaustive_global_enumeration(self) -> None:
        for previous in (False, True):
            root = protected_retry(self.deposit, self.backend, previous)
            for raw in (False, True):
                profile = protected_profile(root, raw)
                self.assertEqual(set(rationality(root, profile)),
                                 set(violations(root, profile, trembles(root))))

    def test_uncertain_collection_has_two_realized_settlement_outcomes(self) -> None:
        first = self.root.branches[0][1]
        attempt = dict(first.children)["attempt0"]
        outcomes = law(attempt, self.raw)
        self.assertEqual(outcomes, {
            (0, 0, 0, True): Fraction(1, 4),
            (0, 0, 0, False): Fraction(3, 4),
        })

    def test_insufficient_expected_escrow_breaks_initial_rationality(self) -> None:
        root = target(ONE, self.backend)
        failures = rationality(root, target_profile(root, True))
        self.assertEqual(set(failures), {f"first:{v}" for v in BITS})
        self.assertTrue(all(failure["gain"] == Fraction(1, 4)
                            for failure in failures.values()))

    def test_pending_canonical_packet_needs_rational_raw_continuation(self) -> None:
        inclusion = Fraction(1, 4)
        root = late_canonical_target(self.deposit, self.backend, inclusion)
        assert_perfect_recall(root)
        fixed = late_profile(root, self.deposit, self.backend, inclusion, False)
        raw = late_profile(root, self.deposit, self.backend, inclusion, True)
        failures = rationality(root, fixed)
        self.assertEqual(set(failures), {
            f"late_attempt:{v}:{attempted}" for v in BITS for attempted in BITS})
        self.assertTrue(all(failure["gain"] == Fraction(3, 8)
                            for failure in failures.values()))
        self.assertEqual(rationality(root, raw), {})
        self.assertEqual(law(root, raw), law(source(), source_profile()))

        # The first packet's outcome is sampled after the owner's choice.
        # A later raw packet raises collection only if the original is accepted.
        pending = dict(root.branches[0][1].children)["late0"]
        original = collection_mass(dict(pending.children)["quiet"], raw)
        retry = collection_mass(dict(pending.children)["attempt"], raw)
        self.assertEqual(original, Fraction(3, 4))
        self.assertEqual(retry, Fraction(13, 16))
        self.assertEqual((retry - original) * self.deposit, Fraction(1, 8))

    def test_first_late_content_favors_raw_before_any_attempt(self) -> None:
        for deposit in (Fraction(2), Fraction(4)):
            root = first_late_content_target(deposit, self.backend)
            assert_perfect_recall(root)
            fixed = first_late_content_profile(root, False)
            raw = first_late_content_profile(root, True)
            failures = rationality(root, fixed)
            self.assertEqual(set(failures), {f"content_late:{v}" for v in BITS})
            self.assertTrue(all(failure["gain"] == Fraction(3, 4) * deposit
                                for failure in failures.values()))
            self.assertEqual(rationality(root, raw), {})
            self.assertEqual(law(root, raw), law(source(), source_profile()))

    def test_certain_traffic_collection_removes_first_late_content_gap(self) -> None:
        backend = ReportBackend(ONE, ONE)
        root = first_late_content_target(HALF, backend)
        for anticipatory in (False, True):
            profile = first_late_content_profile(root, anticipatory)
            self.assertEqual(rationality(root, profile), {})
            self.assertEqual(law(root, profile), law(source(), source_profile()))

    def test_first_late_content_still_needs_sufficient_initial_escrow(self) -> None:
        root = first_late_content_target(ONE, self.backend)
        failures = rationality(root, first_late_content_profile(root, True))
        self.assertEqual(set(failures), {f"content_first:{v}" for v in BITS})
        self.assertTrue(all(failure["gain"] == Fraction(1, 4)
                            for failure in failures.values()))

    def test_risk_is_observed_before_action_and_retained_in_private_recall(self) -> None:
        late = OwnerOpportunity(True, True, True, False, False)
        next_protected = OwnerOpportunity(True, True, True, True, False)
        self.assertTrue(risk_seen((), late))
        for response in ("wait", "foreign", "bare0", "cert0"):
            self.assertTrue(risk_seen(((late, response),), next_protected))
        # A protected packet already recorded in own recall remains protected;
        # a subsequent activation alone does not introduce a first-attempt risk.
        recorded_pending = OwnerOpportunity(True, True, True, False, True)
        self.assertFalse(risk_seen((), recorded_pending))
        foreign_turn = OwnerOpportunity(False, True, True, False, False)
        self.assertFalse(risk_seen((), foreign_turn))
        lawful_withholding = OwnerOpportunity(True, False, True, False, False)
        self.assertFalse(risk_seen((), lawful_withholding))
        self.assertFalse(risk_seen(((lawful_withholding, "wait"),), lawful_withholding))

    def test_due_unexpired_first_binding_has_zero_incremental_fine(self) -> None:
        for deposit in (Fraction(2), Fraction(4)):
            root = due_unexpired_target(deposit, self.backend)
            assert_perfect_recall(root)
            fixed = due_profile(root, False)
            raw = due_profile(root, True)
            failures = rationality(root, fixed)
            self.assertEqual(set(failures), {f"due_late:{v}" for v in BITS})
            self.assertTrue(all(failure["gain"] == HALF for failure in failures.values()))
            self.assertEqual(rationality(root, raw), {})
            self.assertEqual(law(root, raw), law(source(), source_profile()))
            for _, first in root.branches:
                due = dict(first.children)["defer"]
                for _, response in due.children:
                    self.assertEqual(collection_mass(response, raw), ONE)

    def test_due_raw_completion_still_needs_sufficient_initial_escrow(self) -> None:
        root = due_unexpired_target(Fraction(1, 4), self.backend)
        failures = rationality(root, due_profile(root, True))
        self.assertEqual(set(failures), {f"due_first:{v}" for v in BITS})
        self.assertTrue(all(failure["gain"] == Fraction(1, 4)
                            for failure in failures.values()))

    def test_due_risk_remembers_readiness_without_requiring_timeliness(self) -> None:
        due = OwnerOpportunity(True, True, False, False, False)
        protected = OwnerOpportunity(True, True, True, True, False)
        self.assertTrue(risk_seen((), due))
        for response in ("wait", "foreign", "rejected_certificate"):
            self.assertTrue(risk_seen(((due, response),), protected))
        recorded = OwnerOpportunity(True, True, False, False, True)
        self.assertFalse(risk_seen((), recorded))
        resolution = OwnerOpportunity(True, False, False, False, False)
        self.assertFalse(risk_seen((), resolution))
        self.assertFalse(risk_seen(((resolution, "wait"),), resolution))


if __name__ == "__main__":
    unittest.main()
