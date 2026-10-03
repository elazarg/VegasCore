"""Exact belief and incentive checks for the late decision signaling probe."""

from fractions import Fraction
import unittest

from adaptive_schedules import ALICE, End, Move, infosets, law
from late_decision_signaling_probe import (
    BAD, FALSE, GOOD, ONE, TRUE, WAIT, ZERO, action_values, bad_limit, bad_posterior,
    candidate, evaluate_family, limiting_beliefs, native, polynomial_family,
    rationality, report, residual_best_responses, source, type_weights,
)
from raw_continuation_probe import assert_perfect_recall


class LateDecisionSignalingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.root = native()

    def test_native_tree_has_all_actions_and_perfect_recall(self) -> None:
        assert_perfect_recall(self.root)
        for site, (who, actions) in infosets(self.root).items():
            self.assertEqual(set(actions), {TRUE, FALSE, WAIT} if who == ALICE else {"Good", "Bad"})
        self.assertEqual(sum(who == ALICE for who, _ in infosets(self.root).values()), 4)

    def test_fully_supported_families_are_probability_laws(self) -> None:
        for root in (source(), self.root):
            for dependent in (False, True):
                family = polynomial_family(root, dependent)
                for n in range(24):
                    profile = evaluate_family(family, Fraction(1, n + 4))
                    self.assertTrue(all(p > ZERO for choices in profile.values()
                                        for p in choices.values()))
                    self.assertEqual(sum(law(root, profile).values()), ONE)

    def test_actual_FALSE_weights_include_type_prior_wait_and_late_tremble(self) -> None:
        for dependent in (False, True):
            family = polynomial_family(self.root, dependent)
            self.assertEqual(type_weights(self.root, family, "early:FALSE"), {
                GOOD: (ZERO, Fraction(1, 2)), BAD: (ZERO, ZERO, Fraction(1, 2))})
            self.assertEqual(type_weights(self.root, family, "late:FALSE"), {
                GOOD: (ZERO, ZERO, Fraction(1, 6)),
                BAD: ((ZERO, ZERO, ZERO, Fraction(1, 2), Fraction(-1, 3)) if dependent else
                      (ZERO, Fraction(1, 2), Fraction(-1, 3)))})

    def test_public_miss_weights_include_censored_TRUE_and_wait(self) -> None:
        for dependent in (False, True):
            family = polynomial_family(self.root, dependent)
            self.assertEqual(type_weights(self.root, family, "public-miss"), {
                GOOD: (ZERO, ZERO, Fraction(1, 6)),
                BAD: ((ZERO, ZERO, ZERO, ZERO, Fraction(1, 3)) if dependent else
                      (ZERO, ZERO, Fraction(1, 3)))})
            epsilon = Fraction(1, 10)
            expected = 2 * epsilon ** 2 / (1 + 2 * epsilon ** 2) if dependent else Fraction(2, 3)
            self.assertEqual(bad_posterior(self.root, family, "public-miss", epsilon), expected)

    def test_censored_TRUE_and_silence_pay_the_actual_default_FALSE_utility(self) -> None:
        early_good, early_bad = (node for _, node in self.root.branches)
        for kind, early in ((GOOD, early_good), (BAD, early_bad)):
            late = dict(early.children)[WAIT]
            self.assertIsInstance(late, Move)
            missed_actions = (WAIT,) if kind == GOOD else (TRUE, WAIT)
            for action in missed_actions:
                receiver = dict(late.children)[action]
                for guess, ending in receiver.children:
                    self.assertIsInstance(ending, End)
                    self.assertEqual(ending.outcome[1:3], (False, True))
                    correct = guess == ("Good" if kind == GOOD else "Bad")
                    expected = (1 if kind == GOOD else 2) * correct - 10
                    self.assertEqual(ending.payoff[ALICE], expected)

    def test_both_families_have_exact_Bayes_limits_at_every_site(self) -> None:
        for dependent in (False, True):
            family = polynomial_family(self.root, dependent)
            beliefs = limiting_beliefs(self.root, family)
            self.assertEqual(set(beliefs), set(infosets(self.root)))
            self.assertEqual(bad_limit(beliefs, "early:FALSE"), ZERO)
            self.assertEqual(bad_limit(beliefs, "late:FALSE"), ZERO if dependent else ONE)
            self.assertEqual(bad_limit(beliefs, "public-miss"),
                             ZERO if dependent else Fraction(2, 3))
            for n in range(24):
                self.assertTrue(residual_best_responses(
                    self.root, family, candidate(self.root, dependent), Fraction(1, n + 4)))

    def test_whole_continuation_comparisons_distinguish_equal_and_dependent_waits(self) -> None:
        source_root = source()
        source_profile = candidate(source_root, True)
        source_beliefs = limiting_beliefs(source_root, polynomial_family(source_root, True))
        self.assertEqual(rationality(source_root, source_profile, source_beliefs), {})
        for dependent in (False, True):
            profile = candidate(self.root, dependent)
            beliefs = limiting_beliefs(self.root, polynomial_family(self.root, dependent))
            self.assertEqual(rationality(self.root, profile, beliefs),
                             {} if dependent else {"early:Bad": ONE})
            self.assertEqual(law(self.root, profile), law(source_root, source_profile))
            self.assertEqual(action_values(self.root, profile, "early:Bad"), {
                TRUE: ONE, FALSE: ZERO, WAIT: ZERO if dependent else Fraction(2)})

    def test_report_keeps_the_finite_probe_scope_explicit(self) -> None:
        result = report()
        self.assertIn("not a certified AsyncServiceSpec", result["scope"])
        self.assertEqual(result["families"]["type_dependent_wait"]
                         ["whole_policy_incentive_violations"], {})


if __name__ == "__main__":
    unittest.main()
