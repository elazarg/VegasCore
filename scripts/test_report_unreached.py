import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "report_unreached", Path(__file__).with_name("report-unreached.py")
)
REPORT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REPORT)


class MentionTests(unittest.TestCase):
    def test_example_uses_are_mentions(self):
        text = ("example : True :=\n"
                "  scheduled_terminalState_law program scheduler profile\n")
        self.assertIn("scheduled_terminalState_law", REPORT.mentions_in(text))

    def test_dotted_names_contribute_suffixes_and_components(self):
        names = REPORT.mentions_in("EventGraphRuntime.State.initial_privateInput_candidate _\n")
        for name in ("EventGraphRuntime.State.initial_privateInput_candidate",
                     "State.initial_privateInput_candidate", "initial_privateInput_candidate",
                     "EventGraphRuntime"):
            with self.subTest(name=name):
                self.assertIn(name, names)

    def test_comments_and_strings_are_not_mentions(self):
        text = ('/-- See `forceDisclose_expect_le`. -/\n'
                '-- scheduled_terminalState_law\n'
                'def note := "openingCompiled_eq_intended"\n')
        self.assertEqual(REPORT.mentions_in(text), set())

    def test_tactics_and_short_local_names_are_not_mentions(self):
        names = REPORT.mentions_in("theorem t : True := by\n  intro h\n  exact rfl\n")
        for word in ("intro", "exact", "rfl", "h", "by"):
            with self.subTest(word=word):
                self.assertNotIn(word, names)

    def test_qualified_names_after_a_dot_are_not_split_out(self):
        self.assertNotIn("alice", REPORT.mentions_in("(.alice) x.lookup\n"))


if __name__ == "__main__":
    unittest.main()
