import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "open_obligations", Path(__file__).with_name("report-open-obligations.py")
)
REPORTER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REPORTER)


class OpenObligationTests(unittest.TestCase):
    def test_marker_with_continuation(self):
        text = (
            "theorem a : True := trivial\n"
            "-- OPEN OBLIGATION: whole-run completion\n"
            "-- honest play publishes every value\n"
            "--\n"
            "-- needs an honest profile\n"
            "theorem b : True := trivial\n"
        )
        self.assertEqual(REPORTER.parse("A.lean", text), [
            REPORTER.Obligation("A.lean", 2, "whole-run completion",
                                ("honest play publishes every value", "", "needs an honest profile"))
        ])

    def test_indented_marker_and_adjacent_markers(self):
        text = "  -- OPEN OBLIGATION: first\n  -- OPEN OBLIGATION: second\n  -- detail\n"
        self.assertEqual(REPORTER.parse("B.lean", text), [
            REPORTER.Obligation("B.lean", 1, "first", ()),
            REPORTER.Obligation("B.lean", 2, "second", ("detail",)),
        ])

    def test_ordinary_comments_and_code_are_not_obligations(self):
        text = "-- open obligation: lowercase\ndef x := \"-- OPEN OBLIGATION: in string\"\n"
        self.assertEqual(REPORTER.parse("C.lean", text), [])

    def test_report_lists_every_obligation(self):
        rendered = REPORTER.report([
            REPORTER.Obligation("A.lean", 2, "first", ("detail",)),
            REPORTER.Obligation("B.lean", 7, "second", ()),
        ])
        self.assertIn("OPEN PROOF OBLIGATIONS: 2", rendered)
        self.assertIn("A.lean:2: first", rendered)
        self.assertIn("    detail", rendered)
        self.assertIn("B.lean:7: second", rendered)

    def test_empty_report(self):
        self.assertEqual(REPORTER.report([]), "No open proof obligations recorded.")

    def test_annotation_escapes_multiline_messages(self):
        rendered = REPORTER.annotation(
            REPORTER.Obligation("A.lean", 3, "100% done", ("next",))
        )
        self.assertEqual(
            rendered,
            "::warning file=A.lean,line=3,title=Open proof obligation::100%25 done%0Anext",
        )


if __name__ == "__main__":
    unittest.main()
