from contextlib import redirect_stderr
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "manuscript_pins", Path(__file__).with_name("check-manuscript-pins.py"))
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class ManuscriptPinTests(unittest.TestCase):
    def test_active_inputs_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "main.tex").write_text(
                "\\input{body} % \\input{unused}\n% \\include{stale}\n", encoding="utf-8")
            (root / "body.tex").write_text(
                "% Lean: Vegas.Paper.isεNash\n\\include{appendix.tex}\n", encoding="utf-8")
            (root / "appendix.tex").write_text(
                "% Lean: Vegas.Paper.second\n% Lean: Vegas.Paper.isεNash\n", encoding="utf-8")
            self.assertEqual(CHECK.marked_results(root), {"Vegas.Paper.isεNash", "Vegas.Paper.second"})

    def test_malformed_result_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "main.tex").write_text("% Lean: Vegas.Paper.\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "Malformed"):
                CHECK.marked_results(root)

    def test_revision_comes_from_the_artifact_entry(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prefix = "https://github.com/elazarg/VegasCore/tree/"
            (root / "vegas-paper.bib").write_text(
                f"@misc{{other,\n note={{{prefix}{'1' * 40}}}}}\n"
                f"@misc{{VegasCoreRepo2026,\n note={{{prefix}{'2' * 40}}}}}\n", encoding="utf-8")
            self.assertEqual(CHECK.cited_revision(root), "2" * 40)

    def test_working_pin_drift_reports_both_directions(self):
        errors = io.StringIO()
        with redirect_stderr(errors):
            matches = CHECK.check_result_names(
                {"Vegas.Paper.old"}, "#print axioms Vegas.Paper.new", "working Paper.lean")
        self.assertFalse(matches)
        self.assertIn("missing from working Paper.lean: Vegas.Paper.old", errors.getvalue())
        self.assertIn("missing from active manuscript: Vegas.Paper.new", errors.getvalue())
