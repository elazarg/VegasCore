"""Regression checks for Lean docstring references."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("check-doc-references.py").resolve()


class DocReferenceTests(unittest.TestCase):
    def run_checker(self, text):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Vegas").mkdir()
            (root / "Vegas/Test.lean").write_text(text, encoding="utf-8")
            return subprocess.run([sys.executable, str(SCRIPT)], cwd=root,
                                  capture_output=True, text=True)

    def test_mixed_case_namespace_does_not_hide_stale_reference(self):
        result = self.run_checker("/-! `SomeNamespace.missing` -/\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("SomeNamespace.missing", result.stdout)

    def test_declaration_docstrings_are_checked(self):
        result = self.run_checker(
            "/-- Uses `Vegas.missingDeclaration`. -/\n"
            "def actualResult := 1\n"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Vegas.missingDeclaration", result.stdout)

    def test_question_mark_and_bang_names_are_checked(self):
        result = self.run_checker(
            "namespace Vegas\n"
            "def lookup? := 1\n"
            "def lookup! := 1\n"
            "/-- `Vegas.lookup?` and `Vegas.lookup!` exist; `Vegas.missing?` does not. -/\n"
            "end Vegas\n"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Vegas.missing?", result.stdout)
        self.assertNotIn("unknown name `Vegas.lookup", result.stdout)

    def test_qualified_name_must_resolve_in_its_namespace(self):
        result = self.run_checker(
            "namespace Actual\n"
            "def existing_name := 1\n"
            "end Actual\n"
            "/-! `Wrong.existing_name` is stale. -/\n"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Wrong.existing_name", result.stdout)

    def test_relative_namespace_and_unqualified_camel_case_resolve(self):
        result = self.run_checker(
            "namespace Vegas.Example\n"
            "def usefulResult := 1\n"
            "/-! `Example.usefulResult` and `usefulResult` are current. -/\n"
            "end Vegas.Example\n"
        )
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_module_doc_uses_parent_namespace_without_arbitrary_suffixes(self):
        result = self.run_checker(
            "namespace Vegas\n"
            "def usefulResult := 1\n"
            "end Vegas\n"
            "/-! `usefulResult` is current, but `Wrong.usefulResult` is not. -/\n"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn("unknown name `usefulResult`", result.stdout)
        self.assertIn("unknown name `Wrong.usefulResult`", result.stdout)

    def test_receiver_notation_resolves_the_complete_member_suffix(self):
        result = self.run_checker(
            "namespace Vegas.Setup\n"
            "def eventSimulation := 1\n"
            "end Vegas.Setup\n"
            "/-! `graph.Setup.eventSimulation` is current; "
            "`graph.Wrong.eventSimulation` is not. -/\n"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn("unknown name `graph.Setup.eventSimulation`", result.stdout)
        self.assertIn("unknown name `graph.Wrong.eventSimulation`", result.stdout)

    def test_top_level_paper_file_is_indexed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Vegas").mkdir()
            (root / "Vegas/Test.lean").write_text(
                "/-! `Vegas.Paper.mainResult` is current. -/\n", encoding="utf-8"
            )
            (root / "Paper.lean").write_text(
                "namespace Vegas.Paper\n"
                "theorem mainResult : True := by trivial\n"
                "end Vegas.Paper\n", encoding="utf-8"
            )
            result = subprocess.run(
                [sys.executable, str(SCRIPT)], cwd=root,
                capture_output=True, text=True,
            )
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_constructor_and_source_filename_are_accepted(self):
        result = self.run_checker(
            "inductive Participant where\n  | scheduler\n"
            "/-! `Participant.scheduler` in `Paper.lean`. -/\n"
        )
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_field_declared_with_binders_is_indexed(self):
        result = self.run_checker(
            "class ResultTypes where\n"
            "  result : Nat\n"
            "  valueEquiv (n : Nat) :\n"
            "    Nat\n"
            "/-! `ResultTypes.valueEquiv` names a field. -/\n"
        )
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_field_assignment_is_not_indexed(self):
        result = self.run_checker(
            "structure Config where\n"
            "  size : Nat\n"
            "/-! `Config.build` is not a field. -/\n"
            "def sample : Config where\n"
            "  build (n : Nat) := n\n"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Config.build", result.stdout)

    def test_stale_lowercase_dotted_reference_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Vegas").mkdir()
            (root / "GameTheory/GameTheory").mkdir(parents=True)
            (root / "Vegas/Test.lean").write_text(
                "/-! A stale citation to `missing.name`. -/\n", encoding="utf-8"
            )
            result = subprocess.run(
                [sys.executable, str(SCRIPT)], cwd=root,
                capture_output=True, text=True,
            )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unknown name `missing.name`", result.stdout)

    def test_tracked_markdown_rejects_nonexistent_exact_project_path(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Vegas/Pending").mkdir(parents=True)
            (root / "Vegas/Pending/EventApplication.lean").write_text(
                "namespace Vegas.EventGraphRuntime\nend Vegas.EventGraphRuntime\n", encoding="utf-8"
            )
            (root / "README.md").write_text(
                "See `Vegas/Pending/EventGraphRuntime.lean`.", encoding="utf-8"
            )
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "add", "README.md"], check=True)
            result = subprocess.run([sys.executable, str(SCRIPT)], cwd=root,
                                    capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing local file `Vegas/Pending/EventGraphRuntime.lean`", result.stdout)

    def test_markdown_checks_lean_names_and_unqualified_camel_case(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Vegas").mkdir()
            (root / "Vegas/Sample.lean").write_text(
                "namespace Vegas.Sample\n"
                "def actualResult := 1\n"
                "end Vegas.Sample\n", encoding="utf-8"
            )
            (root / "README.md").write_text(
                "Valid: `Vegas.Sample.actualResult`, `actualResult`. "
                "Stale: `Vegas.Sample.missingResult`.\n", encoding="utf-8"
            )
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "add", "README.md"], check=True)
            result = subprocess.run([sys.executable, str(SCRIPT)], cwd=root,
                                    capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Markdown cites unknown Lean name `Vegas.Sample.missingResult`",
                      result.stdout)
        self.assertNotIn("unknown Lean name `actualResult`", result.stdout)

    def test_relative_markdown_links_resolve_from_source_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "docs").mkdir()
            (root / "docs/guide.md").write_text(
                "[root](../README.md) [missing](missing.md)", encoding="utf-8"
            )
            (root / "README.md").write_text("root", encoding="utf-8")
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "add", "README.md", "docs/guide.md"],
                           check=True)
            result = subprocess.run([sys.executable, str(SCRIPT)], cwd=root,
                                    capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing local file `missing.md`", result.stdout)
        self.assertNotIn("missing local file `../README.md`", result.stdout)

    def test_untracked_markdown_is_excluded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "README.md").write_text("No local paths.", encoding="utf-8")
            (root / "notes.md").write_text(
                "See `Vegas/Pending/DoesNotExist.lean`.", encoding="utf-8"
            )
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "add", "README.md"], check=True)
            result = subprocess.run([sys.executable, str(SCRIPT)], cwd=root,
                                    capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_non_git_run_announces_markdown_omission(self):
        result = self.run_checker("/-! No cited declarations. -/\n")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("Markdown path inventory was not checked", result.stdout)

    def test_tracked_documentation_has_no_directory_exemption(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            reference = root / "archive" / "notes.md"
            reference.parent.mkdir()
            reference.write_text("See [missing](absent.md).", encoding="utf-8")
            (root / "README.md").write_text(
                "[Reference material](archive/missing.md)", encoding="utf-8"
            )
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "add", "README.md", "archive/notes.md"],
                           check=True)
            result = subprocess.run([sys.executable, str(SCRIPT)], cwd=root,
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("archive/missing.md", result.stdout)
            self.assertIn("absent.md", result.stdout)

    def test_broken_git_inventory_is_a_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / ".git").mkdir()
            result = subprocess.run([sys.executable, str(SCRIPT)], cwd=root,
                                    capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Cannot enumerate tracked Markdown", result.stdout)


if __name__ == "__main__":
    unittest.main()
