import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "lean_options", Path(__file__).with_name("check-lean-options.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class LeanOptionTests(unittest.TestCase):
    def test_strict_central_options_pass(self):
        self.assertEqual(CHECKER.check_central_options({
            "autoImplicit": False,
            "relaxedAutoImplicit": False,
            "warningAsError": True,
        }), [])

    def test_missing_options_fail(self):
        self.assertEqual(len(CHECKER.check_central_options({})), 3)

    def test_relaxed_flag_alone_does_not_disable_implicit_binders(self):
        errors = CHECKER.check_central_options({
            "relaxedAutoImplicit": False,
            "warningAsError": True,
        })
        self.assertEqual(len(errors), 1)
        self.assertIn("autoImplicit", errors[0])

    def test_each_required_option_is_enforced(self):
        valid = {
            "autoImplicit": False,
            "relaxedAutoImplicit": False,
            "warningAsError": True,
        }
        for name, value in valid.items():
            with self.subTest(option=name):
                errors = CHECKER.check_central_options({**valid, name: not value})
                self.assertEqual(len(errors), 1)
                self.assertIn(name, errors[0])

    def test_admission_tokens_are_detected(self):
        text = "theorem a : True := by\n  sorry\ntheorem b : True := by admit\n#check sorryAx\n"
        self.assertEqual(CHECKER.admission_tokens(text), [
            (2, "sorry"), (3, "admit"), (4, "sorryAx")
        ])

    def test_comments_and_strings_do_not_supply_admissions(self):
        text = (
            "/- outer sorry /- nested admit -/ sorryAx -/\n"
            "-- sorry\n"
            "def explanation := \"sorry admit sorryAx\"\n"
            "theorem safe : True := True.intro\n"
        )
        self.assertEqual(CHECKER.admission_tokens(text), [])

    def test_escaped_string_does_not_end_early(self):
        text = 'def note := "quoted \\\" sorryAx"\ntheorem open : True := by sorry\n'
        self.assertEqual(CHECKER.admission_tokens(text), [(2, "sorry")])

    def test_only_root_paper_audit_may_admit(self):
        admitted = "theorem target : True := by sorry\n"
        self.assertEqual(CHECKER.check_admissions(Path("Paper.lean"), admitted), [])
        for path in (Path("Vegas/Proof.lean"), Path("Paper/Source.lean"),
                     Path("Other.lean")):
            with self.subTest(path=path):
                errors = CHECKER.check_admissions(path, admitted)
                self.assertEqual(len(errors), 1)
                self.assertIn("forbidden proof admission", errors[0])


if __name__ == "__main__":
    unittest.main()
