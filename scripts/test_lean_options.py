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

    def test_guarded_audit_pin_passes(self):
        text = ("theorem witness : True := True.intro\n"
                "#guard_msgs (whitespace := lax) in\n"
                "#print axioms Vegas.Paper.witness\n")
        self.assertEqual(CHECKER.check_audit_pins(text), [])

    def test_audit_theorem_requires_guarded_pin(self):
        for pin in ("", "#print axioms Vegas.Paper.witness\n",
                    "/- #guard_msgs in\n#print axioms Vegas.Paper.witness -/\n"):
            with self.subTest(pin=pin):
                failures = CHECKER.check_audit_pins("theorem witness : True := True.intro\n" + pin)
                self.assertTrue(any("missing guarded axiom pin" in error for error in failures))

    def test_stale_audit_pin_fails(self):
        failures = CHECKER.check_audit_pins("#guard_msgs in\n#print axioms Vegas.Paper.absent\n")
        self.assertTrue(any("names no audit theorem" in error for error in failures))

    def test_duplicate_audit_pin_fails(self):
        failures = CHECKER.check_audit_pins(
            "theorem witness : True := True.intro\n" +
            "#guard_msgs in\n#print axioms Vegas.Paper.witness\n" * 2)
        self.assertTrue(any("duplicate axiom pin" in error for error in failures))

    def test_adjacent_pins_allow_documentation_and_indented_proof_bodies(self):
        text = (
            "namespace Vegas.Paper\n"
            "theorem first : True :=\n  True.intro\n"
            "/-- Expected dependencies. -/\n"
            "#guard_msgs in\n#print axioms Vegas.Paper.first\n"
            "/-- Another delegated theorem. -/\n"
            "theorem second : True := first\n"
            "#guard_msgs in\n#print axioms Vegas.Paper.second\n"
            "end Vegas.Paper\n"
        )
        self.assertEqual(CHECKER.check_audit_pins(text), [])

    def test_footer_pins_are_not_adjacent(self):
        text = (
            "theorem first : True := True.intro\n"
            "theorem second : True := True.intro\n"
            "#guard_msgs in\n#print axioms Vegas.Paper.first\n"
            "#guard_msgs in\n#print axioms Vegas.Paper.second\n"
        )
        failures = CHECKER.check_audit_pins(text)
        self.assertEqual(sum("must immediately follow" in error for error in failures), 2)

    def test_pin_cannot_precede_theorem_or_follow_another_command(self):
        theorem = "theorem witness : True := True.intro\n"
        pin = "#guard_msgs in\n#print axioms Vegas.Paper.witness\n"
        for text in (pin + theorem, theorem + "def unrelated := 0\n" + pin):
            with self.subTest(text=text):
                self.assertTrue(any("must immediately follow" in error
                                    for error in CHECKER.check_audit_pins(text)))

    def test_axiom_prints_are_allowed_only_in_root_audit(self):
        commands = ("#print axioms witness\n",
                    "#guard_msgs in #print axioms witness\n",
                    "#guard_msgs in\n#print\n  axioms\n  witness\n")
        for text in commands:
            with self.subTest(text=text):
                self.assertEqual(CHECKER.check_axiom_prints(Path("Paper.lean"), text), [])
                for path in ("Vegas/Proof.lean", "Interaction/Example.lean",
                             "VegasTests/Example.lean", "Paper/Source.lean"):
                    self.assertEqual(len(CHECKER.check_axiom_prints(Path(path), text)), 1)

    def test_documented_axiom_prints_are_not_commands(self):
        text = ('/- /- #print axioms hidden -/ -/\n'
                '-- #print axioms hidden\n'
                'def help := "#print axioms hidden"\n')
        self.assertEqual(CHECKER.check_axiom_prints(Path("Vegas/Help.lean"), text), [])

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
