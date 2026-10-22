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
            "warn": {"sorry": False},
        }), [])

    def test_missing_options_fail(self):
        self.assertEqual(len(CHECKER.check_central_options({})), 4)

    def test_relaxed_flag_alone_does_not_disable_implicit_binders(self):
        errors = CHECKER.check_central_options({
            "relaxedAutoImplicit": False,
            "warningAsError": True,
            "warn": {"sorry": False},
        })
        self.assertEqual(len(errors), 1)
        self.assertIn("autoImplicit", errors[0])

    def test_each_required_option_is_enforced(self):
        valid = {
            "autoImplicit": False,
            "relaxedAutoImplicit": False,
            "warningAsError": True,
            "warn": {"sorry": False},
        }
        for name, value in valid.items():
            with self.subTest(option=name):
                invalid = ({**valid, "warn": {"sorry": True}} if name == "warn"
                           else {**valid, name: not value})
                errors = CHECKER.check_central_options(invalid)
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

    def test_set_option_is_found_anywhere_outside_comments_and_strings(self):
        text = (
            'def note := "set_option maxRecDepth 1"\n'
            '-- set_option maxRecDepth 2\n'
            '/- set_option maxRecDepth 3 -/\n'
            'namespace Example\nsection; set_option maxRecDepth 4 in #check Nat\nend Example\n'
        )
        errors = CHECKER.check_forbidden_constructs(Path("Vegas/Test.lean"), text)
        self.assertEqual(len(errors), 1)
        self.assertIn("source-local `set_option`", errors[0])
        self.assertIn(":5:", errors[0])

    def test_trust_and_codegen_escape_hatches_are_rejected(self):
        text = (
            "axiom trusted : True\n"
            "axioms first : True\n"
            "namespace Scoped in axiom nested : True\n"
            "@[extern \"unchecked\"] axiom attributed : Nat\n"
            "unsafe def unchecked := 1\n"
            "example : True := by native_decide\n"
            "@[implemented_by unchecked] def checked := 1\n"
            '#print axioms checked\n'
        )
        errors = CHECKER.check_forbidden_constructs(Path("Vegas/Test.lean"), text)
        self.assertEqual(sum("axiom declaration" in error for error in errors), 4)
        self.assertEqual(sum("`unsafe`" in error for error in errors), 1)
        self.assertEqual(sum("`native_decide`" in error for error in errors), 1)
        self.assertEqual(sum("`implemented_by`" in error for error in errors), 1)

    def test_forbidden_constructs_in_comments_and_strings_are_ignored(self):
        text = (
            '/- axiom hidden : True; unsafe def hidden := 0 -/\n'
            '-- native_decide @[implemented_by hidden]\n'
            'def note := "set_option axiom unsafe native_decide implemented_by"\n'
        )
        self.assertEqual(
            CHECKER.check_forbidden_constructs(Path("Vegas/Test.lean"), text), []
        )

    def test_paper_axiom_pins_are_not_declarations(self):
        text = (
            "#guard_msgs in\n#print axioms Vegas.Paper.result\n"
            "#print\n  axioms\n  Vegas.Paper.result\n"
        )
        self.assertEqual(CHECKER.check_forbidden_constructs(Path("Paper.lean"), text), [])

    def test_guarded_audit_pin_passes(self):
        text = ("theorem witness : True := True.intro\n"
                "#guard_msgs (whitespace := lax) in\n"
                "#print axioms Vegas.Paper.witness\n")
        self.assertEqual(CHECKER.check_audit_pins(text), [])

    def test_explicit_open_capstone_with_adjacent_pin_passes(self):
        text = (
            "/-- error: declaration uses `sorry` -/\n"
            "#guard_msgs (whitespace := lax) in\n"
            "-- OPEN OBLIGATION: target - prospective capstone\n"
            "theorem target : True := by\n  sorry\n"
            "/-- info: 'Vegas.Paper.target' depends on axioms: [sorryAx] -/\n"
            "#guard_msgs (whitespace := lax) in\n"
            "#print axioms Vegas.Paper.target\n"
        )
        self.assertEqual(CHECKER.check_audit_pins(text), [])
        self.assertEqual(CHECKER.check_admissions(Path("Paper.lean"), text,
            {("Paper.lean", "target"): "review.md"}), [])
        self.assertEqual(CHECKER.admission_tokens(text), [(5, "sorry")])

    def test_paper_admission_requires_marker_even_with_guard(self):
        for prefix in ("", "#guard_msgs in\n"):
            errors = CHECKER.check_admissions(
                Path("Paper.lean"), prefix + "theorem target : True := by\n  sorry\n")
            self.assertEqual(len(errors), 1)
            self.assertIn("OPEN OBLIGATION", errors[0])

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

    def test_axiom_prints_are_allowed_only_in_dedicated_audits(self):
        commands = ("#print axioms witness\n",
                    "#guard_msgs in #print axioms witness\n",
                    "#guard_msgs in\n#print\n  axioms\n  witness\n")
        for text in commands:
            with self.subTest(text=text):
                self.assertEqual(CHECKER.check_axiom_prints(Path("Paper.lean"), text), [])
                for path in ("Vegas/Proof.lean", "Interaction/Example.lean",
                             "VegasTests/Example.lean", "Paper/Source.lean"):
                    self.assertEqual(len(CHECKER.check_axiom_prints(Path(path), text)), 1)

    def test_regression_axiom_prints_require_guards(self):
        path = Path("VegasTests/AxiomAudit/Source.lean")
        for text in ("#guard_msgs in #print axioms witness\n",
                     "#guard_msgs (whitespace := lax) in\n#print\n  axioms\n  witness\n"):
            with self.subTest(text=text):
                self.assertEqual(CHECKER.check_axiom_prints(path, text), [])
        self.assertEqual(len(CHECKER.check_axiom_prints(path, "#print axioms witness\n")), 1)
        self.assertTrue(CHECKER.check_admissions(path, "#guard_msgs in\ntheorem bad : True := by sorry\n"))

    def test_documented_axiom_prints_are_not_commands(self):
        text = ('/- /- #print axioms hidden -/ -/\n'
                '-- #print axioms hidden\n'
                'def help := "#print axioms hidden"\n')
        self.assertEqual(CHECKER.check_axiom_prints(Path("Vegas/Help.lean"), text), [])

    def test_named_obligations_are_allowed_in_each_source_layer(self):
        marked = ("-- OPEN OBLIGATION: target - reviewed finite argument\n"
                  "private theorem target : True := by\n  sorry\n")
        for path in ("Vegas/Proof.lean", "Paper/Source.lean", "Other.lean", "Paper.lean"):
            with self.subTest(path=path):
                self.assertEqual(CHECKER.check_admissions(Path(path), marked,
                    {(Path(path).as_posix(), "target"): "review.md"}), [])
                self.assertEqual(CHECKER.obligation_ranges(marked)[0][0][3], "target")

    def test_markers_do_not_authorize_admit_or_sorry_ax(self):
        for token in ("admit", "sorryAx"):
            marked = ("-- OPEN OBLIGATION: target - reviewed argument\n"
                      f"theorem target : True := by {token}\n")
            errors = CHECKER.check_admissions(Path("Paper.lean"), marked)
            self.assertTrue(any(f"`{token}`" in error for error in errors))

    def test_marker_must_name_the_following_theorem(self):
        for declaration in ("theorem other : True := by sorry",
                            "def target : True := by sorry",
                            "#check Nat\ntheorem target : True := by sorry"):
            marked = "-- OPEN OBLIGATION: target - reviewed argument\n" + declaration
            self.assertTrue(CHECKER.check_admissions(Path("Vegas/Test.lean"), marked))

    def test_marker_requires_explanation_and_adjacency(self):
        for prefix in ("-- OPEN OBLIGATION: target\n",
                       "-- OPEN OBLIGATION: target - \n",
                       "-- OPEN OBLIGATION: target - reviewed\n-- unrelated\n"):
            self.assertTrue(CHECKER.check_admissions(
                Path("Vegas/Test.lean"), prefix + "theorem target : True := by sorry\n"))

    def test_marker_cannot_be_spoofed_inside_string_or_nested_comment(self):
        for hidden in ('def note := "-- OPEN OBLIGATION: target - reviewed"\n',
                       '/-\n-- OPEN OBLIGATION: target - reviewed\n-/\n'):
            self.assertTrue(CHECKER.check_admissions(
                Path("Vegas/Test.lean"), hidden + "theorem target : True := by sorry\n"))

    def test_marker_does_not_cover_later_declarations(self):
        text = ("-- OPEN OBLIGATION: first - reviewed\n"
                "theorem first : True := by sorry\n"
                "theorem second : True := by sorry\n")
        errors = CHECKER.check_admissions(Path("Vegas/Test.lean"), text,
            {("Vegas/Test.lean", "first"): "review.md"})
        self.assertEqual(len(errors), 1)
        self.assertIn(":3:", errors[0])

    def test_marker_tracks_exactly_one_hole(self):
        for body in ("True.intro", "by\n  have h : True := by sorry\n  sorry"):
            text = "-- OPEN OBLIGATION: target - reviewed\ntheorem target : True := " + body
            self.assertTrue(any("exactly one sorry" in error for error in
                                CHECKER.check_admissions(Path("Vegas/Test.lean"), text)))

    def test_generic_obligation_note_is_informational_only(self):
        note = "-- OPEN OBLIGATION: compiler correctness remains open\n"
        self.assertEqual(CHECKER.check_admissions(Path("Vegas/Test.lean"), note), [])
        self.assertEqual(CHECKER.obligation_ranges(note)[0], [])
        self.assertTrue(CHECKER.check_admissions(
            Path("Vegas/Test.lean"), note + "theorem target : True := by sorry\n"))

    def test_named_marker_must_be_standalone_comment(self):
        text = ("def n := 0 -- OPEN OBLIGATION: target - reviewed\n"
                "theorem target : True := by sorry\n")
        self.assertTrue(CHECKER.check_admissions(Path("Vegas/Test.lean"), text))

    def test_actual_toml_configuration_uses_selective_sorry_option(self):
        root = Path(__file__).resolve().parent.parent
        with (root / "lakefile.toml").open("rb") as source:
            options = CHECKER.tomllib.load(source)["leanOptions"]
        self.assertEqual(CHECKER.check_central_options(options), [])
        self.assertIs(options["warningAsError"], True)
        self.assertIs(options["warn"]["sorry"], False)

    def test_marker_alone_does_not_register_a_new_obligation(self):
        text = "-- OPEN OBLIGATION: target - reviewed\ntheorem target : True := by sorry\n"
        self.assertTrue(any("unregistered" in error for error in
                            CHECKER.check_admissions(Path("Vegas/Test.lean"), text)))
        for registry in ({("Wrong.lean", "target"): "review.md"},
                         {("Vegas/Test.lean", "target"): ""}):
            self.assertTrue(any("unregistered" in error for error in
                CHECKER.check_admissions(Path("Vegas/Test.lean"), text, registry)))

    def test_repository_has_no_approved_open_obligations(self):
        self.assertEqual(CHECKER.APPROVED_OPEN_OBLIGATIONS, {})

    def test_orphan_marker_is_rejected(self):
        self.assertTrue(CHECKER.check_admissions(
            Path("Vegas/Test.lean"), "-- OPEN OBLIGATION: target - reviewed\n"))


if __name__ == "__main__":
    unittest.main()
