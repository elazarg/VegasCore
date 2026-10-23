import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "lean_options", Path(__file__).with_name("check-lean-options.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)

STRICT = {"autoImplicit": False, "relaxedAutoImplicit": False, "warningAsError": True}


def pin(name, axioms="propext, Classical.choice, Quot.sound", guard="(whitespace := lax) "):
    return (f"/-- info: 'Vegas.Paper.{name}' depends on axioms:\n[{axioms}] -/\n"
            f"#guard_msgs {guard}in\n#print axioms Vegas.Paper.{name}\n")


class LeanOptionTests(unittest.TestCase):
    def test_strict_central_options_pass(self):
        self.assertEqual(CHECKER.check_central_options(STRICT), [])
        self.assertEqual(CHECKER.check_central_options({**STRICT, "warn": {"sorry": True}}), [])

    def test_missing_options_fail(self):
        self.assertEqual(len(CHECKER.check_central_options({})), 3)

    def test_relaxed_flag_alone_does_not_disable_implicit_binders(self):
        errors = CHECKER.check_central_options({"relaxedAutoImplicit": False,
                                                "warningAsError": True})
        self.assertEqual(len(errors), 1)
        self.assertIn("autoImplicit", errors[0])

    def test_each_required_option_is_enforced(self):
        for name, value in STRICT.items():
            with self.subTest(option=name):
                errors = CHECKER.check_central_options({**STRICT, name: not value})
                self.assertEqual(len(errors), 1)
                self.assertIn(name, errors[0])

    def test_sorry_warnings_cannot_be_disabled(self):
        errors = CHECKER.check_central_options({**STRICT, "warn": {"sorry": False}})
        self.assertEqual(len(errors), 1)
        self.assertIn("warn.sorry", errors[0])

    def test_options_outside_the_central_table_are_rejected(self):
        config = {
            "leanOptions": STRICT,
            "moreLeanArgs": ["-DwarningAsError=false"],
            "weakLeanArgs": ["-j4"],
            "lean_lib": [{"name": "Vegas", "leanOptions": {"warningAsError": False}},
                         {"name": "Paper", "weakLeanArgs": ["-DmaxHeartbeats=0"]}],
        }
        errors = CHECKER.check_lakefile(config)
        self.assertEqual(len(errors), 3)
        self.assertTrue(any("package sets option -DwarningAsError" in e for e in errors))
        self.assertTrue(any("lean_lib Vegas sets leanOptions" in e for e in errors))
        self.assertTrue(any("lean_lib Paper sets option -DmaxHeartbeats" in e for e in errors))

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

    def test_character_literal_quote_does_not_open_a_string(self):
        text = "def quote := '\"'\ntheorem open : True := by sorry\n"
        self.assertEqual(CHECKER.admission_tokens(text), [(2, "sorry")])

    def test_escaped_character_literals_are_blanked(self):
        text = "def marks := ['\\'', '\\\\', '\\x41', '\\u{2200}'] ++ [sorry]\n"
        self.assertEqual(CHECKER.admission_tokens(text), [(1, "sorry")])

    def test_prime_after_a_name_is_not_a_character_literal(self):
        text = "theorem a'b' : h' 'c' := x₁'\n"
        self.assertEqual(CHECKER.strip_lean_comments_and_strings(text),
                         "theorem a'b' : h'     := x₁'\n")

    def test_raw_strings_end_only_at_their_delimiter(self):
        text = ('def raw := r#"a " sorry -- /- "#\n'
                'def plain := r"admit"\n'
                "theorem open : True := by sorry\n")
        self.assertEqual(CHECKER.admission_tokens(text), [(3, "sorry")])

    def test_guillemet_names_cannot_open_comments_or_strings(self):
        text = 'def «a -- b» := 1\ndef «c " d» := 2\ntheorem open : True := by sorry\n'
        self.assertEqual(CHECKER.admission_tokens(text), [(3, "sorry")])

    def test_string_gaps_keep_line_numbers(self):
        text = 'def gap := "a\\\n  b"\ntheorem open : True := by sorry\n'
        self.assertEqual(CHECKER.admission_tokens(text), [(3, "sorry")])

    def test_every_admission_is_rejected_in_every_file(self):
        text = "#guard_msgs in\ntheorem target : True := by\n  sorry\n"
        for path in ("Paper.lean", "Vegas/Proof.lean", "VegasTests/Example.lean"):
            with self.subTest(path=path):
                errors = CHECKER.check_admissions(Path(path), text)
                self.assertEqual(len(errors), 1)
                self.assertIn(":3:", errors[0])

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
            "example : True := by decide +native\n"
            "@[implemented_by unchecked] def checked := 1\n"
            "theorem reduced : True := Lean.ofReduceBool _ _ rfl\n"
            "run_cmd Lean.addDecl declaration\n"
            "elab \"hole\" : tactic => Lean.Elab.admitGoal\n"
            "#eval Lean.Meta.mkSorry\n"
            "set_option debug.skipKernelTC true in theorem x : True := trivial\n"
            '#print axioms checked\n'
        )
        errors = CHECKER.check_forbidden_constructs(Path("Vegas/Test.lean"), text)
        self.assertEqual(sum("axiom declaration" in error for error in errors), 4)
        for description in ("`unsafe`", "`native_decide`", "`+native`", "`implemented_by`",
                            "compiler-trusting reduction", "skipped kernel check"):
            with self.subTest(description=description):
                self.assertEqual(sum(description in error for error in errors), 1)
        self.assertEqual(sum("declaration-adding metaprogram" in error for error in errors), 2)
        self.assertEqual(sum("elaboration-time program" in error for error in errors), 3)

    def test_forbidden_constructs_in_comments_and_strings_are_ignored(self):
        text = (
            '/- axiom hidden : True; unsafe def hidden := 0; run_cmd addDecl -/\n'
            '-- native_decide @[implemented_by hidden] #eval skipKernelTC\n'
            'def note := "set_option axiom unsafe native_decide implemented_by +native"\n'
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

    def test_exact_audit_pin_passes(self):
        text = "theorem witness : True := True.intro\n\n" + pin("witness")
        self.assertEqual(CHECKER.check_audit_pins(text), [])

    def test_pin_must_expect_exactly_the_standard_axioms(self):
        for axioms in ("sorryAx", "propext, Classical.choice, Quot.sound, sorryAx",
                       "propext, Quot.sound"):
            with self.subTest(axioms=axioms):
                failures = CHECKER.check_audit_pins(
                    "theorem witness : True := True.intro\n" + pin("witness", axioms))
                self.assertTrue(any("must expect exactly" in error for error in failures))

    def test_pin_must_use_the_lax_whitespace_guard(self):
        for guard in ("", "(drop all) ", "(whitespace := exact) "):
            with self.subTest(guard=guard):
                failures = CHECKER.check_audit_pins(
                    "theorem witness : True := True.intro\n" + pin("witness", guard=guard))
                self.assertTrue(any("must expect exactly" in error for error in failures))

    def test_pin_without_expected_output_fails(self):
        failures = CHECKER.check_audit_pins(
            "theorem witness : True := True.intro\n"
            "#guard_msgs (whitespace := lax) in\n#print axioms Vegas.Paper.witness\n")
        self.assertTrue(any("must expect exactly" in error for error in failures))

    def test_audit_theorem_requires_guarded_pin(self):
        for unpinned in ("", "#print axioms Vegas.Paper.witness\n",
                         "/- #guard_msgs in\n#print axioms Vegas.Paper.witness -/\n"):
            with self.subTest(unpinned=unpinned):
                failures = CHECKER.check_audit_pins(
                    "theorem witness : True := True.intro\n" + unpinned)
                self.assertTrue(any("missing guarded axiom pin" in error for error in failures))

    def test_theorems_with_attributes_or_modifiers_require_pins(self):
        for header in ("@[simp] theorem", "protected theorem", "lemma", "@[simp] private lemma"):
            with self.subTest(header=header):
                failures = CHECKER.check_audit_pins(f"{header} witness : True := True.intro\n")
                self.assertTrue(any("missing guarded axiom pin for witness" in error
                                    for error in failures))

    def test_stale_audit_pin_fails(self):
        failures = CHECKER.check_audit_pins(pin("absent"))
        self.assertTrue(any("names no audit theorem" in error for error in failures))

    def test_duplicate_audit_pin_fails(self):
        failures = CHECKER.check_audit_pins(
            "theorem witness : True := True.intro\n" + pin("witness") * 2)
        self.assertTrue(any("duplicate axiom pin" in error for error in failures))

    def test_adjacent_pins_allow_documentation_and_indented_proof_bodies(self):
        text = (
            "namespace Vegas.Paper\n"
            "open Vegas in\n"
            "theorem first : True :=\n  True.intro\n" + pin("first") +
            "/-- Another delegated theorem. -/\n"
            "theorem second : True := first\n" + pin("second") +
            "end Vegas.Paper\n"
        )
        self.assertEqual(CHECKER.check_audit_pins(text), [])

    def test_footer_pins_are_not_adjacent(self):
        text = (
            "theorem first : True := True.intro\n"
            "theorem second : True := True.intro\n" + pin("first") + pin("second")
        )
        failures = CHECKER.check_audit_pins(text)
        self.assertEqual(sum("must immediately follow" in error for error in failures), 2)

    def test_pin_cannot_precede_theorem_or_follow_another_command(self):
        theorem = "theorem witness : True := True.intro\n"
        for text in (pin("witness") + theorem, theorem + "def unrelated := 0\n" + pin("witness")):
            with self.subTest(text=text):
                self.assertTrue(any("must immediately follow" in error
                                    for error in CHECKER.check_audit_pins(text)))

    def test_axiom_prints_are_allowed_only_in_paper(self):
        commands = ("#print axioms witness\n",
                    "#guard_msgs in #print axioms witness\n",
                    "#guard_msgs in\n#print\n  axioms\n  witness\n")
        for text in commands:
            with self.subTest(text=text):
                self.assertEqual(CHECKER.check_axiom_prints(Path("Paper.lean"), text), [])
                for path in ("Vegas/Proof.lean", "Interaction/Example.lean",
                             "VegasTests/AxiomAudit/Source.lean", "Paper/Source.lean"):
                    self.assertEqual(len(CHECKER.check_axiom_prints(Path(path), text)), 1)

    def test_documented_axiom_prints_are_not_commands(self):
        text = ('/- /- #print axioms hidden -/ -/\n'
                '-- #print axioms hidden\n'
                'def help := "#print axioms hidden"\n')
        self.assertEqual(CHECKER.check_axiom_prints(Path("Vegas/Help.lean"), text), [])

    def test_actual_lakefile_passes(self):
        root = Path(__file__).resolve().parent.parent
        with (root / "lakefile.toml").open("rb") as source:
            config = CHECKER.tomllib.load(source)
        self.assertEqual(CHECKER.check_lakefile(config), [])
        self.assertNotEqual(config["leanOptions"].get("warn", {}).get("sorry"), False)

    def test_actual_paper_pins_are_exact(self):
        root = Path(__file__).resolve().parent.parent
        self.assertEqual(CHECKER.check_audit_pins(
            (root / "Paper.lean").read_text(encoding="utf-8")), [])


if __name__ == "__main__":
    unittest.main()
