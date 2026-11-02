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


def statement(name="result", **kwargs):
    return (f"theorem Vegas.Paper.{name} : (True) := (True.intro)\n" + pin(name, **kwargs))


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

    def test_exact_owning_pin_passes(self):
        self.assertEqual(CHECKER.check_audit_pins(statement("source_result")), [])

    def test_paper_concepts_do_not_need_axiom_pins(self):
        concepts = (
            "def Vegas.Paper.InRange (low high cash : ℝ) : (Prop) := (low ≤ cash ∧ cash ≤ high)\n",
            "abbrev Vegas.Paper.Receipts (Player : Type) := (Player → ℝ)\n",
            "structure Vegas.Paper.CashObservation where\n  amount : (ℝ)\n  defaulted : (Bool)\n",
        )
        for concept in concepts:
            with self.subTest(concept=concept):
                self.assertEqual(CHECKER.check_audit_pins(concept + statement()), [])

    def test_paper_concept_names_are_fully_qualified(self):
        for command in ("def InRange : (Prop) := (True)\n", "abbrev Receipts := (Nat → ℝ)\n",
                        "structure CashObservation where\n  amount : (ℝ)\n"):
            with self.subTest(command=command):
                errors = CHECKER.check_audit_pins(command + statement())
                self.assertTrue(any("fully qualified paper concept name" in e for e in errors))

    def test_theorem_using_local_concept_keeps_full_statement_and_exact_pin(self):
        concept = "def Vegas.Paper.InRange (low high cash : ℝ) : (Prop) := (low ≤ cash ∧ cash ≤ high)\n"
        header = ("theorem Vegas.Paper.range_lower (low high cash : ℝ)\n"
                  "    (within : Vegas.Paper.InRange low high cash)")
        theorem = header + " : (low ≤ cash) := (within.1)\n"
        self.assertEqual(CHECKER.check_audit_pins(concept + theorem + pin("range_lower")), [])
        mutations = (
            (header + " := within.1\n" + pin("range_lower"), "full explicit statement"),
            (theorem, "missing guarded axiom pin"),
            (theorem + pin("range_lower", guard=""), "must expect exactly"),
            (theorem + pin("range_lower", axioms="propext"), "must expect exactly"),
            (theorem + "abbrev Vegas.Paper.Receipts := Nat → ℝ\n" + pin("range_lower"),
             "immediately follow"),
        )
        for mutation, expected_error in mutations:
            with self.subTest(mutation=mutation):
                errors = CHECKER.check_audit_pins(concept + mutation)
                self.assertTrue(any(expected_error in e for e in errors))

    def test_pins_cannot_target_concepts_without_local_theorems(self):
        for concept in ("def Vegas.Paper.InRange : Prop := True\n",
                        "abbrev Vegas.Paper.InRange := True\n",
                        "structure Vegas.Paper.InRange where\n  lower : ℝ\n"):
            with self.subTest(concept=concept):
                errors = CHECKER.check_audit_pins(concept + pin("InRange") + statement())
                self.assertTrue(any("axiom pin names no local paper theorem: Vegas.Paper.InRange"
                                    in e for e in errors))

    def test_empty_or_import_only_paper_fails(self):
        for text in ("", "import Vegas.Game.SequentialCompilation\n", "/- no pins -/\n",
                     "def Vegas.Paper.InRange : Prop := True\n"):
            with self.subTest(text=text):
                self.assertTrue(CHECKER.check_audit_pins(text))

    def test_pin_must_expect_exactly_the_standard_axioms(self):
        for axioms in ("sorryAx", "propext, Classical.choice, Quot.sound, sorryAx",
                       "propext, Quot.sound", "propext, Classical.choice, Quot.sound, propext"):
            with self.subTest(axioms=axioms):
                self.assertTrue(CHECKER.check_audit_pins(statement("result", axioms=axioms)))

    def test_pin_must_use_the_lax_whitespace_guard(self):
        for guard in ("", "(drop all) ", "(whitespace := exact) "):
            with self.subTest(guard=guard):
                self.assertTrue(CHECKER.check_audit_pins(statement("result", guard=guard)))

    def test_unguarded_or_undocumented_print_fails(self):
        for text in ("#print axioms Vegas.Paper.result\n",
                     "#guard_msgs (whitespace := lax) in\n#print axioms Vegas.Paper.result\n",
                     pin("result").replace("#guard_msgs (whitespace := lax) in\n", "")):
            with self.subTest(text=text):
                self.assertTrue(CHECKER.check_audit_pins(text))

    def test_expected_name_must_match_printed_name(self):
        self.assertTrue(CHECKER.check_audit_pins(
            statement("first").replace("#print axioms Vegas.Paper.first", "#print axioms Vegas.Paper.second")))

    def test_duplicate_pin_fails(self):
        self.assertTrue(CHECKER.check_audit_pins(statement("result") * 2))

    def test_unicode_owning_names_pass(self):
        self.assertEqual(CHECKER.check_audit_pins(statement("intended_isεNash_preserved")), [])

    def test_unqualified_or_malformed_print_fails(self):
        for text in (statement("result").replace("Vegas.Paper.result", "result"),
                     pin("result") + "#print axioms\n"):
            with self.subTest(text=text):
                self.assertTrue(CHECKER.check_audit_pins(text))

    def test_inferred_statement_is_rejected(self):
        self.assertTrue(CHECKER.check_audit_pins(
            "theorem Vegas.Paper.result := Vegas.other\n" + pin("result")))

    def test_empty_and_placeholder_statements_are_rejected(self):
        for result in ("", "   ", "_", "(_)", "?result"):
            with self.subTest(result=result):
                errors = CHECKER.check_audit_pins(
                    f"theorem Vegas.Paper.result : {result} := Vegas.other\n" + pin("result"))
                self.assertTrue(any("full explicit statement" in e for e in errors))

    def test_pin_without_local_statement_is_rejected(self):
        self.assertTrue(CHECKER.check_audit_pins(pin("result")))

    def test_pin_must_follow_its_statement(self):
        text = statement().replace("#guard_msgs", "#check Nat\n#guard_msgs")
        self.assertTrue(CHECKER.check_audit_pins(text))

    def test_binder_colon_does_not_supply_result_statement(self):
        self.assertTrue(CHECKER.check_audit_pins(
            "theorem Vegas.Paper.result (x : Nat) := Vegas.other x\n" + pin("result")))

    def test_pins_in_comments_or_strings_do_not_supply_guards(self):
        for fake in ("/- " + pin("result") + " -/\n",
                     'def note := "' + pin("result") + '"\n'):
            with self.subTest(fake=fake):
                self.assertTrue(CHECKER.check_audit_pins(fake + "#print axioms Vegas.Paper.result\n"))

    def test_actual_paper_mutations_fail(self):
        paper = (Path(__file__).resolve().parent.parent / "Paper.lean").read_text(encoding="utf-8")
        mutations = ["", paper.replace("#guard_msgs (whitespace := lax) in", ""),
                     paper.replace("propext, Classical.choice, Quot.sound", "sorryAx"),
                     paper.replace("#guard_msgs (whitespace := lax) in", "", 1)]
        for index, text in enumerate(mutations):
            with self.subTest(mutation=index):
                self.assertTrue(CHECKER.check_audit_pins(text))

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

    def test_unpinned_declarations_cannot_hide_in_layout_or_prefixes(self):
        hidden = "theorem Vegas.Paper.hidden : True := True.intro\n"
        variants = (
            "/-- documentation -/ " + hidden,
            "open Nat in " + hidden,
            "section\n  " + hidden + "end\n",
            "section\n\t" + hidden + "end\n",
            "theorem\n  Vegas.Paper.hidden : True := True.intro\n",
            "noncomputable " + hidden,
        )
        for variant in variants:
            with self.subTest(variant=variant):
                self.assertTrue(CHECKER.check_audit_pins(statement() + variant))

    def test_documented_and_indented_statements_are_audited(self):
        self.assertEqual(CHECKER.check_audit_pins("/-- documentation -/ " + statement()), [])
        text = "section\n  " + statement() + "end\n"
        self.assertEqual(CHECKER.check_audit_pins(text), [])
        self.assertTrue(CHECKER.check_audit_pins(text.replace("#guard_msgs", "-- #guard_msgs")))

    def test_paper_command_allowlist_rejects_semantic_modifiers(self):
        commands = (
            "local instance : Inhabited Nat := ⟨0⟩\n",
            "attribute [local instance] Nat.instInhabited\n",
            "@[local instance] def Vegas.Paper.hidden : Inhabited Nat := ⟨0⟩\n",
            "inductive Hidden where | hidden\n",
            "macro_rules | `(hidden) => `(True)\n",
            'syntax "hidden" : command\n',
            "namespace Hidden\nend Hidden\n",
            "#check Nat\n",
            "unknown_command\n",
            "%%\n",
        )
        for command in commands:
            for prefix in ("", "  "):
                with self.subTest(command=command, prefix=prefix):
                    text = statement() + "\nsection\n" + prefix + command + "end\n"
                    self.assertTrue(CHECKER.check_audit_pins(text))

    def test_same_line_commands_cannot_change_a_pinned_statement(self):
        commands = (
            "section attribute [local instance] Nat.instInhabited\n",
            "open Nat in " + statement(),
            "local notation \"hidden\" => True attribute [local instance] Nat.instInhabited\n",
        )
        for command in commands:
            with self.subTest(command=command):
                self.assertTrue(CHECKER.check_audit_pins(command + statement()))

    def test_imported_commands_cannot_hide_as_term_continuations(self):
        for command in ("alias Vegas.Paper.hidden := Nat.add_comm", 'notation3 "privateToken" => True'):
            for indent in ("", "  ", "      "):
                with self.subTest(command=command, indent=indent):
                    text = (statement() + "section\n"
                            "  def Vegas.Paper.anchor : (Nat) := (0)\n"
                            + indent + command + "\nend\n")
                    self.assertTrue(CHECKER.check_audit_pins(text))

    def test_multiline_declarations_use_structural_boundaries(self):
        text = ("section\n  theorem Vegas.Paper.result\n"
                "    (x : Nat) : (\n      x = x) := (by\n    rfl)\n"
                + pin("result") + "end\n")
        self.assertEqual(CHECKER.check_audit_pins(text), [])
        self.assertTrue(CHECKER.check_audit_pins(text.replace("rfl)", "rfl")))

    def test_structure_fields_cannot_install_derived_instances(self):
        root = Path(__file__).resolve().parent.parent
        paper = (root / "Paper.lean").read_text(encoding="utf-8")
        for tail in ("where deriving Inhabited",
                     "where field : (Nat) deriving Inhabited",
                     "where\n  field : (Nat) deriving Inhabited",
                     "where\n  field : (Nat)\n  deriving Inhabited"):
            with self.subTest(tail=tail):
                self.assertTrue(CHECKER.check_audit_pins(
                    paper + "\nstructure Vegas.Paper.Hidden " + tail + "\n"))

    def test_actual_paper_rejects_hidden_results_and_command_changes(self):
        root = Path(__file__).resolve().parent.parent
        paper = (root / "Paper.lean").read_text(encoding="utf-8")
        hidden = "theorem Vegas.Paper.hidden : True := True.intro\n"
        mutations = (
            "/-- documentation -/ " + hidden,
            "open Nat in " + hidden,
            "section\n  " + hidden + "end\n",
            "local instance : Inhabited Nat := ⟨0⟩\n",
            "attribute [local instance] Nat.instInhabited\n",
            "inductive Hidden where | hidden\n",
            "macro_rules | `(hidden) => `(True)\n",
        )
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                self.assertTrue(CHECKER.check_audit_pins(paper + "\n" + mutation))


if __name__ == "__main__":
    unittest.main()
