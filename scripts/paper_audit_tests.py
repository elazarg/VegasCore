"""Behavioral and mutation tests for the Lean-native paper audit (run after lake build)."""
import importlib.util
from pathlib import Path
import tempfile
import textwrap
import unittest
from unittest.mock import patch
import subprocess

SPEC = importlib.util.spec_from_file_location('paper_audit', Path(__file__).with_name('check-paper-audit.py'))
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)
ROOT = AUDIT.ROOT
HEADER = 'import Lean\nimport Mathlib.Tactic\n'


def pin(name='result', expected=None):
    expected = expected or f"info: 'Vegas.Paper.{name}' does not depend on any axioms"
    return (f'/-- {expected} -/\n#guard_msgs (whitespace := lax) in\n'
            f'#print axioms Vegas.Paper.{name}\n')


def proof(name='result', kind='theorem', result='True', body='True.intro'):
    return f'{kind} Vegas.Paper.{name} : {result} := {body}\n'


class PaperAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        (ROOT / '.lake/paper-audit').mkdir(parents=True, exist_ok=True)
        cls.temp = tempfile.TemporaryDirectory(prefix='cases-', dir=ROOT / '.lake/paper-audit')
        cls.addClassCleanup(cls.temp.cleanup)
        cls.directory = Path(cls.temp.name)
        assert cls.directory.resolve().is_relative_to((ROOT / '.lake/paper-audit').resolve())
        base = proof() + pin()
        cls.cases = {
            'valid': base,
            'missing': base + proof('hidden'),
            'adjacency': proof() + 'def Vegas.Paper.counter : Nat := 0\n' + pin(),
            'placeholder': proof(kind='abbrev', result='(_)') + pin(),
            'inferred': 'def Vegas.Paper.result := True.intro\n' + pin(),
            'inferred_binder': 'def Vegas.Paper.result (h : True) := h\n' + pin(),
            'commented_guard': proof() + '-- #guard_msgs (whitespace := lax) in\n'
                '#print axioms Vegas.Paper.result\n',
            'wrong_guard': proof() + pin().replace('(whitespace := lax)', '(drop all)'),
            'wrong_expected': proof() + pin(expected="info: 'Vegas.Paper.result' depends on axioms: [sorryAx]"),
            'duplicate': base + pin(),
            'definition_proof': base + proof('hidden', kind='def', result='1 = 1', body='rfl'),
            'abbreviation_proof': base + proof('hidden', kind='abbrev', result='1 = 1', body='rfl'),
            'pinned_definition': proof(kind='def') + pin(),
            'pinned_abbreviation': proof(kind='abbrev') + pin(),
            'documented': '/-- A reflexive result. -/ ' + proof() + pin(),
            'indented': 'section\n  ' + proof() + pin() + 'end\n',
            'scoped': 'def Vegas.Paper.counter : Nat := 0\nopen Vegas.Paper in ' + proof() + pin(),
            'multiline': 'theorem Vegas.Paper.result\n  : True\n  := by\n    trivial\n' + pin(),
            'concept': 'def Vegas.Paper.Predicate : Prop := True\n' + base,
            'concept_pin': 'def Vegas.Paper.Predicate : Prop := True\n' + pin('Predicate') + base,
            'structure': 'structure Vegas.Paper.Observation where\n'
                         '  /-- A number. -/\n  amount : Nat\n\n'
                         '  /-- A certificate. -/\n  property : amount = amount\n' + base,
            'proof_default': 'structure Vegas.Paper.Hidden where\n  fact : (∀ n : Nat, n + 0 = n) := by simp\n' + base,
            'type_proof_default': 'structure Vegas.Paper.Hidden : Type where\n'
                '  fact : (1 : Nat) = 1 := rfl\n' + base,
            'data_default': 'structure Vegas.Paper.Counter where\n  value : Nat := 0\n' + base,
            'derive': 'structure Vegas.Paper.Observation where deriving Inhabited\n' + base,
            'local_instance': 'local instance : Inhabited Nat := ⟨0⟩\n' + base,
            'attribute': 'attribute [local instance] instInhabitedNat\n' + base,
            'alias': 'def Vegas.Paper.anchor : Nat := 0\n  alias Vegas.Paper.hidden := Nat.add_comm\n' + base,
            'notation3': 'def Vegas.Paper.anchor : Nat := 0\n  notation3 "privateToken" => True\n' + base,
            'open_classical': 'open Classical\n' + base,
            'open_scoped_classical': 'open scoped Classical\n' + base,
            'shadow_true': 'local notation "True" => (False)\n' + base,
            'exit': base + '#exit\n' + proof('hidden'),
            'shadow_keyword': 'local notation "by" => True\n' + base,
            'shadow_variable': 'section\nvariable (value : Nat)\nlocal notation "value" => 0\n' + base + 'end\n',
            'fresh_notation': 'local notation "auditCounter" => Nat\ndef Vegas.Paper.counter : auditCounter := 0\n' + base,
            'class': 'class Vegas.Paper.Hidden extends Inhabited Nat\n' + base,
            'prop_structure': 'structure Vegas.Paper.Claim : Prop where\n  fact : (1 : Nat) = 1\n' + base,
            'subtype_data': 'def Vegas.Paper.certified : {n : Nat // n = n} := ⟨0, rfl⟩\n' + base,
            'plift_data': 'def Vegas.Paper.certified : PLift (1 = 1) := ⟨rfl⟩\n' + base,
            'structure_data': 'structure Vegas.Paper.Certified : Type where\n  fact : (1 : Nat) = 1\n'
                'def Vegas.Paper.certificate : Vegas.Paper.Certified := ⟨rfl⟩\n' + base,
            'open_pointwise': 'open Pointwise\n' + base,
            'term_open_classical': 'def Vegas.Paper.Condition (p : Prop) : Prop := '
                '(open Classical in (if p then True else True))\n' + base,
            'tactic_open_pointwise': proof('hidden', body='by open Pointwise in trivial') + base,
            'safe_term_open': 'def Vegas.Paper.counter : Nat := 0\n' +
                proof(result='(open Vegas.Paper in counter = counter)', body='rfl') + pin(),
            'fresh_main': 'local notation "main" => Nat\ndef Vegas.Paper.counter : main := 0\n' + base,
            'late_open_shadow': 'def Vegas.Paper.Inner.foo : Prop := True\n'
                'local notation "foo" => False\nopen Vegas.Paper.Inner\n'
                + proof(result='foo → False', body='id') + pin(),
            'late_decl_shadow': 'def Vegas.Paper.Inner.anchor : Nat := 0\n'
                'open Vegas.Paper.Inner\nlocal notation "foo" => False\n'
                'def Vegas.Paper.Inner.foo : Prop := True\n'
                + proof(result='foo → False', body='id') + pin(),
            'scoped_open_shadow': 'def Vegas.Paper.Inner.foo : Prop := True\n'
                'local notation "foo" => False\nopen Vegas.Paper.Inner in '
                + proof('hidden', result='foo → False', body='id') + base,
            'expired_notation': 'def Vegas.Paper.Inner.foo : Prop := True\nsection\n'
                'local notation "foo" => False\n' + proof('inside', result='foo → False', body='id')
                + pin('inside') + 'end\nopen Vegas.Paper.Inner\n'
                + proof(result='foo', body='True.intro') + pin(),
            'where_hidden': 'def Vegas.Paper.container : Nat := 0 where\n'
                '  _hidden : (1 : Nat) = 1 := rfl\n' + base,
            'where_visible': 'def Vegas.Paper.container : Nat := 0 where\n'
                '  visible : (1 : Nat) = 1 := rfl\n' + base,
            'letrec_hidden': 'def Vegas.Paper.container : Nat :=\n'
                '  let rec _hidden : (1 : Nat) = 1 := rfl\n  0\n' + base,
            'letrec_visible': 'def Vegas.Paper.container : Nat :=\n'
                '  let rec visible : (1 : Nat) = 1 := rfl\n  0\n' + base,
            'inherited_proof_default': 'structure Vegas.Paper.Parent : Type where\n'
                '  fact : (1 : Nat) = 1\nstructure Vegas.Paper.Child extends Vegas.Paper.Parent where\n'
                '  fact := rfl\n' + base,
            'inherited_data_default': 'structure Vegas.Paper.Parent : Type where\n'
                '  value : Nat\nstructure Vegas.Paper.Child extends Vegas.Paper.Parent where\n'
                '  value := 0\n' + base,
            'rw_equation': 'def Vegas.Paper.f (n : Nat) : Nat := n + 1\n'
                'theorem Vegas.Paper.result (n : Nat) : Vegas.Paper.f n = n + 1 := by\n'
                '  rw [Vegas.Paper.f]\n' + pin(),
            'simp_equation': 'def Vegas.Paper.f (n : Nat) : Nat := n + 1\n'
                'theorem Vegas.Paper.result (n : Nat) : Vegas.Paper.f n = n + 1 := by\n'
                '  simp [Vegas.Paper.f]\n' + pin(expected=
                    "info: 'Vegas.Paper.result' depends on axioms: [propext]"),
            'placeholder_binder': 'theorem Vegas.Paper.result (x : _) : '
                'x = (1 : Nat) → x = 1 := id\n' + pin(),
            'untyped_binder': 'theorem Vegas.Paper.result (x) : '
                'x = (1 : Nat) → x = 1 := id\n' + pin(),
            'anonymous_function': 'theorem Vegas.Paper.result (x : Nat) : '
                '(fun _ : Nat => True) x := True.intro\n' + pin(),
            'anonymous_binder_function': 'theorem Vegas.Paper.result '
                '(h : (fun _ : Nat => True) 0) : True := h\n' + pin(),
            'placeholder_lambda_type': 'theorem Vegas.Paper.result '
                '(h : (fun (x : _) => True) (0 : Nat)) : True := h\n' + pin(),
            'variable_hole': 'variable (x : _)\n' +
                proof(result='x = (1 : Nat) → x = 1', body='id') + pin(),
            'variable_named_hole': 'variable (x : ?a)\n' +
                proof(result='x = (1 : Nat) → x = 1', body='id') + pin(),
            'named_binder_type': 'theorem Vegas.Paper.result (x : ?a) : '
                'x = (1 : Nat) → x = 1 := id\n' + pin(),
            'implicit_variable': 'variable (x : Nat)\nvariable {x}\n' +
                proof(result='x = x', body='rfl') + pin(),
            'forall_anonymous': 'theorem Vegas.Paper.result '
                '(h : ∀ _ : Nat, True) : True := h 0\n' + pin(),
            'exists_anonymous': 'theorem Vegas.Paper.result '
                '(h : ∃ _ : Nat, True) : True := h.elim (fun _ proof => proof)\n' + pin(),
            'match_pattern': 'theorem Vegas.Paper.result (n : Nat) '
                '(h : match n with | _ => True) : True := h\n' + pin(),
            'lambda_match': 'theorem Vegas.Paper.result '
                '(h : (fun | _ => True) (0 : Nat)) : True := h\n' + pin(),
            'empty': '',
        }
        cls.paths = {}
        for name, text in cls.cases.items():
            path = cls.directory / (name + '.lean')
            path.write_text(HEADER + text, encoding='utf-8')
            cls.paths[name] = path
        # These files deliberately have different import headers. A merged driver
        # would make Real available to lean_only and invalidate this test.
        for name, header in (('lean_only', 'import Lean\n'), ('mathlib_real', HEADER)):
            path = cls.directory / (name + '.lean')
            path.write_text(header + 'def Vegas.Paper.RealType : Type := Real\n' + base,
                            encoding='utf-8')
            cls.paths[name] = path
        # The real paper does not import the full Lean frontend umbrella.
        # Auditing it catches dependencies that the small fixture headers hide.
        cls.paths['actual_paper'] = ROOT / 'Paper.lean'
        reports = AUDIT.audit_files(list(cls.paths.values()))
        cls.reports = dict(zip(cls.paths, reports))

    def error(self, case, message):
        errors = self.reports[case]['errors']
        self.assertTrue(any(message in error for error in errors), (case, message, errors))
        self.assertFalse(any('Lean parser:' in e or 'Lean elaboration:' in e for e in errors), errors)

    def test_missing_pin_is_reported_for_a_valid_explicit_theorem(self):
        self.error('missing', 'missing guarded axiom pin for Vegas.Paper.hidden')

    def test_adjacency_is_reported_for_an_intervening_valid_definition(self):
        self.error('adjacency', 'exact axiom pin must immediately follow')

    def test_placeholder_type_is_rejected_by_lean(self):
        self.assertTrue(any('Failed to infer type' in e
                            for e in self.reports['placeholder']['errors']))

    def test_commented_guard_is_a_real_unguarded_print(self):
        self.error('commented_guard', 'unsupported Paper command kind: Lean.Parser.Command.printAxioms')

    def test_proof_definitions_and_abbreviations_need_pins(self):
        for case in ('definition_proof', 'abbreviation_proof'):
            with self.subTest(case=case):
                self.error(case, 'missing guarded axiom pin for Vegas.Paper.hidden')

    def test_accepted_ordinary_lean_forms(self):
        for case in ('valid', 'pinned_definition', 'pinned_abbreviation', 'documented',
                     'indented', 'scoped', 'multiline', 'concept', 'structure', 'fresh_notation', 'data_default', 'prop_structure',
                     'subtype_data', 'plift_data', 'structure_data', 'fresh_main', 'safe_term_open',
                     'mathlib_real'):
            with self.subTest(case=case):
                self.assertEqual(self.reports[case]['errors'], [])

    def test_pin_integrity(self):
        self.error('wrong_guard', 'requires exactly #guard_msgs')
        self.error('duplicate', 'duplicate axiom pin')
        self.error('inferred', 'needs its full explicit statement')
        self.error('inferred_binder', 'needs its full explicit statement')
        self.error('concept_pin', 'axiom pin names no local result')
        self.assertTrue(any('Lean elaboration:' in e for e in self.reports['wrong_expected']['errors']))
        self.error('empty', 'must contain stated results')

    def test_instances_aliases_and_syntax_extensions_reject(self):
        self.error('derive', 'Paper declarations cannot derive instances')
        self.error('class', 'Paper declarations cannot create classes')
        self.error('local_instance', 'unsupported Paper declaration kind: Lean.Parser.Command.instance')
        self.error('attribute', 'unsupported Paper command kind: Lean.Parser.Command.attribute')
        for case in ('alias', 'notation3'):
            with self.subTest(case=case):
                self.error(case, 'unsupported Paper command kind')

    def test_notation_stays_fresh_as_scope_changes(self):
        for case in ('late_open_shadow', 'late_decl_shadow', 'scoped_open_shadow'):
            with self.subTest(case=case):
                self.error(case, 'Paper notation shadows an existing name: foo')
        self.assertEqual(self.reports['expired_notation']['errors'], [])

    def test_local_recursive_helpers_are_rejected(self):
        for case in ('where_hidden', 'where_visible', 'letrec_hidden', 'letrec_visible'):
            with self.subTest(case=case):
                self.error(case, 'cannot use where or let rec helpers')

    def test_inherited_defaults_distinguish_proofs_and_data(self):
        self.error('inherited_proof_default', 'proof-valued structure default')
        self.assertEqual(self.reports['inherited_data_default']['errors'], [])

    def test_rewriting_and_simplification_may_generate_equation_lemmas(self):
        for case in ('rw_equation', 'simp_equation'):
            with self.subTest(case=case):
                self.assertEqual(self.reports[case]['errors'], [])

    def test_binder_types_are_explicit_without_rejecting_anonymous_functions(self):
        for case in ('placeholder_binder', 'untyped_binder', 'placeholder_lambda_type'):
            with self.subTest(case=case):
                self.error(case, 'needs explicit binder types')
        self.assertEqual(self.reports['anonymous_function']['errors'], [])
        self.assertEqual(self.reports['anonymous_binder_function']['errors'], [])

    def test_section_variables_and_named_type_holes(self):
        for case in ('variable_hole', 'variable_named_hole'):
            with self.subTest(case=case):
                self.error(case, 'Paper section variable types cannot contain holes')
        self.error('named_binder_type', 'needs explicit binder types')
        self.assertEqual(self.reports['implicit_variable']['errors'], [])

    def test_anonymous_quantifiers_and_match_patterns_are_valid(self):
        for case in ('forall_anonymous', 'exists_anonymous', 'match_pattern', 'lambda_match'):
            with self.subTest(case=case):
                self.assertEqual(self.reports[case]['errors'], [])

    def test_freshness_gate_rejects_an_edited_source_without_rebuilding(self):
        directory = ROOT / '.lake/paper-audit'
        with tempfile.TemporaryDirectory(prefix='freshness-', dir=directory) as temp:
            project = Path(temp)
            self.assertTrue(project.resolve().is_relative_to(directory.resolve()))
            (project / 'lean-toolchain').write_text(
                (ROOT / 'lean-toolchain').read_text(encoding='utf-8'), encoding='utf-8')
            (project / 'lakefile.toml').write_text(
                'name = "audit_freshness"\n[[lean_lib]]\nname = "Paper"\n'
                '[[lean_lib]]\nname = "Tools"\n', encoding='utf-8')
            source = project / 'Paper.lean'
            source.write_text('def certificate : Nat := 0\n', encoding='utf-8')
            (project / 'Tools.lean').write_text('def helper : Nat := 0\n', encoding='utf-8')
            built = subprocess.run(['lake', 'build', 'Paper', 'Tools'], cwd=project,
                                   capture_output=True, text=True, timeout=180)
            self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            artifact = project / '.lake/build/lib/lean/Paper.olean'
            original = artifact.read_bytes()
            with patch.object(AUDIT, 'ROOT', project):
                AUDIT.ensure_fresh_build()
                source.write_text('def certificate : Nat := 1\n', encoding='utf-8')
                with self.assertRaisesRegex(RuntimeError, 'build is missing or stale'):
                    AUDIT.ensure_fresh_build()
            self.assertEqual(artifact.read_bytes(), original)

    def test_actual_paper_passes_with_its_own_import_header(self):
        report = self.reports['actual_paper']
        self.assertEqual(report['errors'], [])
        self.assertTrue(report['results'])
        self.assertEqual(set(report['results']), set(report['pins']))

    def test_each_file_uses_only_its_own_imports(self):
        self.assertEqual(self.reports['mathlib_real']['errors'], [])
        self.assertTrue(any("Unknown identifier `Real`" in e
                            for e in self.reports['lean_only']['errors']),
                        self.reports['lean_only']['errors'])

    def test_rejections_are_policy_diagnostics_and_keep_later_results(self):
        for case in ('class', 'open_pointwise', 'term_open_classical', 'attribute'):
            with self.subTest(case=case):
                report = self.reports[case]
                self.assertIn('Vegas.Paper.result', report['results'])
                self.assertFalse(any('unexpected internal error' in e or
                                     'must contain stated results' in e for e in report['errors']))

    def test_lean_process_has_a_bounded_timeout(self):
        with patch.object(AUDIT.subprocess, 'run', side_effect=subprocess.TimeoutExpired('lean', 180)) as run:
            with self.assertRaisesRegex(RuntimeError, 'Lean audit exceeded 180 seconds'):
                AUDIT.lean(['fixture.lean'])
            self.assertEqual(run.call_args.kwargs['timeout'], 180)

    def test_meaning_changing_opens_and_notations_reject(self):
        self.error('open_classical', 'Paper opens only Vegas, GameTheory and Interaction')
        self.error('open_pointwise', 'Paper opens only Vegas, GameTheory and Interaction')
        self.error('term_open_classical', 'Paper opens only Vegas, GameTheory and Interaction')
        self.error('tactic_open_pointwise', 'Paper opens only Vegas, GameTheory and Interaction')
        self.error('open_scoped_classical', 'ordinary namespace opens')
        self.error('shadow_true', 'shadows an existing name')
        self.error('shadow_keyword', 'shadows a parser token')
        self.error('exit', 'unsupported terminal Paper command')
        self.error('shadow_variable', 'shadows a section variable')
        self.error('proof_default', 'proof-valued structure default')
        self.error('type_proof_default', 'proof-valued structure default')

    def test_validation_checks_have_isolated_mutation_witnesses(self):
        source = (ROOT / 'Tools/PaperAudit.lean').read_text(encoding='utf-8')
        mutations = [
            ('missingPinErrors', 'missing', 'state.results.toArray.filterMap (fun _ => none)'),
            ('checkAdjacency', 'adjacency', 'do\n  let _ := state\n  let _ := pending\n  let _ := target\n  pure ()'),
            ('checkExplicitStatement', 'inferred', 'do\n  let _ := state\n  let _ := decl\n  let _ := name\n  pure ()'),
        ]
        for function, case, body in mutations:
            with self.subTest(function=function):
                start = source.index('private def PaperAudit.' + function)
                assignment = source.index(':=', start)
                end = source.index('\nprivate ', assignment)
                mutant = source[:assignment] + ':=\n' + textwrap.indent(body, '  ') + '\n' + source[end:]
                report = AUDIT.audit_files([self.paths[case]], source_override=mutant)[0]
                self.assertEqual(report['errors'], [],
                    'The mutant must remove this check alone; otherwise its fixture is vacuous.')


if __name__ == '__main__':
    unittest.main()
