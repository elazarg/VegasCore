"""Behavioral and mutation tests for the Lean-native paper audit (run after lake build)."""
import importlib.util
from pathlib import Path
import tempfile
import textwrap
import unittest

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
            'scoped': 'open Nat in ' + proof() + pin(),
            'multiline': 'theorem Vegas.Paper.result\n  : True\n  := by\n    trivial\n' + pin(),
            'concept': 'def Vegas.Paper.Predicate : Prop := True\n' + base,
            'concept_pin': 'def Vegas.Paper.Predicate : Prop := True\n' + pin('Predicate') + base,
            'structure': 'structure Vegas.Paper.Observation where\n'
                         '  /-- A number. -/\n  amount : Nat\n\n'
                         '  /-- A certificate. -/\n  property : amount = amount\n' + base,
            'proof_default': 'structure Vegas.Paper.Hidden where\n  fact : (∀ n : Nat, n + 0 = n) := by simp\n' + base,
            'data_default': 'structure Vegas.Paper.Counter where\n  value : Nat := 0\n' + base,
            'derive': 'structure Vegas.Paper.Observation where deriving Inhabited\n' + base,
            'local_instance': 'local instance : Inhabited Nat := ⟨0⟩\n' + base,
            'attribute': 'attribute [local instance] Nat.instInhabited\n' + base,
            'alias': 'def Vegas.Paper.anchor : Nat := 0\n  alias Vegas.Paper.hidden := Nat.add_comm\n' + base,
            'notation3': 'def Vegas.Paper.anchor : Nat := 0\n  notation3 "privateToken" => True\n' + base,
            'open_classical': 'open Classical\n' + base,
            'open_scoped_classical': 'open scoped Classical\n' + base,
            'shadow_true': 'local notation "True" => (False)\n' + base,
            'exit': base + '#exit\n' + proof('hidden'),
            'shadow_keyword': 'local notation "by" => True\n' + base,
            'shadow_variable': 'section\nvariable (value : Nat)\nlocal notation "value" => 0\n' + base + 'end\n',
            'fresh_notation': 'local notation "auditCounter" => Nat\ndef Vegas.Paper.counter : auditCounter := 0\n' + base,
            'empty': '',
        }
        cls.paths = {}
        for name, text in cls.cases.items():
            path = cls.directory / (name + '.lean')
            path.write_text(HEADER + text, encoding='utf-8')
            cls.paths[name] = path
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
                     'indented', 'scoped', 'multiline', 'concept', 'structure', 'fresh_notation', 'data_default'):
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
        for case in ('derive', 'local_instance', 'attribute', 'alias', 'notation3'):
            with self.subTest(case=case):
                self.assertTrue(self.reports[case]['errors'], case)

    def test_meaning_changing_opens_and_notations_reject(self):
        self.error('open_classical', 'opening Classical changes')
        self.error('open_scoped_classical', 'ordinary namespace opens')
        self.error('shadow_true', 'shadows an existing name')
        self.error('shadow_keyword', 'shadows a parser token')
        self.error('exit', 'unsupported terminal Paper command')
        self.error('shadow_variable', 'shadows a section variable')
        self.error('proof_default', 'proof-valued structure default')

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
