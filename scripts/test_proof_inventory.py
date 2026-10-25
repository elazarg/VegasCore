import importlib.util
from pathlib import Path
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location("proof_inventory",
    Path(__file__).with_name("proof-inventory.py"))
INVENTORY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(INVENTORY)


class ProofInventoryTests(unittest.TestCase):
    def test_blank_lines_do_not_truncate_proofs(self):
        text = "theorem first : True := by\n  have h : True := trivial\n\n  exact h\n\ntheorem second : True := trivial\n"
        rows = list(INVENTORY.proof_bodies(text))
        self.assertEqual([row["body_lines"] for row in rows], [3, 1])
        self.assertEqual([row["line"] for row in rows], [1, 6])

    def test_comments_do_not_create_declarations_or_proof_lines(self):
        text = "/- theorem fake : True := by\n  trivial -/\ntheorem real : True := by\n  -- comment\n  trivial\n"
        rows = list(INVENTORY.proof_bodies(text))
        self.assertEqual([(row["name"], row["line"], row["body_lines"]) for row in rows],
                         [("real", 3, 2)])

    def test_computational_definition_is_not_a_proof(self):
        rows = list(INVENTORY.proof_bodies("def data : Nat := 1\ndef proof : True := by\n  trivial\n"))
        self.assertEqual([row["name"] for row in rows], ["proof"])

    def test_duplicate_windows_need_different_files(self):
        text = "theorem one : True := by\n  have h : True := trivial\n  exact h\n"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text(text)
            self.assertEqual(INVENTORY.inventory(root, ["A.lean"], 2)[2], [])
            (root / "B.lean").write_text(text)
            rows = INVENTORY.inventory(root, ["A.lean", "B.lean"], 2)[2]
            self.assertEqual(len(rows), 2)
            self.assertEqual({item["path"] for item in rows[0]}, {"A.lean", "B.lean"})

    def test_dependency_module_names_and_layer(self):
        self.assertEqual(INVENTORY.module_name("GameTheory/GameTheory/Core/Utility.lean"),
                         "GameTheory.Core.Utility")
        self.assertEqual(INVENTORY.layer("Vegas/Game/Example.lean"), "Vegas.Game")

    def test_result_type_lets_are_not_proof_assignments(self):
        text = ("theorem result :\n"
                "    let common := 3\n"
                "    let payoff := common + 1\n"
                "    payoff = 4 := by\n"
                "  rfl\n")
        rows = list(INVENTORY.proof_bodies(text))
        self.assertEqual([row["body_lines"] for row in rows], [2])
        surface = INVENTORY.DEFS.strip_proof(text.splitlines())
        self.assertEqual(surface[-1], "    payoff = 4")
        self.assertIn("    let payoff := common + 1", surface)

    def test_nested_result_bindings_and_named_arguments(self):
        text = ("theorem result :\n"
                "    let common := let nested := (f (value := 3)); nested\n"
                "    have witness : True := trivial\n"
                "    common = common := by\n"
                "  rfl\n")
        rows = list(INVENTORY.proof_bodies(text))
        self.assertEqual([row["body_lines"] for row in rows], [2])

    def test_binding_words_in_comments_strings_and_identifiers(self):
        text = ('theorem «let» :\n'
                '    let message := "let fake := have hidden :="\n'
                '    /- let omitted := 0 /- have nested := 1 -/ -/\n'
                '    let haveData := 3\n'
                '    haveData = 3 := by\n'
                '  rfl\n')
        rows = list(INVENTORY.proof_bodies(text))
        self.assertEqual([row["body_lines"] for row in rows], [2])

    def test_result_type_lets_keep_computational_definitions(self):
        text = "def result : let kind := Nat; kind := 1\n"
        self.assertEqual(list(INVENTORY.proof_bodies(text)), [])
        self.assertEqual(INVENTORY.DEFS.strip_tactic_body(text.splitlines()),
                         text.splitlines())


if __name__ == "__main__":
    unittest.main()
