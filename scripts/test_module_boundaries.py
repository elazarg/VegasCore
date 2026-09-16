import importlib.util
from pathlib import Path
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location(
    "module_boundaries", Path(__file__).with_name("check-module-boundaries.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class ModuleBoundaryTests(unittest.TestCase):
    def fixture(self, directory, modules, extra_config=""):
        root = Path(directory)
        (root / "lakefile.toml").write_text(
            'defaultTargets = ["Vegas", "VegasTests", "Paper"]\n'
            '[[lean_lib]]\nname = "Vegas"\n'
            '[[lean_lib]]\nname = "VegasTests"\n'
            '[[lean_lib]]\nname = "Paper"\n' + extra_config, encoding="utf-8"
        )
        for module, text in modules.items():
            path = root.joinpath(*module.split(".")).with_suffix(".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        return root

    def test_comments_do_not_create_imports(self):
        self.assertEqual(CHECKER.imports(
            "/- import Bogus\n/- nested -/ -/\nimport Vegas.Foundation -- comment\n"
        ), ["Vegas.Foundation"])

    def test_downstream_import_and_orphan_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.toml").write_text(
                'defaultTargets = ["Vegas", "VegasTests"]\n'
                '[[lean_lib]]\nname = "Vegas"\n'
                '[[lean_lib]]\nname = "VegasTests"\n', encoding="utf-8"
            )
            (root / "Vegas.lean").write_text("import VegasTests\n", encoding="utf-8")
            (root / "VegasTests.lean").write_text("", encoding="utf-8")
            (root / "Vegas").mkdir()
            (root / "Vegas" / "Orphan.lean").write_text("", encoding="utf-8")
            errors = CHECKER.check(root)
            self.assertTrue(any("core imports downstream" in error for error in errors))
            self.assertTrue(any("Vegas.Orphan: unreachable" in error for error in errors))

    def test_missing_local_import_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {"Vegas": "import Vegas.Missing"})
            self.assertTrue(any("missing local import Vegas.Missing" in error
                                for error in CHECKER.check(root)))

    def test_reference_files_cannot_supply_a_missing_local_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {"Vegas": "import Vegas.Backend"})
            references = root / "references" / "Vegas"
            references.mkdir(parents=True)
            reference = references / "Backend.lean.txt"
            reference.write_bytes(b"\xff\xfe not a Lean module")
            errors = CHECKER.check(root)
            self.assertTrue(any("missing local import Vegas.Backend" in error for error in errors))
            reference.unlink()
            self.assertEqual(CHECKER.check(root), errors)

    def test_reference_text_does_not_shadow_active_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {"Vegas": "import Vegas.Foundation", "Vegas.Foundation": ""})
            references = root / "references" / "Vegas"
            references.mkdir(parents=True)
            (references / "Foundation.lean.txt").write_text("", encoding="utf-8")
            self.assertEqual(CHECKER.check(root), [])

    def test_interaction_cannot_import_language_or_its_tests(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "", "Interaction": "import Vegas InteractionTests",
                "InteractionTests": "",
            }, '[[lean_lib]]\nname = "Interaction"\n'
               '[[lean_lib]]\nname = "InteractionTests"\n')
            errors = CHECKER.check(root)
            self.assertTrue(any("interaction carrier imports downstream module Vegas" in error
                                for error in errors))
            self.assertTrue(any("imports interaction test InteractionTests" in error
                                for error in errors))

    def test_game_theory_extensions_cannot_import_runtime_or_language(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import GameTheoryExtensions",
                "GameTheoryExtensions": "import Vegas Interaction",
                "Interaction": "",
            }, '[[lean_lib]]\nname = "GameTheoryExtensions"\n'
               '[[lean_lib]]\nname = "Interaction"\n')
            errors = CHECKER.check(root)
            for dependency in ("Vegas", "Interaction"):
                self.assertTrue(any(f"game-theory extension imports {dependency}" in error
                                    for error in errors))

    def test_production_cannot_import_game_theory_tests(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import GameTheoryExtensionsTests",
                "GameTheoryExtensionsTests": "",
            }, '[[lean_lib]]\nname = "GameTheoryExtensionsTests"\n')
            errors = CHECKER.check(root)
            self.assertTrue(any("imports game-theory test" in error for error in errors))

    def test_game_theory_tests_cannot_import_runtime(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "", "Interaction": "",
                "GameTheoryExtensionsTests": "import Interaction",
            }, '[[lean_lib]]\nname = "GameTheoryExtensionsTests"\n'
               '[[lean_lib]]\nname = "Interaction"\n')
            errors = CHECKER.check(root)
            self.assertTrue(any("game-theory test imports downstream" in error for error in errors))

    def test_game_theory_extensions_can_use_upstream_probability_and_forms(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import GameTheoryExtensions",
                "GameTheoryExtensions": "import GameTheory.Core.Utility Mathlib.Data.Real.Basic",
            }, '[[lean_lib]]\nname = "GameTheoryExtensions"\n')
            self.assertEqual(CHECKER.check(root), [])

    def test_interaction_tests_remain_language_independent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "", "Interaction": "",
                "InteractionTests": "import Vegas",
            }, '[[lean_lib]]\nname = "Interaction"\n'
               '[[lean_lib]]\nname = "InteractionTests"\n')
            self.assertTrue(any("runtime-independent test imports Vegas" in error
                                for error in CHECKER.check(root)))

    def test_semantic_layers_reject_upward_and_prototype_dependencies(self):
        forbidden = {
            "Vegas.Foundation": ("Vegas.Expr", "Vegas.Language"),
            "Vegas.Expr": ("Vegas.Language", "Vegas.Source"),
            "Vegas.Source": ("Vegas.EventGraph", "Vegas.Pending", "Vegas.Language"),
            "Vegas.EventGraph": ("Vegas.Source", "Vegas.Pending", "Vegas.Compile"),
            "Vegas.Pending": ("Vegas.Source", "Vegas.Compile", "Vegas.Game"),
            "Vegas.Compile": ("Vegas.Pending", "Vegas.Language"),
            "Vegas.Game": ("Vegas.Language",),
            "Vegas.Language": ("Vegas.Pending",),
        }
        for layer, dependencies in forbidden.items():
            for dependency in dependencies:
                with self.subTest(layer=layer, dependency=dependency), \
                        tempfile.TemporaryDirectory() as directory:
                    root = self.fixture(directory, {
                        "Vegas": f"import {layer}.Example",
                        f"{layer}.Example": f"import {dependency}.Example",
                        f"{dependency}.Example": "",
                    })
                    expected = f"{layer} imports outside its layer contract: {dependency}.Example"
                    self.assertTrue(any(expected in error for error in CHECKER.check(root)))

    def test_semantic_layers_accept_the_intended_compilation_tower(self):
        with tempfile.TemporaryDirectory() as directory:
            modules = {"Vegas": "import " + " ".join(
                f"{layer}.Example" for layer in CHECKER.VEGAS_LAYERS)}
            for layer, allowed in CHECKER.VEGAS_LAYERS.items():
                modules[f"{layer}.Example"] = "\n".join(
                    f"import {dependency}.Example" for dependency in allowed if dependency != layer)
            root = self.fixture(directory, modules)
            self.assertEqual(CHECKER.check(root), [])

    def test_unclassified_vegas_top_level_layer_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Experimental.Widget",
                "Vegas.Experimental.Widget": "",
            })
            errors = CHECKER.check(root)
            self.assertTrue(any(
                "unclassified Vegas top-level layer Vegas.Experimental" in error
                for error in errors
            ))

    def test_umbrella_import_cannot_bypass_a_layer_contract(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.EventGraph.Example",
                "Vegas.EventGraph.Example": "import Vegas",
            })
            self.assertTrue(any("Vegas.EventGraph imports outside its layer contract: Vegas" in error
                                for error in CHECKER.check(root)))

    def test_test_reachability_does_not_mask_incomplete_aggregator(self):
        for layer in ("Vegas.EventGraph", "Vegas.Pending", "Vegas.Game", "Vegas.Expr", "Vegas.Language"):
            with self.subTest(layer=layer), tempfile.TemporaryDirectory() as directory:
                root = self.fixture(directory, {
                    "Vegas": f"import {layer}", layer: "",
                    f"{layer}.Adapter": "", "VegasTests": f"import {layer}.Adapter",
                })
                errors = CHECKER.check(root)
                self.assertTrue(any(f"absent from {layer} aggregator" in error for error in errors))
                self.assertFalse(any("unreachable" in error for error in errors))

    def test_all_default_targets_are_followed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "", "VegasTests": "import Vegas",
                "Paper": "import Vegas Paper.Extra", "Paper.Extra": "import Vegas",
            })
            self.assertEqual(CHECKER.check(root), [])

    def test_overlapping_libraries_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {"Vegas": "import Vegas.Foundation", "Vegas.Foundation": ""},
                                '[[lean_lib]]\nname = "Duplicate"\nroots = ["Vegas.Foundation"]\n')
            self.assertTrue(any("belongs to both" in error for error in CHECKER.check(root)))

    def test_two_layer_cycle_reports_import_witnesses(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Alpha.One Vegas.Beta.Two",
                "Vegas.Alpha.One": "import Vegas.Beta.One",
                "Vegas.Alpha.Two": "",
                "Vegas.Beta.One": "",
                "Vegas.Beta.Two": "import Vegas.Alpha.Two",
            })
            errors = CHECKER.check(root)
            report = next(error for error in errors if "sibling layer import cycle" in error)
            self.assertIn("Vegas.Alpha.One imports Vegas.Beta.One", report)
            self.assertIn("Vegas.Beta.Two imports Vegas.Alpha.Two", report)

    def test_three_module_cycle_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Foundation.A",
                "Vegas.Foundation.A": "import Vegas.Foundation.B",
                "Vegas.Foundation.B": "import Vegas.Foundation.C",
                "Vegas.Foundation.C": "import Vegas.Foundation.A",
            })
            errors = CHECKER.check(root)
            report = next(error for error in errors if "local module import cycle" in error)
            self.assertIn("Vegas.Foundation.A imports Vegas.Foundation.B", report)
            self.assertIn("Vegas.Foundation.C imports Vegas.Foundation.A", report)

    def test_acyclic_diamond_is_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Game.Top",
                "Vegas.Game.Top": "import Vegas.Game.Left Vegas.Game.Right",
                "Vegas.Game.Left": "import Vegas.Game.Bottom",
                "Vegas.Game.Right": "import Vegas.Game.Bottom",
                "Vegas.Game.Bottom": "",
            })
            self.assertEqual(CHECKER.check(root), [])

    def test_aggregators_nested_siblings_and_external_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Game Mathlib.Data.Nat.Basic",
                "Vegas.Game": "import Vegas.Game.Basic Vegas.Game.Deep.Left.A "
                              "Vegas.Game.Deep.Right.B",
                "Vegas.Game.Basic": "",
                "Vegas.Game.Deep.Left.A": "import Vegas.Game.Shared.Value",
                "Vegas.Game.Deep.Right.B": "import Vegas.Game.Deep.Left.A",
                "Vegas.Game.Shared.Value": "",
            })
            self.assertEqual(CHECKER.check(root), [])

    def test_three_layer_cycle_with_acyclic_module_graph(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Alpha.A Vegas.Beta.B Vegas.Gamma.C",
                "Vegas.Alpha.A": "import Vegas.Beta.Leaf",
                "Vegas.Beta.B": "import Vegas.Gamma.Leaf",
                "Vegas.Beta.Leaf": "",
                "Vegas.Gamma.C": "import Vegas.Alpha.Leaf",
                "Vegas.Gamma.Leaf": "",
                "Vegas.Alpha.Leaf": "",
            })
            errors = CHECKER.check(root)
            self.assertFalse(any("local module import cycle" in error for error in errors))
            self.assertTrue(any("Vegas.Alpha -> Vegas.Beta -> Vegas.Gamma -> Vegas.Alpha"
                                in error for error in errors))

    def test_nested_sibling_cycle_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Game",
                "Vegas.Game": "import Vegas.Game.Deep.Left.A Vegas.Game.Deep.Right.B",
                "Vegas.Game.Deep.Left.A": "import Vegas.Game.Deep.Right.Leaf",
                "Vegas.Game.Deep.Left.Leaf": "",
                "Vegas.Game.Deep.Right.B": "import Vegas.Game.Deep.Left.Leaf",
                "Vegas.Game.Deep.Right.Leaf": "",
            })
            errors = CHECKER.check(root)
            self.assertTrue(any("sibling layer import cycle under Vegas.Game.Deep" in error
                                for error in errors))


if __name__ == "__main__":
    unittest.main()
