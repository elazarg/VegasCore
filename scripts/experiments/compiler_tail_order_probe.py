"""Check six existing-tail-lemma substitutions without editing Lean source.

Requires the ordinary project build. The complete two consumer modules are
checked with the central Lake options, in a temporary directory.
"""

import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
SETUP = ROOT / ".lake/build-stable/ir/GameTheoryExtensions/Analysis/Protocol/PublicScheduling.setup.json"
SPEC = importlib.util.spec_from_file_location("compiler_probe_defs", ROOT / "lean-defs.py")
DEFS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DEFS)


def surface(text):
    lines = []
    for block in DEFS.parse_blocks(text.splitlines()):
        processed = DEFS.classify_and_process(block)
        if processed is not None:
            lines.extend(processed)
    return re.sub(r"\s+", " ", "\n".join(lines)).strip()


def candidates():
    source = ROOT / "Vegas/Compile/EventGraphLaw.lean"
    original = source.read_text(encoding="utf-8")
    pattern = (r"\(by\n\s+intro readName cell source remaining\n"
               r"\s+cases source with\n\s+\| here =>\n.*?\n"
               r"\s+\| there source => exact refsBefore source \(Fin.succ remaining\)\)")
    changed, count = re.subn(pattern,
        "(refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl)",
        original, flags=re.S)
    if count != 3:
        raise RuntimeError(f"{source.name}: expected three candidate sites, found {count}")
    yield "CompilerTailLaw", original, changed

    source = ROOT / "Vegas/Compile/EventGraphPolicyAlignment.lean"
    original = source.read_text(encoding="utf-8")
    pattern = (r"(have tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by\n)"
               r"\s+intro readName cell source remaining\n\s+cases source with\n"
               r"\s+\| here =>\n.*?\n"
               r"\s+\| there source => exact refsBefore source \(Fin.succ remaining\)")
    changed, count = re.subn(pattern,
        r"\1          exact refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl",
        original, flags=re.S)
    if count != 3:
        raise RuntimeError(f"{source.name}: expected three candidate sites, found {count}")
    yield "CompilerTailPolicy", original, changed


def main():
    setup = json.loads(SETUP.read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory(prefix="vegas-compiler-tail-") as directory:
        for name, original, changed in candidates():
            if surface(original) != surface(changed):
                raise RuntimeError(name + ": candidate changes the declaration surface")
            source = Path(directory) / (name + ".lean")
            configuration = source.with_suffix(".setup.json")
            source.write_text(changed, encoding="utf-8")
            configuration.write_text(json.dumps({**setup, "name": "ProofReview." + name}),
                                     encoding="utf-8")
            print("Checking " + name, flush=True)
            result = subprocess.run(["lake", "env", "lean", "--setup", str(configuration),
                                     str(source)], cwd=ROOT)
            if result.returncode:
                return result.returncode
            saving = len(original.splitlines()) - len(changed.splitlines())
            print(f"PASS {name}: {saving} fewer physical lines", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
