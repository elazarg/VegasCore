import Vegas.MAID.Backend
import Vegas.MAID.Compile
import Vegas.MAID.Fold
import Vegas.MAID.Correctness
import Vegas.MAID.Strategic
import Vegas.MAID.PureBridge
import Vegas.MAID.PerfectRecall
import Vegas.MAID.Reflection
import Vegas.MAID.Kuhn
import Vegas.MAID.VegasMAID
import Vegas.MAID.CompileV
import Vegas.MAID.DefsV
import Vegas.MAID.PerfectRecallV
import Vegas.MAID.BridgeV
import Vegas.MAID.KuhnV

/-!
# Vegas MAID backend

Main entrypoint for the MAID backend: backend assumptions, compilation,
fold-based evaluation, correctness theorems, pure bridge, perfect recall,
policy reflection, and the Vegas Kuhn theorem.

Includes VegasMAID factored-observation path (experimental):
VegasMAID.lean, CompileV.lean, DefsV.lean, BridgeV.lean, PerfectRecallV.lean, KuhnV.lean.
-/
