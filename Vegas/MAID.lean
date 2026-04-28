import Vegas.MAID.Backend
import Vegas.MAID.Compile
import Vegas.MAID.VegasMAID
import Vegas.MAID.CompileLemmas
import Vegas.MAID.Defs
import Vegas.MAID.PerfectRecall
import Vegas.MAID.Bridge
import Vegas.MAID.Kuhn

/-!
# Vegas MAID backend

Main entrypoint for the MAID backend: backend assumptions, compilation,
perfect-recall metatheory, and the MAID-specific raw-program Kuhn theorem.

The public checked-program game-theoretic API lives outside this namespace.
In particular, the MAID theorem is not the final `WFProgram` theorem over
guard-legal Vegas strategy subtypes.
-/
