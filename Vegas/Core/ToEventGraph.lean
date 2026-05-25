import Vegas.Core.ToEventGraph.Checkpoint
import Vegas.Core.ToEventGraph.RoundView
import Vegas.Core.ToEventGraph.FiniteMachine
import Vegas.Core.ToEventGraph.SourceAdequacy
import Vegas.Core.ToEventGraph.Kuhn
import Vegas.Core.ToEventGraph.Games
import Vegas.Core.ToEventGraph.SolutionConcepts
import Vegas.Core.ToEventGraph.Transport

/-!
# Core-to-event-graph elaboration

Checked Vegas programs compile directly to canonical event graphs with numeric
field and node ids.  Strategic game construction additionally attaches an
explicit checkpoint presentation policy.
-/
