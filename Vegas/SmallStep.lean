import Vegas.SmallStep.Defs
import Vegas.SmallStep.Agreement
import Vegas.SmallStep.Properties

/-!
# Public entrypoint for Vegas small-step semantics

This module collects the raw `FDist`-valued small-step semantics for Vegas.
The layer is intentionally raw: it runs against an
`OmniscientOperationalProfile` over neutral `World`s from `Vegas.Config`.
Checked, legal, PMF-valued one-step execution is exposed from
`Vegas.FOSG.SmallStep`.

Main user-facing declarations:

* `SmallStep.Step`: one labelled probabilistic transition from a nonterminal
  world.
* `SmallStep.StepSupport`: a positive-mass labelled one-step target.
* `SmallStep.Steps`: qualitative multi-step reachability through supported
  edges. `Steps` deliberately carries no numeric mass; weights live on
  `terminalPathDist`.
* `SmallStep.runSmallStep_eq_outcomeDist`: the raw small-step evaluator is the
  canonical `outcomeDist` packaged over worlds.
* `SmallStep.step_bind_runSmallStep`: one raw step followed by the evaluator
  preserves the source outcome value.
* `SmallStep.labelDist_eq_traceDist_map_traceLabels`: complete small-step
  label runs are the trace distribution projected to labels.
* `SmallStep.labelDist_apply_eq_traceLabel_sum`: pointwise label mass is the
  sum of weights of traces projecting to that label list.
* `SmallStep.terminalPathDist`: finite weighted enumeration of terminal
  labelled paths.
* `SmallStep.labelDist_apply_eq_terminalPath_sum`: pointwise label mass is the
  sum of masses of enumerated terminal paths with that label list.
* `SmallStep.terminalPathDist_support_terminal_steps`: every enumerated path
  is terminal and has a `Steps` witness.
* `SmallStep.mem_terminalPathDist_iff_terminal_steps`: terminal enumerated
  paths are exactly terminal `Steps` paths.
* `SmallStep.exists_terminal_steps_of_pos_weight_trace`: every positive-weight
  trace gives a terminal `Steps` path with the same labels.
* `SmallStep.progress`, `SmallStep.step_functional`, and syntax-step bounds:
  basic operational sanity properties.
* `SmallStep.runSmallStep_comm_commit` and
  `SmallStep.runSmallStep_comm_reveal`: small-step evaluator forms of the
  adjacent scheduler/permutation commute theorems.
-/
