/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile
import Vegas.EventGraph
import Vegas.Game.Kuhn
import Vegas.Machine
import Vegas.Machine.Contract.SimpleEVMExprCorrect
import Vegas.Runtime
import Vegas.Scheduled

/-!
# Paper-facing claim surface

Every theorem the paper states, restated here **in full**, so that the
statement can be read and audited without chasing definitions through the
development.  Each proof is an immediate delegation to the theorem that does
the work; nothing is proved in this file.

The point of the file is that it fails to compile if a paper claim stops being
true, stops being provable in the stated form, or is renamed out from under the
prose.  A claim with no entry here is a claim the mechanization does not back.

Two conventions, both load-bearing:

* Statements are spelled out rather than abbreviated behind a definition, even
  where that makes them long.  A reader auditing the paper should not have to
  trust that some `Adequate P` abbreviation says what its name suggests.
* Delegations are one-liners.  If an entry ever needs real proof work, that
  work belongs in the module that owns the concept, not here.
-/

namespace Vegas

namespace Paper

open GameTheory
open EventGraph

/-! ## Source adequacy -/

/-- **Source-payoff adequacy** (paper: `thm:source-adequacy`).

Every terminal reachable machine state of a checked program reconstructs a
terminal source environment that the source program can actually reach, and in
which the compiled payoff code and the original source payoff expressions
evaluate to the same vector. -/
theorem source_payoff_adequacy
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (source : WFProgram Player L)
    (state : (Machine.compile source).State)
    (hterminal : (Machine.compile source).terminal state) :
    ∃ terminalEnv :
        VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env,
          cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx,
          env := terminalEnv,
          cont := .ret
            (ToEventGraph.compile source.core).sourcePayoffs } ∧
      evalPayoffs? (Machine.compile source).payoffs state.1.store =
        some (evalPayoffs
          (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) :=
  Machine.compile_sourceStar source state hterminal

/-! ## Event-graph structure -/

/-- **Schedule confluence** (paper: `thm:confluence`).

Completing a fixed assignment of node values along two orderings of the same
duplicate-free node list reaches the same configuration: independent events
commute, so the reached state depends on *which* nodes ran, not on the order
they ran in. -/
theorem schedule_confluence
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L} (cfg : Config G)
    (value : Fin G.nodeCount → TypedValue L)
    {left right : List (Fin G.nodeCount)}
    (hperm : List.Perm left right) (hnodup : left.Nodup) :
    cfg.scheduleComplete value left = cfg.scheduleComplete value right :=
  Config.scheduleComplete_perm cfg value hperm hnodup

/-- **Commit–reveal barrier** (paper: `thm:fence`).

A reveal node is ordered behind every source-earlier commit: such a commit is
a graph prerequisite of the reveal, so a ready reveal has all of them already
completed.

Deliberately graph-local.  It asserts nothing about cryptographic hiding, does
not force a reveal transaction to be sent, and does not suppress target-only
timing information. -/
theorem commit_reveal_barrier
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (G : Graph Player L)
    {node prior : Fin G.nodeCount}
    {event priorEvent : EventNode Player L} {source : Nat}
    {who : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some event)
    (hprior : G.nodes[prior]? = some priorEvent)
    (hlt : (prior : Nat) < (node : Nat))
    (hreveal : event.sem = .reveal source)
    (hcommit : priorEvent.sem = .commit who guard) :
    prior ∈ G.prereqs node :=
  G.prior_commit_mem_prereqs_of_reveal hnode hprior hlt hreveal hcommit

/-! ## Scheduling discipline

The compiler's choice of checkpoint policy is what decides whether the realized
order is a strategic degree of freedom.  These two entries are a genuine
separation, not a restatement: the sequential policy determines the
completed-node trajectory, and the permissive one provably does not. -/

/-- **The sequential schedule carries no information.**

Under `sequentialCheckpointPolicy`, checkpoints that have completed the same
nodes advance to checkpoints that have completed the same nodes — across
different runs and whatever values the players and nature wrote.  So the
completed-node trajectory is a function of the graph alone, and a target
strategy has no scheduler choice to condition on.

Scope, stated precisely because it is easy to overstate: this is a theorem
about `CheckpointPolicy`, and the compiled game is currently built by
`toExecutionProtocol`, which does **not** consume a checkpoint policy.  So this
does not yet license the order-free `PublicObservation` used by
`Machine.Program.observation`; connecting the two is open work. -/
theorem sequential_schedule_determined
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L}
    {srcLeft srcRight dstLeft dstRight : ReachableConfig G}
    (hsrc : srcLeft.1.done = srcRight.1.done)
    (hleft : (sequentialCheckpointPolicy G).allowed srcLeft dstLeft)
    (hright : (sequentialCheckpointPolicy G).allowed srcRight dstRight) :
    dstLeft.1.done = dstRight.1.done :=
  sequentialCheckpointPolicy_done_congr hsrc hleft hright

/-- **The permissive schedule does not.**

Wherever two distinct nodes are simultaneously ready,
`primitiveDownsetCheckpointPolicy` allows two checkpoints from one source whose
completed-node sets differ.  Under that policy the realized order is a real
scheduler choice, and on a public runtime it is observable — which is what
enlarges the target strategy carrier beyond `Info → Action`. -/
theorem permissive_schedule_not_determined
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    {src : ReachableConfig G} {left right : Fin G.nodeCount}
    (hne : left ≠ right)
    (hleft : Ready G src.1 left) (hright : Ready G src.1 right) :
    ∃ dstLeft dstRight : ReachableConfig G,
      (primitiveDownsetCheckpointPolicy G).allowed src dstLeft ∧
        (primitiveDownsetCheckpointPolicy G).allowed src dstRight ∧
          dstLeft.1.done ≠ dstRight.1.done :=
  primitiveDownsetCheckpointPolicy_done_not_determined hwf hguards hne
    hleft hright

/-! ## Code generation -/

/-- **Word code generation is correct.**

Compiled word-expression code pushes exactly the value its IR denotes and
leaves the rest of the stack untouched, for any variable-loading fragment that
is itself correct.

The arithmetic here is the machine's, not an idealization: `Val .word` is
`BitVec 256`, its `+`, `-` and `*` wrap modulo `2 ^ 256`, and the proof runs
against the executable interpreter `stepInstruction`.  In particular the
operand-order discipline is discharged rather than assumed — `SUB` reads its
minuend from the top of the stack, so `compile` emits its operands in the
opposite order from `ADD`, and the composition lemmas fix that per operation. -/
theorem word_codegen_correct
    {Γ : CtxSimple}
    (pre : Machine.Contract.EVM.BoolExprPrecondition)
    (maxStack : Nat)
    (variableCode : Machine.Contract.EVM.VariableCode Γ)
    (env : PlainEnv Γ)
    (hvariable :
      Machine.Contract.EVM.VariableCodeCorrect pre env variableCode)
    (source : Expr Γ .word) (code : Machine.Contract.EVM.Assembly)
    (hcompile :
      Machine.Contract.EVM.compileWordExpr? maxStack variableCode source
        = some code) :
    Machine.Contract.EVM.WordExprCorrect pre (evalExpr source env) code :=
  Machine.Contract.EVM.compileWordExpr?_correct pre maxStack variableCode env
    hvariable source code hcompile

/-- **Boolean guard code generation is correct.**

Whenever `compileBoolExpr?` accepts a source Boolean expression, the assembly it
emits pushes exactly that expression's canonical Boolean word.

This is the statement that matters for commit guards, since a guard is what a
player's proposed action is checked against.  It now covers guards that compare
*word arithmetic* — `x + y < z`, `x * y = z` — not only Boolean connectives,
because `BoolExprIR` carries `wordEqual` and `wordLess` over `WordExprIR`.

`VariableCodeCorrect` is one hypothesis for both types: a loading fragment must
push `encodeSimpleValue τ` of the variable's value, which is `encodeBool` at
`.bool` and the identity at `.word`. -/
theorem guard_codegen_correct
    {Γ : CtxSimple}
    (pre : Machine.Contract.EVM.BoolExprPrecondition)
    (maxStack : Nat)
    (variableCode : Machine.Contract.EVM.VariableCode Γ)
    (env : PlainEnv Γ)
    (hvariable :
      Machine.Contract.EVM.VariableCodeCorrect pre env variableCode)
    (source : Expr Γ .bool) (code : Machine.Contract.EVM.Assembly)
    (hcompile :
      Machine.Contract.EVM.compileBoolExpr? maxStack variableCode source
        = some code) :
    Machine.Contract.EVM.BoolExprCorrect pre (evalExpr source env) code :=
  Machine.Contract.EVM.compileBoolExpr?_correct pre variableCode env
    hvariable source code maxStack hcompile

/-! ## Strategy presentations -/

/-- **Frontier Kuhn correspondence, behavioral to mixed-pure**
(paper: `thm:kuhn`).

Every checked finite-domain program has a deviation-adequacy certificate from
its behavioral frontier game to its mixed-pure frontier game: a profile
translation preserving outcome laws, together with a back-translation matching
every unilateral target replacement. -/
theorem kuhn_behavioral_to_mixedPure
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : WFProgram Player L) [FiniteDomains program] :
    Nonempty
      (Runtime.DeviationAdequacy program.game.behavioral
        program.game.mixedPure) :=
  ⟨program.behavioralToMixedPureAdequacy⟩

/-- **Frontier Kuhn correspondence, mixed-pure to behavioral**
(paper: `thm:kuhn`, converse direction). -/
theorem kuhn_mixedPure_to_behavioral
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : WFProgram Player L) [FiniteDomains program] :
    Nonempty
      (Runtime.DeviationAdequacy program.game.mixedPure
        program.game.behavioral) :=
  ⟨program.mixedPureToBehavioralAdequacy⟩

/-! ## Scheduling -/

/-- **Confluence of effects is not invisibility of order.**

Two schedulers that choose different orders for the same submissions induce
different successor laws, *whatever the underlying state machine does* — in
particular even when the two orders have identical effects, so that the
underlying state law is schedule-invariant.

The distinction this draws is the one the development turns on. A
schedule-invariance result about a state machine constrains what the machine
computes; it says nothing about what a player observes. Only a statement about
the protocol state does, and that requires the realized order to be part of that
state rather than quotiented out of it.

`Vegas.idle_step_ne` witnesses that this is not vacuous, in the most extreme
case available: a system in which every action is the identity, so effects
commute maximally, and two schedulers are still distinguishable.

Scope. The order published here is the *settled* one, which is common knowledge
once a round is on chain — the reading a public signal carries in an information
model. In-flight submissions are visible to some observers but are **not**
common knowledge, so they cannot be modelled as a public signal at all, and this
development assumes no player observes a submission before it is applied.
Front-running is therefore outside the model. -/
theorem schedule_is_observable
    {ι : Type} (sys : ScheduledSystem ι)
    {left right : sys.Scheduler}
    {state : sys.State}
    {legalLeft : { joint // (sys.toExecutionProtocol left).Legal state joint }}
    {legalRight : { joint // (sys.toExecutionProtocol right).Legal state joint }}
    (hjoint : legalLeft.1 = legalRight.1)
    (horder : left state legalLeft.1 ≠ right state legalLeft.1) :
    (sys.toExecutionProtocol left).step state legalLeft ≠
      (sys.toExecutionProtocol right).step state legalRight :=
  sys.step_ne_of_order_ne hjoint horder

/-! ## Deviation adequacy -/

/-- **Utility preservation at compiled profiles** (paper: `lem:expected-utility`,
first equation). -/
theorem utility_preservation_honest
    {Player : Type} [DecidableEq Player]
    {source target : UtilityGame Player}
    (adequacy : Runtime.DeviationAdequacy source target)
    (profile : Profile source.form.sig) (who : Player) :
    expectedUtility target.utility who
        (target.form.play (adequacy.compileProfile profile)) =
      expectedUtility source.utility who (source.form.play profile) :=
  adequacy.expectedUtility_compileProfile profile who

/-- **Utility preservation under unilateral target deviation**
(paper: `lem:expected-utility`, second equation).

`replacement` ranges over the *whole* target strategy type, not only over
strategies in the image of `compileStrategy`.  That is what makes the
back-translation obligation non-vacuous. -/
theorem utility_preservation_deviation
    {Player : Type} [DecidableEq Player]
    {source target : UtilityGame Player}
    (adequacy : Runtime.DeviationAdequacy source target)
    (profile : Profile source.form.sig) (who : Player)
    (replacement : target.form.sig.Strategy who) :
    expectedUtility target.utility who
        (target.form.play
          (Profile.update (adequacy.compileProfile profile) who replacement)) =
      expectedUtility source.utility who
        (source.form.play
          (Profile.update profile who
            (adequacy.backtranslateStrategy who replacement))) :=
  adequacy.expectedUtility_deviation profile who replacement trivial

/-- **Nash equivalence relative to a deviation class.**

A compiled profile withstands every *considered* target deviation exactly when
the source profile withstands every source deviation.  The class is a parameter,
so the same theorem covers both tiers the development cares about: the honest
tier, where a player reads only what the source made visible, and the robust
tier below, where a player may read anything the target exposes.

Because `Considered` appears in the statement, a result about the honest tier
cannot be misread as a result about all strategies. -/
theorem nash_equivalence_against
    {Player : Type} [DecidableEq Player]
    {source target : UtilityGame Player}
    {Considered : (who : Player) → target.form.sig.Strategy who → Prop}
    (adequacy : Runtime.DeviationAdequacyOn source target Considered)
    (profile : Profile source.form.sig) :
    Runtime.IsNashAgainst target Considered (adequacy.compileProfile profile) ↔
      IsNash source.form (euPreference source.utility) profile :=
  adequacy.isNashAgainst_compileProfile_iff profile

/-- **Nash equivalence** (paper: `thm:nash-equivalence`).

A compiled profile is a target Nash equilibrium exactly when the source profile
is a source Nash equilibrium.  Preservation *and* reflection, at compiled
profiles, for every player of the shared player type — there is no restriction
to a subset of "joined" players. -/
theorem nash_equivalence
    {Player : Type} [DecidableEq Player]
    {source target : UtilityGame Player}
    (adequacy : Runtime.DeviationAdequacy source target)
    (profile : Profile source.form.sig) :
    IsNash target.form (euPreference target.utility)
        (adequacy.compileProfile profile) ↔
      IsNash source.form (euPreference source.utility) profile :=
  adequacy.isNash_compileProfile_iff profile


/-! ## Trusted base

Every claim above must rest on Lean's three standard axioms and nothing else.
These pins are the guard: `#print axioms` emits an info message, and
`#guard_msgs` turns a *different* message into a build error.  If a claim ever
acquires `sorryAx`, a `native_decide` kernel extension, or a bespoke axiom, the
build fails here rather than silently widening what the paper is trusting.

`whitespace := lax` because `#print axioms` wraps its list across lines. -/

/-- info: 'Vegas.Paper.source_payoff_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_payoff_adequacy

/-- info: 'Vegas.Paper.schedule_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.schedule_confluence

/-- info: 'Vegas.Paper.commit_reveal_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commit_reveal_barrier

/-- info: 'Vegas.Paper.sequential_schedule_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sequential_schedule_determined

/-- info: 'Vegas.Paper.permissive_schedule_not_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.permissive_schedule_not_determined

/-- info: 'Vegas.Paper.kuhn_behavioral_to_mixedPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.kuhn_behavioral_to_mixedPure

/-- info: 'Vegas.Paper.kuhn_mixedPure_to_behavioral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.kuhn_mixedPure_to_behavioral

/-- info: 'Vegas.Paper.utility_preservation_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.utility_preservation_honest

/-- info: 'Vegas.Paper.utility_preservation_deviation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.utility_preservation_deviation

/-- info: 'Vegas.Paper.nash_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.nash_equivalence

/-- info: 'Vegas.Paper.nash_equivalence_against' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.nash_equivalence_against

/-- info: 'Vegas.Paper.word_codegen_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.word_codegen_correct

/-- info: 'Vegas.Paper.guard_codegen_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.guard_codegen_correct

/-- info: 'Vegas.Paper.schedule_is_observable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.schedule_is_observable

end Paper

end Vegas
