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

The point of the file is that it fails to compile if a claim stops being true,
stops being provable in the stated form, or is renamed out from under the prose.

Two directions, and only one of them is machine-checked.  *Everything here is
proved and axiom-pinned* — that the build enforces, and it is what licenses
citing an entry.  *Everything the paper claims appears here* is a manual
obligation this repository cannot verify, since the prose is not tracked in it.
Reviewers have found gaps in that direction before: perfect recall, bounded
horizon, and the arena's status as a defined rather than translated FOSG were all
asserted in prose while missing here.  They are listed now.  Treat an absent
claim as unbacked until checked against this file, not as evidence of anything.

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
open GameTheory.Math.Probability
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

/-- **What a commit writes does not depend on the configuration**
(paper: `thm:write-determinacy`).

Two availability witnesses for the same commit action, at two arbitrary
configurations, write the same typed value.

This is the operational content behind `schedule_confluence`, and it is what
that theorem needs in order to say anything about execution. Permutation
invariance holds of a *fixed* assignment of node values; using it on a real
round requires that the round have a fixed assignment, which is not automatic.
`CommitAvailable` is `Nonempty (CommitStep ..)`, the protocol layer picks a
witness with `Classical.choice`, and the proposition it picks from mentions the
configuration — so a priori the value written at a node could depend on which
peers ran first, and reordering would not be a permutation of one assignment at
all.

It cannot. A step's row is pinned by `row_get`, its guard by `sem_eq` given the
row, and its value by `value_ok` given the guard: reading the committed value at
the guard's type is a function, not a choice. The configuration appears only in
`ready`, `env` and `guard_ok` — in *whether* the step exists, never in what it
writes. So the noncomputable selection is a selection among witnesses that all
agree on the one thing the semantics reads off them. -/
theorem commit_writes_are_configuration_independent
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : EventGraph.Graph Player L} {left right : EventGraph.Config G}
    {who : Player} {action : EventGraph.CommitAction G who}
    (stepLeft : EventGraph.CommitStep G left who action)
    (stepRight : EventGraph.CommitStep G right who action) :
    (⟨stepLeft.guard.ty, stepLeft.value⟩ : EventGraph.TypedValue L) =
      ⟨stepRight.guard.ty, stepRight.value⟩ :=
  EventGraph.CommitStep.written_eq stepLeft stepRight

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

/-! ## Game extraction

The strategic object a checked program denotes, and the two structural facts
every downstream equilibrium result depends on.  Both were claimed in prose
before being listed here, which is exactly the failure this file exists to
prevent. -/

/-- **Compiled information has perfect recall** (paper: `thm:perfect-recall`).

A player's information state remembers its own earlier information and actions,
while abstracting from event ordering that does not concern it.

This is the hypothesis the Kuhn correspondence below runs on: without it
behavioral and mixed presentations are not interchangeable, and the Nash
transport in `kuhn_behavioral_to_mixedPure` does not hold. -/
theorem compiled_perfect_recall
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : WFProgram Player L) :
    (Machine.compile program).information.PerfectRecall :=
  (Machine.compile program).perfectRecall

/-- **Compiled execution has a bounded horizon** (paper: `thm:bounded`).

The graph's node count bounds every strategy's play length uniformly. Finiteness
here is structural rather than assumed: a Vegas program is a finite graph, and
each step strictly grows the completed set.

Boundedness is what makes the extracted game a *finite* object, so the
equilibrium notions below are the finite ones. -/
theorem compiled_bounded_horizon
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : WFProgram Player L) :
    (Machine.compile program).execution.BoundedHorizon
      (Machine.compile program).graph.nodeCount :=
  (Machine.compile program).boundedHorizon

/-- **The extracted arena is a bounded stochastic game** (paper: `thm:arena`).

The `Game` a checked program denotes carries its own horizon proof, so the
strategic view is bounded by construction rather than by a side condition a
consumer must re-establish.

Note what this is not. The arena is *defined* as a first-order stochastic game
in `Vegas.Game`; there is no separate proved translation from a native frontier
game into the FOSG interface, and prose describing one would be wrong. The
FOSG-to-extensive-form results the paper leans on are `GameTheory`'s, not this
development's, and belong to that library in any attribution. -/
theorem extracted_arena_is_bounded
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (program : WFProgram Player L) [FiniteDomains program] :
    program.game.arena.execution.BoundedHorizon program.game.horizon :=
  program.game.bounded

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

/-- **A compiled strategic round is atomic** (paper: `thm:atomic`).

At a strategic checkpoint with no ready internal work, the round's successor is
a point mass determined by the joint packet alone. The whole frontier is applied
as one action.

This is what the compiler does *instead of* serializing, and it is the reason
the scheduling results below apply to it only vacuously. There is no scheduler
coordinate in this protocol to enforce, restrict, or reason about: a schedule is
not chosen, so it cannot be observed, and no strategy can condition on one. That
is strictly stronger than `enforced_schedule_makes_scheduler_inert`, which
neutralizes a scheduler that exists.

The canonical node order inside `applyFrontier` is therefore an implementation
detail rather than a semantic commitment — it is invisible at this interface,
which exposes only the packet and the resulting configuration.

What this does **not** say is that a serialized runtime would be equivalent. It
would not: `order_aware_deviations_exist` shows a runtime publishing the
realized order admits a policy conditioning on it, one that no schedule-free
policy induces. That result is stated over an abstract
`ScheduledSystem`, and connecting them to a *compiled* Vegas program — showing
this specific atomicity is what averts that specific failure — is not yet
mechanized. The two halves are proved; the bridge between them is prose. -/
theorem compiled_round_is_atomic
    {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
    (G : EventGraph.Graph Player L) (hwf : G.WF) (hguards : EventGraph.GuardLive G)
    (state : EventGraph.ReachableConfig G)
    (legal : { joint : ∀ who, Option (EventGraph.FrontierAction G who) //
      (EventGraph.toExecutionProtocol G hwf hguards).Legal state joint })
    (noInternal : EventGraph.readyInternalNodes G state.1 = ∅) :
    (EventGraph.toExecutionProtocol G hwf hguards).step state legal =
      FinDist.pure (EventGraph.applyFrontier G state legal.1) :=
  EventGraph.toExecutionProtocol_step_eq_pure_applyFrontier
    G hwf hguards state legal noInternal

/-! ## Scheduling -/

/-- **Confluence of effects is not invisibility of order.**

Two joint submissions scheduling different orders induce different successor
laws, *whatever the underlying state machine does* — in particular even when the
two orders have identical effects, so the underlying state law is
schedule-invariant.

A schedule-invariance result about a state machine constrains what the machine
computes; it says nothing about what a participant observes. Only a statement
about the protocol state does, and that requires the realized order to be part
of that state rather than quotiented out of it.

`Vegas.coin_step_ne` witnesses that this is not vacuous, in the most extreme
case available: a system in which every action is the identity, so effects
commute maximally, and two schedules remain distinguishable.

Scope. The order published here is the *settled* one, common knowledge once a
round is on chain — the reading a public signal carries in an information model.
In-flight submissions are visible to some observers but are **not** common
knowledge, so they cannot be modelled as a public signal at all, and this
development assumes no participant observes a submission before it is applied.
Front-running is outside the model. -/
theorem schedule_is_observable
    {ι : Type} (sys : ScheduledSystem ι)
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (horder : sys.scheduledOrder left.1 ≠ sys.scheduledOrder right.1) :
    sys.toExecutionProtocol.step state left ≠
      sys.toExecutionProtocol.step state right :=
  sys.step_ne_of_order_ne horder

/-- **The order-oblivious deviation class is proper.**

A policy is *order-oblivious* when the schedule cannot change what it does. That
restricts what a participant reads, never what it can express, so the class
contains every policy a schedule-free source could offer
(`liftPolicy_orderOblivious`).

It is nonetheless a proper subclass. `Vegas.coinOrderAware` acts differently at
two histories that agree on every public view and differ only in how a round was
ordered, over a system whose actions are all the identity.

This is the obstruction to back-translation, and it says what shape the
remaining work has: adequacy against order-oblivious deviations does not extend
to adequacy against arbitrary ones, because the arbitrary ones have no source
counterpart to translate back to. -/
theorem order_aware_deviations_exist (i : Fin 2) :
    ¬ Vegas.coinSystem.OrderOblivious (Vegas.coinOrderAware i) :=
  Vegas.coinOrderAware_not_orderOblivious i

/-- **An order-enforcing runtime makes the scheduler strategically inert.**

Two legal joint submissions agreeing on every player's submission induce the
same successor law, whatever the scheduler submitted. So under a runtime that
accepts one order per view, the scheduler cannot influence the outcome at all.

This matters because compiling to a scheduled runtime adds a participant the
source program does not have, whose payoff is nowhere in that program and cannot
be inferred from it. There is no honest way to assume a miner's incentives.
Enforcement makes them *irrelevant* instead — a property of the emitted
artifact, which a compiler can establish rather than assume.

Restricting attention to order-oblivious play would not do this. Equilibrium
quantifies over the deviations a participant has *available*, so a class of
well-behaved policies cannot be imposed by fiat: such a restriction describes a
profile, not an equilibrium. Enforcement removes the availability.

Enforcement is a dial, not a default. `schedules` is a field of the system, so
an artifact is permissive or enforcing by construction and `EnforcesOrder` is a
hypothesis here rather than a standing assumption. A developer wanting no
order-sensitive guarantee keeps the permissive runtime's parallelism and this
result simply does not apply; one who wants the guarantee pays for exactly it.

Scope: enforcement removes *order* as a channel, not every channel. Timing —
block height, elapsed time, who was slow — remains public and is not modelled
here at all, and in-flight visibility is excluded by a separate assumption. -/
theorem enforced_schedule_makes_scheduler_inert
    {ι : Type} (sys : ScheduledSystem ι) (henforce : sys.EnforcesOrder)
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (hplayers : ∀ i, left.1 (.player i) = right.1 (.player i)) :
    sys.toExecutionProtocol.step state left =
      sys.toExecutionProtocol.step state right :=
  sys.step_eq_of_enforcesOrder henforce hplayers

/-- **Commuting effects make the scheduler payoff-inert without enforcing an
order.**

Two legal joint submissions agreeing on every player's submission reach the same
law over *underlying states*, whatever the scheduler submitted — provided every
order the runtime accepts has the same effect.

This is the cheaper of the two answers to an order-aware deviation. Enforcement
makes such a deviation unavailable; commutation lets it stay available and shows
it gains nothing. The second suffices because equilibrium asks of each available
deviation only that it not improve on the equilibrium payoff, so a deviation
that exists and never pays is no threat — and there is then nothing to
back-translate.

What it buys is strictly less than enforcement, and the gap is the point.
Enforcement determines the whole successor law, log included, so no observation
separates two schedules. Commutation determines only the base state: the log
still differs, so a payoff that reads the log still sees a difference.
Payoff-irrelevance is therefore commutation *plus* a schedule-blind game, and
that second half is a condition on the game, not on the runtime.

Neither discipline covers a scheduler that reacts to what it is ordering. Both
quantify over a fixed joint submission, which is this model's standing
assumption that the scheduler commits without seeing the round's submissions.
Front-running is a different system, not a corner of this one. -/
theorem commuting_effects_make_scheduler_payoff_inert
    {ι : Type} (sys : ScheduledSystem ι) (hcommute : sys.EffectsCommute)
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (hplayers : ∀ i, left.1 (.player i) = right.1 (.player i)) :
    (sys.toExecutionProtocol.step state left).map ScheduledSystem.State.base =
      (sys.toExecutionProtocol.step state right).map ScheduledSystem.State.base :=
  sys.step_base_eq_of_effectsCommute hcommute hplayers

/-- **The permissive tier is inhabited: order can be available, observable, and
still useless.**

For a runtime where two players each add to a running total and either order is
accepted: the runtime does *not* enforce an order; the two schedules are
genuinely distinguishable, inducing different successor laws because the log
records which happened; and the laws over totals nevertheless coincide.

All three at once is the claim. A developer who does not care about order keeps
the parallelism, an order-aware deviation remains expressible against them, and
a payoff reading the total is untouched by it. The witness is not degenerate:
the total genuinely moves, so commutation here is a fact about addition rather
than about nothing happening. -/
theorem order_available_observable_and_useless :
    ¬ counterSystem.EnforcesOrder ∧
      ∀ state : counterSystem.State,
        counterSystem.toExecutionProtocol.step state (counterZeroFirst state) ≠
            counterSystem.toExecutionProtocol.step state (counterOneFirst state) ∧
          (counterSystem.toExecutionProtocol.step state
              (counterZeroFirst state)).map ScheduledSystem.State.base =
            (counterSystem.toExecutionProtocol.step state
              (counterOneFirst state)).map ScheduledSystem.State.base :=
  ⟨counter_not_enforcesOrder,
    fun state => ⟨counter_step_ne state, counter_step_base_eq state⟩⟩

/-- **And the permissive tier has a boundary.**

For a runtime where one player doubles a total and another adds to it, the two
accepted orders reach different totals, so `EffectsCommute` fails. The
hypothesis of `commuting_effects_make_scheduler_payoff_inert` is therefore a
real restriction rather than something every system satisfies, and a system in
this shape — two pending operations whose order changes the result, which is the
shape a public runtime actually has — is one where a preservation claim must pay
for `EnforcesOrder` instead of arguing that order does not matter. -/
theorem commutation_is_a_real_restriction : ¬ raceSystem.EffectsCommute :=
  race_not_effectsCommute

/-- **The protocol layer forbids sending nothing at all.**

At a legal joint submission every *active* player has submitted something:
`IsLegalJoint` reads `none` as "not active", so abstention is legal exactly when
a participant has nothing to do.

This is not a prohibition on declining. Declining, in Vegas, is a null *value*
rather than an absent submission: a surface `yield` lowers to a nullable sealed
commitment whose guard accepts `none` unconditionally, so `some Option.none` is
a legal submission, and the continuation — typed at `option b` and eliminated by
`isNone`/`getD` — must say what happens when a player takes it. The two are easy
to conflate because both are spelled `none`, and they are different: the second
is a transaction the program sees.

What the condition rules out is sending nothing whatsoever, which no public
runtime can prevent. The claim is recorded because it marks exactly where the
model is stronger than the runtime it describes. -/
theorem active_participation_is_forced
    {ι : Type} (sys : ScheduledSystem ι) {state : sys.State}
    (joint : { joint // sys.toExecutionProtocol.Legal state joint })
    (i : ι) (hactive : sys.active state.base i) :
    ∃ action, joint.1 (.player i) = some action := by
  have hlegal := joint.2.2 (.player i)
  cases hjoint : joint.1 (.player i) with
  | none => rw [hjoint] at hlegal; exact absurd hactive hlegal
  | some action => exact ⟨action, rfl⟩

/-- **Silence is inert, sometimes available, and not universally so.**

Three things at once. A round in which every player sends nothing leaves the
state where it was in *every* order, so the payoff to vanishing depends on the
state alone — the baseline a dominance argument compares against, needing no
`EffectsCommute` since inert actions commute with everything. The running-total
runtime affords silence. The doubling-and-adding one does not, every action
there moving the total, so `AllowsSilence` is a real hypothesis rather than
something every system satisfies.

Silence is the residual gap left by the source language's own way of declining.
A `yield`'s null submission is a transaction: the program sees it, continues,
and can slash a deposit on the spot. Silence is not, and `silence_inert` is why
— within the round nothing separates a silent player from one never asked, so a
protocol wanting to charge for it must measure elapsed time. That is what a
timeout is for, and why the deposit story needs a mechanism rather than a rule
saying players must reveal.

Not shown here: that silence fails to pay. That is a statement about payoffs,
which live a layer above this one. -/
theorem silence_is_inert_available_and_not_universal :
    (∀ {ι : Type} (sys : ScheduledSystem ι) (hsilent : sys.AllowsSilence)
        (order proposed : sys.Order) (state : sys.Base),
      sys.applyOrder (hsilent.allSilent proposed) order state = FinDist.pure state) ∧
    Nonempty counterSystem.AllowsSilence ∧ IsEmpty raceSystem.AllowsSilence :=
  ⟨fun _ hsilent order proposed state => hsilent.applyOrder_silent order proposed state,
    ⟨counter_allowsSilence⟩, race_no_silence⟩

/-- **Declining and silence are different, and ordered.**

Every runtime affording silence affords declining, by forgetting that the
submission was inert. The converse fails: the doubling-and-adding runtime lets a
player submit — every action is accepted — while no action there is inert, so
nobody can vanish without trace.

The two were conflated in this development because both wanted the spelling
`none`, and the error was not caught by types. They now have names.
*Declining* is `declineValue`, the null value a player submits to a nullable
commitment: `Expr.nullableCommitGuard` accepts it whatever the environment, the
continuation is typed at `option b` and must handle it, and the program may
charge for it on the spot. *Silence* is sending nothing, which
`active_participation_is_forced` shows the protocol layer forbids and no public
runtime can.

The gap between them is the room a protocol has to charge for declining, and it
is why a deposit is slashable against a decline directly but against silence
only through a timeout. -/
theorem declining_is_weaker_than_silence :
    (∀ (ι : Type) (sys : ScheduledSystem ι),
        sys.AllowsSilence → Nonempty sys.AllowsDeclining) ∧
      Nonempty raceSystem.AllowsDeclining ∧ IsEmpty raceSystem.AllowsSilence :=
  ⟨fun _ _ hsilent => ⟨hsilent.toAllowsDeclining⟩,
    ⟨race_allowsDeclining⟩, race_no_silence⟩

/-- **A nullable commitment can never be declined illegally.**

Whatever the environment, some submission satisfies the guard — namely
`declineValue`. So a surface `yield` is a form a player can never be stuck on,
and declining is a *source* strategy needing no back-translation.

The contrast is `commit`, whose payload `CommitPayloadTy` restricts to
non-nullable types: that form obliges a player to act, and its satisfiability is
an obligation discharged elsewhere rather than a theorem about the form. -/
theorem declining_is_always_live
    {P : Type} [DecidableEq P] {Γ : VCtx P simpleExpr}
    {x : VarId} {b : BaseTy} [DefaultVal b]
    (R : Expr ((x, b) :: eraseVCtx Γ) .bool) :
    ∀ env : Env Val (eraseVCtx Γ),
      ∃ a : Val (.option b),
        Vegas.evalGuard (Player := P) (L := simpleExpr)
          (Expr.nullableCommitGuard R) a env = true :=
  nullableCommitGuard_satisfiable R

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

/-- info: 'Vegas.Paper.commit_writes_are_configuration_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commit_writes_are_configuration_independent

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

/-- info: 'Vegas.Paper.compiled_perfect_recall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_perfect_recall

/-- info: 'Vegas.Paper.compiled_bounded_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_bounded_horizon

/-- info: 'Vegas.Paper.extracted_arena_is_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.extracted_arena_is_bounded

/-- info: 'Vegas.Paper.kuhn_mixedPure_to_behavioral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.kuhn_mixedPure_to_behavioral

/-- info: 'Vegas.Paper.compiled_round_is_atomic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_round_is_atomic

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

/-- info: 'Vegas.Paper.order_aware_deviations_exist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.order_aware_deviations_exist

/-- info: 'Vegas.Paper.enforced_schedule_makes_scheduler_inert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.enforced_schedule_makes_scheduler_inert

/-- info: 'Vegas.Paper.commuting_effects_make_scheduler_payoff_inert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commuting_effects_make_scheduler_payoff_inert

/-- info: 'Vegas.Paper.order_available_observable_and_useless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.order_available_observable_and_useless

/-- info: 'Vegas.Paper.commutation_is_a_real_restriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commutation_is_a_real_restriction

/-- info: 'Vegas.Paper.active_participation_is_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.active_participation_is_forced

/-- info: 'Vegas.Paper.silence_is_inert_available_and_not_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.silence_is_inert_available_and_not_universal

/-- info: 'Vegas.Paper.declining_is_weaker_than_silence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.declining_is_weaker_than_silence

/-- info: 'Vegas.Paper.declining_is_always_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.declining_is_always_live

end Paper

end Vegas
