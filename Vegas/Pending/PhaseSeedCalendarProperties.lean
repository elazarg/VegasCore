/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedCalendar
import Vegas.Pending.PhaseSeedFreshness
import Interaction.ReactiveAddressedFreshSeed

/-! # Original local laws at actual fresh phase namespaces

The concrete all-event request planner cannot read a seed from any namespace
other than the current one. Actual retry and phase transitions therefore make
the existing unread-seed law apply to the newly installed address.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The concrete planner never queries a retired or not-yet-installed namespace. -/
theorem request_ne_of_namespace (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (selected : PhaseSeedAddress graph) (past : List (app).EnvironmentEntry)
    (view : (app).EnvironmentView) (different : selected.1.attempt ≠ view.application.attempt)
    (rest : RestSeed) :
    ((controller runtime leaks delay bound priority).request rest past view).map Prod.fst ≠
      some selected := by
  intro requested
  cases chosen : selectOpen runtime leaks (replayClosed runtime leaks priority rest past)
      view (priority rest past view) with
  | none =>
      simp only [controller, chosen, Option.bind_none, Option.map_none] at requested
      cases requested
  | some coordinate =>
      cases acting : graph.actor? coordinate.1.event with
      | none =>
          simp only [controller, chosen, Option.bind_some, acting, Option.map_none] at requested
          cases requested
      | some owner =>
          have same : coordinate = selected := by
            simpa only [controller, chosen, Option.bind_some, acting, Option.map_some,
              Option.some.injEq] using requested
          subst coordinate
          have openMember := selectOpen_mem runtime leaks chosen
          obtain ⟨owner, ready⟩ := (PhaseSeedScheduler.mem_eligible runtime leaks _ _).mp
            (Finset.mem_filter.mp openMember).1
          exact different ready.1

/-- Replacing an opening's declared value or evidence preserves the actual
calendar command, including which immutable envelope identifier it includes. -/
theorem reply_opening_raw (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (elapsed : Nat) (clocks : List Nat)
    (before after : List (Nat × Message Player (CommitAttemptPacket graph)))
    (attempt : CommitAttemptId) (clock : Nat) (identifier : MessageId Player)
    (event : graph.EventId) (handle : Handle graph) (first second : Raw L)
    (firstEvidence secondEvidence : Option (OpeningFact graph))
    (token : Option (ReadinessToken graph)) :
    reply runtime leaks delay bound coordinate seed
      (PhaseSeedInput.operational coordinate.1.attempt
        ⟨elapsed, clocks, before ++
          [(clock, ⟨identifier, ⟨attempt, ⟨.opening event handle first, firstEvidence, token⟩⟩⟩)] ++
            after⟩) =
      reply runtime leaks delay bound coordinate seed
        (PhaseSeedInput.operational coordinate.1.attempt
          ⟨elapsed, clocks, before ++
            [(clock, ⟨identifier,
              ⟨attempt, ⟨.opening event handle second, secondEvidence, token⟩⟩⟩)] ++
              after⟩) := by
  have same := PhaseSeedInput.operationalEmission_opening coordinate.1.attempt attempt clock
    identifier event handle first second firstEvidence secondEvidence token
  simpa only [PhaseSeedInput.operational, List.map_append, List.map_cons, List.map_nil] using
    congrArg (fun emission => reply runtime leaks delay bound coordinate seed
      ⟨elapsed, clocks,
        before.map (PhaseSeedInput.operationalEmission coordinate.1.attempt) ++ [emission] ++
          after.map (PhaseSeedInput.operationalEmission coordinate.1.attempt)⟩) same

omit [DecidableEq Player] in
/-- The clocked local activation log prevents a second activation at the same
relative tick, independently of hidden seed values or handle choices. -/
theorem decision_ne_activation_of_recorded (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (input : PhaseSeedOperationalInput graph) (recorded : input.elapsed ∈ input.activationClocks) :
    decision runtime delay bound coordinate seed input ≠ .activation := by
  unfold decision
  split
  · decide
  · rw [ite_eq_right (fun ready => ready.2 recorded)]
    dsimp only
    split <;> (intro same; cases same)

omit [DecidableEq Player] in
/-- At its actual deadline every seed prescribes expiry of its own address. -/
theorem decision_deadline (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (input : PhaseSeedOperationalInput graph)
    (late : runtime.deadline coordinate.1.event ≤ input.elapsed) :
    decision runtime delay bound coordinate seed input = .expiry := by
  exact ite_eq_left late

/-- An actual namespace-changing environment move leaves every newly addressed
seed at its original local law before its first query. The complete remainder
retains the old seeds, voided observations, and original remainder randomness. -/
theorem posterior_after_namespace_change (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (laws : PhaseSeedAddress graph → PMF (Seed runtime delay)) (restLaw : PMF RestSeed)
    (execution next : (app).Execution) (command : (app).Command)
    (valid : PhaseSeedFreshness.NamespacePast runtime leaks execution)
    (reached : next ∈ (execution.environmentStep app command).support)
    (different : execution.application.attempt ≠ next.application.attempt)
    (selected : PhaseSeedAddress graph) (current : selected.1.attempt = next.application.attempt) :
    ∃ updated : (side : Bool) → PMF
        (ReactiveApplication.AddressedScheduler.SplitSeed
          (LocalSeed := Seed runtime delay) (RestSeed := RestSeed) selected side),
      ((app).schedulerMixture
        (independentProduct
          (ReactiveApplication.AddressedScheduler.splitLaws laws restLaw selected))
        (fun values before view => PMF.pure
          ((controller runtime leaks delay bound priority).splitChoose selected
            values before view))).posterior next.environmentRecall = independentProduct updated ∧
          updated false = laws selected := by
  apply (controller runtime leaks delay bound priority).posterior_before_request
  intro before entry recordedPrefix rest
  have member : entry ∈ next.environmentRecall := recordedPrefix.subset (by simp)
  have fresh := PhaseSeedFreshness.fresh_after_environment runtime leaks execution next command
    valid reached different entry member
  apply request_ne_of_namespace runtime leaks delay bound priority selected before entry.beforeView
  rwa [current]

end Vegas.EventGraphRuntime.PhaseSeedCalendar
