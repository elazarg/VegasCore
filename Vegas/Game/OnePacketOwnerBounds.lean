module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketSwapFiberSum
public import Vegas.Game.OnePacketOwnerSwap
public import Vegas.Pending.ReactiveBoundedValues

@[expose] public section

/-! # The owner swap keeps the message bounds

Along every history of the one-packet game, every openable candidate in the
contract's catalogue is within the message bounds, when the bounds cover every
value of every initial binding input (`Vegas.candidate_mem_values_of_trace`).
Initially an openable candidate is the typed value of an initial binding input
of its owner. Afterwards a value becomes openable only when a submission of the
menu prepares it, and the menu admits only bounded opening data; freezing only
makes fresh candidates unopenable, and inclusion and environment service only
freeze.

Hence the owner swap between two views of one player at two histories of the
one-packet game keeps the message bounds (`Vegas.ownerSwap_bounded`): each pair
it transposes consists of two openable candidates of the views.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}

omit [IExpr.ResultTypes L] in
/-- A typed initial value makes openable only a value of a binding field. -/
private theorem openable_of_candidateOfValue (owner : Player)
    (kind : EventGraph.EventField Player L) (value : kind.Value) (raw : Raw L)
    (found : State.candidateOfValue owner kind value = .openable raw) :
    ∃ (inputOwner : Player) (payload : L.Ty) (typed : L.Val payload),
      kind = .binding inputOwner payload ∧ raw = ⟨payload, typed⟩ := by
  cases kind with
  | publicData | publication | privateInput => cases found
  | binding inputOwner payload =>
      simp only [State.candidateOfValue] at found
      split_ifs at found
      cases value with
      | failure => cases found
      | success typed => cases found; exact ⟨inputOwner, payload, typed, rfl, rfl⟩

variable {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- Every initial state of the supplied runtime has its openable candidates
within the bounds when the bounds cover the initial binding inputs. -/
private theorem candidateValues_initial (covers : bounds.CoversInputValues)
    (state : EventGraphRuntime.State (graph setup)) (member : state ∈ (initialLaw setup).support) :
    bounds.CandidateValues state := by
  rw [initialLaw, serviceInitialLaw, PMF.support_map] at member
  obtain ⟨initial, _, rfl⟩ := member
  rintro ⟨owner, slot⟩ raw found
  rw [EventGraphRuntime.State.initial_candidate] at found
  cases slot with
  | prepared serial => cases found
  | initial input =>
      obtain ⟨inputOwner, payload, typed, layoutEq, rfl⟩ :=
        openable_of_candidateOfValue owner _ _ raw found
      exact covers input inputOwner payload layoutEq typed

/-- A transposition of two values within the bounds keeps the bounds. -/
private theorem pairSwap_mem_values {pair : Option (Raw L × Raw L)}
    (within : ∀ left right, pair = some (left, right) →
      left ∈ bounds.values ∧ right ∈ bounds.values)
    {raw : Raw L} (member : raw ∈ bounds.values) :
    EventGraph.pairSwap pair raw ∈ bounds.values := by
  cases pair with
  | none => exact member
  | some pair =>
      rcases pair with ⟨left, right⟩
      obtain ⟨leftWithin, rightWithin⟩ := within left right rfl
      simp only [EventGraph.pairSwap]
      by_cases isLeft : raw = left
      · subst isLeft
        rw [@Equiv.swap_apply_left _ (fun a b => Classical.propDecidable (a = b))]
        exact rightWithin
      · by_cases isRight : raw = right
        · subst isRight
          rw [@Equiv.swap_apply_right _ (fun a b => Classical.propDecidable (a = b))]
          exact leftWithin
        · rw [@Equiv.swap_apply_of_ne_of_ne _ (fun a b => Classical.propDecidable (a = b)) _ _ _
            isLeft isRight]
          exact member

/-- **The owner swap keeps the bounds** when the openable candidates of both
views are within the bounds. -/
theorem ownerSwap_bounded_of_candidates (who : Player)
    (first second : EventGraphRuntime.PlayerView (graph setup))
    (firstWithin : ∀ slot raw, first.candidates slot = .openable raw → raw ∈ bounds.values)
    (secondWithin : ∀ slot raw, second.candidates slot = .openable raw → raw ∈ bounds.values) :
    ∀ handle raw, raw ∈ bounds.values →
      (ownerSwap who first second).raw handle raw ∈ bounds.values := by
  intro handle raw member
  change EventGraph.pairSwap (ownerHandlePairs who first second handle) raw ∈ _
  refine pairSwap_mem_values (fun left right paired => ?_) member
  unfold ownerHandlePairs at paired
  split_ifs at paired
  split at paired
  · rename_i firstLeft secondRight firstFound secondFound
    split_ifs at paired
    cases paired
    exact ⟨firstWithin _ _ firstFound, secondWithin _ _ secondFound⟩
  · cases paired

variable [Fintype Player]

variable (leaks bounds) in
/-- Openable candidates stay within the bounds along every one-packet response
and every environment step. -/
private theorem candidateValues_serviceInvariant :
    (bounds.onePacketMenu timeouts leaks).ServiceInvariant scheduler
      (fun execution => bounds.CandidateValues execution.application) where
  respond execution who action valid member :=
    bounds.candidateValues_respond timeouts leaks execution who action valid (by
      intro material transmitted
      have allowed := (bounds.menu_mem timeouts leaks who _ _ _).mp
        ((bounds.mem_onePacketActions timeouts leaks who _ _ _).mp member).1
      rw [transmitted] at allowed
      exact allowed.1.1.2)
  environment execution next command valid _ reached :=
    bounds.candidateValues_environment timeouts leaks execution next command valid reached

/-- **Openable candidates are within the bounds.** Along every history of the
one-packet game, every openable candidate of the catalogue is within the message
bounds, when the bounds cover every value of every initial binding input. -/
theorem candidate_mem_values_of_trace (covers : bounds.CoversInputValues)
    {control : (application setup timeouts leaks).Control}
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some control))
    {handle : Handle (graph setup)} {raw : Raw L}
    (found : control.execution.application.candidates.lookup handle = .openable raw) :
    raw ∈ bounds.values :=
  (candidateValues_serviceInvariant (timeouts := timeouts) leaks bounds).history (initialLaw setup)
    horizon
    (fun state member => candidateValues_initial covers state member) trace handle raw found

/-- **The owner swap between two views of one-packet histories keeps the
bounds.** For two histories of the one-packet game, the owner swap between the
views of `who` at their end states moves values within the message bounds, when
the bounds cover every value of every initial binding input. -/
theorem ownerSwap_bounded (covers : bounds.CoversInputValues) (who : Player)
    {firstControl secondControl : (application setup timeouts leaks).Control}
    (firstTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      (some firstControl))
    (secondTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      (some secondControl)) :
    ∀ handle raw, raw ∈ bounds.values →
      (ownerSwap who (firstControl.execution.observe (application setup timeouts leaks)
        who).application
        (secondControl.execution.observe (application setup timeouts leaks) who).application).raw
          handle raw ∈ bounds.values :=
  ownerSwap_bounded_of_candidates who _ _
    (fun _ _ found => candidate_mem_values_of_trace (timeouts := timeouts) covers firstTrace found)
    (fun _ _ found => candidate_mem_values_of_trace (timeouts := timeouts) covers secondTrace found)

end Vegas
