/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingNoise

/-! # Arbitrary raw responses after an opaque foreign binding -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A foreign opaque binding followed by actual activation and any raw response
retains the private source draw independently of the observer's complete input
and chosen response. No restriction is imposed on the raw deviation. -/
theorem reactiveBinding_activation_response_joint_law (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner observer : Player) (different : observer ≠ owner)
    (event : graph.EventId) (payload : L.Ty) (serial : Nat)
    (choices : PMF (PublicationResult (L.Val payload)))
    (deviation : (runtime.reactiveApplication leaks).Policy) :
    (choices.bind fun result =>
      ((execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveBinding leaks owner event payload result serial)).environmentStep
          (runtime.reactiveApplication leaks) (.activate observer)).bind fun next =>
            (deviation (next.recall observer)
              (next.observe (runtime.reactiveApplication leaks) observer)).map fun action =>
                (result, ((next.recall observer,
                  next.observe (runtime.reactiveApplication leaks) observer), action))) =
      bindPairLaw choices (fun _ =>
        ((execution.respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveBinding leaks owner event payload .failure serial)).environmentStep
            (runtime.reactiveApplication leaks) (.activate observer)).bind fun next =>
              (deviation (next.recall observer)
                (next.observe (runtime.reactiveApplication leaks) observer)).map fun action =>
                  ((next.recall observer,
                    next.observe (runtime.reactiveApplication leaks) observer), action)) := by
  have inputs := runtime.reactiveBinding_activation_joint_result_law leaks execution
    owner observer
    different event payload serial choices
  have moved := congrArg (fun joint => joint.bind fun pair =>
    (deviation pair.2.1 pair.2.2).map fun action => (pair.1, (pair.2, action))) inputs
  simpa only [bindPairLaw, PMF.bind_map, PMF.bind_bind, PMF.map_bind, PMF.map_comp,
    Function.comp_def] using moved

/-- Even after conditioning on the full activated native input and arbitrary raw
response, the foreign private binding draw has exactly its original prior.
The existing posterior fallback also gives this equality at impossible inputs. -/
theorem reactiveBinding_activation_response_posterior (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner observer : Player) (different : observer ≠ owner)
    (event : graph.EventId) (payload : L.Ty) (serial : Nat)
    (choices : PMF (PublicationResult (L.Val payload)))
    (deviation : (runtime.reactiveApplication leaks).Policy)
    (observed : (List (runtime.reactiveApplication leaks).PlayerEntry ×
      (runtime.reactiveApplication leaks).PlayerView) ×
      (runtime.reactiveApplication leaks).Action) :
    let joint :=
      (choices.bind fun result =>
        ((execution.respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveBinding leaks owner event payload result serial)).environmentStep
            (runtime.reactiveApplication leaks) (.activate observer)).bind fun next =>
              (deviation (next.recall observer)
                (next.observe (runtime.reactiveApplication leaks) observer)).map fun action =>
                  (result, ((next.recall observer,
                    next.observe (runtime.reactiveApplication leaks) observer), action)))
    (fiberPosterior (joint.map Prod.swap) Prod.fst observed).map Prod.snd = choices := by
  dsimp only
  rw [runtime.reactiveBinding_activation_response_joint_law leaks execution owner observer
    different event payload serial choices deviation, bindPairLaw_const_map_swap]
  exact fiberPosterior_snd_bindPairLaw_const _ choices observed

end Vegas.EventGraphRuntime
