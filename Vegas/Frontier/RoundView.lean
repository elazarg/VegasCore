import Vegas.Frontier.RoundView.Commits
import Vegas.Frontier.RoundView.InternalClosure
import Vegas.Frontier.RoundView.Canonical
import Vegas.Frontier.RoundView.Bounded
import Vegas.Frontier.RoundView.KernelGames

/-!
# EventGraph frontier round views (umbrella)

Connects compiled event graphs to the native `Machine.RoundView` carrier. The
content lives in focused modules under `Vegas.Frontier.RoundView`:

* `Commits` — frontier actions and selected commit batches.
* `InternalClosure` — ready internal events and internal closure.
* `Canonical` — canonical round semantics and kernel-game definitions.
* `Bounded` — bounded round semantics and outcome support.
* `KernelGames` — completed/frontier kernel-game surfaces.
-/
