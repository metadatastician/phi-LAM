defmodule PhiLam.Orchestrator.Adapter do
  @moduledoc "External-effect port. Ambiguity is data and must never be retried automatically."
  @type result ::
          {:committed, String.t()}
          | {:rejected_before_effect, term()}
          | {:ambiguous_after_effect, term()}

  @callback invoke(term(), PhiLam.Orchestrator.Request.t(), idempotency_key :: String.t()) ::
              result()
end
