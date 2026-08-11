defmodule PhiLam.Orchestrator.Store do
  @moduledoc "Atomic request acceptance and durable lifecycle port."
  alias PhiLam.Orchestrator.Request

  @type snapshot :: %{
          request: Request.t(),
          state: PhiLam.Orchestrator.Lifecycle.state(),
          sequence: non_neg_integer(),
          events: [PhiLam.Orchestrator.Lifecycle.event()]
        }

  @callback accept_if_absent(GenServer.server(), Request.t()) ::
              {:accepted, snapshot()} | {:duplicate, snapshot()}
  @callback transition(GenServer.server(), String.t(), PhiLam.Orchestrator.Lifecycle.event()) ::
              {:ok, snapshot()} | {:error, :not_found | :invalid_transition}
  @callback load(GenServer.server(), String.t()) :: {:ok, snapshot()} | :not_found
end
