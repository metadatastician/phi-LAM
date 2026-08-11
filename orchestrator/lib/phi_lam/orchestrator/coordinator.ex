defmodule PhiLam.Orchestrator.Coordinator do
  @moduledoc "Thin coordinator; concrete queue and adapter integrations are intentionally ports."
  alias PhiLam.Orchestrator.Request

  @spec accept(module(), GenServer.server(), Request.t()) ::
          {:accepted, PhiLam.Orchestrator.Store.snapshot()}
          | {:duplicate, PhiLam.Orchestrator.Store.snapshot()}
  def accept(store, server, request), do: store.accept_if_absent(server, request)

  @spec record(module(), GenServer.server(), String.t(), atom()) ::
          {:ok, PhiLam.Orchestrator.Store.snapshot()} | {:error, atom()}
  def record(store, server, request_id, event), do: store.transition(server, request_id, event)
end
