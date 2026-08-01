defmodule PhiLamOrchestrator.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    children = [
      PhiLamOrchestrator.KnotSupervisor,
      PhiLamOrchestrator.AmbientLoop
    ]

    opts = [strategy: :one_for_one, name: PhiLamOrchestrator.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
