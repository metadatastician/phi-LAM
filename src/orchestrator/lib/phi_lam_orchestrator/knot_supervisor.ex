defmodule PhiLamOrchestrator.KnotSupervisor do
  use DynamicSupervisor
  require Logger

  @moduledoc """
  The KnotSupervisor manages the dynamic spawning and tracking of 
  individual reasoning paths (Strands) within the Knot of Thought.
  """

  def start_link(init_arg) do
    DynamicSupervisor.start_link(__MODULE__, init_arg, name: __MODULE__)
  end

  @impl true
  def init(_init_arg) do
    Logger.info("KnotSupervisor started. Ready to orchestrate reasoning strands.")
    DynamicSupervisor.init(strategy: :one_for_one)
  end

  def spawn_strand(event_context) do
    spec = {PhiLamOrchestrator.Strand, event_context}
    DynamicSupervisor.start_child(__MODULE__, spec)
  end
end
