defmodule PhiLamOrchestrator.AmbientLoop do
  use GenServer
  require Logger

  @moduledoc """
  The AmbientLoop is the primary entrypoint for the event-driven LAM.
  It constantly listens for telemetry, audio wake-words, or UI events,
  and triggers reasoning strands when it detects actionable context.
  """

  # Client API
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, :ok, opts ++ [name: __MODULE__])
  end

  def ingest_event(event) do
    GenServer.cast(__MODULE__, {:ingest, event})
  end

  # Server Callbacks
  @impl true
  def init(:ok) do
    Logger.info("AmbientLoop started. Listening for ambient environmental events...")
    {:ok, %{events_processed: 0}}
  end

  @impl true
  def handle_cast({:ingest, event}, state) do
    Logger.info("AmbientLoop received event: #{inspect(event)}")
    
    # In a full Type 6 system, we trigger a new Knot of Thought strand here.
    PhiLamOrchestrator.KnotSupervisor.spawn_strand(event)
    
    {:noreply, %{state | events_processed: state.events_processed + 1}}
  end
end
