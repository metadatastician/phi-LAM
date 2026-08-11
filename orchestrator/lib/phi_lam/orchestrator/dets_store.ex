defmodule PhiLam.Orchestrator.DetsStore do
  @moduledoc "Serialized DETS-backed store. Each transition replaces one request snapshot."
  use GenServer
  @behaviour PhiLam.Orchestrator.Store

  alias PhiLam.Orchestrator.{Lifecycle, Request}

  def start_link(opts), do: GenServer.start_link(__MODULE__, opts, Keyword.take(opts, [:name]))

  @impl PhiLam.Orchestrator.Store
  def accept_if_absent(server, %Request{} = request),
    do: GenServer.call(server, {:accept_if_absent, request})

  @impl PhiLam.Orchestrator.Store
  def transition(server, request_id, event),
    do: GenServer.call(server, {:transition, request_id, event})

  @impl PhiLam.Orchestrator.Store
  def load(server, request_id), do: GenServer.call(server, {:load, request_id})

  @impl true
  def init(opts) do
    path = opts |> Keyword.fetch!(:path) |> String.to_charlist()
    table = Keyword.get(opts, :table, __MODULE__)
    {:ok, table} = :dets.open_file(table, file: path, type: :set, auto_save: 100)
    {:ok, table}
  end

  @impl true
  def handle_call({:accept_if_absent, request}, _from, table) do
    snapshot = %{request: request, state: :accepted, sequence: 0, events: [:accepted]}

    reply =
      if :dets.insert_new(table, {request.request_id, snapshot}) do
        :ok = :dets.sync(table)
        {:accepted, snapshot}
      else
        [{_, existing}] = :dets.lookup(table, request.request_id)
        {:duplicate, existing}
      end

    {:reply, reply, table}
  end

  def handle_call({:transition, request_id, event}, _from, table) do
    reply =
      case :dets.lookup(table, request_id) do
        [] ->
          {:error, :not_found}

        [{_, snapshot}] ->
          case Lifecycle.transition(snapshot.state, event) do
            {:ok, next_state} ->
              updated = %{
                snapshot
                | state: next_state,
                  sequence: snapshot.sequence + 1,
                  events: snapshot.events ++ [event]
              }

              :ok = :dets.insert(table, {request_id, updated})
              :ok = :dets.sync(table)
              {:ok, updated}

            {:error, :invalid_transition} = error ->
              error
          end
      end

    {:reply, reply, table}
  end

  def handle_call({:load, request_id}, _from, table) do
    reply =
      case :dets.lookup(table, request_id) do
        [{_, snapshot}] -> {:ok, snapshot}
        [] -> :not_found
      end

    {:reply, reply, table}
  end

  @impl true
  def terminate(_reason, table), do: :dets.close(table)
end
