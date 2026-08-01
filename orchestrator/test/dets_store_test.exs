defmodule PhiLam.Orchestrator.DetsStoreTest do
  use ExUnit.Case
  alias PhiLam.Orchestrator.{DetsStore, Request}

  setup do
    path = Path.join(System.tmp_dir!(), "phi-lam-#{System.unique_integer([:positive])}.dets")
    table = :phi_lam_orchestrator_test_store
    on_exit(fn -> File.rm(path) end)
    %{path: path, table: table}
  end

  test "concurrent duplicates cross one atomic acceptance boundary", context do
    {:ok, store} = DetsStore.start_link(path: context.path, table: context.table)
    {:ok, request} = Request.new("same-request", 7, %{})

    results =
      1..64
      |> Task.async_stream(fn _ -> DetsStore.accept_if_absent(store, request) end,
        max_concurrency: 16,
        ordered: false
      )
      |> Enum.map(fn {:ok, result} -> result end)

    assert Enum.count(results, &match?({:accepted, _}, &1)) == 1
    assert Enum.count(results, &match?({:duplicate, _}, &1)) == 63
    GenServer.stop(store)
  end

  test "snapshot and event sequence survive process restart", context do
    {:ok, first} = DetsStore.start_link(path: context.path, table: context.table)
    {:ok, request} = Request.new("recoverable", 8, %{work: "fixture"})
    assert {:accepted, _} = DetsStore.accept_if_absent(first, request)

    assert {:ok, %{state: :started, sequence: 1}} =
             DetsStore.transition(first, "recoverable", :started)

    GenServer.stop(first)

    {:ok, second} = DetsStore.start_link(path: context.path, table: context.table)

    assert {:ok, %{state: :started, sequence: 1, events: [:accepted, :started]}} =
             DetsStore.load(second, "recoverable")

    GenServer.stop(second)
  end
end
