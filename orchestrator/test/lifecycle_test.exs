defmodule PhiLam.Orchestrator.LifecycleTest do
  use ExUnit.Case, async: true
  alias PhiLam.Orchestrator.Lifecycle

  test "commit path is explicit" do
    assert {:ok, :accepted} = Lifecycle.transition(:unseen, :accepted)
    assert {:ok, :started} = Lifecycle.transition(:accepted, :started)
    assert {:ok, :effect_committed} = Lifecycle.transition(:started, :effect_committed)
    assert {:ok, :completed} = Lifecycle.transition(:effect_committed, :completed)
  end

  test "completion cannot leap over effect commitment" do
    assert {:error, :invalid_transition} = Lifecycle.transition(:started, :completed)

    assert {:error, :invalid_transition} =
             Lifecycle.transition(:ambiguous_after_effect, :retry_requested)
  end
end
