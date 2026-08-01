defmodule PhiLam.Orchestrator.Lifecycle do
  @moduledoc "Pure lifecycle corresponding to contracts/v1/lifecycle.json."

  @type state ::
          :unseen
          | :accepted
          | :started
          | :effect_committed
          | :completed
          | :failed_before_commit
          | :ambiguous_after_effect

  @type event ::
          :accepted
          | :started
          | :effect_committed
          | :completed
          | :failed_before_commit
          | :ambiguous_after_effect
          | :retry_requested

  @transitions %{
    {:unseen, :accepted} => :accepted,
    {:accepted, :started} => :started,
    {:started, :effect_committed} => :effect_committed,
    {:effect_committed, :completed} => :completed,
    {:accepted, :failed_before_commit} => :failed_before_commit,
    {:started, :failed_before_commit} => :failed_before_commit,
    {:started, :ambiguous_after_effect} => :ambiguous_after_effect,
    {:effect_committed, :ambiguous_after_effect} => :ambiguous_after_effect,
    {:failed_before_commit, :retry_requested} => :accepted
  }

  @spec transition(state(), event()) :: {:ok, state()} | {:error, :invalid_transition}
  def transition(state, event) do
    case Map.fetch(@transitions, {state, event}) do
      {:ok, next} -> {:ok, next}
      :error -> {:error, :invalid_transition}
    end
  end

  @spec terminal?(state()) :: boolean()
  def terminal?(state), do: state in [:completed, :failed_before_commit, :ambiguous_after_effect]
end
