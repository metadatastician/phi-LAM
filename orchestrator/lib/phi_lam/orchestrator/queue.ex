defmodule PhiLam.Orchestrator.Queue do
  @moduledoc "Delivery port. Acknowledgement occurs only after durable lifecycle change."
  @callback publish(term(), map()) :: :ok | {:error, term()}
  @callback acknowledge(term(), String.t()) :: :ok | {:error, term()}
  @callback reject(term(), String.t(), :retry | :dead_letter) :: :ok | {:error, term()}
end
