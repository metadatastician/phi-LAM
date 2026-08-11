defmodule PhiLam.Orchestrator.Request do
  @moduledoc "A validated identity pair at the operational/core boundary."
  @enforce_keys [:request_id, :core_id, :payload]
  defstruct [:request_id, :core_id, :payload]

  @type t :: %__MODULE__{request_id: String.t(), core_id: non_neg_integer(), payload: map()}

  @spec new(String.t(), integer(), map()) :: {:ok, t()} | {:error, :invalid_request}
  def new(request_id, core_id, payload)
      when is_binary(request_id) and byte_size(request_id) > 0 and is_integer(core_id) and
             core_id >= 0 and is_map(payload),
      do: {:ok, %__MODULE__{request_id: request_id, core_id: core_id, payload: payload}}

  def new(_, _, _), do: {:error, :invalid_request}
end
