defmodule PhiLamOrchestrator.MixProject do
  use Mix.Project

  def project do
    [
      app: :phi_lam_orchestrator,
      version: "0.1.0",
      elixir: "~> 1.18",
      start_permanent: Mix.env() == :prod,
      elixirc_options: [warnings_as_errors: true],
      deps: []
    ]
  end

  def application do
    [extra_applications: [:logger], mod: {PhiLam.Orchestrator.Application, []}]
  end
end
