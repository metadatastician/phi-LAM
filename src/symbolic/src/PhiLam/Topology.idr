module PhiLam.Topology

-- A reasoning Strand represents a sequence of actions or logical derivations.
-- In a topological sense, we can model reasoning steps as segments in a braid.

public export
data Action : Type where
  ReadMemory  : Action
  EvaluateLLM : Action
  CallSandbox : Action

public export
data Strand : Type where
  Base   : Strand
  -- A strand is built by sequentially appending actions.
  Extend : Action -> Strand -> Strand

-- In a Knot of Thought, Strands can be tangled.
-- We define a basic Isotopy rule to prove equivalence of Strands.
-- Example: If an EvaluateLLM action is followed immediately by another EvaluateLLM 
-- with no sandbox or memory change, they can be topologically reduced (pruned) 
-- into a single evaluation, equivalent to a Reidemeister move smoothing a kink.

public export
data Isotopy : Strand -> Strand -> Type where
  -- Reflexivity: A strand is isotopic to itself
  ReflIsotopy : Isotopy s s
  
  -- The core move for our reasoning knot:
  -- Two back-to-back LLM evaluations without external action collapse into one.
  PruneRedundantEval : Isotopy (Extend EvaluateLLM (Extend EvaluateLLM rest)) (Extend EvaluateLLM rest)
  
  -- Transitivity to chain isotopies
  TransIsotopy : Isotopy s1 s2 -> Isotopy s2 s3 -> Isotopy s1 s3
