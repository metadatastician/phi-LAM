module PhiLamInference

export InferenceRequest, InferenceResult, infer

struct InferenceRequest
    request_id::String
    features::Vector{Float64}
    function InferenceRequest(request_id::String, features::Vector{Float64})
        isempty(request_id) && throw(ArgumentError("request_id must not be empty"))
        isempty(features) && throw(ArgumentError("features must not be empty"))
        all(isfinite, features) || throw(ArgumentError("features must be finite"))
        new(request_id, features)
    end
end

struct InferenceResult
    request_id::String
    model::String
    score::Float64
end

"""
    infer(request)

Deterministic fixture model used to exercise the boundary. This arithmetic
mean is not a trained model and carries no predictive-quality claim.
"""
function infer(request::InferenceRequest)::InferenceResult
    score = sum(request.features) / length(request.features)
    InferenceResult(request.request_id, "fixture-mean-v1", score)
end

end
