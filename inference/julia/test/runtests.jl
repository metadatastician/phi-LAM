using Test
using PhiLamInference

@testset "deterministic inference boundary" begin
    request = InferenceRequest("req-0001", [0.25, 0.75])
    first = infer(request)
    second = infer(request)
    @test first.request_id == "req-0001"
    @test first.model == "fixture-mean-v1"
    @test first.score == 0.5
    @test first.score == second.score
end

@testset "boundary validation" begin
    @test_throws ArgumentError InferenceRequest("", [1.0])
    @test_throws ArgumentError InferenceRequest("req", Float64[])
    @test_throws ArgumentError InferenceRequest("req", [Inf])
end
