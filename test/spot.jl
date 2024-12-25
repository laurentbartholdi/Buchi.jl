d = APDict(:a,:b)

@testset "SpotOmegaWord" begin
    v = SpotOmegaWord(d,[:a],[:a,:b])
    @test OmegaWord(v) == OmegaWord([:a],[:a,:b])
end

@testset "SpotAutomaton" begin
    a = SpotAutomaton(d,Buchi.AcceptBuchi(),0=>:a=>0,0=>:b=>0,0=>:a=>1,1=>(:a,0)=>1)
    @test !isempty(a)
    @test SpotOmegaWord(d,[:b],[:a])∈a
    @test SpotOmegaWord(d,[:b,:a])∉a
    @test SpotOmegaWord(a)∈a
end
