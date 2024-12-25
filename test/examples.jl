@testset "Grigorchuk" begin
    """
    o = Buchi.diagonal(CBuchiAutomaton(1=>1=>1,1=>2=>1))
    @test nstates(o) == 1
    @test grigorchuk.a^2 == grigorchuk.b^2 == grigorchuk.c^2 == grigorchuk.d^2 == grigorchuk.b*grigorchuk.c*grigorchuk.d == o
    @test OmegaWord([1])*grigorchuk.a == OmegaWord([2],[1])
"""
end

@testset "Tribonacci" begin
"""    o = Buchi.tribonacci₁
    @test o*o == o
    @test o*tribonacci == tribonacci*o == tribonacci
    @test inv(tribonacci)*tribonacci == o
    e = tribonacci*inv(tribonacci)
    @test e*e == e
"""
end
