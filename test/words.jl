@testset "InfiniteRange" begin
    r = 10:ω
    @test length(r) == ω
    @test 1+r == r+1 == r-(-1) == 11:ω
    @test r ∩ (12:ω) == (12:ω) ∩ r == 12:ω
    @test r ∩ (12:20) == (12:20) ∩ r == 12:20
    @test r ∩ (8:20) == (8:20) ∩ r == 10:20
    @test 12∈r
    @test 8∉r
    @test r ⊆ (8:ω)
    @test !(r ⊆ (12:ω))

    s = 13:3:ω
    t = 17:5:ω
    @test length(s) == ω
    @test 1+s == s+1 == s-(-1) == 14:3:ω
    @test s+r == r+s == 23:4:ω
    @test s+t == t+s == 30:8:ω
    @test s*2 == 2*s == 26:6:ω
    @test r*3-17 == 3*r + (-17) == s
    
    @test r ∩ s == s ∩ r == s
    @test s ∩ (20:ω) == 22:3:ω
    @test s ∩ t == t ∩ s == 22:15:ω
    @test s ∩ (23:5:100) == 28:15:100
    @test 43∈s
    @test 8∉t
end

@testset "OmegaWord" begin
    a = OmegaWord([1,2,3],[2,3])
    @test a == OmegaWord([1,2],[3,2])
    @test size(a) == (1,2)
    @test length(a) == ω
    @test a ≤ a
    @test a < OmegaWord([1,2,3,2],[3,3,2])
    @test a > OmegaWord([1],[2])
    @test a[4]==2
    @test a[4:7]==[2,3,2,3]
    @test a[4:ω] == OmegaWord([2,3])
    @test a[3:2:ω] == OmegaWord([3])
end
