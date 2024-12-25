@testset "CBuchiAutomaton" begin
    sheep = CBuchiAutomaton{Int,Char}(1=>'b'=>2,2=>'a'=>3,3=>'a'=>1,3=>'b'=>2,minimize=false)
    @test nstates(sheep) == 3
    @test sheep[1] == ['b'=>2]
    @test sheep[1,'a'] == 0
    @test sheep[1,'b'] == 2
    @test OmegaWord(['b','a']) ∈ sheep
    @test OmegaWord(['b','a','a'],['b','a']) ∈ sheep

    s2 = copy(sheep)
    @test s2 == sheep
    push!(s2,4=>'a'=>1)
    @test nstates(s2) == 4
    Buchi.remove_unreachables!(s2)
    @test s2 == sheep

    s3 = copy(sheep)
    push!(s3,3=>'a'=>4)
    push!(s3,3=>'a'=>5)
    push!(s3,4=>'a'=>5)
    resize!(s3,5)
    Buchi.remove_deadends!(s3)
    @test s3 == sheep
end

@testset "CBuchiTransducer" begin
    upcase = CBuchiAutomaton{Int,Tuple{Char,Char}}(1=>('a','A')=>1,1=>('b','B')=>1)
    @test upcase[1]==[('a','A')=>1,('b','B')=>1]
    @test upcase[1,('a','A')] == 1
    @test upcase[1,('a','B')] == 0
    @test collect(upcase[1,'a']) == [('A',) => 1]
end
