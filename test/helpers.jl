@testset "IntRefinablePartition" begin
    p = Buchi.IntRefinablePartition(5)
    Buchi.sanitycheck(p)
    @test length(p)==1
    Buchi.mark(p,3)
    Buchi.mark(p,2)
    Buchi.split(p)
    @test length(p)==2
    @test p[1]==[1,4,5]
    @test collect(p)==[[1,4,5],[3,2]]
end

@testset "VectorVector" begin
    v = Buchi.VectorVector{Int,Char}()
    @test length(v)==0
    resize!(v,1)
    @test length(v)==1
    push!(v,1=>'a')
    @test collect(v)==[['a']]
    @test length(v[])==1
    @test collect(v[])==[1=>'a']
    append!(v,[2=>'b',2=>'c'])
    @test collect(v)==[['a'],['b','c']]
    @test collect(v[])==[1=>'a',2=>'b',2=>'c']
    @test v[][2]==(2=>'b')
    v[2][1] = 'a'
    @test collect(v[])==[1=>'a',2=>'a',2=>'c']
    delete!(v[],'a')
    @test collect(v)==[[],['c']]
    push!(v,3=>'a')
    deleteat!(v,1)
    @test collect(v)==[['c'],['a']]
    deleteat!(v,2)
    @test collect(v)==[['c']]
    append!(v,[1=>'a',2=>'b',4=>'d',4=>'e',5=>'f'])
    deleteat!(v,BitVector([false,true,true,false,true]))
    @test collect(v)==[['c','a'],['d','e']]
    append!(v,[4=>'a',5=>'b',7=>'d'])
    deleteat!(v,[2,5,6])
    @test collect(v)==[['c','a'],[],['a'],['d']]
end
