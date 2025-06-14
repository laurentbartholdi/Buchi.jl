# examples of useful transducers

export grigorchuk, tribonacci, fibonacci, thuemorse

function grigorchuk()
    transitions = [5=>(1,1)=>5,5=>(2,2)=>5,4=>(1,2)=>5,4=>(2,1)=>5,3=>(1,1)=>4,3=>(2,2)=>2,2=>(1,1)=>4,2=>(2,2)=>1,1=>(1,1)=>5,1=>(2,2)=>3]
    d = CBuchiAutomaton(transitions)
    (a = reinitialize(d,4), b = reinitialize(d,3), c = reinitialize(d,5), d)
end

function tribonacci()
    proj = CBuchiAutomaton(2=>(1,1)=>2,2=>(2,2)=>3,3=>(3,3)=>2,3=>(4,4)=>4,4=>(5,5)=>2,
                           5=>(3,5)=>2,6=>(1,3)=>2,6=>(2,4)=>5,7=>(5,2)=>6,8=>(4,1)=>7,9=>(2,1)=>8,7=>(5,1)=>9,
                           1=>(3,5)=>2,1=>(1,3)=>2,1=>(2,4)=>5,1=>(5,2)=>6,1=>(4,1)=>7,1=>(2,1)=>8,1=>(5,1)=>9)

    proj₂ = CBuchiAutomaton(2=>1=>2,2=>2=>3,3=>3=>2,3=>4=>4,4=>5=>2,
                              1=>1=>2,1=>2=>3,1=>3=>2,1=>4=>4,1=>5=>2)

    add = CBuchiAutomaton(2=>('z','z')=>4,3=>('x','x')=>2,3=>('b','b')=>5,3=>('c','c')=>6,4=>('y','y')=>3,
    5=>('x','x')=>2,5=>('y','y')=>3,5=>('z','z')=>4,6=>('b','b')=>5,
    7=>('x','x')=>2,8=>('y','y')=>3,9=>('z','z')=>4,10=>('y','b')=>7,10=>('z','b')=>8,10=>('x','b')=>9,10=>('y','c')=>6,
    10=>('y','x')=>11,11=>('c','z')=>12,12=>('b','y')=>10,
    1=>('y','b')=>7,1=>('z','b')=>8,1=>('x','b')=>9,1=>('y','c')=>6,1=>('y','x')=>11,1=>('c','z')=>12,1=>('b','y')=>10)

    add₁ = CBuchiAutomaton(2=>('z','z')=>4,3=>('x','x')=>2,3=>('b','b')=>5,3=>('c','c')=>6,4=>('y','y')=>3,
                           5=>('x','x')=>2,5=>('y','y')=>3,5=>('z','z')=>4,6=>('b','b')=>5,
                           1=>('x','x')=>2,1=>('y','y')=>3,1=>('z','z')=>4,1=>('b','b')=>5,1=>('c','c')=>6)

    (proj, proj₂, add, add₁)
end

function fibonacci()
    add = CBuchiAutomaton(2=>('x','x')=>3,2=>('b','b')=>4,3=>('y','y')=>2,4=>('x','x')=>3,4=>('y','y')=>2,
  6=>('x','x')=>3,5=>('y','y')=>2,
  7=>('x','b')=>5,7=>('y','b')=>6,7=>('y','x')=>8,8=>('b','y')=>7,
  1=>('x','b')=>5,1=>('y','b')=>6,1=>('y','x')=>8,1=>('b','y')=>7)

    add₁ = CBuchiAutomaton(2=>('x','x')=>3,2=>('b','b')=>4,3=>('y','y')=>2,4=>('x','x')=>3,4=>('y','y')=>2,
    1=>('y','y')=>2,1=>('x','x')=>3,1=>('b','b')=>4)

    (add, add₁)
end

# The Thue-Morse subshift, just encoding the positive part.
# we don't yet have Büchi automata, so we simulate the termination condition
# by having the letter 𝟎′ having to appear at the end.

function thuemorse()
    # the alphabet itself
    id = CBuchiAutomaton(2=>:𝟎a=>2,2=>:𝟏b=>3,3=>:𝟏a=>2,3=>:𝟎b=>3,
        1=>:𝟎a=>2,1=>:𝟏b=>3,1=>:𝟏a=>2,1=>:𝟎b=>3)

# the generator, i.e. the one-sided shift
    add = CBuchiAutomaton(2=>(:𝟎a,:𝟎a)=>2,2=>(:𝟏b,:𝟏b)=>3,3=>(:𝟏a,:𝟏a)=>2,3=>(:𝟎b,:𝟎b)=>3,
        4=>(:𝟎a,:𝟏a)=>2,4=>(:𝟏b,:𝟎b)=>6,5=>(:𝟎b,:𝟏b)=>3,5=>(:𝟏a,:𝟎a)=>7,6=>(:𝟏a,:𝟎b)=>4,7=>(:𝟏b,:𝟎a)=>5,
        1=>(:𝟎a,:𝟏a)=>2,1=>(:𝟏b,:𝟎b)=>6,1=>(:𝟎b,:𝟏b)=>3,1=>(:𝟏a,:𝟎a)=>7,1=>(:𝟏a,:𝟎b)=>4,1=>(:𝟏b,:𝟎a)=>5)

# the encoding of the action
    𝟎,𝟏,𝟎′ = :𝟎,:𝟏,:𝟎′
    action = CBuchiAutomaton(2=>(:𝟎a,:𝟎a,𝟎′)=>2,2=>(:𝟏b,:𝟏b,𝟎′)=>3,3=>(:𝟏a,:𝟏a,𝟎′)=>2,3=>(:𝟎b,:𝟎b,𝟎′)=>3,
        4=>(:𝟎a,:𝟏a,𝟎′)=>2,4=>(:𝟏b,:𝟎b,𝟎′)=>6,5=>(:𝟎b,:𝟏b,𝟎′)=>3,5=>(:𝟏a,:𝟎a,𝟎′)=>7,6=>(:𝟏a,:𝟎b,𝟎′)=>4,7=>(:𝟏b,:𝟎a,𝟎′)=>5,
        8=>(:𝟎a,:𝟏a,𝟏)=>2,8=>(:𝟏b,:𝟎b,𝟏)=>6,9=>(:𝟎b,:𝟏b,𝟏)=>3,9=>(:𝟏a,:𝟎a,𝟏)=>7,10=>(:𝟏a,:𝟎b,𝟏)=>4,11=>(:𝟏b,:𝟎a,𝟏)=>5,
        8=>(:𝟎a,:𝟎b,𝟎)=>8,8=>(:𝟏b,:𝟏a,𝟎)=>9,9=>(:𝟎b,:𝟎a,𝟎)=>9,9=>(:𝟏a,:𝟏b,𝟎)=>8,
        10=>(:𝟎b,:𝟎b,𝟎)=>10,10=>(:𝟏a,:𝟏a,𝟎)=>11,11=>(:𝟎a,:𝟎a,𝟎)=>11,11=>(:𝟏b,:𝟏b,𝟎)=>10,
        4=>(:𝟎a,:𝟎b,𝟏)=>4,4=>(:𝟏b,:𝟏a,𝟏)=>5,5=>(:𝟏a,:𝟏b,𝟏)=>4,5=>(:𝟎b,:𝟎a,𝟏)=>5,
  4=>(:𝟎a,:𝟏a,𝟎)=>11,5=>(:𝟎b,:𝟏b,𝟎)=>10,6=>(:𝟎b,:𝟏a,𝟎)=>9,7=>(:𝟎a,:𝟏b,𝟎)=>8,
  6=>(:𝟎b,:𝟎b,𝟏)=>6,6=>(:𝟏a,:𝟏a,𝟏)=>7,7=>(:𝟏b,:𝟏b,𝟏)=>6,7=>(:𝟎a,:𝟎a,𝟏)=>7,
  8=>(:𝟎a,:𝟏a,𝟏)=>11,9=>(:𝟎b,:𝟏b,𝟏)=>10,10=>(:𝟎b,:𝟏a,𝟏)=>9,11=>(:𝟎a,:𝟏b,𝟏)=>8,

  1=>(:𝟎a,:𝟎a,𝟎′)=>2,1=>(:𝟏b,:𝟏b,𝟎′)=>3,1=>(:𝟏a,:𝟏a,𝟎′)=>2,1=>(:𝟎b,:𝟎b,𝟎′)=>3,
  1=>(:𝟎a,:𝟏a,𝟏)=>2,1=>(:𝟏b,:𝟎b,𝟏)=>6,1=>(:𝟎b,:𝟏b,𝟏)=>3,1=>(:𝟏a,:𝟎a,𝟏)=>7,1=>(:𝟏a,:𝟎b,𝟏)=>4,1=>(:𝟏b,:𝟎a,𝟏)=>5,
  1=>(:𝟎a,:𝟎b,𝟎)=>8,1=>(:𝟏b,:𝟏a,𝟎)=>9,1=>(:𝟎b,:𝟎a,𝟎)=>9,1=>(:𝟏a,:𝟏b,𝟎)=>8,
  1=>(:𝟎b,:𝟎b,𝟎)=>10,1=>(:𝟏a,:𝟏a,𝟎)=>11,1=>(:𝟎a,:𝟎a,𝟎)=>11,1=>(:𝟏b,:𝟏b,𝟎)=>10,
  1=>(:𝟎a,:𝟏a,𝟏)=>11,1=>(:𝟎b,:𝟏b,𝟏)=>10,1=>(:𝟎b,:𝟏a,𝟏)=>9,1=>(:𝟎a,:𝟏b,𝟏)=>8,
)

    binadder = CBuchiAutomaton(1=>(𝟎′,𝟎′,𝟎′)=>1,1=>(𝟏,𝟏,𝟎′)=>1,1=>(𝟎′,𝟏,𝟏)=>1,1=>(𝟏,𝟎′,𝟏)=>2,
        2=>(𝟎′,𝟏,𝟎′)=>1,2=>(𝟎′,𝟎′,𝟏)=>2,2=>(𝟏,𝟎′,𝟎′)=>2,2=>(𝟏,𝟏,𝟏)=>2)

    (id, add, action, binadder)
end

function int2buchibin(n)
    s = 1
    x = Pair{Int,Pair{Tuple{Symbol},Int}}[]
    while n>0
        if iseven(n)
            push!(x,s=>(𝟎,)=>s+1)
            push!(x,s=>(𝟎′,)=>s+1)
        else
            push!(x,s=>(𝟏,)=>s+1)
        end
        s += 1
        n ÷= 2
    end
    push!(x,s=>(𝟎′,)=>s)
    CBuchiAutomaton(x)
end

#@assert thuemorseaction*CBuchiAutomaton(OmegaWord([𝟎′])) == Buchi.diagonal(thuemorse₀)
#@assert all(i->thuemorseaction*int2buchibin(i) == thuemorse^i,1:10)

# fibonacci
function fibo2()
    fib_adder = CBuchiAutomaton(1=>(0,0,0)=>2,1=>(0,0,1)=>3,1=>(0,1,0)=>4,1=>(0,1,1)=>5,1=>(1,0,0)=>6,1=>(1,0,1)=>7,1=>(1,1,0)=>8,1=>(1,1,1)=>9,
2=>(0,0,0)=>2,2=>(0,0,1)=>10,2=>(0,1,0)=>11,2=>(0,1,1)=>5,2=>(1,0,0)=>12,2=>(1,0,1)=>7,2=>(1,1,1)=>9,
3=>(0,0,0)=>13,3=>(0,1,0)=>14,3=>(1,0,0)=>14,3=>(1,1,0)=>8,
4=>(0,0,0)=>14,4=>(0,0,1)=>13,4=>(1,0,0)=>15,
5=>(0,0,0)=>2,5=>(1,0,0)=>12,
6=>(0,0,0)=>14,6=>(0,0,1)=>13,6=>(0,1,0)=>16,
7=>(0,0,0)=>2,7=>(0,1,0)=>11,
8=>(0,0,0)=>17,8=>(0,0,1)=>18,
9=>(0,0,0)=>14,
10=>(0,0,0)=>13,
11=>(0,0,0)=>14,11=>(1,0,0)=>15,
12=>(0,0,0)=>14,12=>(0,1,0)=>16,
13=>(0,1,0)=>14,13=>(1,0,0)=>14,13=>(1,1,0)=>8,
14=>(0,0,1)=>13,
15=>(0,0,0)=>17,15=>(0,0,1)=>18,15=>(0,1,1)=>11,
16=>(0,0,0)=>17,16=>(0,0,1)=>18,16=>(1,0,1)=>12,
17=>(0,0,0)=>14,17=>(0,1,0)=>16,17=>(1,0,0)=>15,17=>(1,1,0)=>19,17=>(1,1,1)=>20,
18=>(0,0,0)=>2,18=>(0,1,0)=>11,18=>(1,0,0)=>12,
19=>(0,0,0)=>21,
20=>(0,0,0)=>17,
21=>(0,0,0)=>17,21=>(0,0,1)=>18,21=>(0,1,1)=>11,21=>(1,0,1)=>12)

# negative fibonacci base

    negafib_adder = CBuchiAutomaton(
1=>(0,0,0)=>2,1=>(0,0,1)=>3,1=>(0,1,0)=>4,1=>(0,1,1)=>5,1=>(1,0,1)=>5,1=>(1,0,0)=>6,1=>(1,1,0)=>7,1=>(1,1,1)=>8,
2=>(0,0,0)=>9,2=>(0,0,1)=>3,2=>(0,1,1)=>5,2=>(1,0,1)=>5,2=>(1,1,0)=>8,
3=>(0,0,0)=>10,3=>(0,1,0)=>4,3=>(1,0,0)=>6,3=>(1,1,0)=>7,
4=>(0,0,0)=>11,4=>(1,0,0)=>12,4=>(1,0,1)=>13,
5=>(0,0,0)=>9,
6=>(0,0,0)=>11,6=>(0,1,0)=>14,6=>(0,1,1)=>15,
7=>(0,0,0)=>16,7=>(0,0,1)=>17,
8=>(0,0,0)=>11,
9=>(0,0,0)=>9,9=>(0,0,1)=>3,9=>(0,1,1)=>5,9=>(1,0,1)=>5,
10=>(1,1,0)=>8,
11=>(0,0,0)=>10,11=>(0,1,0)=>4,11=>(1,0,0)=>6,11=>(1,1,0)=>7,11=>(1,1,1)=>8,
12=>(0,0,0)=>9,12=>(0,0,1)=>3,12=>(0,1,1)=>5,
13=>(0,0,0)=>10,13=>(0,1,0)=>4,
14=>(0,0,0)=>9,14=>(0,0,1)=>3,14=>(1,0,1)=>5,
15=>(0,0,0)=>10,15=>(1,0,0)=>6,
16=>(0,0,1)=>5,
17=>(0,0,0)=>18,17=>(0,1,0)=>7,17=>(1,0,0)=>7,
18=>(0,0,0)=>11,18=>(0,1,0)=>14,18=>(0,1,1)=>15,18=>(1,0,0)=>12,18=>(1,0,1)=>13,18=>(1,1,1)=>5)

    negafib_gen = CBuchiAutomaton(1=>(0, 0)=>2, 1=>(0, 1)=>3, 1=>(1, 0)=>4,
  2=>(1, 0)=>5, 3=>(0, 0)=>6, 4=>(0, 0)=>7, 4=>(0, 1)=>8,
  5=>(0, 0)=>6, 6=>(0, 0)=>6, 6=>(1, 1)=>3,
                                  7=>(0, 1)=>3, 8=>(0, 0)=>2, 8=>(1, 0)=>4)

    (fib_adder, negafib_adder, negafib_gen)
end

function thuemorse_spot()
    # the alphabet itself
    factory = APDictFactory(3,[:𝟎a,:𝟏a,:𝟎b,:𝟏b,:𝟎,:𝟏])
    𝟎,𝟏 = :𝟎,:𝟏
    
    id = SpotAutomaton(factory[],1=>:𝟎a=>1,1=>:𝟏b=>2,2=>:𝟏a=>1,2=>:𝟎b=>2,
        0=>:𝟎a=>1,0=>:𝟏b=>2,0=>:𝟏a=>1,0=>:𝟎b=>2)

# the generator, i.e. the one-sided shift
    increment = SpotAutomaton(factory[2],2=>(:𝟎a,:𝟎a)=>2,2=>(:𝟏b,:𝟏b)=>3,3=>(:𝟏a,:𝟏a)=>2,3=>(:𝟎b,:𝟎b)=>3,
        4=>(:𝟎a,:𝟏a)=>2,4=>(:𝟏b,:𝟎b)=>6,5=>(:𝟎b,:𝟏b)=>3,5=>(:𝟏a,:𝟎a)=>1,6=>(:𝟏a,:𝟎b)=>4,1=>(:𝟏b,:𝟎a)=>5,
        0=>(:𝟎a,:𝟏a)=>2,0=>(:𝟏b,:𝟎b)=>6,0=>(:𝟎b,:𝟏b)=>3,0=>(:𝟏a,:𝟎a)=>1,0=>(:𝟏a,:𝟎b)=>4,0=>(:𝟏b,:𝟎a)=>5)

# the encoding of the action
    action = SpotAutomaton(factory[3],AcceptBuchi(),
        2=>((:𝟎a,:𝟎a,𝟎),0)=>2,2=>((:𝟏b,:𝟏b,𝟎),0)=>3,3=>((:𝟏a,:𝟏a,𝟎),0)=>2,3=>((:𝟎b,:𝟎b,𝟎),0)=>3,
        4=>((:𝟎a,:𝟏a,𝟎),0)=>2,4=>((:𝟏b,:𝟎b,𝟎),0)=>6,5=>((:𝟎b,:𝟏b,𝟎),0)=>3,5=>((:𝟏a,:𝟎a,𝟎),0)=>7,6=>((:𝟏a,:𝟎b,𝟎),0)=>4,7=>((:𝟏b,:𝟎a,𝟎),0)=>5,
        8=>(:𝟎a,:𝟏a,𝟏)=>2,8=>(:𝟏b,:𝟎b,𝟏)=>6,9=>(:𝟎b,:𝟏b,𝟏)=>3,9=>(:𝟏a,:𝟎a,𝟏)=>7,10=>(:𝟏a,:𝟎b,𝟏)=>4,1=>(:𝟏b,:𝟎a,𝟏)=>5,
        8=>(:𝟎a,:𝟎b,𝟎)=>8,8=>(:𝟏b,:𝟏a,𝟎)=>9,9=>(:𝟎b,:𝟎a,𝟎)=>9,9=>(:𝟏a,:𝟏b,𝟎)=>8,
        10=>(:𝟎b,:𝟎b,𝟎)=>10,10=>(:𝟏a,:𝟏a,𝟎)=>1,1=>(:𝟎a,:𝟎a,𝟎)=>1,1=>(:𝟏b,:𝟏b,𝟎)=>10,
        4=>(:𝟎a,:𝟎b,𝟏)=>4,4=>(:𝟏b,:𝟏a,𝟏)=>5,5=>(:𝟏a,:𝟏b,𝟏)=>4,5=>(:𝟎b,:𝟎a,𝟏)=>5,
        4=>(:𝟎a,:𝟏a,𝟎)=>1,5=>(:𝟎b,:𝟏b,𝟎)=>10,6=>(:𝟎b,:𝟏a,𝟎)=>9,7=>(:𝟎a,:𝟏b,𝟎)=>8,
        6=>(:𝟎b,:𝟎b,𝟏)=>6,6=>(:𝟏a,:𝟏a,𝟏)=>7,7=>(:𝟏b,:𝟏b,𝟏)=>6,7=>(:𝟎a,:𝟎a,𝟏)=>7,
        8=>(:𝟎a,:𝟏a,𝟏)=>1,9=>(:𝟎b,:𝟏b,𝟏)=>10,10=>(:𝟎b,:𝟏a,𝟏)=>9,1=>(:𝟎a,:𝟏b,𝟏)=>8,

        0=>(:𝟎a,:𝟎a,𝟎)=>2,0=>(:𝟏b,:𝟏b,𝟎)=>3,0=>(:𝟏a,:𝟏a,𝟎)=>2,0=>(:𝟎b,:𝟎b,𝟎)=>3,
        0=>(:𝟎a,:𝟏a,𝟏)=>2,0=>(:𝟏b,:𝟎b,𝟏)=>6,0=>(:𝟎b,:𝟏b,𝟏)=>3,0=>(:𝟏a,:𝟎a,𝟏)=>7,0=>(:𝟏a,:𝟎b,𝟏)=>4,0=>(:𝟏b,:𝟎a,𝟏)=>5,
        0=>(:𝟎a,:𝟎b,𝟎)=>8,0=>(:𝟏b,:𝟏a,𝟎)=>9,0=>(:𝟎b,:𝟎a,𝟎)=>9,0=>(:𝟏a,:𝟏b,𝟎)=>8,
        0=>(:𝟎b,:𝟎b,𝟎)=>10,0=>(:𝟏a,:𝟏a,𝟎)=>1,0=>(:𝟎a,:𝟎a,𝟎)=>1,0=>(:𝟏b,:𝟏b,𝟎)=>10,
        0=>(:𝟎a,:𝟏a,𝟏)=>1,0=>(:𝟎b,:𝟏b,𝟏)=>10,0=>(:𝟎b,:𝟏a,𝟏)=>9,0=>(:𝟎a,:𝟏b,𝟏)=>8)

    binadder = SpotAutomaton(factory[3],0=>(𝟎,𝟎,𝟎)=>0,0=>(𝟏,𝟏,𝟎)=>0,0=>(𝟎,𝟏,𝟏)=>0,0=>(𝟏,𝟎,𝟏)=>1,
        1=>(𝟎,𝟏,𝟎)=>0,1=>(𝟎,𝟎,𝟏)=>1,1=>(𝟏,𝟎,𝟎)=>1,1=>(𝟏,𝟏,𝟏)=>1)

    int2word = n->begin
        s = 1
        preperiod = Symbol[]
        while n>0
            push!(preperiod, iseven(n) ? 𝟎 : 𝟏)
            n ÷= 2
        end
        SpotOmegaWord(factory[],preperiod,[𝟎])
    end
    
    (factory = factory, id, increment, action, binadder, int2word)
end

function substitutive(ϕ::Dict{Char,String})
    Σ₀ = keys(ϕ) |> collect |> sort
    N = length(Σ₀)
    alphabet = Dict{Any,Int}(c=>n for (n,c)=enumerate(Σ₀))
    for (m,c)=enumerate(Σ₀), (n,d)=enumerate(Σ₀)
        alphabet[c,d] = m*N+n
    end
    Σ = [Symbol(c,'𝟎'+i) for c=Σ₀ for i=0:length(ϕ[c])-1]

    factory = APDictFactory(3,Σ)
    id = let trans = Pair{Int,Pair{Symbol,Int}}[]
        for c=Σ₀, i=0:length(ϕ[c])-1
            d = collect(ϕ[c])[i+1]
            push!(trans,alphabet[d]=>Symbol(c,'𝟎'+i)=>alphabet[c])
            push!(trans,0=>Symbol(c,'𝟎'+i)=>alphabet[c])
        end
        SpotAutomaton(factory[], N+1, trans)
    end

    increment = let trans = Pair{Int,Pair{NTuple{2,Symbol},Int}}[]
        for c=Σ₀, i=0:length(ϕ[c])-1
            d = collect(ϕ[c])[i+1]
            push!(trans,alphabet[d]=>(Symbol(c,'𝟎'+i),Symbol(c,'𝟎'+i))=>alphabet[c])
        end
        for c=Σ₀, i=0:length(ϕ[c])-2
            d₀ = collect(ϕ[c])[i+1]
            d₁ = collect(ϕ[c])[i+2]
            push!(trans,alphabet[d₀,d₁]=>(Symbol(c,'𝟎'+i),Symbol(c,'𝟎'+i+1))=>alphabet[c])
        end
        for c₀=Σ₀, c₁=Σ₀
            d₀ = collect(ϕ[c₀])[end]
            d₁ = collect(ϕ[c₁])[1]
            push!(trans,alphabet[d₀,d₁]=>(Symbol(c₀,'𝟎'+length(ϕ[c])-1),Symbol(c₁,'𝟎'))=>alphabet[c₀,c₁])
            push!(trans,0=>(Symbol(c₀,'𝟎'+length(ϕ[c])-1),Symbol(c₁,'𝟎'))=>alphabet[c₀,c₁])
        end
    end
    (factory = factory, Σ₀, Σ, id, increment)
end
