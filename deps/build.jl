using CxxWrap, Libdl, Spot_julia_jll

mkpath(string(VERSION))
cd(string(VERSION)) do
    run(`cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_PREFIX_PATH=$(CxxWrap.prefix_path()) -DJulia_EXECUTABLE=$(joinpath(Sys.BINDIR,"julia")) -DSpot_DIR=$(Spot_julia_jll.artifact_dir) ..`)
    run(`cmake --build . --config Release`)
end

isdir("roll-library") && cd("roll-library") do
    run(setenv(`./build.sh`,"PATH"=>"/opt/homebrew/bin:"*ENV["PATH"]))
end
