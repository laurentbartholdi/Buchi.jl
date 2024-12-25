using CxxWrap, Libdl, Spot_julia_jll

run(`cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_PREFIX_PATH=$(CxxWrap.prefix_path()) -DJulia_EXECUTABLE=$(joinpath(Sys.BINDIR,"julia")) -DSpot_DIR=$(Spot_julia_jll.artifact_dir) .`)
run(`cmake --build . --config Release`)
