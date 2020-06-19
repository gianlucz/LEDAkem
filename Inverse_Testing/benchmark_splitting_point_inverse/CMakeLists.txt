cmake_minimum_required(VERSION 3.10)
project(inverse_bench C)

set(CC gcc)

##No avx
##set(CMAKE_C_FLAGS  "${CMAKE_C_FLAGS} -Wall -pedantic -Wuninitialized -march='nocona' -O3")

##avx
set(CMAKE_C_FLAGS  "${CMAKE_C_FLAGS} -Wall -pedantic -Wuninitialized -march='sandybridge' -O3")

##avx2
##set(CMAKE_C_FLAGS  "${CMAKE_C_FLAGS} -Wall -pedantic -Wuninitialized -march=native -O3")

##Asan active
##set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -pedantic -Wuninitialized -march=native -g3 -l asan -fsanitize=address")

##Debug
##set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -pedantic -Wuninitialized -march='native' -g3")

message("FLAGS" ${CMAKE_C_FLAGS})

set(HEADERS gf2x_limbs.h
            gf2x_arith_mod_xPplusOne.h
            gf2x_arith.h
            architecture_detect.h
            djbsort.h
            timing_and_stats.h)

set(SOURCES gf2x_arith.c
            gf2x_arith_mod_xPplusOne.c
            djbsort.c)


foreach(prime  7547
               7853
              14341
              14939
              16067
              22691
              25693
              27437
              35899
              36877
              52147
              57899
              89051
              96221
              152267)
    add_executable(inverse_bench_${prime} ${HEADERS} ${SOURCES} inverse_bench.c)
    target_link_libraries(inverse_bench_${prime} m)
    set_property(TARGET inverse_bench_${prime} APPEND PROPERTY
                 COMPILE_FLAGS "-DCPU_WORD_BITS=64 -DP=${prime}")

endforeach(prime)
