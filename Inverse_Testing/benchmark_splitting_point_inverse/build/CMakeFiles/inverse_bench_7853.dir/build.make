# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.15

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/local/bin/cmake

# The command to remove a file.
RM = /usr/local/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/gianluca/Desktop/benchmark_splitting_point_inverse

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/gianluca/Desktop/benchmark_splitting_point_inverse/build

# Include any dependencies generated for this target.
include CMakeFiles/inverse_bench_7853.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/inverse_bench_7853.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/inverse_bench_7853.dir/flags.make

CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.o: CMakeFiles/inverse_bench_7853.dir/flags.make
CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.o: ../gf2x_arith.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/gianluca/Desktop/benchmark_splitting_point_inverse/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building C object CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.o   -c /home/gianluca/Desktop/benchmark_splitting_point_inverse/gf2x_arith.c

CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/gianluca/Desktop/benchmark_splitting_point_inverse/gf2x_arith.c > CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.i

CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/gianluca/Desktop/benchmark_splitting_point_inverse/gf2x_arith.c -o CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.s

CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.o: CMakeFiles/inverse_bench_7853.dir/flags.make
CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.o: ../gf2x_arith_mod_xPplusOne.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/gianluca/Desktop/benchmark_splitting_point_inverse/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building C object CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.o   -c /home/gianluca/Desktop/benchmark_splitting_point_inverse/gf2x_arith_mod_xPplusOne.c

CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/gianluca/Desktop/benchmark_splitting_point_inverse/gf2x_arith_mod_xPplusOne.c > CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.i

CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/gianluca/Desktop/benchmark_splitting_point_inverse/gf2x_arith_mod_xPplusOne.c -o CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.s

CMakeFiles/inverse_bench_7853.dir/djbsort.c.o: CMakeFiles/inverse_bench_7853.dir/flags.make
CMakeFiles/inverse_bench_7853.dir/djbsort.c.o: ../djbsort.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/gianluca/Desktop/benchmark_splitting_point_inverse/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building C object CMakeFiles/inverse_bench_7853.dir/djbsort.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/inverse_bench_7853.dir/djbsort.c.o   -c /home/gianluca/Desktop/benchmark_splitting_point_inverse/djbsort.c

CMakeFiles/inverse_bench_7853.dir/djbsort.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/inverse_bench_7853.dir/djbsort.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/gianluca/Desktop/benchmark_splitting_point_inverse/djbsort.c > CMakeFiles/inverse_bench_7853.dir/djbsort.c.i

CMakeFiles/inverse_bench_7853.dir/djbsort.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/inverse_bench_7853.dir/djbsort.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/gianluca/Desktop/benchmark_splitting_point_inverse/djbsort.c -o CMakeFiles/inverse_bench_7853.dir/djbsort.c.s

CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.o: CMakeFiles/inverse_bench_7853.dir/flags.make
CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.o: ../inverse_bench.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/gianluca/Desktop/benchmark_splitting_point_inverse/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building C object CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.o   -c /home/gianluca/Desktop/benchmark_splitting_point_inverse/inverse_bench.c

CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/gianluca/Desktop/benchmark_splitting_point_inverse/inverse_bench.c > CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.i

CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/gianluca/Desktop/benchmark_splitting_point_inverse/inverse_bench.c -o CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.s

# Object files for target inverse_bench_7853
inverse_bench_7853_OBJECTS = \
"CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.o" \
"CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.o" \
"CMakeFiles/inverse_bench_7853.dir/djbsort.c.o" \
"CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.o"

# External object files for target inverse_bench_7853
inverse_bench_7853_EXTERNAL_OBJECTS =

inverse_bench_7853: CMakeFiles/inverse_bench_7853.dir/gf2x_arith.c.o
inverse_bench_7853: CMakeFiles/inverse_bench_7853.dir/gf2x_arith_mod_xPplusOne.c.o
inverse_bench_7853: CMakeFiles/inverse_bench_7853.dir/djbsort.c.o
inverse_bench_7853: CMakeFiles/inverse_bench_7853.dir/inverse_bench.c.o
inverse_bench_7853: CMakeFiles/inverse_bench_7853.dir/build.make
inverse_bench_7853: CMakeFiles/inverse_bench_7853.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/gianluca/Desktop/benchmark_splitting_point_inverse/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Linking C executable inverse_bench_7853"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/inverse_bench_7853.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/inverse_bench_7853.dir/build: inverse_bench_7853

.PHONY : CMakeFiles/inverse_bench_7853.dir/build

CMakeFiles/inverse_bench_7853.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/inverse_bench_7853.dir/cmake_clean.cmake
.PHONY : CMakeFiles/inverse_bench_7853.dir/clean

CMakeFiles/inverse_bench_7853.dir/depend:
	cd /home/gianluca/Desktop/benchmark_splitting_point_inverse/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/gianluca/Desktop/benchmark_splitting_point_inverse /home/gianluca/Desktop/benchmark_splitting_point_inverse /home/gianluca/Desktop/benchmark_splitting_point_inverse/build /home/gianluca/Desktop/benchmark_splitting_point_inverse/build /home/gianluca/Desktop/benchmark_splitting_point_inverse/build/CMakeFiles/inverse_bench_7853.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/inverse_bench_7853.dir/depend

