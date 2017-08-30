# Makefile for Constrained Persistent Perfect Phylogeny
SRC_DIR	=src
OBJ_DIR	=obj
LIB_DIR =lib
TEST_DIR = tests
BIN_DIR	=bin
CC = g++

P = $(BIN_DIR)/polytime-cpp
SRCS := $(wildcard $(SRC_DIR)/*.cpp)
SOURCES := $(SRCS:$(SRC_DIR)/%=%)

CFLAGS_STD = -g -Wall -march=native -Wno-deprecated -Wno-parentheses -Wno-format
# DEBUG_LIBS = #efence

CFLAGS_EXTRA =  -m64 
# #CFLAGS_LIBS = `pkg-config --cflags $(STD_LIBS)`
# LDLIBS = `pkg-config --libs $(STD_LIBS)`
CFLAGS = $(CFLAGS_STD) $(CFLAGS_EXTRA)
OBJECTS = $(SOURCES:%.cpp=$(OBJ_DIR)/%.o) $(LIBS)
CC_FULL = $(CC) $(CFLAGS) $(CFLAGS_LIBS)

paper: bin
	cd paper && ./run_experiment

# dist: CFLAGS +=  -O3 -DNDEBUG
# dist: bin
bin: $(P)

# debug: CFLAGS += -DDEBUG -O0
# debug: LDLIBS += -lefence
# debug: bin

# debug-dist: CFLAGS += -DDEBUG -O3

# debug-dist: bin

# profile: CFLAGS += -O3 -DNDEBUG

# profile: dist
# 	rm -f callgrind.*
# 	valgrind -q --tool=callgrind --dump-instr=yes $(P) -o /dev/null $(REG_TESTS_DIR)/input/test-counterexample-recomb-cg-2015.txt
# 	# See the results with kcachegrind


$(P): $(OBJECTS)
	@echo 'Linking $@'
	@mkdir -p $(BIN_DIR)
	$(CC_FULL) -o $@ $(OBJECTS)

# all: $(P) doc
# 	echo $(OBJECTS)

${OBJ_DIR}/%.o: $(SRC_DIR)/%.cpp $(LIBS)
	@echo '* Compiling $<'
	@mkdir -p $(dir $@)
	$(CC_FULL) -o $@ -c $<


clean: clean-test
	@echo "Cleaning..."
	rm -rf  ${OBJ_DIR} ${P} $(SRC_DIR)/*.d $(SRC_DIR)/cmdline.[ch] callgrind.out.*

clean-test:
	@echo "Cleaning tests..."
	rm -rf ${TEST_DIR}/*.o ${TEST_DIR}/*/output/*

# tests: test


# doc: dist
# 	doxygen && cd docs/latex/ && latexmk -recorder -use-make -pdf refman

.PHONY: all clean doc paper

# ifneq "$(MAKECMDGOALS)" "clean"
# -include ${SOURCES:.c=.d}
# -include ${T_SOURCES:.c=.d}
# endif

# $(SRC_DIR)/cmdline.c $(SRC_DIR)/cmdline.h: cppp.ggo
# 	gengetopt -i $< --output-dir=$(SRC_DIR)
