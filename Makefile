#ifeq (${COMMON},)
#$(error "Must set the common directory. Source the develop script at the root of the repository or set the COMMON environment variable")
#endif

ROOT=../../
COMMON=${ROOT}/apps/common

include ${COMMON}/Makefile.inc

GHCINC=${CUDD_HASKELL_PATH} \
       ${TSL_PATH} \
       ${SYNTHESIS_PATH} \
       ${FSM_PATH} \
       ${DEBUGGER_PATH} \
       $(ABSTRACT_PATH) \
       $(BACKEND_PATH)
LIBS=${CUDDLIBS} ${CUDDHLIB} ${SYNTHLIB}
LIBPATHS=${CUDDLIBPATHS} \
	 ${CUDD_HASKELL_PATH} \
	 ${SYNTHESIS_PATH} \
	 ${TSL_PATH}
TARGET=parser.hs
CLIBS=${LIBS} stdc++
GHC_FLAGS+=-o parser # -prof -auto-all -rtsopts # -fforce-recomp 

example: parser
	make -C examples/uart


#-rtsopts=all -debug
#GHC_FLAGS+=-o $(ROOT)/bin/termite -prof -auto-all -caf-all #-fforce-recomp 


#CFLAGS=-g
#TARGET=termite
#
#WHERE=../../3rd_party/lib/cudd-2.4.2
#INCLUDE=-I$(WHERE)/include
#FFI=../../lib/CUDD_haskell
#DEBUGLIB=../../lib/debug
#ABSTRACTLIB=../../lib/abstract
#SYNTHLIB=../../lib/synthesis
#FSM_LIB=../../lib/FSM_draw
#TSL_COMPILER=../../lib/tsl
#
#GHCINC=$(FFI):$(TSL_COMPILER):$(DEBUGLIB):$(ABSTRACTLIB):$(SYNTHLIB):$(FSM_LIB)
#
#LIBS=-L$(WHERE)/dddmp -L$(WHERE)/cudd -L$(WHERE)/mtr -L$(WHERE)/st -L$(WHERE)/util -L$(WHERE)/epd -L$(FFI)
#
#LIBNAMES=-ldddmp -lcudd -lmtr -lst -lutil -lepd -lcuddwrap
#
#CLIBNAMES=-optl-lcudd -optl-ldddmp -optl-lmtr -optl-lst -optl-lutil -optl-lepd
#
##make -C $FFI
#
#
#all: $(TARGET)
#
#debug: 
#	ghci $(TARGET).hs $(INCLUDE) $(WHERE)/dddmp/*.o \
#    		  $(WHERE)/cudd/*.o \
#		  $(WHERE)/mtr/*.o \
#		  $(WHERE)/st/*.o \
#		  $(WHERE)/util/safe_mem.o \
#		  $(WHERE)/util/cpu_time.o \
#		  $(WHERE)/util/datalimit.o \
#		  $(WHERE)/epd/*.o \
#		  $(FFI)/*.o \
#		  -i../../lib/tsl/:../../lib/CUDD_haskell:../../lib/abstract\
#		  -fbyte-code \
#		  -fbreak-on-error
#
#.PHONY: $(TARGET)
#$(TARGET):
#	ghc --make -debug -ferror-spans -O2 -i$(GHCINC) $(TARGET).hs $(INCLUDE) $(LIBS) $(LIBNAMES) $(CLIBNAMES)
#
#clean:
#	rm -f *.o  *.hi $(TARGET)
