#!/bin/bash

# Coq branch: ssr-bang-rewrite
# HoTT branch: ssr

# coq_makefile -f ssreflect-_CoqProject -o ssreflect-Makefile

make -f /home/andreas/Source/math-comp/mathcomp/ssreflect/ssreflect-Makefile \
  COQC=/home/andreas/Source/HoTT-Local/hoqc \
  COQTOP=/home/andreas/Source/HoTT-Local/hoqtop \
  COQDEP=/home/andreas/Source/HoTT-Local/hoqdep
