#!/bin/sh
# Remaining runs: typed composite sample (direct counts) and prime moduli via FFT.
cd "$(dirname "$0")"
( time bin/eos_full list data/list_full_sample.txt data/full_sample.csv ) > data/log_full_sample.txt 2>&1
( time bin/eos_char data/list_primes_char_small.txt data/char_small.csv ) > data/log_char_small.txt 2>&1
( time env OMP_NUM_THREADS=6 bin/eos_char data/list_primes_char_big.txt data/char_big.csv ) > data/log_char_big.txt 2>&1
echo ALLDONE >> data/log_char_big.txt
