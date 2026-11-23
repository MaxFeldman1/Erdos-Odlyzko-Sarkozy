CC=clang
CFLAGS=-O3 -mcpu=native -Wall -Xpreprocessor -fopenmp -I/opt/homebrew/opt/libomp/include -I/opt/homebrew/opt/fftw/include
LDFLAGS=-L/opt/homebrew/opt/libomp/lib -lomp -L/opt/homebrew/opt/fftw/lib -lm
all: bin/eos_cover bin/eos_full bin/eos_char
bin/eos_cover: src/eos_cover.c src/common.h
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)
bin/eos_full: src/eos_full.c src/common.h
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)
bin/eos_char: src/eos_char.c src/common.h
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS) -lfftw3
