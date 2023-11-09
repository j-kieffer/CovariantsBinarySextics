
FLINT_DIR = /home/jean/install

all:
	gcc -I$(FLINT_DIR)/include/flint -I$(FLINT_DIR)/include hecke_matrices.c -L$(FLINT_DIR)/lib -lflint -lgmp -o hecke_matrices.exe
	gcc -I$(FLINT_DIR)/include/flint -I$(FLINT_DIR)/include hecke_eigenvalues.c -L$(FLINT_DIR)/lib -lflint -lgmp -lm -o hecke_eigenvalues.exe
