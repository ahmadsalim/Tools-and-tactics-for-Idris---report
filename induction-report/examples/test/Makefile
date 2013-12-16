all: clean compile
clean:
	- rm test.ibc test.log
compile:
	idris --log 2 test.idr -o test.ibc > test.log
run:
	idris test.idr
