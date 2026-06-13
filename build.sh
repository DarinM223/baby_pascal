gcc -Wall -c utils.c -std=c99
as --64 -g -o $1.o $1.s
gcc -z noexecstack -o $1 $1.o utils.o