aarch64-linux-gnu-gcc -Wall -c utils.c -std=c99
aarch64-linux-gnu-as -g -o $1.o $1.s
aarch64-linux-gnu-gcc -z noexecstack -o $1 $1.o utils.o