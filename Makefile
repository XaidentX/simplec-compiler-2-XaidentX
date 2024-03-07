SRC := \
	typecheck.c \
	table.c \
	ast.c \
	ast_printer.c \
	util.c \
	main.c

OBJ := $(SRC:%.c=%.o)

PRG := simplec

.PHONY: all ast clean

all: simplec

simplec: $(OBJ) parser.tab.o.precompiled lexer.o.precompiled
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c $<

clean:
	rm -f $(OBJ) simplec
