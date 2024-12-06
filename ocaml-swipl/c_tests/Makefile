SOURCES = $(wildcard *.c)
TARGETS = $(basename $(SOURCES))
Q = @

FLAGS = $(shell pkg-config --cflags --libs swipl)

all: $(TARGETS)

%: %.c
	@echo "[CC] $< → $@"
	$(Q)$(CC) $(FLAGS) -o $@ $<

clean:
	@echo "[RM] $(TARGETS)"
	$(Q)rm -rf $(TARGETS)
