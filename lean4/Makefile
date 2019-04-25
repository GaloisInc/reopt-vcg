
# TODO: Set LEAN_DIR

LEAN=$(LEAN_DIR)/bin/lean
LEANC=$(LEAN_DIR)/bin/leanc
LEAN_PATH=$(LEAN_DIR)/library:.

COMMON_SRCS = hex.lean json.lean rbnode.lean reader.lean
SRCS = $(COMMON_SRCS) test_json_parse.lean test_json_render.lean
OLEANS = $(SRCS:.lean=.olean)
COMMON_OBJS=$(COMMON_SRCS:.lean=.o)
DEPS = $(SRCS:.lean=.depend)

.PHONY : all clean

all : bin/test_json_render $(OLEANS)

bin/test_%: test_%.o $(COMMON_OBJS)
	@mkdir -p bin
	$(LEANC) -o $@ $^

%.o: %.cpp
	$(LEANC) -c $(CPPFLAGS) -o $@ $<

%.depend: %.lean
	echo $(<:.lean=.olean): `$(LEAN) --deps $< | python relative.py` > $@

%.olean: %.lean %.depend
	$(LEAN) --make --cpp="$*.cpp.tmp" $<
	mv "$*.cpp.tmp" "$*.cpp"
	@touch $*.olean

%.cpp: %.olean
	@

clean :
	rm -rf *.cpp
	rm -rf *.depend
	rm -rf *.o
	rm -rf *.olean
	rm -rf bin

# Dependencies

.PRECIOUS: %.depend %.cpp %.o

-include $(DEPS)
