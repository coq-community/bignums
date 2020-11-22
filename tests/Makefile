COQC=coqc

all: success output

success: $(addsuffix o,$(wildcard success/*.v))

output: $(addsuffix o,$(wildcard output/*.v))

success/%.vo: success/%.v
	$(COQC) $<

output/%.vo: output/%.v
	input=$<; \
	output=$${input%.v}.out.real; \
	$(COQC) $< 2>&1 > $$output; \
	diff --strip-trailing-cr $${input%.v}.out $$output
