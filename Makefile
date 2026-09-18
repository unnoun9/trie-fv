.PHONY: all clean
build_dir := build
src := abs_aut abs_ex conc_aut conc_ex sim

all: $(src)

# pattern rule: make foo compiles foo.v to build/foo.vo
%: %.v
	@mkdir -p $(build_dir)
	rocq compile -Q build Trie $< -o $(build_dir)/$@.vo

# what each file requires has to be compiled first
abs_ex conc_aut: abs_aut 
conc_ex sim: conc_aut

clean:
	rm -rf $(build_dir)
	rm .lia.cache
