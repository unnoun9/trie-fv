.PHONY: all clean
build_dir := build
src := AbstractAutomata ConcreteAutomata

all: $(src)

# pattern rule: make foo compiles foo.v to build/foo.vo
%: %.v
	@mkdir -p $(build_dir)
	rocq compile -Q build Trie $< -o $(build_dir)/$@.vo

clean:
	rm -rf $(build_dir)
	rm .lia.cache