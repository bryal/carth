prefix=~/.carth
bin_dir=$(prefix)/bin
lib_dir=$(prefix)/lib
mod_dir=$(prefix)/mod

.PHONY: all
all: carth-bin foreign-core

.PHONY: install
install: install-bin install-lib install-mods

.PHONY: carth-bin
carth-bin: foreign-core
	stack build

.PHONY: foreign-core
foreign-core:
	cd foreign-core; cargo build --release

.PHONY: install-bin
install-bin: carth-bin
	mkdir -p $(bin_dir) && stack install --local-bin-path $(bin_dir)

.PHONY: install-lib
install-lib: foreign-core
	mkdir -p $(lib_dir) && cp foreign-core/target/release/libcarth_foreign_core.a $(lib_dir)

.PHONY: install-mods
install-mods:
	mkdir -p $(mod_dir) && cp std/* $(mod_dir)/

.PHONY: clean
clean:
	stack clean --full && rm carth.cabal
