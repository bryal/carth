prefix=~/.carth
bin_dir=$(prefix)/bin
lib_dir=$(prefix)/lib
mod_dir=$(prefix)/mod

.PHONY: carth-bin
carth-bin:
	stack build

.PHONY: foreign-core
foreign-core:
	cd foreign-core; cargo build --release

.PHONY: install
install: install-bin install-lib install-mods

.PHONY: install-bin
install-bin: carth-bin bin-dir
	stack install --local-bin-path $(bin_dir)

.PHONY: install-lib
install-lib: foreign-core lib-dir
	cp foreign-core/target/release/libcarth_foreign_core.a $(lib_dir)

.PHONY: install-mods
install-mods: mod-dir
	cp std/* $(mod_dir)/

.PHONY: bin-dir
bin-dir:
	mkdir -p $(bin_dir)

.PHONY: lib-dir
lib-dir:
	mkdir -p $(lib_dir)

.PHONY: mod-dir
mod-dir:
	mkdir -p $(mod_dir)

.PHONY: clean
clean:
	stack clean
