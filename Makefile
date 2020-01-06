CARTH_DIR=~/.carth
BIN_DIR=$(CARTH_DIR)/bin
LIB_DIR=$(CARTH_DIR)/lib
MOD_DIR=$(CARTH_DIR)/mod

.PHONY: carth-bin
carth-bin: bin-dir clean-stack
	(export CARTH_LIB_DIR=$(LIB_DIR); export CARTH_MOD_DIR=$(MOD_DIR); stack build)

.PHONY: foreign-core
foreign-core: lib-dir
	cd foreign-core; cargo build --release

.PHONY: install
install: install-bin install-lib install-mods

.PHONY: install-bin
install-bin: carth-bin
	stack install --local-bin-path $(BIN_DIR)

.PHONY: install-lib
install-lib: foreign-core
	cp foreign-core/target/release/libcarth_foreign_core.a $(LIB_DIR)

.PHONY: install-mods
install-mods: mod-dir
	cp std/* $(MOD_DIR)/

.PHONY: bin-dir
bin-dir: carth-dir
	mkdir -p $(BIN_DIR)

.PHONY: lib-dir
lib-dir: carth-dir
	mkdir -p $(LIB_DIR)

.PHONY: mod-dir
mod-dir: carth-dir
	mkdir -p $(MOD_DIR)

.PHONY: carth-dir
carth-dir:
	mkdir -p $(CARTH_DIR)

.PHONY: clean-stack
clean-stack:
	stack clean
