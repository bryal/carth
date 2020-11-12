bin_dir=~/.local/bin
lib_dir=~/.local/lib
mod_dir=~/.carth/mod

.PHONY: all
all: carth-bin std-rs

.PHONY: install
install: install-bin install-lib install-mods

.PHONY: carth-bin
carth-bin: std-rs
	stack build

.PHONY: std-rs
std-rs:
	cd std-rs && cargo build --release

.PHONY: install-bin
install-bin: carth-bin
	mkdir -p $(bin_dir) && stack install --local-bin-path $(bin_dir)

.PHONY: install-lib
install-lib: std-rs
	mkdir -p $(lib_dir) && cp std-rs/target/release/libcarth_std_rs.a $(lib_dir)

.PHONY: install-mods
install-mods:
	mkdir -p $(mod_dir) && cp std/* $(mod_dir)/

.PHONY: clean
clean:
	stack clean --full && rm carth.cabal
	cd std-rs && cargo clean
