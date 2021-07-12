The Carth programming language
==============================

*Purely functional programming with lisp-syntax. Less infix, more parens!*

Visit <https://carth.pink/> for an overview of
the language and more info.

WORK IN PROGRESS
------------------

Just as a little disclaimer: this project is still in alpha
development, so there are no guarantees of stability etc.

Features
--------

- Scheme-inspired syntax and feel
- Static, Hindley-Milner typechecking à la ML
- Currying
- Closures
- Algebraic datatypes
- LLVM backend

Roadmap
-------

This is a high-level overview of what is planned for the language, and
some of the points are just tentative. See [TODO.org](./TODO.org) for
more extensive list of planned features and more detailed descriptions.

- Typeclasses
- Type families
- Higher kinded types
- Effect system
- Linear types

Building Carth
--------------

The compiler is written in [Haskell](https://haskell.org) and uses the
[Stack](https://www.haskellstack.org/) build system, while the
core-library is written in [Rust](https://rust-lang.org). The external
dependencies required are [LLVM](https://llvm.org/) version 9.

To build the project and install the `carth` binary, the core library,
and the standard library, simply run `make install`, which defaults to
installing the binary in `~/.local/bin`, the core library in
`~/.local/lib`, and the modules of the Carth standard library in
`~/.carth/mod`.

Building with Carth
-------------------

At compiler runtime, the dependencies are `libsigsegv`, `libdl`,
`libpthread`, `libm`, and `libgc`, which are linked into the executables
produced by Carth.

Carth must further be able to find the core library and standard library
modules, so you must have added the directory of the installed core
library (default `~/.local/lib`) to your `LIBRARY_PATH` environment
variable, the directory of the installed standard library (default
`~/.carth/mod`) to your `CARTH_MODULE_PATH` environment variable.

Running
-------

```bash
# General help
carth help
carth -h
carth --help

# Help for a specific subcommand
carth help c

# Compile and run a program with default output filename
carth c examples/fizzbuzz.carth
./out

# Run with the JIT compiler
carth run examples/fizzbuzz.carth

# Compile a program with a specific output filename
carth c -o examples/fizzbuzz examples/fizzbuzz.carth
./examples/fizzbuzz
```

License
-------

*Preface: copyright is a spook & capitalism is killing this planet.*

Carth is dual licensed under the Anti-Capitalist Software License or
the AGPL version 3 or later. See [LICENSE-ACSL](./LICENSE-ACSL) and
[LICENSE-AGPLv3](./LICENSE-AGPLv3) for the full license texts. For
more information about the licenses, go to
[anticapitalist.software](https://anticapitalist.software) or
[gnu.org](https://www.gnu.org/licenses/agpl-3.0.en.html).

About the seriousness and enforcability of the anti-capitalist
software license, there's this quote from the homepage which sums it
up quite well:

> Copyright is easier to apply to how a work is used than to who uses
> it, and this license has not been tested in court. That said, using
> ACSL software against its terms would open the user to
> litigation. ACSL may best be considered a strong deterrent [against
> organizations organized along capitalist lines], as well as a way to
> state the politics and moral center of your code.

I include the AGPLv3+ as an alternative to be at least a little
pragmatic ;)
