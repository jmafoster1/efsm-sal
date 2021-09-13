# EFSM SAL
EFSM models fit nicely with the notion of model checking. We can therefore express properties over EFSMs in LTL and check that these properties are true with a model checker. We present a toolset to convert EFSM models and LTL properties between the Isabelle theorem prover and the SAL model checker. This repository demonstrates our toolset with four case studies.

## Cloning
This repository makes reference to several submodules. When cloning this repository, you should do so with the `--recursive` option, i.e. `git clone --recursive https://github.com/jmafoster1/efsm-sal.git`

## Prerequisites
### SAL
Our toolset is designed to work with the [Symbolic Analysis Laboratory (SAL)](http://sal.csl.sri.com/) model checker. You need to have this installed on your system. Full installation instructions can be found [here](http://sal.csl.sri.com/download.shtml).

In order to run SAL on these examples, you need to have the `lib` directory location in your `SALCONTEXTPATH` environment variable. You can set this variable in your `.bashrc` file if you're using bash. If you're not using bash, you're on your own!

### Isabelle
Our toolset is designed to work with the [Isabelle/HOL](https://isabelle.in.tum.de/) theorem prover. Our toolset makes reference to the [Extended Finite State Machine](https://www.isa-afp.org/entries/Extended_Finite_State_Machines.html) entry in the Archive of Formal Proofs. This is only available from 2020 onwards. If you are using an older version, you will need to upgrade or manually install the entry.

## Tools
Our tools are located in the `jars` directory. Each can be run using `java -jar TOOLNAME.jar file/to/convert`, where `file/to/convert` is the filepath of the file to convert, and `TOOLNAME` is one of the following:
- `dottoisabelle` - converts DOT files representing EFSMs into an Isabelle representation. This enables EFSMs to be edited graphically. For examples of the syntax to use, see the [`examples`](/tree/master/examples) directory.
- `isabellesal` converts Isabelle representations of EFSMs and LTL properties to SAL for quick and easy counterexample generation.
- `salisabelle` converts SAL EFSMs and properties to Isabelle to enable coinductive proofs for the strongest assurance.

If called without a file argument, all three tools will bring up a file chooser window.

## Make commands
Our repository contains a makefile with several supported commands.
- `dot` - Converts DOT files to PDFs for easy viewing
- `clean` - deletes Isabelle temporary files
- `cleanall` - deletes Isabelle temporary files, dot files, PDF files, and SAL files. This is used for testing and assumes that Isabelle theories are the "original".
- `wellformed` - runs the SAL wellformedness checker on all SAL files in the repository.

The `examples` directory also contains a makefile, with several commands relating to the examples.
- `clean` - similar to `cleanall` above but also removes temporary files (e.g. error logs) created by our toolset.
- `testwf` - similar to `wellformed` above, but specifically for the `examples` directory.
- `testsal` - executes SAL on all theorems to ensure they pass and fail as expected.
- `dot` - Same as `dot` above.
