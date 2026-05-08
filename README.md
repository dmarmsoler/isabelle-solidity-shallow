# A Shallow Embedding of Solidity for Isabelle/HOL

This directory contains a shallow embedding of Solidity in Isabelle/HOL.
It is a copy of the corresponding [AFP entry](https://www.isa-afp.org/entries/Isabelle-Solidity.html).
A corresponding deep embedding is available [here](https://github.com/dmarmsoler/isabelle-solidity-deep).

## Prerequisites

* The formalization requires [Isabelle 2025-2](https://isabelle.in.tum.de/).
Please follow the instructions on the Isabelle home page for your operating system.
In the following, we assume that the ``isabelle`` tool is available on the command line.
This might require to add the Isabelle binary directory to the ``PATH`` environment variable of your system.

* The formalization also requires [Finite Maps Extras](https://www.isa-afp.org/entries/Finite-Map-Extras.html) from the [AFP](https://www.isa-afp.org/).
[Here](https://www.isa-afp.org/help/) is a guide on how to include the AFP for local builds.

## Using the Formalization

The formalization can be loaded into Isabelle/jEdit by executing 

```sh
isabelle jedit Solidity_Main.thy
```

on the command line. Alternatively, you can start Isabelle/jEdit by 
clicking on the Isabelle icon and loading the theory 
[Solidity_Main.thy](./Solidity_Main.thy) manually. 

To use a command line build that also generates a PDF document,
first add ``path/to/solidity`` to your Isabelle roots file which is
a file called ``ROOTS`` in your Isabelle home directory.
Then, the build can be started by executing:

```sh
isabelle build -D .
```