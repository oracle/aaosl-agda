# Formal Verification of Authenticated, Append-Only Skip Lists in Agda

  This repository provides the Agda proofs described in the paper "Formal Verification of Authenticated, Append-Only Skip Lists in Agda", published in [CPP2021](https://popl21.sigplan.org/home/CPP-2021); the remaining description assumes familiarity with that paper.  The repository contains a model of a class of Authenticated Append-Only SkipLists (AAOSLs), proofs of some key correctness properties of this class, and an instantiation of the class that yields a specific AAOSL due to [Maniatis and Baker](http://arxiv.org/abs/cs.CR/0302010), thus confirming the properties argued manually in that paper.  The model and proofs are written in [Agda](https://agda.readthedocs.io).

## Repository structure

The development is structured as follows:

* The [Data namespace](Data) contains auxiliary definitions and proofs relating to injective encoding of natural numbers and reasoning about whether they are odd or even.
* The [Abstract namespace](AAOSL/Abstract) contains a model of a class of AAOSLs, parameterized by a _dependency relation_ `DepRel` that defines the "hops" used by an AAOSL, along with properties this relation is required to obey.  It includes proofs of the key correctness properties, culminating in the Evolutionary Collision Resistance (EVO-CR) property.
* The [Concrete module](AAOSL/Concrete.agda) provides a concrete instance of our AAOSLs (by constructing a `DepRel`), which is equivalent to the one presented by [Maniatis and Baker](http://arxiv.org/abs/cs.CR/0302010).  It depends on definitions and key properties presented in the [Hops.agda](AAOSL/Hops.agda) module.

## Getting started

To work with `aaosl-agda`, you need to have Agda and its standard library installed.  The project currently works with Agda version 2.6.1.1 and Agda Standard Library v1.3 (i.e., we can successfully run `./Scripts/run-everything.sh yes` without errors or warnings).  Detailed instructions for installing Agda and setting up your environment are included in the [Getting Started section](https://plfa.github.io/GettingStarted) of [Programming Language Foundations in Agda](https://plfa.github.io), which is an excellent resource for learning Agda.

Once you have installed the correct version of Agda, you should be able to run `./Scripts/run-everything.sh yes` from the root directory of the project and observe successful completion with no errors or warnings.

To explore the repo, we suggest starting with the [`AAOSL.Abstract.Advancement`](AAOSL/Abstract/Advancement.agda) module to understand the abstract correctness proof for a class of AAOSLs, and then examine the [`AAOSL.Concrete`](AAOSL/Concrete.agda) module to see how we instantiate this class to achieve proofs of key properties of the original AAOSL due to [Maniatis and Baker](http://arxiv.org/abs/cs.CR/0302010).

If you would like to consider contributing to the project, please see our [Contribution Guide](CONTRIBUTING.md).

## Get Support

* Open a [GitHub issue](https://github.com/oracle/aaosl-agda/issues) to provide feedback, raise issues or ask questions.
* Report a security vulnerability according to the [Reporting Vulnerabilities guide](https://www.oracle.com/corporate/security-practices/assurance/vulnerability/reporting.html). More information at [SECURITY](SECURITY.md).

## License

`aaosl-agda` is [licensed](LICENSE.txt) under [UPL 1.0](https://opensource.oracle.com/licenses/upl).

## Contributors

As of the beginning of this repo, contributions have been made by
[Victor Cacciari Miraldo](https://github.com/VictorCMiraldo), [Harold Carr](https://github.com/haroldcarr), [Mark Moir](https://github.com/mark-moir), and [Lisandra Silva](https://github.com/lisandrasilva), all while employed at Oracle Labs.

We are grateful to the following people for contributions since then:
* [Chris Jenkins](https://github.com/cwjnkins)
* `[your name here]`

