Eldarica
========

Eldarica is a model checker for Horn clauses, Numerical Transition
Systems, and Scala programs.  Inputs can be read in a variety of
formats, including SMT-LIB 2 and Prolog for Horn clauses, and are
analysed using a variant of the Counterexample-Guided Abstraction
Refinement (CEGAR) method. Eldarica is fast and includes sophisticated
interpolation-based techniques for synthesising new predicates for
CEGAR, enabling it to solve a wide range of verification problems.

Eldarica has been developed by Hossein Hojjat and Philipp Ruemmer,
with further contributions by Filip Konecny and Pavle Subotic.

There is a simple **web interface** to experiment with the C interface
of Eldarica:
http://logicrunch.it.uu.se:4096/~wv/eldarica

The latest **nightly build** is available from: http://logicrunch.it.uu.se:4096/~wv/eldarica/eldarica-bin-nightly.zip

Documentation
-------------

You can either download a binary release of Eldarica, or compile the Scala
code yourself. For the latter, you need a recent Scala compiler, and set
the environment variable <code>SCALA_HOME</code> to point to the directory of the Scala
distribution. After that you can simply call <code>ant</code> to start
the build.

After compilation (or downloading a binary release), calling Eldarica
is normally as easy as saying

  <code>./eld regression-tests/horn-smt-lib/rate_limiter.c.nts.smt2</code>

You can use the script <code>eld-client</code> instead of
<code>eld</code> in order to run Eldarica in a server-client mode,
which significantly speeds up processing of multiple problems.

A full list of options can be obtained by calling <code>./eld
-h</code>.<br> In particular, the options <code>-disj</code>,
<code>-abstract</code>, <code>-stac</code> can be used to control
predicate generation.

Papers
------

* The canonical reference to Eldarica:
  "A Verification Toolkit for Numerical Transition Systems - Tool Paper."
  http://link.springer.com/chapter/10.1007%2F978-3-642-32759-9_21
* "Guiding Craig Interpolation with Domain-specific Abstractions"
  http://link.springer.com/article/10.1007%2Fs00236-015-0236-z
* "Accelerating Interpolants"
  http://link.springer.com/chapter/10.1007%2F978-3-642-33386-6_16
* "Disjunctive Interpolants for Horn-Clause Verification"
  http://link.springer.com/chapter/10.1007%2F978-3-642-39799-8_24
* "Exploring interpolants"
  http://dx.doi.org/10.1109/FMCAD.2013.6679393

Related Links
-------------

* A library of Horn clause benchmarks:
  https://svn.sosy-lab.org/software/sv-benchmarks/trunk/clauses/LIA/Eldarica/
* Numerical transition system benchmarks:
  http://richmodels.epfl.ch/ntscomp/ntslib

[![Build Status](https://travis-ci.org/uuverifiers/eldarica.svg?branch=master)](https://travis-ci.org/uuverifiers/eldarica)
