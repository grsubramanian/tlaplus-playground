Running the TLA+ model checker on the specs
==

0. Ensure `$CLASSPATH` contains the path to the bundled `tlatools2.jar` file.
1. Understand the various options for the TLA+ model checker tool by running `java tlc2.TLC -help`.
2. Learn more about how to write model checker config files by reading https://apalache.informal.systems/docs/apalache/tlc-config.html.
3. For a simple run, execute `java -XX:+UseParallelGC tlc2.TLC -config <configfile.cfg> <specfile.tla>`.
