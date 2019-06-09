# Sim-SODA
Analysis of the relationship between efficiency, power consumption and AVF


[Alpha processor](https://en.wikipedia.org/wiki/DEC_Alpha) is used in this project and SPEC2000 is the benchmark.

The purpose of this project is to calculate the power consumption for different periods of a program.

-interval can help in [sim-SODA](https://pdfs.semanticscholar.org/b490/7b8a9d4c597acf947246f401e3752f30ff0b.pdf) to devie the instructions of program in to intervals.

-cycleinterval is used for time devision in sim-SODA

sim-SODA do not report replacement and write back in cache timing but [McPat](https://www.hpl.hp.com/research/mcpat/) need the number of hits, miss replacement and write bach.
