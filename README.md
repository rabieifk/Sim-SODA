# Sim-SODA

**Objective:** Analysis of the relationship between efficiency, power consumption and AVF.

**Tools:** [Sim-SODA](https://pdfs.semanticscholar.org/b490/7b8a9d4c597acf947246f401e3752f30ff0b.pdf), [McPat](https://www.hpl.hp.com/research/mcpat/) and [Matlab](https://www.mathworks.com/products/matlab.html)


[Alpha processor](https://en.wikipedia.org/wiki/DEC_Alpha) is used in this project and SPEC2000 is the benchmark. The Sim-SODA simulator works based on Alpha processor and after running a benchmark it reports utilization, performance and AVF. The purpose of this project is to calculate the power consumption for different periods of a program. For this purpose I should change Sim-SODA to report AVF for every intrevals. Then the result of Sim-SODA sould be translated to be understandable for McPat.

-interval can help in [sim-SODA] to devie the instructions of program in to intervals.

-cycleinterval is used for time devision in sim-SODA

sim-SODA do not report replacement and write back in cache timing but [McPat] need the number of hits, miss replacement and write bach.
