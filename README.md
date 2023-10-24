# EC551_Lab1
Programming Assignment 1 – Logic Synthesis Engine for EC551

# Repo Organization
program1.py -- Contains main function as well as all sub-functions called during the main function

input_examples/ -- Contains two examples of inputs to program1.py

   input.txt shows an example boolean algebraic function input 

   BILF.txt shows an example of BILF (Berkeley Logic Interchange Format) input which 
   represents a digital combinational logic circuit

# Tool Description
This tool is an attempt to make a logic synthesis engine. It takes either a boolean algebraic
function or a digital combinational logic circuit (BILF) input from a text file and produces a 
variety of outputs:
1. The design as a canonical SOP
2. The design as a canonical POS
3. The design INVERSE as a canonical SOP
4. The design INVERSE as a canonical POS
5. A minimized number of literals representation in SOP
  a. The number of saved literals vs. the canonical version
6. A minimized number of literals representation in POS
  a. Report on the number of saved literals vs. the canonical version
7. The number of Prime Implicants
8. The number of Essential Prime Implicants
9. The number of ON-Set minterms
10. The number of ON-Set maxterms
11. The total number of transistors needed for the minimized SOP design
12. The total number of transistors needed for the minimized POS design
    
The tool also produces the inputted boolean expression, variable names, minterms, maxterms, and
recommends SOP or POS design based on required transistor numbers.

Essential prime implicants and prime implicants are found through the use of the Quine-
McCluskey method. An open source python library (shown here: https://github.com/tpircher-zz/quine-mccluskey/tree/master) 
was used to calculate the Essential Prime Implicants through the provided QM algorithm, and the 
sympy library was used for much of the boolean algebra.

# How to run the program
Some libraries may need to be downloaded, such as sympy and pyeda, to run the code properly.
Ensure that input files are located in the same directory as the program.
The program can be run with the following command on windows:

**python .\program1.py input.txt**

When prompted with: "Is the input a combinational logic circuit or a boolean algebraic function? (C/B):"
input 'C' for combinational logic circuit and 'B' for boolean algebraic function.

The input file is passed as an argument with the run command.
Input constraints can be found on the example input text files.

# Collaborators 
This program was made with the assistance of ChatGPT-3.5 as an AI coding copilot. ChatGPT was 
used mainly for debugging/syntax and recommendations on function implementations.
  
