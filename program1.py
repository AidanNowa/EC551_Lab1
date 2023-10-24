import argparse
import sympy
from sympy import Not, simplify
from sympy.abc import A, B, C, D
from sympy.parsing.sympy_parser import (parse_expr, standard_transformations, implicit_multiplication_application)
from sympy.logic.boolalg import Or, And
from itertools import product
from quine_mccluskey.qm import QuineMcCluskey
import re

def parse_boolean_expression_file(file_path):
    with open(file_path, 'r') as file:
        for line in file:
            line = line.strip()
            if line.startswith('#') or not line:
                continue #ignore comments/empty lines
            return line #we assume only one line for the expression
        
    return None # return none if no expression found


def read_blif(filename):
    inputs = []
    outputs = []
    logic = []

    with open(filename, 'r') as file:
        lines = file.readlines()

    for line in lines:
        if line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) == 0:
            continue
        if parts[0] == ".inputs":
            inputs = parts[1:]
        elif parts[0] == ".outputs":
            outputs = parts[1:]
        elif parts[0] == ".names":
            output_var = parts[-1]
            input_vars = parts[1:-1]
            #generate truth table from BLIF by reading the file truth table after each gate declaration
            truth_table = []
            for line in lines:
                if line.startswith("1"):
                    truth_table.append(line.strip()[:-2])
                elif line.startswith("0"):
                    truth_table.append("~" + line.strip()[:-2])
                elif line.startswith("."):
                    break
            #pair output_var with the logical expression created and append to the 'logic' list
            logic.append((output_var, And(*[Or(*(Not(v) for v in input_vars), *truth_table)])))

    return inputs, outputs, logic


def extract_symbols(expression):
    variable_names = list(set(re.findall(r'[A-Za-z]', expression)))
    symbol_set = set(re.findall(r'[A-Za-z]+', expression))

    symbol_string = ' '. join(sorted(symbol_set))

    return symbol_string, variable_names


def boolean_expression_to_minterms(expression, input_symbols):
    symbols = input_symbols.split()
    num_symbols = len(symbols)

    #for sympy, specify list of transformation to be used on an expression
    transformations = (standard_transformations + (implicit_multiplication_application,))
    expression = sympy.parse_expr(expression, transformations=transformations)

    #generate truth table
    truth_table = []
    for assignment in product([0, 1], repeat=num_symbols):
        assignment_dict = dict(zip(symbols, assignment))
        truth_table.append((assignment, expression.subs(assignment_dict)))

    #Extract minterms from the tt (1 in tt)
    minterms = []
    for index, (assignment, value) in enumerate(truth_table):
        if value:
            minterm = []
            for i, symbol in enumerate(symbols):
                if assignment[i] == 0:
                    minterm.append(f'~{symbol}')
                else:
                    minterm.append(symbol)
            minterms.append(" & ".join(minterm))

    return minterms

def boolean_expression_to_maxterms(expression, input_symbols):
    symbols = input_symbols.split()
    num_symbols = len(symbols)

    transformations = (standard_transformations + (implicit_multiplication_application,))
    expression =sympy.parse_expr(expression, transformations=transformations)

    truth_table = []
    for assignment in product([0, 1], repeat=num_symbols):
        assignment_dict = dict(zip(symbols, assignment))
        #not(expression) utilize the not of the expression and find minterms as before (maxterms now)
        truth_table.append((assignment, not(expression).subs(assignment_dict)))

    #Extract maxterms from the tt (0 in tt)
    maxterms = []
    for index, (assignment, value) in enumerate(truth_table):
        if value:
            maxterm = []
            for i, symbol in enumerate(symbols):
                if assignment[i] == 0:
                    maxterm.append(f'~{symbol}')
                else:
                    maxterm.append(symbol)
            maxterms.append(" & ".join(maxterm))

    return maxterms

#used to generate the sop expression of the minterms -> simplify() is used to get minimized rep.
def minterms_to_canonical_sop(minterms):
    sop_terms = []
    for minterm in minterms:
        literals = minterm.split(" & ")
        sum_terms = []

        for literal in literals:
            if '~' in literal:
                symbol = literal[1:]
                sum_terms.append(f"~{symbol}")
            else:
                symbol = literal
                sum_terms.append(symbol)
        
        sop_terms.append(f"({' & '.join(sum_terms)})")
    
    sop_expression = " | ".join(sop_terms)

    return sop_expression 

#used to generate the pos expression of the minterms -> simplify() is used to get minimized rep.
def minterms_to_canonical_pos(minterms):
    pos_terms = []

    for minterm in minterms:
        literals = minterm.split(" & ")
        product_terms = []

        for literal in literals:
            if '~' in literals:
                symbol = literal[1:]
                product_terms.append(f"{symbol}")
            else:
                symbol = literal
                product_terms.append(f"({' | '.join(product_terms)})")

    pos_expression = " & ".join(pos_terms)

    return pos_expression


#count literals in both originial and min and subtract to find saved
def calculate_saved_literals(sop_expression, minimized_exp, symbols):

    symbol_list = symbols.split()
    minimized_exp_str = str(minimized_exp)
    original_literals = 0
    minimized_literals = 0

    for symbol in symbol_list:
        original_literals += sop_expression.count(symbol)
        minimized_literals += minimized_exp_str.count(symbol)
    
    saved_literals = original_literals-minimized_literals
    return saved_literals, minimized_literals


#hard coding of converting minterm format (~A & ~B & ~C & ~D) to binary (0000)
def convert_minterms_to_binary(minterms):
    binary_minterms = []
    for minterm in minterms:
        minterm = minterm.replace('~A', '0')
        minterm = minterm.replace('~B', '0')
        minterm = minterm.replace('~C', '0')
        minterm = minterm.replace('~D', '0')
        minterm = minterm.replace('A', '1')
        minterm = minterm.replace('B', '1')
        minterm = minterm.replace('C', '1')
        minterm = minterm.replace('D', '1')
        minterm = minterm.replace('(', '')
        minterm = minterm.replace(')', '')
        minterm = minterm.replace('&', '')
        minterm = minterm.replace('|', '')
        minterm = minterm.replace('+', '')
        minterm = minterm.replace('*', '')
        minterm = minterm.replace(' ', '')

        binary_minterms.append(minterm)

    return binary_minterms

#based off minterm value in binary convert to decimal index for summation notation
def minterms_to_indices(binary_minterms): 
    indices = []
    for i, minterm in enumerate(binary_minterms):
        count = 0
        for j, bit in enumerate(minterm):
            if bit == '1':
                count = count + 2 ** (-1*j + 3)

        indices.append(count)
    return indices

#hamming distance is used to dertermine the difference in combination of input variables in minterms or maxterms
def hamming_distance(s1, s2):
    return sum(c1 != c2 for c1, c2 in zip(s1, s2))

def generate_minterm_table(minterms):
    # Sort minterms by the number of ones (Hamming weight)
    sorted_minterms = sorted(minterms, key=lambda x: x.count('1'))

    while True:
        new_table = []
        used_indices = set()

        for i, term1 in enumerate(sorted_minterms):
            if i in used_indices:
                continue

            for j, term2 in enumerate(sorted_minterms[i + 1:], start=i + 1):
                #organize if they differ by one
                if hamming_distance(term1, term2) == 1:
                    used_indices.add(i)
                    used_indices.add(j)
                    common_bits = [
                        c1 if c1 == c2 else '-'
                        for c1, c2 in zip(term1, term2)
                    ]
                    new_table.append("".join(common_bits))

        if not new_table:
            break

        sorted_minterms = new_table

    return sorted_minterms

def estimate_transistors(expression):
    # Remove spaces for consistent parsing
    expression = expression.replace(" ", "")
    
    # Initialize counts
    num_inverters = 0
    num_and_gates = 0
    num_or_gates = 0
    
    # Find all instances of ~{variable}
    if(expression.find('~A') >= 0):
        num_inverters += 1
    if(expression.find('~B') >= 0):
        num_inverters += 1    
    if(expression.find('~C') >= 0):
        num_inverters += 1    
    if(expression.find('~D') >= 0):
        num_inverters += 1    
    
    # Split the expression into terms based on the '|' symbol
    or_terms = expression.split('|')
    num_or_gates = len(or_terms)
    
    for term in or_terms:
        # Count the number of '&' symbols in each term to determine the number of AND gates
        num_and_gates += term.count('&') + 1 # Add 1 because each term starts with an implicit AND
    
    total_transistors = num_inverters + (2 * num_and_gates) + (2 * num_or_gates)

    return num_inverters, num_and_gates, num_or_gates, total_transistors


def estimate_transistors_pos(expression):
    # Remove spaces for consistent parsing
    expression = expression.replace(" ", "")
    
    # Initialize counts
    num_inverters = 0
    num_and_gates = 0
    num_or_gates = 0
    
    # Find all instances of ~{variable}
    if(expression.find('~A') >= 0):
        num_inverters += 1
    if(expression.find('~B') >= 0):
        num_inverters += 1    
    if(expression.find('~C') >= 0):
        num_inverters += 1    
    if(expression.find('~D') >= 0):
        num_inverters += 1    
    
    # Split the expression into terms based on the '|' symbol
    or_terms = expression.split('&')
    num_or_gates = len(or_terms)
    
    for term in or_terms:
        # Count the number of '&' symbols in each term to determine the number of AND gates
        num_and_gates += term.count('|') + 1 # Add 1 because each term starts with an implicit AND
    
    total_transistors = (num_inverters * 2) + (2 * num_and_gates) + (2 * num_or_gates)

    return num_inverters, num_and_gates, num_or_gates, total_transistors

    
def replace_subexpressions(expression, output_to_expression):
    for key, value in output_to_expression.items():
        expression = expression.replace(key, f'({value[0]})')
    return expression

def main():
    qm = QuineMcCluskey()
    expression_converted = False
    parser = argparse.ArgumentParser(description ='Boolean Expression and Circuit Parser')
    parser.add_argument('input_file', help='Input file containing a boolean expression or circuit description')

    args = parser.parse_args()

    input_file = args.input_file

    is_logic_circuit = input('Is the input a combinational logic circuit or a boolean algebraic function? (C/B): ')
    print('') #add spacing for output visability

    circuit_to_bool_expression = ''
    if is_logic_circuit == 'C':
        bilf_file = input_file
        output_to_expression = {}
 
        inputs, outputs, logic = read_blif(bilf_file)
        #convert output from file parse to dict
        for output_var, expression in logic:
            key = str(output_var)
            value = str(expression)
            if key in output_to_expression:
                output_to_expression[key].append(value)
            else:
                output_to_expression[key] = [value]

        #simplify expression to be output in terms of just inputs
        if 'Y' in output_to_expression:
            y_expression = output_to_expression['Y'][0]  # Get the expression for Y
            y_expression = replace_subexpressions(y_expression, output_to_expression)
            
        # Update the dictionary for Y with the new expression
            output_to_expression['Y'] = [y_expression]

        #send value to logic circuit
        circuit_to_bool_expression = str(output_to_expression['Y'])
        expression_converted = True

    if is_logic_circuit == 'B' or expression_converted == True:
        if expression_converted == False:
            expression = parse_boolean_expression_file(input_file)
            expression = expression.upper()
        elif expression_converted == True:
            expression = circuit_to_bool_expression
            expression = expression.strip("[]'")
        if expression:
            print('Boolean Expression:', expression)
        
            symbols_str, variable_names = extract_symbols(expression)
            print('')
            print('Variable names: ', variable_names)
            
            minterms = boolean_expression_to_minterms(expression, symbols_str)
            print('')
            print('Minterms:', minterms)
            
            maxterms = boolean_expression_to_maxterms(expression, symbols_str)
            print('')
            print('Maxterms:', maxterms)
            binary_minterms = convert_minterms_to_binary(minterms)
            minterm_indices = minterms_to_indices(binary_minterms)
            print('')
            print('1.) Canonical SOP: ', minterm_indices)
            binary_maxterms = convert_minterms_to_binary(maxterms)
            maxterm_indices = minterms_to_indices(binary_maxterms)
            print('')
            print('2.) Canonical POS: ', maxterm_indices)
            sop_expression = minterms_to_canonical_sop(minterms)

            pos_expression = minterms_to_canonical_sop(maxterms)
            print('')
            print('3.) Inverse SOP:', maxterm_indices)

            print('')
            print('4.) Inverse POS:', minterm_indices)
            minimized_sop = simplify(sop_expression, symbols_str)

            minimized_pos = simplify(pos_expression,symbols_str)
            saved_sop_literals, sop_literals = calculate_saved_literals(sop_expression, minimized_sop, symbols_str)

            print('')
            print('5.) Minimized representation in SOP: ', minimized_sop)
            print('5a.) Number of saved literals in SOP: ', saved_sop_literals)
            saved_pos_literals, pos_literals = calculate_saved_literals(pos_expression, minimized_pos, symbols_str)
            print('')
            print('6.) Minimized representation in POS: ', minimized_pos)
            print('6a.) Number of saved literals in SOP: ', saved_pos_literals)


            binary_minterms = convert_minterms_to_binary(minterms)
            minterm_indices = minterms_to_indices(binary_minterms)

            prime_implicants = generate_minterm_table(binary_minterms)

            qm_EPIs = qm.simplify(minterm_indices)
            pi_string = (str(prime_implicants) + ', ' + str(qm_EPIs))
            pi_string_edit = pi_string.replace("[", '').replace("]", '')
            pi_string_final = pi_string_edit.replace("{", '').replace("}", '')
            print('')
            print('Prime Implicants: ', pi_string_final)
            print('7.) Number of Prime Implicants: ', len(prime_implicants) + len(qm_EPIs))
            print('')
            print('Essential Prime Implicants: ', qm_EPIs)
            print('8.) Number of EPIs: ', len(qm_EPIs))
            print('')
            print('9.) Number of ON-set minterms: ', len(minterms))
            print('')
            print('10.) Number of ON-set maxterms: ', len(maxterms))
            print('')
            print("Assumptions:")
            print("Inverter = 2 transitors")
            print("AND and OR gates = 2N transistors where N is # inputs")
            print('')
            inverter_count, and_gate_count, or_gate_count, total_transistors_sop = estimate_transistors(str(minimized_sop))
            print("11.) Total Transistors in SOP Design: ", total_transistors_sop)
            print('')
            inverter_count_pos, and_gate_count_pos, or_gate_count_pos, total_transistors_pos = estimate_transistors_pos(str(minimized_pos))
            print("12.) Total Transistors in POS Design: ", total_transistors_pos)
            print('')
            if(total_transistors_sop > total_transistors_pos):
                print("Recommendation: Select POS design for reduced transister design.")
            elif(total_transistors_pos > total_transistors_sop):
                print("Recommendation: Select SOP design for reduced transister design.")
            else:
                print("SOP and POS yeild same number of transistors.")
            print('')
        else:
            print('No valid expression found in the input file.')
    
    else:
        print('Incompatible Input please input "C" or "B".')

if __name__ == '__main__':
    main()