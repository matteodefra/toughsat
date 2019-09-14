# Copyright (C) 2011 by Henry Yuen, Joseph Bebel

# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:

# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.


# Subset Sum Routine
# written by Henry Yuen

# for ToughSat Project


import math
import copy
import sys
import shutil
import gc
import random


verbose = 0
testing = 0

assignment = {}

n = 5
formula = []

vars = {}
postfix_counter = 0

def make_var():
	global vars
	global postfix_counter
	postfix_counter = postfix_counter + 1
	
	return "X" + str(postfix_counter)

def make_conj(exprs):
	conj = ["&"]
	for e in exprs:
		conj.append(copy.copy(e))
	return conj
	
def make_disj(exprs):
	conj = ["V"]
	for e in exprs:
		conj.append(copy.copy(e))
	return conj

def make_neg(expr):
	conj = ["neg",copy.copy(expr)]
	return conj

#def make_val(v):
#	return ["val",v]
	
def make_iff(e1,e2):
	#same as equals, essentially
	return ["<->",copy.copy(e1),copy.copy(e2)]

def make_xor(e1,e2):
	#pos = make_conj([e1,make_neg(e2)])
	#neg = make_conj([e2,make_neg(e1)])
	#return make_disj([pos,neg])
	return ["+",copy.copy(e1),copy.copy(e2)]

def allocate_var(name,num):
	global vars
	vars[name] = []
	for i in range(num):
		varname = make_var()
		vars[name].append(["var",varname])

def measure_formula(formula):
	count = 0
	if formula[0] != "var" and formula[0] != "val":
		for i in range(1,len(formula)):
			count += measure_formula(formula[i])
	else:
		return 1
		
	return count

def print_formula(formula):
	s = ""
	t = formula[0]
	if t == "val":
		if formula[1] == 1:
			s += "T"
		else:
			s += "F"
	if t == "neg":
		s += "~"
		if formula[1][0] != "var":
			s += "("
			
		s += print_formula(formula[1])
		
		if formula[1][0] != "var":
			s += ")"
	
	
	if t == "<->":	#iff
		s += "("
		s += print_formula(formula[1])
		s += " <--> "
		s += print_formula(formula[2])
		s += ")"
	
	
	if t == "+":	#iff
		s += "("
		s += print_formula(formula[1])
		s += " + "
		s += print_formula(formula[2])
		s += ")"
	
	
	if t == "var":
		s += formula[1]
	if t == "V":
		s += "("
		for j in range(1,len(formula)-1):
			s += print_formula(formula[j])
			s += " V "
		s += print_formula(formula[len(formula)-1])
		s += ")"
	if t == "&":
		s += "("
		for j in range(1,len(formula)-1):
			s += print_formula(formula[j])
			s += " & "
		s += print_formula(formula[len(formula)-1])
		s += ")"
	
	return s

def evaluate_formula(formula,assignment):
	#print formula
	t = formula[0]
	if t == "val":
		return formula[1]
	if t == "neg":
		return (evaluate_formula(formula[1],assignment) + 1) % 2
	if t == "var":
		return assignment[formula[1]]
	if t == "V":
		for j in range(1,len(formula)):
			v = evaluate_formula(formula[j],assignment)
			if v == 1:
				return 1
		
		return 0
		
	if t == "&":
		for j in range(1,len(formula)):
			v = evaluate_formula(formula[j],assignment)
			if v == 0:
				return 0
		
		return 1
	if t == "+":
		v1 = evaluate_formula(formula[1],assignment)
		v2 = evaluate_formula(formula[2],assignment)
		
		return (v1 + v2) % 2
		
	if t == "<->":
		v1 = evaluate_formula(formula[1],assignment)
		v2 = evaluate_formula(formula[2],assignment)
		
		return (1 + v1 + v2) % 2
		
	return 0
	

	


		
#convert to CNF
def distribute_negs(formula):
	#print formula
	t = formula[0]
	if t == "neg":
		if formula[1][0] == "val":
			formula[1][1] = (formula[1][1]+1)%2	#negate the value
			formula = formula[1]
		elif formula[1][0] == "neg":
			#undo negation
			formula = formula[1][1]
		elif formula[1][0] in ["&","V"]:
			#distribute over
			if formula[1][0] == "&":
				formula[1][0] = "V"
			else:
				formula[1][0] = "&"
			
			for i in range(1,len(formula[1])):
				formula[1][i] = make_neg(formula[1][i])
			
			formula = formula[1]
		elif formula[1][0] in ["<->"]:
			#change it to xor
			formula[1][0] = "+"
			formula = formula[1]
			
		elif formula[1][0] in ["+"]:
			#change it to xor
			formula[1][0] = "<->"
			formula = formula[1]

	#it may have changed
	t = formula[0]
	if t == "val":
		return formula

	if t == "var":
		return formula
	
	for i in range(1,len(formula)):
		formula[i] = distribute_negs(formula[i])
	
	return formula


def variabilize_values(formula):
	t = formula[0]
	if t == "var":
		return formula
	
	if t == "val":
		return vars["constants"][formula[1]]
	
	for i in range(1,len(formula)):
		formula[i] = variabilize_values(formula[i])
		
	return formula

def associatize(formula):
	threshold = 4
	t = formula[0]
	if t in ["&","V"]:
		if len(formula) > threshold:
			sub_formula = [t]
			sub_formula.extend(formula[threshold-1:])
			#formula = [t,formula[1],sub_formula]
			temp_formula = [t]
			temp_formula.extend(formula[1:threshold-1])
			temp_formula.append(sub_formula)
			formula = temp_formula
	
	if t not in ["val","var"]:
		for i in range(1,len(formula)):
			formula[i] = associatize(formula[i])
	
	return formula
	
#auxiliary helper function
#to take a formula in a tree structure (consisting of AND and OR and IFF and XOR operations only)
#and assign every internal node a dummy variable
def flatten_formula_tree(formula,nodevar):
	t = formula[0]
	
	flattened_subtree = []
	flattened_clause = []
	
	if t in ["&","V","<->","+"]:
		flattened_clause = [t]
		for i in range(1,len(formula)):
			e = formula[i]
				
			#check if we have to create new variables (we have encountered a leaf or an internal node)
			if e[0] in ["&","V","<->","+"]:
				e_nodevar = ["var",make_var()]
				flattened_clause.append(e_nodevar)
				
				#now we flatten this branch of the tree
				flattened_subtree.extend(flatten_formula_tree(e,e_nodevar))
			else:
				flattened_clause.append(e)	#e1 is either neg or var
	else:
		return []

	#so now our clause looks like: v1 <-> (v2 & v3 & ...)
	
	flattened_subtree.append(["<->",nodevar,flattened_clause])
	return flattened_subtree
			
		
def convert_1_to_3(expr):
	#create auxiliary variables
	v1 = ["var",make_var()]
	v2 = ["var",make_var()]
	v1_neg = make_neg(v1)
	v2_neg = make_neg(v2)
	
	return [make_disj([expr,v1,v2]),	\
			make_disj([expr,v1,v2_neg]),	\
			make_disj([expr,v1_neg,v2]),	\
			make_disj([expr,v1_neg,v2_neg])]

def convert_2_to_3(expr1,expr2):
	#create auxiliary variables
	v1 = ["var",make_var()]
	v1_neg = make_neg(v1)
	
	return [make_disj([expr1,expr2,v1]),	\
			make_disj([expr1,expr2,v1_neg])]

#extract all the variables present in a clause
#assuming all we have are <->, &, V, negs, and vars
def extract_variables(formula):
	if formula[0] == "var":
		return [formula[1]]
	
	v = []
	for i in range(1,len(formula)):
		v2 = extract_variables(formula[i])
		for u in v2:
			if u not in v:
				v.append(u)
	return v
	
def write_cnf_clauses_to_file(fh,clauses):
	for clause in clauses:
		s = ""
		t = clause[0]
		
		if t in ["&","V"]:	
			for i in range(1,len(clause)):
				t = clause[i][0]
				if t == "neg":
					s += "-" + str(clause[i][1][1][1: ]) + " "
				else:	#it's a var
					s += str(clause[i][1][1:]) + " "
		elif t in ["neg"]:
			s += "-" + str(clause[1][1][1: ]) + " "
		elif t in ["var"]:
			s += str(clause[1][1:]) + " "
		
		
		s += "0\n"
		fh.write(s)
	
def convert_clause_to_cnf(clause):
	#otherwise, make truth table!
	#extract the variables in this clause
	vs = extract_variables(clause)
	#create all possible assignments for the v's
	cnf_clauses = []
	
	for j in range(2**len(vs)):
		temp_assgn = {}
		v = []
		
		for k in range(len(vs)):
			bit = (j >> k) % 2
			temp_assgn[vs[k]] = bit
			if bit == 0:
				v.append(["var",vs[k]])
			else:
				v.append(make_neg(["var",vs[k]]))
		
		#test the truth assignment
		val = evaluate_formula(clause,temp_assgn)
		
		#if we have a 0, we have winner winner chicken dinner
		if val == 0:
			cnf_clauses.append(make_disj(v))	
	
	return cnf_clauses
	
def convert_to_3cnf_canonical(formula):
	formula = distribute_negs(formula)
	formula = associatize(formula)
	
	#now that we've variabilized the values
	#and we've distributed the negs
	#and we've associatized
	#we're ready to rock and roll - convert to 3CNF baby!
	
	#our input formula is in a tree data structure now
	#give dummy variables to all the internal nodes
	root_nodevar = ["var",make_var()]
	clauses = flatten_formula_tree(formula,root_nodevar)
	
	#now, we can convert each clause
	#to CNF
	#add the root nodevar
	#cnf_clauses = convert_1_to_3(root_nodevar)
	cnf_clauses = [root_nodevar]
	
	for i in range(len(clauses)):
		clause = clauses[i]
		#if the clause is already disjunctive then we're fine
		if clause[0] == "V":
			cnf_clauses.append(clause)
			continue
		
		cnf_clauses.extend(convert_clause_to_cnf(clause))
	
	#write_cnf_clauses_to_file(fh,cnf_clauses)
	return cnf_clauses

def convert_to_3cnf_efficient(formula):
	t = formula[0]
	
	#print print_formula(formula)
	
	if t in ["var","neg"]:
		return convert_1_to_3(formula)
	
	if t in ["&"]:
		return convert_to_3cnf_canonical(formula)
	
	#we're of the "V" type now
	l = len(formula)
	
	if l == 2:
		return convert_1_to_3(formula[1])
		
	if l == 3:
		return convert_2_to_3(formula[1],formula[2])
		
	if l == 4:
		return [formula]	#is already in 3CNF form
		
	if l > 5:
		return convert_to_3cnf_canonical(formula)
	
	#takes a 4cnf clause and converts it to 3cnf
	#print print_formula(formula)
	dummyvar = ["var",make_var()]
	
	cnf_clauses = []

	part1 = formula[0:3]
	part1.append(dummyvar)
	
	#print print_formula(part1)
	cnf_clauses.append(part1)
	
	part2 = ["<->",dummyvar,["V"] + formula[3:5]]
	#print print_formula(part2)
	cnf_clauses.extend(convert_clause_to_cnf(part2))
	
	return cnf_clauses

def is_empty_clause(clause):
	if clause == []:
		return True
	
	t = clause[0]
	if t in ["&","V"]:
		if len(clause) == 2:
			return True
			
	return False
	
#assume that we're in CNF form already
def identify_a_unit_clause(clauses):
	for clause in clauses:
		if is_empty_clause(clause):
			continue
			
		t = clause[0]
		if t in ["var","neg"]:
			return clause
			
		elif t in ["&","V"]:
			if len(clause) == 2:
				return identify_a_unit_clause([clause[1]])
		
	return None

def clause_has_literal(clause,literal):
	if is_empty_clause(clause):
		return False
	
	t = clause[0]
	
	if t in ["var","neg"]:
		#this is a literal
		#check if literals are equal
		if compare_literals(clause,literal):
			return True

	else:	#& and V
		for j in range(1,len(clause)):
			#check whether this clause contains the literal
			if compare_literals(clause[j],literal):
				return True

	return False

def compare_literals(lit1,lit2):
	t1 = lit1[0]
	t2 = lit2[0]
	
	if t1 != t2:
		return False
	
	v1 = None
	v2 = None
	if t1 in ["neg"]:
		v1 = lit1[1]
		v2 = lit2[1]
	else:
		v1 = lit1
		v2 = lit2

	if v1[1] == v2[1]:
		return True
		
	return False
	


def excise_literal_from_clause(clause,literal):
	if is_empty_clause(clause):
		return clause
	
	t = clause[0]
	
	if t in ["var","neg"]:
		#this is a literal
		#check if literals are equal
		if compare_literals(clause,literal):
			return []
		
		#if they're negations, we're hosed anyways (UNSATISFIABLE)
	else:	#& and V
		modified_clause = [t]
		for j in range(1,len(clause)):
			#check whether this clause contains the literal
			if compare_literals(clause[j],literal):
				return []	#this is a redundant clause
			else:
				#or the negation of the literal
				vs1 = extract_variables(literal)
				vs2 = extract_variables(clause[j])
				if vs1 != vs2:	#we don't have a negation, preserve this literal
					modified_clause.append(clause[j])

		clause = modified_clause
		return clause
		
	
	return clause

def process_unit_clauses(clauses):
	#given a heap of clauses, find the unit clauses

	unfinished = True
	#print print_formula(make_conj(clauses))	
	while unfinished:
		gc.collect()
		##print "="*30
		#look for unit clauses in the 
		unit_clause = identify_a_unit_clause(clauses)
		if unit_clause == None:
			break
		
		#print "Found unit clause",print_formula(unit_clause)
		
		modified_clauses = clauses
		clauses = []
		for clause in modified_clauses:		
			##print "Excising from clause: ",print_formula(clause)
			clause2 = excise_literal_from_clause(clause,unit_clause)
			if not is_empty_clause(clause2):
				clauses.append(clause2)
				##print "New clause: ",print_formula(clause2)
			
		#clauses = modified_clauses
		#print print_formula(make_conj(clauses))
		
	return modified_clauses
	
def process_easy_literals(clauses):
	#easy literals are those whose
	#negations never occur
	global postfix_counter
	
	occurrence = {}
	
	for clause in clauses:
		vs = extract_variables(clause)
		for v in vs:
			if v not in occurrence.keys():
				occurrence[v] = [0,0]
			
			pos_lit = ["var",v]
			neg_lit = make_neg(pos_lit)
			
			if clause_has_literal(clause,pos_lit):
				occurrence[v][0] += 1
			if clause_has_literal(clause,neg_lit):
				occurrence[v][1] += 1
				
	modified_clauses = []
	
	for clause in clauses:
		vs = extract_variables(clause)

		marked = False
		for v in vs:
			if occurrence[v][0] + occurrence[v][1] > 0 and \
				occurrence[v][0]*occurrence[v][1] == 0:
				marked = True
				
		if marked == False:
			modified_clauses.append(clause)
	
	clauses = modified_clauses
				
	return clauses
				
		

def remap_variables(clauses):
	var_counter = 0
	var_map = {}
	vs = []
	for clause in clauses:
		vs.extend(extract_variables(clause))
	
	vs = sorted(vs,key=lambda x:int(x[1:]))

	for v in vs:
		if v not in var_map:
			var_counter += 1
			var_map[v] = var_counter
	
	return var_map


def write_cnf_clauses_to_file_remapped(clauses,var_map):

	output = ""
	for clause in clauses:
		s = ""
		t = clause[0]
		
		if t in ["&","V"]:	
			for i in range(1,len(clause)):
				t = clause[i][0]
				if t == "neg":
					var = clause[i][1][1]
					s += "-" + str(var_map[var]) + " "
				else:	#it's a var
					var = clause[i][1]
					s += str(var_map[var]) + " "
		elif t in ["var"]:
			var = clause[1]
			s += str(var_map[var]) + " "
		elif t in ["neg"]:
			var = clause[1][1]
			s += "-" + str(var_map[var]) + " "
		
		s += "0\n"
		output += s
		
	return output
	

#=============================================================================================================
#
#
#						MAIN SUBSETSUM CODE
#
#
#
#=============================================================================================================

def make_adder(a,b,c,a_length,b_length,c_length,stage):
	global vars
	global verbose
	global testing
	global assignment
	
	formula = []
	cbv = "carry_bits_" + str(stage)
	#a and b are the names of variables that represent
	#the bits of the summands a and b
	#c holds the result (is a_length)
	
	#it is assumed that c_length >= a_length >= b_length
	allocate_var(cbv,a_length)
		
	f = make_iff(vars[c][0],	\
					make_xor(vars[a][0],vars[b][0]))
	
	formula.extend(convert_clause_to_cnf(f))
	
	#make the carry bit
	f = make_iff(	\
					vars[cbv][0],	\
					make_conj([vars[a][0],vars[b][0]]) \
					)	
	formula.extend(convert_clause_to_cnf(f))
	
	for i in range(1,a_length):
		f = []
		
		if i < b_length:
			f = make_iff(	\
					vars[c][i],	\
					make_xor(	\
						make_xor(vars[cbv][i-1],vars[a][i]),	\
						vars[b][i])	\
						)

			formula.extend(convert_clause_to_cnf(f))
			f = make_iff(vars[cbv][i],	\
						make_xor(\
							make_conj([vars[a][i],vars[b][i]]),\
							make_conj([vars[cbv][i-1],\
										make_xor(vars[a][i],vars[b][i])])))

			formula.extend(convert_clause_to_cnf(f))
		else:
			f = make_iff(	\
					vars[c][i],make_xor(vars[cbv][i-1],vars[a][i]))
		
			formula.extend(convert_clause_to_cnf(f))
			
			#carry bit iff both previous carry bit and i are true
			f = make_iff(vars[cbv][i],make_conj([vars[cbv][i-1],vars[a][i]]))

			formula.extend(convert_clause_to_cnf(f))
		
	#add the last carry bit to the overflow	
	if c_length > a_length:
		f = make_iff(	\
						vars[c][a_length],	\
						vars[cbv][a_length-1]	\
						)
		
		formula.extend(convert_clause_to_cnf(f))
		
		for i in range(a_length+1,c_length):
			f = make_neg(vars[c][i])
			formula.append(f)
		

	return formula

def set_variable_to_number(variable,number,n):
	global vars
	global assignment
	
	formula = []
	#set them equal to their respective numbers
	for i in range(n):
		bit = (number >> i) % 2
		if bit == 1:
			f = vars[variable][i]
		else:
			f = make_neg(vars[variable][i])
		
		formula.append(f)
		
	return formula	
	
	
def halt():
	a = 0
	b = 3/a

def generate_instance(numbers,target,op_3cnf,hidden_subset=None):
	global formula
	global vars
	global postfix_counter
	global num_clauses
	
	formula = []

	vars = {}
	postfix_counter = 0

	num_clauses = 0

	
	formula = []
	f = []
	num_clauses = 0

	m = len(numbers)
	numbers = sorted(numbers)	#just sort them again just in case
	
	numbersizes = [int(math.log(numbers[i]+1,2))+1 for i in range(m)]
	n = int(math.log(sum(numbers),2))+1

	sumsizes = [int(math.log(sum(numbers[0:i+1])+1,2))+1 for i in range(m)]
	
	targetsize = int(math.log(target,2))+1

	
	#ANSWER VARIABLES ALWAYS GO FIRST
	#allocate subset indication
	allocate_var("subset",m)

	#allocate numbers
	for i in range(m):
		allocate_var("num" + str(i),numbersizes[i])
		formula.extend(set_variable_to_number("num"+str(i),numbers[i],numbersizes[i]))


	for i in range(m):
		ppv = "partial_product_" + str(i)
		allocate_var(ppv,numbersizes[i])

		#generate partial product expressions		
		for j in range(numbersizes[i]):
			f = make_iff(					\
							vars[ppv][j],	\
							make_conj([vars["subset"][i],vars["num"+str(i)][j]])	\
							)
			formula.extend(convert_clause_to_cnf(f))


	#generate the adder code
	allocate_var("partial_sum_0",sumsizes[0])

	for i in range(sumsizes[0]):
		f = []
		if i < numbersizes[0]:
			f = make_iff(	\
					vars["partial_sum_0"][i],	\
					vars["partial_product_0"][i]	\
					)
		else:
			f = make_neg(vars["partial_sum_0"][i])
		
		formula.extend(convert_clause_to_cnf(f))

		

	for i in range(1,m):
		allocate_var("partial_sum_" + str(i),sumsizes[i])
		f = make_adder("partial_sum_" + str(i-1),"partial_product_" + str(i),"partial_sum_" + str(i),sumsizes[i-1],numbersizes[i],sumsizes[i],i)
		formula.extend(f)

	for i in range(sumsizes[m-1]):
		bit = (target >> i) % 2
		if bit == 1:
			f = vars["partial_sum_" + str(m-1)][i]
		else:
			f = make_neg(vars["partial_sum_" + str(m-1)][i])

		formula.append(f)

	#convert to 3cnf
	if op_3cnf is True:
		cnf_clauses = []
		for f in formula:
			g = convert_to_3cnf_efficient(f)
			cnf_clauses.extend(g)
			
			#print print_formula(make_conj(g))
			#break
			
		formula = cnf_clauses

	#halt()
	
	var_map = remap_variables(formula)
	#for i in range(m):
	#	#print "X" + str(i+1),var_map["X" + str(i+1)]

	num_variables = len(var_map)
	num_clauses = len(formula)
	output = ""

	output += "c A 3SAT instance whose satisfying assignment encodes the subset of " + str(numbers) + " that add up to " + str(target) + "\n"
	if hidden_subset != None:
		output += "c One possible solution is: " + str(hidden_subset) + "\n"
	output += "p cnf " + str(num_variables) + " " + str(num_clauses) + "\n"

	output += write_cnf_clauses_to_file_remapped(formula,var_map)
	return output

def generate_instance_random(setsize,rng,op_3cnf):
	
	#open the set file
	#numbers = [1,2,3,4,5]
	numbers = sorted([random.randint(1,rng) for i in range(setsize)])
	m = setsize
	#select a random subset	
	hidden_subset = [random.randint(0,1) for j in range(m)]
	target = sum([int(hidden_subset[i]*numbers[i]) for i in range(m)])
	
	return generate_instance(numbers,target,op_3cnf,hidden_subset)
	
def main():
	#generate partial product sums
	args = sys.argv

	#format: subsetsum.py <range> <setsize> <outputfile>
	if len(args) != 5:
		print "Usage: subsetsum.py <range> <setsize> <op_3cnf> <outputfile>"
		exit()

	rng = int(args[1])
	setsize = int(args[2])
	op_3cnf = args[3] == "1"
	
	output = generate_instance(random,setsize,rng,op_3cnf)
	
	f = open(args[4],"w")
	f.write(output)
	f.close()
	

if __name__ == '__main__':
    main()
