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


# Concatenate several DIMACS files
# written by Henry Yuen

# for ToughSat Project

def readjust_variables(dimacs,var_offset):
	var_map = {}
	
	lines = dimacs.split("\n")
	output = ""
	header = ""
	
	num_clauses = 0
	num_variables = 0
	
	for line in lines:
		#check if it's a comment
		if len(line) == 0:
			break
		
		if line[0] in ["c"]:
			header += line + "\n"
			continue
			
		if line[0] in ["p"]:	#we don't need this anymore
			continue
			
		literals = line.split()
		if len(literals) == 0:
			break
		
		num_clauses += 1		
		
		new_line = ""
		for l in literals:
			lit = int(l)
			var = abs(lit)
			
			new_var = var
			if var != 0:
				new_var += var_offset
			else:
				break
			
			if var not in var_map:
				var_map[var] = 1
			
			sign = var/lit

			new_lit = sign*new_var
			new_line += str(new_lit) + " "
			
		new_line += "0\n"
		output += new_line
		
	num_variables = len(var_map)
	return num_variables,num_clauses,header,output
			
def test():
	t1 = '''c Testing
	c Hello
	p 1 1
	-1 -3 0
	'''

	t2 = '''c Testing2
	c Hello2
	p 1 1
	-1 2 0
	'''

	outputs = []
	num_vars,num_clauses,header,output = readjust_variables(t1,0)
	outputs.append(output)
	num_vars,num_clauses,header,output = readjust_variables(t2,num_vars+0)
	outputs.append(output)

	outputs = header + "".join(outputs)
	print outputs




			
			
		
		