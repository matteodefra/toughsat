#!/usr/bin/env python3
# Copyright (C) 2011-2017 by Henry Yuen, Joseph Bebel

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

# ToughSat Project

import math, collections, random, sys, functools, itertools, time
from circuit_ops import *   

    #TODO: integrate and/or ops into clauses (unneeded?)
    #todo: find and chain adders?


def num_var(cnf):
    return len(set(abs(literal) for clause in cnf for literal in clause))

def cnf_to_dimacs(cnf, n_a, n_b, target, a,b, includefactors, variables = False):
    #print(cnf)
    dimacs = "p cnf %d %d \n" % (num_var(cnf), len(cnf))
    dimacs += "c Factors encoded in variables 1-%d and %d-%d\n"  % (n_a, n_a+1,n_a+n_b)
    dimacs += "c Target number: %d\n" % (target)
    if includefactors:
        dimacs += "c Factors: %d x %d\n" % (a,b)
    dimacs += " 0\n".join( (" ".join(map(str, clause)) for clause in cnf) ) + " 0\n"
    return dimacs
    
def circuit_to_cnf(circuit, equals, inverses, n_a, n_b, optimize=True, variables=None):
    cnf = []
    if not variables:
        # defaultdict that increments default variable number every time we use a new variable
        variables = collections.defaultdict((lambda k: lambda: next(k))(itertools.count(1)))
        
        #add inputs to veriable list so they're the first
        for i in range(n_a):
            variables["x_" + str(i)]
        for i in range(n_b):
            variables["y_" + str(i)]

        #simplify equal variables
        for x,y in equals:
            variables[y] = variables[x]
        for x,y in inverses:
            variables[y] = -variables[x]

        # start with our zero and one constants
        cnf, variables['zero'] = [(variables["one"],)], -variables['one']

    # #implement circuit operations
    for line in circuit:
        cnf.extend(line['op'](v=variables, **line))
    #eliminate any variables that are known to be constants

    def constant_equivs(clause, one_equivs):
        for i in one_equivs:
            if i in clause: return tuple()
        return tuple(L for L in clause if -L not in one_equivs)
    input_constants = []
    for cleanups in range(10):
        one_equivs = tuple(clause[0] for clause in cnf if len(clause) == 1)
        input_constants.extend( (i for i in one_equivs if abs(i) <= n_a+n_b) )
        if len(one_equivs) == 0: break
        cnf = set(constant_equivs(clause, one_equivs) for clause in cnf)
    cnf.update(set((i,) for i in input_constants))
    # cnf = convert_to_3cnf(cnf)
    return set(clause for clause in cnf if len(clause) > 0), variables

def convert_to_3cnf(cnf):
    good_clauses = [c for c in cnf if len(c) <= 3]
    bad_clauses = [c for c in cnf if len(c) > 3]
    tmp_var = num_var(cnf) + 1
    def reduce_clause(clause, tmp_var):
        cur_var = tmp_var
        if len(clause) <= 3:
            return [clause], tmp_var
        tmp_clause = list(clause[2:])
        tmp_clause.append(cur_var)
        tmp_clause2, tmp_var = reduce_clause(tmp_clause, tmp_var+1)
        tmp_clause2.append( [clause[0], clause[1], -cur_var])
        return tmp_clause2, tmp_var
    for c in bad_clauses:
        tmp_clause3, tmp_var = reduce_clause(c, tmp_var)
        good_clauses.extend(tmp_clause3)
    return good_clauses


bits = lambda t: int(math.ceil(math.log(t+1)/math.log(2)))
def generate_instance_known_factors(a,b, includefactors=True):
    a, b = max(a,b), min(a,b) # a is the longer 
    n_a, n_b = bits(a), bits(b)
    return generate_instance(a*b, n_a, n_b, a, b, includefactors)
    
def generate_instance(target, n_a, n_b, a=0, b=0, includefactors=False):
    n = bits(target)
    n_a, n_b = max(n_a, n_b),min(n_a, n_b)
    x = tuple('x_' + str(i) for i in range(n_a)) # x_0 ... x_(n_a-1)
    y = tuple('y_' + str(i) for i in range(n_b)) # y_0 ... y_(n_b-1)
    circuit = [ {'op':atleastoneof, 'x':x[1:]}, {'op':atleastoneof, 'x':y[1:]} ]
    equals, inverses = [],[]
    dummy = ('d_' + str(i) for i in itertools.count())

    def invert_string(s):
        return list(not_v for (v, not_v) in zip(s, (next(dummy) for b in s)) if not inverses.append((v, not_v)))

    def addbits(_x,_y, cin='zero', sub=False): #assume x >= y
        if len(_x) < len(_y): 
            if sub: print("ERROR NEGATIVE NUM")
            _y,_x=_x,_y

        cout = _x[0] if len(_x) > len(_y) else _y[0]
        _x, _y, xplusy = list(_x), list(_y)+['zero']*(len(_x)-len(_y)), []
        addsub = subtractor if sub else adder

        for adder_size in adders:
            while len(_x) >= adder_size and len(_y) >= adder_size:
                xplusy.extend( tuple(next(dummy) for i in range(adder_size)) )
                cout = next(dummy)
                circuit.append( {'op':addsub, 'cin':str(cin), 'x':_x[:adder_size], 'y':_y[:adder_size], 'z':xplusy[-adder_size:], 'cout':str(cout)})
                cin,_x,_y = cout,_x[adder_size:],_y[adder_size:]

        equals.append(('one', cout)) if sub else xplusy.append(cout)
        return tuple(xplusy)
    def karatsuba(_x,_y): #input two vectors of bits
        if len(_x) == 0 or len(_y) == 0: return ('zero',)
        (_x,_y) = (_x, _y) if len(_x) >= len(_y) else (_y,_x)
        midpoint = -(-len(_x)//2)
        smaller_size, larger_size = sorted((len(_x),len(_y)))
        if smaller_size == 1:
            circuit.append( {'op':and_gates, 'x': _x*len(_y), 'y':_y*len(_x), 'z':map(next,(dummy,)*larger_size)})
            return circuit[-1]['z']
        if larger_size <= max(multipliers):
            z= tuple(next(dummy) for i in range(2*larger_size))
            pad_x, pad_y = _x+('zero',)*(larger_size-len(_x)),_y+('zero',)*(larger_size-len(_y))
            circuit.append({'op': multiplier, 'x': pad_x, 'y': pad_y, 'z': z})            
            return z

        x0, x1, y0, y1 = _x[0:midpoint], _x[midpoint:], _y[0:midpoint], _y[midpoint:]
        z0, z2, x1plusx0, y1plusy0 = karatsuba(x0, y0), karatsuba(x1, y1), addbits(x0, x1), addbits(y0, y1)
        x1plusx0timesy1plusy0 = karatsuba(x1plusx0, y1plusy0)
        z1plusz0 = addbits(x1plusx0timesy1plusy0, z2, cin='one', sub=True)
        z1 = addbits(z1plusz0, z0, cin='one', sub=True)
        return z0[0:midpoint] + addbits(z0[midpoint:2*midpoint] + z2, z1)
        
    z = karatsuba(x,y)
    target_bits = tuple('one' if i=='1' else 'zero' for i in ('{0:0' + str(n) + 'b}').format(target)[::-1])
    equals.extend(zip(target_bits + ('zero',)*(len(z)-len(target_bits)),z))
    #print("constructed circuit")
    #return {'circuit':circuit, 'equals': equals, 'inverses':inverses, 'n_a':n_a, 'n_b':n_b}
    # return circuit_to_cnf(circuit, equals, inverses, n_a, n_b)
    return cnf_to_dimacs(circuit_to_cnf(circuit, equals, inverses, n_a, n_b)[0] , n_a, n_b, target, a, b, includefactors)

def t(a,b,nm):
    c = generate_instance_known_factors(a,b)
    print(c)
    print(type(c))
    cnf, var = circuit_to_cnf(**c)
    open(str(nm)+'.dimacs', 'w').write(cnf_to_dimacs(cnf, c['n_a'], c['n_b'], var))

def undovariables(dimacs, solution):
    import json
    variables = json.loads(dimacs.split('c $$$')[1])
    n = variables['__numberofbitsinfactors']
    x = ""
    y = ""
    solns = solution.split('\n')[1].split(' ')
    for i in range(n):
        if int(solns[variables['x' + str(i)]-1]) > 0:
            x = '1' + x
        else:
            x = '0' + x
        if int(solns[variables['y' + str(i)]-1]) > 0:
            y = '1' + y
        else:
            y = '0' + y
    print("x = " + str(int(x,2)))
    print("y = " + str(int(y,2)))

primes = { 16 : [37423, 59167, 48907, 54499, 34231, 48523, 44959, 62383, 44537, 
62801, 56941, 59539, 47149, 62743, 49037, 55691, 52103, 56951, 40253, 
55837, 60103, 49121, 57667, 63367, 36269, 48533, 33461, 41999, 44131, 
61879],
17: [121367, 89977, 104009, 113963, 70237, 112603, 103723, 122167, 86297, 
83137, 120737, 124147, 123581, 105817, 76103, 121883, 106531, 112859, 
93761, 102829, 88259, 87539, 95549, 99829, 67369, 66179, 86423, 
96181, 112397, 72823],
18: [240073, 216157, 164071, 163063, 201683, 206501, 259723, 175621, 
184007, 219727, 131759, 229499, 151279, 247993, 247463, 163351, 
158761, 176213, 217499, 231019, 193301, 241667, 213539, 189479, 
247393, 160049, 187843, 161461, 146539, 192133],
19: [332951, 515153, 501133, 514741, 423427, 316861, 380117, 279689, 
292079, 370663, 392087, 426161, 417097, 446921, 471949, 429467, 
508451, 361687, 484027, 405343, 281069, 514277, 467021, 396293, 
304807, 389999, 282563, 474647, 341879, 355087],
20:[581411, 666901, 949129, 875983, 1022129, 688951, 533573, 865211, 
770167, 1010549, 569671, 914723, 847193, 760373, 1013399, 531143, 
605323, 655331, 881099, 1046081, 936361, 681049, 636749, 681949, 
619027, 992513, 991057, 652903, 559549, 620603],
21: [1848641, 1953811, 1815733, 1388011, 1417183, 1978199, 1434023, 
1128629, 1097483, 1338367, 1865893, 2025187, 1057367, 1237433, 
1113199, 1313041, 1393927, 1967419, 1567901, 2067211, 1588661, 
1951793, 1219919, 2074031, 1759159, 1147417, 1873093, 1813817, 
1843997, 1249243],
22:[2986397, 2721197, 2697697, 2744933, 3209681, 2934143, 2407943, 
2279419, 2968223, 2300021, 3964589, 3252409, 3280187, 2781377, 
3210017, 2540339, 2201543, 3690329, 2601337, 3880421, 3450121, 
2308589, 2643133, 3133171, 2240159, 3355699, 3360197, 3823559, 
3859019, 3182479],
23:[8381123, 6760003, 7264009, 6142261, 5730073, 8004047, 5478677, 
7573519, 8105221, 8143271, 7703741, 4908107, 7400293, 6830869, 
5806961, 6273053, 5092861, 6541831, 6027247, 4675249, 5294587, 
6214223, 5329229, 7698703, 7952909, 6986219, 4922681, 6088763, 
6325031, 6486791],
24: [8475119, 9735949, 11919983, 16759969, 16085261, 9600319, 11406401, 
12738307, 13025561, 9151573, 11588561, 14732299, 13674113, 13628039, 
13420229, 12528793, 11695297, 11119021, 14590091, 11417477, 12987497, 
10273787, 11059271, 13254821, 9909791, 9255991, 9920021, 11932153, 
13335349, 8389001],
25: [20148367, 17223923, 21937841, 18842869, 29602789, 28371269, 30312157, 
26098027, 18715727, 28008797, 18396347, 29792327, 30940411, 31788971, 
31376879, 22125023, 23925179, 27990247, 16925917, 23687777, 21231407, 
30647147, 29172401, 25249867, 26738077, 27389641, 28014013, 16847893, 
18558797, 24051067],
26: [63565213, 62604193, 48382603, 62933953, 51809077, 64852063, 64662337, 
53881363, 60617593, 55437163, 50132947, 61865047, 50933711, 41659927, 
52975397, 44929217, 51105023, 50735827, 66312893, 64471201, 44249687, 
43595371, 56933857, 45752717, 59466611, 38168671, 56192399, 53748001, 
40364689, 38103509],
27:[112480981, 91908007, 123176831, 128189381, 131734177, 117071819, 
91636327, 103446689, 81981343, 70843057, 127639483, 90571097, 
127346647, 112658291, 106392287, 96907309, 132096551, 80467771, 
72280939, 107715271, 112768129, 120226783, 104635961, 117347227, 
124050211, 71984191, 86668597, 68874283, 83833637, 98594039],
28:[266527097, 239217977, 258529763, 182592757, 242662093, 134715079, 
176160601, 247051139, 242139659, 210624103, 248873791, 215287687, 
200808269, 153112451, 248589973, 190121287, 176670071, 192618193, 
172962949, 166009871, 159323939, 236079931, 173200771, 242682943, 
244860589, 252829553, 217950203, 162146449, 138098041, 245202677],
29:[445611937, 404744867, 489132331, 388883309, 535756099, 305146739, 
504601921, 353449661, 381145451, 457740313, 427705963, 445403477, 
282394271, 324445699, 388591589, 491535053, 351507389, 375748073, 
312441517, 406498321, 514507619, 342047813, 368706773, 454001747, 
360623573, 415095097, 269444171, 339985231, 461853949, 457639859],
30:[570381719, 1029149119, 762263443, 761364511, 900644531, 665902603, 
742600757, 977965609, 1054312921, 896469293, 1001675371, 1068045967, 
669501533, 1022632757, 1055926381, 894399491, 785917129, 934443163, 
980081639, 1066293187, 981066553, 824430049, 713499187, 829943011, 
826787627, 903790577, 953283491, 720905047, 988189607, 614524403],
31:[1099864511, 1856571671, 1579366871, 1734843631, 2048762893, 
1185234023, 1908915317, 1248552857, 1473372959, 1725167707, 
1596040063, 2016084209, 1173572207, 1608645361, 1519634617, 
1939847839, 1593501521, 1136824237, 1883033357, 1200205211, 
1857889687, 1364162771, 1206941023, 1899910139, 1641146513, 
2006223629, 1970456287, 1934505401, 1608090079, 1076775407],
32:(2316644917, 4173991301, 3503565953, 2658438689, 2244625459, 
3241345823, 2811374053, 2199635257, 2553909179, 3007351843, 
3236271187, 3936839003, 2476529479, 3862827361, 2575414991, 
4202873849, 3679876063, 3135672637, 3619587007, 2414296271, 
2826875627, 3974822087, 4120038761, 2648270887, 2621519437, 
3247434259, 2288597141, 3686287247, 2906348671, 2634343799),
64:(10086124837380661049, 18311984027837140229, 13147305481532659531, \
12460583606501790241, 12303475786185894377, 12801478627450700269, \
15862226639395282849, 9548662038335876783, 15214273286930516683, \
12862743339916456229, 13844811189923386181, 15333876750005584241, \
10814462913795860149, 10026898481225127647, 12214723832217529979, \
10410870213229651049, 11296652295987291151, 10456684402009108687, \
13367411165667845773, 16047111683829323887, 16297044460459749743, \
12416930095903594589, 14866113315256690489, 15255620538830977933, \
17523311071498959079, 10109194564259170903, 9482918037137737001, \
14701277006332016851, 11141258962047518699, 15544657161291927089),
256:(66472471648529495886964553550517070180699507238687807583096518162159299199373, 
59021768262109476587361698420173898869557952423161767465608254828850881775213),
128:(306109526669749265476345451342494701457,
235730238689668179669179458194650948543)
}

def soln_to_factors(s):
    s = s.replace('\nv', '').split(' ')
    s.reverse()
    s = (1 if int(i) > 0 else 0 if int(i) < 0 else -1 for i in (j for j in s if j != ''))
    return int("".join(str(i) for i in s),2)
