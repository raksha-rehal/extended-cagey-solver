# =============================
# Student Names: Raksha Rehal & Nicholas Tillo  
# Group ID: 62
# Date: 2024 - 02 - 01
# =============================
# CISC 352 - W23
# cagey_csp.py
# desc:
#

#Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects
representing the board. The returned list of lists is used to access the
solution.

For example, after these three lines of code

    csp, var_array = binary_ne_grid(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array is a list of all variables in the given csp. If you are returning an entire grid's worth of variables
they should be arranged in a linearly, where index 0 represents the top left grid cell, index n-1 represents
the top right grid cell, and index (n^2)-1 represents the bottom right grid cell. Any additional variables you use
should fall after that (i.e., the cage operand variables, if required).

1. binary_ne_grid (worth 10/100 marks)
    - A model of a Cagey grid (without cage constraints) built using only
      binary not-equal constraints for both the row and column constraints.

2. nary_ad_grid (worth 10/100 marks)
    - A model of a Cagey grid (without cage constraints) built using only n-ary
      all-different constraints for both the row and column constraints.

3. cagey_csp_model (worth 20/100 marks)
    - a model of a Cagey grid built using your choice of (1) binary not-equal, or
      (2) n-ary all-different constraints for the grid, together with Cagey cage
      constraints.


Cagey Grids are addressed as follows (top number represents how the grid cells are adressed in grid definition tuple);
(bottom number represents where the cell would fall in the var_array):
+-------+-------+-------+-------+
|  1,1  |  1,2  |  ...  |  1,n  |
|       |       |       |       |
|   0   |   1   |       |  n-1  |
+-------+-------+-------+-------+
|  2,1  |  2,2  |  ...  |  2,n  |
|       |       |       |       |
|   n   |  n+1  |       | 2n-1  |
+-------+-------+-------+-------+
|  ...  |  ...  |  ...  |  ...  |
|       |       |       |       |
|       |       |       |       |
+-------+-------+-------+-------+
|  n,1  |  n,2  |  ...  |  n,n  |
|       |       |       |       |
|n^2-n-1| n^2-n |       | n^2-1 |
+-------+-------+-------+-------+

Boards are given in the following format:
(n, [cages])

n - is the size of the grid,
cages - is a list of tuples defining all cage constraints on a given grid.


each cage has the following structure
(v, [c1, c2, ..., cm], op)

v - the value of the cage.
[c1, c2, ..., cm] - is a list containing the address of each grid-cell which goes into the cage (e.g [(1,2), (1,1)])
op - a flag containing the operation used in the cage (None if unknown)
      - '+' for addition
      - '-' for subtraction
      - '*' for multiplication
      - '/' for division
      - '?' for unknown/no operation given

An example of a 3x3 puzzle would be defined as:
(3, [(3,[(1,1), (2,1)],"+"),(1, [(1,2)], '?'), (8, [(1,3), (2,3), (2,2)], "+"), (3, [(3,1)], '?'), (3, [(3,2), (3,3)], "+")])

'''

from cspbase import *
from itertools import *

def binary_ne_grid(cagey_grid):
    ##IMPLEMENT
    n = cagey_grid[0]
    cages = cagey_grid[1]
    csp = CSP("Cagey")
    allvars = []

    #Add Variables
    for i in range(1,n+1):
        for j in range(1,n+1):
            new_var = Variable("Cell("+str(i)+","+str(j)+")", list(range(1,n+1)))
            allvars.append(new_var)
            csp.add_var(new_var)
    

    #INNIT CONSTRAINTS
    y = []
    for x in permutations(range(1,n+1),2):
        y.append(x)
    #Row Constraints
    
    i = 0
    while i < n*n:
        row = []
        for j in range(n):
            row.append(allvars[i + j])
        ober = combinations(row,2) 
        for q in ober:
            cons = Constraint("Cons",q)
            cons.add_satisfying_tuples(y) 
            csp.add_constraint(cons)
        
        i += n
    #Column Constraints
    
    for j in range(n):
        column = []
        i = 0
        while i < n*n:
            column.append(allvars[i + j])
            i += n
        ober2 = combinations(column,2)
        for q in ober2:
            cons = Constraint("Name",q)
            cons.add_satisfying_tuples(y) 
            csp.add_constraint(cons)
    
    return csp, allvars

#LOOK OVER ALL THIS CODE LOL TOO TIRED> 

def nary_ad_grid(cagey_grid):
    ## IMPLEMENT
    n = cagey_grid[0]
    cages = cagey_grid[1]
    csp = CSP("Cagey")
    allvars = []
    #Add Variables
    for i in range(1,n+1):
        for j in range(1,n+1):
            new_var = Variable("Cell("+str(i)+","+str(j)+")", list(range(1,n+1)))
            allvars.append(new_var)
            csp.add_var(new_var)

    
    #INNIT CONSTRAINTS
    y = []
    for x in permutations(range(1,n + 1),n):
        y.append(x)
    #Row Constraints
    i = 0
    while i < n*n:
        row = []
        for j in range(n):
            row.append(allvars[i + j])
        cons = Constraint("Name",row)
        cons.add_satisfying_tuples(y) 
        csp.add_constraint(cons)
        i += n
    
    #Column Constraints
    for j in range(n):
        column = []
        i = 0
        while i < n*n:
            column.append(allvars[i + j])
            i += n

        cons = Constraint("2",column)
        cons.add_satisfying_tuples(y) 
        csp.add_constraint(cons)
    return csp,  allvars

def cagey_csp_model(cagey_grid):
    ## IMPLEMENT
    n = cagey_grid[0]
    cages = cagey_grid[1]
    csp = CSP("Cagey")
    allvars = []
    #Add Variables
    for i in range(1,n+1):
        for j in range(1,n+1):
            new_var = Variable("Cell("+str(i)+","+str(j)+")", list(range(1,n+1)))
            allvars.append(new_var)
            csp.add_var(new_var)

    
    #INNIT CONSTRAINTS
    y = []
    for x in permutations(range(1,n + 1),n):
        y.append(x)
    #Row Constraints
    i = 0
    while i < n*n:
        row = []
        for j in range(n):
            row.append(allvars[i + j])
        cons = Constraint("Name",row)
        cons.add_satisfying_tuples(y) 
        csp.add_constraint(cons)
        i += n
    
    #Column Constraints
    for j in range(n):
        column = []
        i = 0
        while i < n*n:
            column.append(allvars[i + j])
            i += n

        cons = Constraint("2",column)
        cons.add_satisfying_tuples(y) 
        csp.add_constraint(cons)
        #Cage Constraints
    for i in cages:
        total = i[0]
        surrounded_boxes = i[1]
        opperator = i[2]

        needed_vars = []
        for k in surrounded_boxes:
            for y in allvars:
                if y.name == "Cell("+str(k[0])+","+str(k[1])+")":
                    needed_vars.append(y)

        
        new_var = Variable("Cage_op("+str(total)+":"+str(opperator)+":"+str(needed_vars)+")")
        csp.add_var(new_var)
        allvars.append(new_var)
        cons_vars = needed_vars[:]
        cons_vars.append(new_var)
        cage_cons = Constraint("2",cons_vars)

        num_in_cage = len(needed_vars)
        domain_sizer = allvars[0].domain_size()
        all_possible_combos = [[]]
        for i in range(num_in_cage):
            temp = []
            for j in all_possible_combos:
                for k in range(1,domain_sizer+1):
                    s = j[:]
                    s.append(k)
                    temp.append(s)
            all_possible_combos = temp[:]
        
        #Turn combos into tuples so that they canbe used. 
        for i in range(len(all_possible_combos)):
            all_possible_combos[i].insert(0,opperator)
            all_possible_combos[i] = tuple(all_possible_combos[i])



        final = []
        if opperator == "+" or opperator == "*": 
            print("Case 1")
            for combo in all_possible_combos:
            #for i in combinations(range(1,domain_sizer + 1),num_in_cage):
            #    print(i)
                if calculate_associative(opperator,combo,total):
                    final.append(combo)
        else:    
            print("Case 2")
            #for i in permutations(range(1,domain_sizer + 1),num_in_cage):
            for combo in all_possible_combos:
                if calculate_non_associative(opperator,combo,total):
                    final.append(i)
        print(final)

        cage_cons.add_satisfying_tuples(final)
        csp.add_constraint(cage_cons)

    return csp,  allvars

def calculate_associative(opperator, tuples, goal):
    total = 0
    if opperator == "+":
        for i in tuples[1:]:
            total += i
        if total == goal:
            return True
    elif opperator == "*":
        for i in tuples[1:]:
            total *= i
        if total == goal:
            return True
    return False
def calculate_non_associative(opperator, tuples, goal):
    total = tuples[1]

    if opperator == "-":
        for i in tuples[2:]:
            total -= i
        if total == goal:
            return True
    
    elif opperator == "/":
        for i in tuples[2:]:
            total /= i
        if total == goal:
            return True

    else:
        return calculate_non_associative("/",tuples,goal) or calculate_non_associative("-",tuples,goal) or calculate_associative("+",tuples,goal) or calculate_associative("*",tuples,goal)

    return False

