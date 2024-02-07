# =============================
# Student Names: Raksha Rehal & Nicholas Tillo  
# Group ID: 62
# Date: 2024 - 02 - 01
# =============================
# CISC 352 - W23
# cagey_csp.py
# desc: implementations of the extended cagey game in a variety of 
# constraint formats, represented as a csp in each case.
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
    """A model of a Cagey grid (without cage constraints) built using only
        binary not-equal constraints for both the row and column constraints."""

    # extract num of rows, cols.
    n = cagey_grid[0]
    cages = cagey_grid[1]

    # begin initializing the csp.
    csp = CSP("Cagey: Binary Not-Equal Constraints")
    allvars = []

    # the variables are represented in this problem as each individual cell
    # of the cagey grid. hence, we will add them to our list of variables,
    # and they will be represented with names in the form "Cell(i,j)".
    #
    # their permanent domains will span from 1-n.
    for i in range(1,n+1):
        for j in range(1,n+1):
            new_var = Variable("Cell("+str(i)+","+str(j)+")", list(range(1,n+1)))
            allvars.append(new_var)
            csp.add_var(new_var)
    
    # the constraints will make use of an itertools method "permutations"
    # that will allow us to define every possible assignment that a variable
    # within this csp could have.
    #
    # as the perma-domain for any var is 1-n, a representation of cagey
    # (without cages right now) with binary constraints would constitute
    # of constraints with a scope of only two variables. hence, all
    # tuples satifying this constraint would be a binary permutation of
    # these n numbers for any given constraint.
    #
    allowed = []
    for valid_assignment in permutations(range(1,n+1),2):
        allowed.append(valid_assignment)

    # building the specific constraints row-wise.
    i = 0
    while i < n*n:
        row = []

        # appending the variables that belong in each row...
        #
        # e.g. if n = 3, our first row will contain variables named
        # ["Cell(1,1)", "Cell(1,2)", "Cell(1,3)"].
        for j in range(n):
            row.append(allvars[i + j])

        # sets up a constraint object between every two variables
        # in each row.
        all_row_cons = combinations(row,2) 

        for c in all_row_cons:
            cons_name = "Constraint for " + str(c)
            cons = Constraint(cons_name,c)
            cons.add_satisfying_tuples(allowed) 
            csp.add_constraint(cons)

        i += n

    # building the specific constraints column-wise.
    for j in range(n):
        column = []

        # appending the variables that belong in each column...
        #
        # e.g. if n = 3, our first column will contain variables named
        # ["Cell(1,1)", "Cell(2,1)", "Cell(3,1)"].
        i = 0
        while i < n*n:
            column.append(allvars[i + j])
            i += n

        all_col_cons = combinations(column,2)
        for c in all_col_cons:
            cons_name = "Constraint for " + str(c)
            cons = Constraint(cons_name,c)
            cons.add_satisfying_tuples(allowed) 
            csp.add_constraint(cons)
    
    return csp, allvars


def nary_ad_grid(cagey_grid):
    """A model of a Cagey grid (without cage constraints) built using only n-ary
      all-different constraints for both the row and column constraints."""
    
    # initialization of the csp.
    n = cagey_grid[0]
    cages = cagey_grid[1]

    csp = CSP("Cagey: n-ary \"alldiff\" Constraints")
    allvars = []
    
    # initialize the variables, i.e. each cell of the grid.
    for i in range(1,n+1):
        for j in range(1,n+1):
            new_var = Variable("Cell("+str(i)+","+str(j)+")", list(range(1,n+1)))
            allvars.append(new_var)
            csp.add_var(new_var)

    # initialize all the constraints.
    
    # specify the allowed tuples, which in this case, is every 
    # possible way that n values can be represented amongst
    # the n present variables in each row/column.
    allowed = []
    for valid_assignment in permutations(range(1,n + 1), n):
        allowed.append(valid_assignment)

    # building the specific constraints row-wise.
    i = 0
    while i < n*n:
        row = []

        for j in range(n):
            row.append(allvars[i + j])
            
        cons_name = "Constraint for " + str(row)
        cons = Constraint(cons_name, row)
        cons.add_satisfying_tuples(allowed) 
        csp.add_constraint(cons)

        # step n times to get to the next row.
        i += n
    
    # building the specific constraints column-wise.
    for j in range(n):
        column = []

        i = 0
        while i < n*n:
            column.append(allvars[i + j])

            # step n times to get to the next column.
            i += n

        cons_name = "Constraint for " + str(column)
        cons = Constraint(cons_name, column)
        cons.add_satisfying_tuples(allowed) 
        csp.add_constraint(cons)

    return csp, allvars


def cagey_csp_model(cagey_grid):
    """a model of a Cagey grid built using n-ary all-different constraints 
      for the grid, together with Cagey cage constraints."""

    # initialization.
    n = cagey_grid[0]
    cages = cagey_grid[1]

    csp = CSP("Extended Cagey with n-ary \"alldiff\" Constraints")
    allvars = []

    # initialize the variables, i.e. each cell of the grid.
    for i in range(1,n+1):
        for j in range(1,n+1):
            new_var = Variable("Cell("+str(i)+","+str(j)+")", list(range(1,n+1)))
            allvars.append(new_var)
            csp.add_var(new_var)
    
    # initialize all the constraints.
    
    # specify the allowed tuples according to n-ary alldiff rules.
    allowed = []
    for valid_assignment in permutations(range(1,n + 1),n):
        allowed.append(valid_assignment)

    # building the specific constraints row-wise.
    i = 0
    while i < n*n:
        row = []

        for j in range(n):
            row.append(allvars[i + j])

        cons_name = "Constraint for " + str(row)
        cons = Constraint(cons_name, row)
        cons.add_satisfying_tuples(allowed) 
        csp.add_constraint(cons)

        i += n
    
    # building the specific constraints column-wise.
    for j in range(n):
        column = []

        i = 0
        while i < n*n:
            column.append(allvars[i + j])
            i += n

        cons_name = "Constraint for " + str(column)
        cons = Constraint(cons_name, column)
        cons.add_satisfying_tuples(allowed) 
        csp.add_constraint(cons)

    # building the constraints for each cage.
    for i in cages:

        total = i[0]  # extract the result of the operation.
        surrounded_boxes = i[1]  # extract a list of tuples meant to reference the variables 
                                 # involved in this cage/constraint.
        opperator = i[2]  # extract the operator.

        # we will put all the variables that we need to find the values for
        # in one big list.
        needed_vars = []

        # for the each tuple within the scope of the the current cage...
        for k in surrounded_boxes:

            # ... we find the corresponding variable object with the same name
            # as each specified tuple (i.e. intended to index the same object).
            name = "Cell("+str(k[0])+","+str(k[1])+")"
            for y in allvars:
                if y.name == name:
                    needed_vars.append(y)

        # create a new variable object to store this cage and its information.
        new_var = Variable("Cage_op("+str(total)+":"+str(opperator)+":"+str(needed_vars)+")", ['+','-','/','*','?'])
        csp.add_var(new_var)
        allvars.append(new_var)

        # add this information (representing a cage) as a constraint object
        cons_vars = needed_vars[:]
        cons_vars.append(new_var)
        cons_name = "Constraint for Variables" + str(needed_vars) + " with operator " + str(opperator)
        cage_cons = Constraint(cons_name, cons_vars)

        # finding all permutations for every variable in the 
        # scope of the current cage/constraint.
        #
        # note: did not use permutations() method from itertools
        # due to conflicts working with the data strucutre used
        # to store the results of said method.
        num_in_cage = len(needed_vars)
        domain_sizer = allvars[0].domain_size()
        all_possible_combos = [[]]

        for i in range(num_in_cage):  # for each variable in the cage...
            temp = []

            for j in all_possible_combos:  # we initialize each permutation within
                                           # a seperate list.

                for k in range(1,domain_sizer+1):
                    s = j[:]  # we put all possible values in a different list
                              # in every possible order...
                    s.append(k)
                    temp.append(s)

            all_possible_combos = temp[:]  # ... and copy it over to our list
                                           # holdihng every permutation in its own list.
        
        # now, turning each permutation into a tuple format such that it can
        # be used and compared to when assessing the validity of assignments
        # to variables.
        for i in range(len(all_possible_combos)):
            all_possible_combos[i].append(opperator)
            all_possible_combos[i] = tuple(all_possible_combos[i])

        # the list "final" will store the satisfying tuples for 
        # the values within the current cage and its variables.
        final = []


        #Check all combonations, and add the ones that pass
        #To the final list. 
        if opperator == "+" or opperator == "*": 
            for combo in all_possible_combos:
                if calculate_associative(opperator,combo,total):
                    final.append(combo)
        else:    
            for combo in all_possible_combos:
                if calculate_non_associative(opperator,combo,total):
                    final.append(i)

        #Add final list to cage constraint and add the constraint to CSP.
        cage_cons.add_satisfying_tuples(final)
        csp.add_constraint(cage_cons)


    return csp, allvars

def calculate_associative(opperator, tuples, goal):
    #Calculate if the corresponding operation applied to tuples 
    #rwesults in goal. 
    total = tuples[0]

    if opperator == "+":
        for i in tuples[1:-1]:
            total += i
        if total == goal:
            return True
    elif opperator == "*":
        for i in tuples[1:-1]:
            total *= i
        if total == goal:
            return True
    return False

def calculate_non_associative(opperator, tuples, goal):
    #Calculate if the corresponding operation applied to tuples 
    #results in goal. 
    total = tuples[0]
    if opperator == "-":
        for i in tuples[1:-1]:
            total -= i
        if total == goal:
            return True
    
    elif opperator == "/":
        for i in tuples[1:-1]:
            total /= i
        
        if int(total) == goal:
            return True

    else:
        return calculate_non_associative("/",tuples,goal) or calculate_non_associative("-",tuples,goal) or calculate_associative("+",tuples,goal) or calculate_associative("*",tuples,goal)

    return False

