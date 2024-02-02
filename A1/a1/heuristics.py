# =============================
# Student Names: Raksha Rehal & Nicholas Tillo
# Group ID: 62
# Date: 2024 - 1 - 28
# =============================
# CISC 352 - W23
# heuristics.py
# desc:
#


#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.

'''This file will contain different constraint propagators to be used within
   the propagators

var_ordering == a function with the following template
    var_ordering(csp)
        ==> returns Variable

    csp is a CSP object---the heuristic can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    var_ordering returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.
   '''

def ord_dh(csp):
    ''' return variables according to the Degree Heuristic '''
    all_vars =  csp.get_all_unasgn_vars()
    return_var = None
    largest = 0

    for var in all_vars:
        var_constraints = csp.get_cons_with_var(var)
        temp = 0

        for cons in var_constraints:
            if cons.get_n_unasgn() == 1:
                pass
            else:
                temp += 1
        
        if temp >= largest:
            largest = temp
            return_var = var
            
    return return_var

def ord_mrv(csp):
    ''' return variable according to the Minimum Remaining Values heuristic '''
    all_vars =  csp.get_all_unasgn_vars()
    min = all_vars[0].cur_domain_size()
    return_var = None

    for var in all_vars:
        temp = var.cur_domain_size()

        if temp <= min:
            min = temp
            return_var = var
            
    return return_var
