#Project 2
#Kyle Rood

#How to run:
#pip install -r requirements.txt
#python project2_rood.py <filename with graph>
# ex) python project2_rood.py test_graph.txt

import pandas as pd
import heapq
from collections import deque
import sys
import os
import time

#Used in argmin --> neutral lambda function
identity = lambda x: x

def parse_file(filename):
    #load in data and parse
    data = ""
    with open(filename, 'r') as file:
        data = file.read()

    lines = data.split("\n")
    collect = 0 #0 = no, 1 = vert, 2 = edges, 3 = start/end

    graph = {}

    #default values
    colors = 3
    arcs = []

    for line in lines:
        #get num colors
        if(line.startswith("colors") or line.startswith("Colors")):
            split_line = line.split("=")
            colors = split_line[1]
            print("Colors: " + colors)
            collect = 1

        #building graph
        if(collect == 2):
            split_line = line.split(",")

            #arcs needed for AC3
            arcs.append((split_line[0], split_line[1]))
            arcs.append((split_line[1], split_line[0]))

            #need both combinations (both directions)
            try:
                graph[split_line[0]].append(split_line[1])
            except:
                graph[split_line[0]] = [split_line[1]]

            try:
                graph[split_line[1]].append(split_line[0])
            except:
                graph[split_line[1]] = [split_line[0]]

        if(line.startswith("#") and collect == 1):
            collect = 2

    #Drop nans
    return graph, colors, arcs

## Heuristic Helper Functions ##
#Counts # positive elements
def num_pos_elements(lst):
    return sum(map(bool, lst))

def conflict(var, var2, val, assignment):
    #compare var, var2 to see if their color assignments work
    return (var2 in assignment and not constraints(var, val, var2, assignment[var2]))

def num_conflicts(var, val, assignment):
    #Count number of conflicts for var
    return num_pos_elements(conflict(var, v, val, assignment) for v in raw_graph[var])

def num_legal_values(var, assignment):
    #num_legal_values aggregates the number of valid assignments/conflicts
    if domains:
        return len(domains[str(var)])
    else:
        return num_pos_elements(num_conflicts(var, val, assignment) == 0
                     for val in domains[str(var)])

def argmin_random_tie(lst, key=identity):
    #minimum element in lst, with random choice on ties
    for i in range(0, len(lst)): 
        lst[i] = int(lst[i])
    return min(sorted(lst, key=os.urandom), key=key)

def heuristic(variables, assignment, cur_var, min_remaining_values=False, least_constraining_value=False):
    #if either of these flags is True, we use that heuristic
    if(min_remaining_values == True):
    #min remaining values sorts the variables based on the size of their domain
        return argmin_random_tie(
            [v for v in variables if v not in assignment],
            lambda var: num_legal_values(var, assignment))
     
    if(least_constraining_value == True):
        #least constraining value sorts based on the lowest number of conflicts
        # choose the one that rules out fewest of remaining variables
        return sorted(domains[str(cur_var)], key=lambda val: num_conflicts(cur_var, val, assignment))
    return None

def addColor(restriction_list, vertex, color):
    # restriction_list is a set of restrictions
    #vertex is the node we are coloring
    #color is what we are coloring node
    ans = [] #list of restrictions
    for rr in restriction_list:
        res = checkRestriction(rr, vertex, color)
        #if not possible return false
        if res == False:
            return False
        elif res == None:
            continue
        #add restriction
        else:
            ans.append(res)
    return ans
        
def checkRestriction(restriction, vertex, color):
    #makes sure the vertex doesn't break the restriction (same color as adjacent nodes)
    #finding the index of the vertex (saved to index)
    index = -1
    other = -1
    if(restriction[0] == vertex):
        index = 0
        other = 1
    elif(restriction[1] == vertex):
        index = 1
        other = 0
    else:
        return restriction

    if(isinstance(restriction[other], int)):
        # other component is a color
        if (color != restriction[other]):
            return None
        #means color is not possible
        else:
            return False
    else:
        #return new restriction
        return [restriction[other], color]

def solveCSP(vertices, n, restriction_list, vertex_num, mrv=False, lcv=False):
    # solving the CSP recursively by variable elimination
    # n is the number of colors
    if (vertex_num == 0):
        # in the beginning any color can be assigned to the first vertex, lets say 1
        new_restriction = addColor(restriction_list, vertices[0], 1)

        if (new_restriction == False):
            return False

        #call recursively on next index 
        ans = {vertices[0]:1}
        res = solveCSP(vertices, n, new_restriction, 1)

        if (res == False):
            return False

        ans.update(res)
        return ans

    elif (vertex_num == len(vertices)):
        return {}

    #heuristics to improve performance
    h = heuristic(vertices, domains[vertices[vertex_num]], vertices[vertex_num], min_remaining_values=mrv, least_constraining_value=lcv)

    # branching over all possible colors for vertices[vertex_num] (this is stored in domain)
    for color in domains[vertices[vertex_num]]:
        #ans is current vertex with color assignment
        ans = {vertices[vertex_num]:color}
        new_restriction = addColor(restriction_list, vertices[vertex_num], color)

        if (new_restriction == False):
            continue

        #call recursively on next index
        res = solveCSP(vertices, n, new_restriction, vertex_num+1)

        if (res == False):
            continue
    
        #add new answer to restrictions
        ans.update(res)
        
        #return most up to date color map
        return ans

    # no choice for the current vertex
    return False

## AC3 Functions ##
def make_arc_consistent(x, y):
    #make variable x arc consistent with variable y
    #this means removing a value from x domain if it occurs in y's domain
    revised = False

    #individual domains for comparison
    x_domain = domains[x]
    y_domain = domains[y]

    # Get all arc (x, y) constraints
    all_constraints = [constraint for constraint in raw_graph if constraint == x or constraint == y]

    for x_value in x_domain:
        for y_value in y_domain:
            #check if and y and x are the same, if they are, staisfies is true
            if(x_value == y_value):
                #check to make sure we don't remove last colorable element
                if(len(x_domain) == 1):
                    y_domain.remove(y_value)
                else:
                    x_domain.remove(x_value)
                revised = True

    return revised

def ac3(arcs):
    # Add all the arcs to a queue.
    queue = arcs[:]

    # Repeat until the queue is empty
    while queue:
        # Take the first arc off the queue (dequeue)
        (x, y) = queue.pop(0)

        # Make x arc consistent with y
        changed = make_arc_consistent(x, y)

        # If the x domain has changed
        if changed:
            # Add all arcs of the form (k, x) to the queue (enqueue)
            neighbors = [neighbor for neighbor in arcs if neighbor[1] == x]
            queue = queue + neighbors



#RUNNING TESTS#
#load in data using argument
try:
    input_filename = str(sys.argv[1])
except:
    input_filename = "./test_graph.txt"

raw_graph, num_colors, arcs = parse_file(input_filename)
num_colors = int(num_colors)
print("Graph:")
print(raw_graph)


#for the AC3 part (change this to be for any color)
#set up domains
domains = {}
for ele in raw_graph:
    domains[ele] = list(range(1, num_colors+1))

colors=[]
for i in range(1,num_colors+1):
    colors.append(i)


#list of restrictions --> list of edges --> these two vertices cannot be the same color
restriction_list = []

# initiaitiong restrictions based on the vertex neighborhood
for x in raw_graph:
    for y in raw_graph[x]:
        restriction_list.append([x,y])

# initiating a list of vertices
input_vertices = []
for p in raw_graph:
    input_vertices.append(p)


print("Starting CSP search...")
start_time = time.time()
print("")

print("Preprocess using AC3...")
ac3(arcs)
print("Updated domains:")
print(domains)
print("")

print("Solving CSP...")
mrv_heuristic=True
lcv_heuristic=True
print(solveCSP(input_vertices, num_colors, restriction_list, 0, mrv_heuristic, lcv_heuristic))

end_time = time.time()
print("Time to execute CSP: " + str(end_time - start_time))
print("")