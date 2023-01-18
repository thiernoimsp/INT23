from docplex.mp.model import Model
from docplex.mp.progress import *
import sys
import csv
import random
import time
import networkx as nx
from collections import defaultdict
from more_itertools import powerset
from random import randint
from Save_Solution import Save_Solution
from itertools import chain, combinations



class ReadInastances:
    def __init__(self, network, nD: int, nV: int, nM: int, nF: int, pGF: int, min_capacity: int, max_capacity: int):
        self.network = network
        #D = list(range(nD)) # number of devices
        V = list(range(nV)) # set of telemetry items
        Size = {} # size of telemetry items
        V_d = defaultdict(list) # telemetry embedded by device d
        F = list(range(nF)) # set of network flows
        self.pGF = pGF # percentage of network flows with given path
        GF = [i for i in range(int((pGF * nF / 100)))] # set of given flows
        FF = [f for f in F if f not in GF] # set of remaining flows
        M = list(range(nM)) # set monitoring applications
        
        
        # Read the data from the CSV file
        with open(self.network, "r") as f:
            reader = csv.reader(f)
            
            # create an empty graph to store the network
            G = nx.Graph()
            
            # fill the graph with the edges
            for row in reader:
                G.add_edge(int(row[0]), int(row[1]))
                
            # set of nodes
            D = list(G.nodes)

            # Create an empty dictionary to store the neighbors of each node
            neighbors = {}
            for d in G.nodes():
                neighbors_d = list(G.neighbors(d))
                neighbors[d] = neighbors_d
                
            # generate size of telemetry items between 2 and 8
            for v in V:
                Size[v] = random.randrange(min_capacity,max_capacity+1, 2)
            
            # adiing telemetry items to all nodes
            for d in D:
                V_d[d] = V
            
        # Generate F flows
        flows = {}
        for f in F:
	        # Choose a random source and destination
	        source = random.randint(0, nD-1)
	        destination = random.randint(0, nD-1)
	        # Make sure the source and destination are not the same
	        while source == destination:
		        destination = random.randint(0, nD-1)
	        # Choose a random capacity for the flow
	        capacity = random.randint(min_capacity, 3*max_capacity)
	        # Add the flow to the dictionary
	        flows[f] = [source, destination, capacity]

        # getting the source, destination and capacity of each flow
        S_f = [source[0] for source in flows.values()]
        D_f = [destination[1] for destination in flows.values()]
        K_f = [capacity[2] for capacity in flows.values()]
                
        # getting the shortest path for each flow
        shortest_path = {}
        for f in F:
            s = S_f[f]
            d = D_f[f]
            shortest_path[f] = nx.shortest_path(G, s, d)
            
        # getting the length of the longest route in the shortest paths
        self.longest_route = len(max(shortest_path.values(), key=len))
        self.max_route = 10
        
        
        # adding monitoring application requirements
        l = int(nV / nM) #length of the monitoring application
        s_r_m = [V[i * l:(i + 1) * l] for i in range((nV + l - 1) // l )]
		
        # setting monitoring requirement for each monitoring application
        R_m = {}
        for m in M:
            R_m[m] = s_r_m[m]
		
		# getting the spatial dependencies
        Rs = {}
        for m in M:
            Rs[m] = [list(x) for x in powerset(R_m[m]) if x]
            
        # getting the temporal dependencies
        Rt = {}
        for m in M:
            Rt[m] = [list(x) for x in powerset(R_m[m]) if x]
				
		# reading required deadlines
        TT = {}
        for m in M:
	        for P in range(len(Rs[m])):
		        TT[P] = randint(0, 20)

        HH = {}
        for m in M:
	        for P in range(len(Rt[m])):
		        HH[P] = randint(0, 20)
		        
		#define the parameters
        self.D = D
        self.neighbors = neighbors
        self.V = V
        self.V_d = V_d
        self.Size = Size
        self.M = M
        self.R_m = R_m
        self.Rs = Rs
        self.Rt = Rt
        self.TT = TT
        self.HH = HH
        self.F = F
        self.S_f = S_f
        self.D_f = D_f
        self.K_f = K_f
        self.GF = GF
        self.FF = FF
        #self.max_route = max_route
        self.shortest_path = shortest_path
        
        
track_progress = list()
class MipGapPrinter(ProgressListener):
    def __init__(self):
        #ProgressListener.__init__(self, ProgressClock.Gap)
        ProgressListener.__init__(self, ProgressClock.Objective)

    def notify_progress(self, pdata):
        gap = pdata.mip_gap
        ms_time = 1000* pdata.time
        obj = pdata.current_objective
        data = [int(pdata.current_objective), round(pdata.mip_gap*100, 2), round(pdata.time, 2)]
        track_progress.append(data)
        #print('-- new gap: {0:.1%}, time: {1:.0f} ms, obj :{2:.2f}'.format(gap, ms_time, obj))
        #print(track_progress)
        if pdata.has_incumbent():
          track_progress.append([int(pdata.incumbent_objective), round(pdata.mip_gap*100, 2), round(pdata.time, 2)])
        return track_progress
        
        
class Compact_Formulation_Mixte:
	""" 
	This class implement the new proposed model using gurobi 
	"""
	def __init__(self, inst):
	    model = Model('OINT')
	    
	    # Create decision variables
	    s_b = {(m,d,P): model.binary_var(name='s_b_{}_{}_{}'.format(m,d,P)) for m in inst.M for d in inst.D for P in range(len(inst.Rs[m]))}
	    t_b = {(m,P): model.binary_var(name='t_b_{}_{}'.format(m,P)) for m in inst.M for P in range(len(inst.Rt[m]))}
	    y = {(d,v,f): model.binary_var(name='y_{}_{}_{}'.format(d,v,f)) for d in inst.D for v in inst.V for f in inst.F}
	    x = {(i,j,f): model.binary_var(name='x_{}_{}_{}'.format(i,j,f)) for i in inst.D for j in inst.D for f in inst.F if i != j}
	    gg = {(i,f): model.continuous_var(name='gg_{}_{}'.format(i,f)) for i in inst.D for f in inst.F}
	    s = {(m,d,P): model.integer_var(name='s_{}_{}_{}'.format(m,d,P)) for m in inst.M for d in inst.D for P in range(len(inst.Rs[m]))}
	    t = {(m,P): model.integer_var(name='t_{}_{}'.format(m,P)) for m in inst.M for P in range(len(inst.Rt[m]))}
	    
	    # constraints the flows to start from the source and end at the destination
	    for f in inst.FF:
	        model.add_constraint(model.sum(x[inst.S_f[f], j, f] for j in inst.D if inst.S_f[f]!=j) == 1 )
	        model.add_constraint(model.sum(x[i, inst.D_f[f], f] for i in inst.D if inst.D_f[f]!=i) == 1 )
	        
	    # Flow conservation constraints
	    for f in inst.FF:
	        for p in inst.D:
	            if p != inst.S_f[f] and p != inst.D_f[f]:
	                model.add_constraint(model.sum(x[i,p,f] for i in inst.D if p!=i) - model.sum(x[p,j,f] for j in inst.D if p!=j) == 0)
	    '''
	    # subtour elemination
	    subsets = [list(x) for x in powerset(inst.D) if x]            
	    for f in inst.FF:
	        for S in subsets:
	            if len(S) >= 2:
	                edges = [(i,j) for i in S for j in S if i != j]
	                expr = sum(x[i,j,f] for i,j in edges)
	                model.add_constraint(expr <= len(S) - 1)
        '''


	        
	    # removing cycle of size two
	    for i in inst.D:
	        for j in inst.D:
	            for f in inst.FF:
	                if i != j:
	                    model.add_constraint(x[i,j,f] + x[j,i,f] <= 1)
	                    
	    #MTZ 
	    for i in inst.D:
	        for j in inst.D:
	            for f in inst.F:
	                if i != j:
	                    model.add_constraint(gg[j,f] >= gg[i,f] + 1 - len(inst.D)*(1-x[i,j,f]))

	    
	    # limitting the route of flows
	    for f in inst.FF:
	        #model.add_constraint(model.sum(x[i, j, f] for i in inst.D for j in inst.D if i!=j) <= inst.max_route - 1)
	        model.add_constraint(model.sum(x[i, j, f] for i in inst.D for j in inst.D if i!=j) <= inst.max_route -1)
	        
	    # collected items are collected from device on the route of the flow
	    for d in inst.D:
	        for v in inst.V_d[d]:
	            for f in inst.FF:
	                model.add_constraint(y[d,v,f] <= model.sum(x[i,d,f] for i in inst.neighbors[d]))
	                
	    # a single telemetry item should be a collected by a single flow
	    for d in inst.D:
	        for v in inst.V_d[d]:
	            model.add_constraint(model.sum(y[d, v, f] for f in inst.F) <=1)
	    
	    # capacity of given flows should not be exceeded
	    for f in inst.GF:
	        model.add_constraint(model.sum(inst.Size[v] * y[d, v, f] for d in inst.shortest_path[f] for v in inst.V_d[d]) <=  inst.K_f[f])
	        model.add_constraint(model.sum(y[d,v,f] for d in [j for j in inst.D if j not in inst.shortest_path[f]] for v in inst.V_d[d] ) <= 0)
	        
	    # capacity
	    for f in inst.FF:
	        model.add_constraint(model.sum(inst.Size[v] * y[d, v, f] for d in inst.D for v in inst.V_d[d]) <=  inst.K_f[f])
	    
	    
	    # counting spatial dependencies
	    for m in inst.M:
	        for d in inst.D:
	            for P in range(len(inst.Rs[m])):
	                model.add_constraint(s[m,d,P] == model.sum(y[d, v, f] for v in inst.Rs[m][P] for f in inst.F))
	                
	    # counting temporal
	    for m in inst.M:
	        for P in range(len(inst.Rt[m])):
	            if inst.HH[P] > inst.TT[P]:
	                model.add_constraint(t[m,P] == model.sum(y[d, v, f] for d in inst.D for v in inst.Rs[m][P] for f in inst.F))
	                
	    # spatial dependencies
	    for m in inst.M:
	        for d in inst.D:
	            for P in range(len(inst.Rs[m])):
	                model.add_constraint(s_b[m,d,P] <= s[m,d,P]/len(inst.Rs[m][P]))
	                
	    # temporal dependencies
	    for m in inst.M:
	        for P in range(len(inst.Rt[m])):
	            model.add_constraint(t_b[m,P] <= t[m,P]/len(inst.Rt[m][P]))	        
	    
	    # the objective function
	    obj_function = model.sum(s_b[m,d,P] for m in inst.M for d in inst.D for P in range(len(inst.Rs[m]))) + model.sum(t_b[m,P] for m in inst.M for P in range(len(inst.Rt[m])))
	    model.maximize(obj_function)
	    # creating class variables
	    self.inst = inst
	    self.model = model
	    self.s_b = s_b
	    self.t_b = t_b
	    self.s = s
	    self.t = t
	    self.x = x
	    self.y = y

	    
	def optimize(self):
	    # connect a listener to the model
	    #self.model.add_progress_listener(MipGapPrinter())
	    printer = MipGapPrinter()
	    self.model.add_progress_listener(printer)
	    # setting cplex parameters
	    #self.model.parameters.relax_type = "LP"
	    self.model.parameters.timelimit.set(600)
	    solution = self.model.solve(log_output = True)
	    #checkfi  the solution is not None
	    if solution is None:
	        print('Error: No solution found')
	        Sol_info = [len(self.inst.D), len(self.inst.F), len(self.inst.V), len(self.inst.M), '--', '--', '--', '--', '--']
	    else:
	        print(self.model.get_solve_details())
	        print(f'Objective value: {solution.objective_value}')    
	        
	        # getting the routes of flows
	        Flow_Path_dict ={} # initate a dictionary for saving the flow path
	        for f in self.inst.FF:
	            ori = self.inst.S_f[f]
	            tour = [ori]
	            while True:
	                # Check if the current node is the destination node
	                #if ori == self.inst.D_f[f]:
	                #   break
	                next_nodes = [i for i in self.inst.D if ori!=i and self.x[ori, i, f].solution_value == 1]
	                if not next_nodes:
	                    # No more nodes to visit, break out of the loop
	                    break
	                ori = next_nodes[0]
	                tour.append(ori)
	                if ori == self.inst.D_f[f] :
	                    break        
	            Flow_Path_dict[f] = tour
	            
	        # getting the spatial dependencies
	        spatial = list()
	        for m in self.inst.M:
	            for d in self.inst.D:
	                #if len(inst.Rsd[m,d]) > 0:
	                for P in range(len(self.inst.Rs[m])):
	                    #for P in range(len(self.inst.Rsd[m,d])):
	                    if self.s_b[m,d,P].solution_value == 1:
	                        data = [m,d,P]
	                        spatial.append(data)
	                            
	        # getting temporal dependencies
	        temporal = list()
	        for m in self.inst.M:
	            for P in range(len(self.inst.Rt[m])):
	                if self.t_b[m,P].solution_value == 1:
	                    data = [m,P]
	                    temporal.append(data)
	                    
	        # getting the collected telemetry item 
	        collected = list()
	        for d in self.inst.D:
	            for v in self.inst.V_d[d]:
	                for f in self.inst.F:
	                    if self.y[d,v,f].solution_value == 1:
	                        data = [d,v,f]
	                        collected.append(data)
	                        
	        #saving the solution
	        Sol_info = [len(self.inst.D), len(self.inst.F), len(self.inst.V), len(self.inst.M), len(collected), solution.objective_value, round(int(self.model.solution.solve_details.best_bound),2), round((self.model.solve_details.mip_relative_gap)*100,2), round(self.model.solve_details.time, 2)]
	        print(Sol_info)
	                        
	        # saving the data 
	        Sol_data = [spatial, temporal, collected, Flow_Path_dict]
						
	    return Sol_info, Sol_data
        
        
        
if __name__ == "__main__":
    if len(sys.argv) != 9:
        print('Usage: python3.7 INT_Mixte_1.py [path to network] [number nodes] [number items] [number monitoring application] [number flows] [percentage of given flows] [min_capacity] [max_capacity]')
        sys.exit(1)
    network = sys.argv[1]
    nD = int(sys.argv[2])
    nV = int(sys.argv[3])
    nM = int(sys.argv[4])
    nF = int(sys.argv[5])
    pGF = int(sys.argv[6])
    min_capacity = int(sys.argv[7])
    max_capacity = int(sys.argv[8])

    inst = ReadInastances(network, nD, nV, nM, nF, pGF, min_capacity, max_capacity)
    mixte = Compact_Formulation_Mixte(inst)
    Sol_info, Sol_data = mixte.optimize()
    
