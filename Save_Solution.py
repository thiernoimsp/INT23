import csv


class Save_Solution:
	def __init__(self, inst):
		self.inst = inst
		
	def write_solution(self, name, sol_info):
		with open(name, "a") as f:
			writer = csv.writer(f, lineterminator='\n')
			writer.writerow(sol_info)

	def write_solution_listener(self, name, track_progress) :
		with open(name, 'w', newline='') as ff:
			writer = csv.writer(ff, lineterminator='\n')
			for nnn in track_progress : 
				writer.writerow(nnn)
			    
			    
			    
	def write_solution_flows_path(self, name, dict_to_save):
		#os.makedirs(os.path.dirname(filename), exist_ok=True)
		with open(name, 'w', newline='') as ff:
			for k,v in dict_to_save.items():
				#s = str(k)+" "+ str(v) +"\n"
				s = str(k)+":"+ str(v) +"\n"
				ff.write(s)
