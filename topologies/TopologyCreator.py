class TopologyCreator(object):
	" Creates custom Topology Configuration Files "

	def __init__(self,type,k):
		if type == "clique" :
			# Make a clique topology of k switches. 
			self.clique(k)
		elif type == "fattree" :
			# Make a k-ary fat tree.
			self.fattree(k)
		else :
			type == "random" 
			# Make a random topology of k switches with atmost k/2 links for each switch.
			self.random(k)

	def clique(self, size) :
		# Make a clique topology of k switches. 

		f1 = open("./clique-" + str(size) + ".topo", 'w')
		f1.write("# CLique topology of " + str(size) + " switches \n")

		for i in range(1, size + 1) :
			if i == size : 
				line = "s" + str(i) + ": [ ]"
			else :
				line = "s" + str(i) + ": [ "
			for j in range(i + 1, size + 1) :
				if j == size : 
					line = line + "s" + str(j) + " ] \n"
				else :
					line = line + "s" + str(j) + " , "
			f1.write(line)

	def random(self, size) :
		# Make a random topology of k switches
		pass

	def fattree(self, k) :
		# Make a k-ary Fat Tree. 
		if not k%2 == 0 :
			k = k - 1
		edge = range(0,k*k/2)
		aggregation = range(k*k/2, k*k)
		core = range(k*k,k*k+(k*k/4))

		f1 = open("fattree-" + str(k) + ".topo", 'w')

		for e in edge :
			f1.write("e" + str(e) + ": [")
			pod = e / (k/2)
			for off in range(0,k/2) :
				agg = k * (k / 2) + (pod * (k/2)) + off
				if off == k/2 - 1: 				
					f1.write(" a" + str(agg) + "]\n")
				else :
					f1.write(" a" + str(agg) + ",")


		for a in aggregation :
			f1.write("a" + str(a) + ": [")
			firstCore = k*k + (a % (k/2)) * (k/2)
			for c in range(firstCore, firstCore + k/2) :
				if c == firstCore + k/2 - 1 :
					f1.write(" c" + str(c) + "]\n")
				else : 
					f1.write(" c" + str(c) + ",")			

		for c in core :
			f1.write("c" + str(c) + ": []\n")




#topotype = input("Enter type of topology ")
#size = int(input('Enter number of switches '))
fattree = TopologyCreator("fattree", 4)

		