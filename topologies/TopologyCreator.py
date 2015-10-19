class TopologyCreator(object):
	" Creates custom Topology Configuration Files "

	def __init__(self,type,k):
		if type == "clique" :
			# Make a clique topology of k switches. 
			self.clique(k)
		else :
			type == "random" 
			# Make a random topology of k switches with atmost k/2 links for each switch.
			self.random(k)

	def clique(self, size) :
		# Make a clique topology of k switches. 

		f1 = open("./topoConf/switches", 'w')

		for i in range(1,size+1) :
			f1.write("s" + str(i) + "\n")

		f2 = open("./topoConf/links", 'w')

		for i in range(1, size + 1) :
			for j in range(i + 1, size + 1) :
				f2.write("s" + str(i) + " s" + str(j) + "\n")


	def random(self, size) :
		# Make a random topology of k switches
		pass



#topotype = input("Enter type of topology ")
#size = int(input('Enter number of switches '))
ring = TopologyCreator("clique", 10)

		