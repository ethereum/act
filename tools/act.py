class Act:
	"""This class is a text representation of an Act specification for a smart contract."""

	def __init__(self, contract, contractName, path):
		"""Builds the specification text from a JSON object.

		Parameters
		----------
		contract : JSON object
			The contract object resulting from Solidity's standard-json compilation.
		contractName : str
			The name of the contract.
		path : str
			The path/source unit that contains the contract.
		"""
		self._name = path + "." + contractName
		self._contract = contract
		self._stateVariables = []
		self._properties = []
		self._behaviors = []

		if "storageLayout" in contract:
			for var in contract["storageLayout"]["storage"]:
				self.buildStateVariable(var, contract["storageLayout"]["types"])

		if "abi" in contract:
			for function in contract["abi"]:
				self.buildFunction(function)

	def buildStateVariable(self, var, types):
		varDecl = var["label"] + " : " + types[var["type"]]["label"]
		self._stateVariables.append(varDecl)

	def buildFunction(self, function):
		"""Builds the specification of a function, including property and behavior."

		Parameters
		----------
		function : JSON object
			The function object from Solidity's ABI output.
		"""
		name = function["name"]
		fProperty = "property " + name + ".post of " + name + "\n"
		fBehavior = "behavior " + name + ".behavior of " + name + "\n"
		fInterface = "interface " + name + "("
		fInterface += ",".join([inParam["type"] + " " + inParam["name"] for inParam in function["inputs"]])
		fInterface += ")"
		fBehavior += fInterface + "\n"
		if len(function["outputs"]) > 0:
			fBehavior + "returns\n\n"

		self._properties.append(fProperty)
		self._behaviors.append(fBehavior)

	def spec(self):
		"""Builds the specification string"""
		return "contract " + self._name + "\n\n" + "\n".join(self._stateVariables) + "\n\ninvariants\n\n" + "\n".join(self._properties) + "\n\n" + "\n".join(self._behaviors) + "\nend\n"
