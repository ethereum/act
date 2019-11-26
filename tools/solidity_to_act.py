from act import Act

import json
import sys

if __name__ == '__main__':
	if len(sys.argv) != 2:
		print("Usage: " + sys.argv[0] + " solOutput.json")
		sys.exit(1)

	solOutput = json.loads(open(sys.argv[1]).read())
	for contractPath in solOutput['contracts']:
		for contract in solOutput['contracts'][contractPath]:
			print(Act(solOutput['contracts'][contractPath][contract], contract, contractPath).spec())
