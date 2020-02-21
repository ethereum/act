.PHONY: parser

parser: parser.timestamp

# generates the haskell files that do parsing (compiler compiler)
parser.timestamp: act.cf
	mkdir -p parser && bnfc -m --haskell act.cf -o parser
	touch parser.timestamp
