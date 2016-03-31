#!/bin/bash
happy -o lib/LTL-Tableaux/src/parser/Parser.hs lib/LTL-Tableaux/src/parser/Grammar.y
alex -o lib/LTL-Tableaux/src/parser/Lexer.hs lib/LTL-Tableaux/src/parser/Tokens.x
ghc -XNPlusKPatterns -isrc:lib/LTL-Tableaux/src -isrc:lib/LTL-Tableaux/src/parser -isrc:lib/LTL-Tableaux/src/util -outputdir build -o $2 $1

