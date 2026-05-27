#!/usr/bin/env sh

# Accepts three flags for the configuration:
# p: name of the top program syntax nonterminal
# x: name of the top variable syntax nonterminal
# s: file path of the symbolic sos specification you want to make the interpreters from
while getopts "p:x:s:" flag; do
    case "${flag}" in
        p) sed -i "s|prog = \".*\"|prog = \"$OPTARG\"|" src/Syntax.hs ;;
        x) sed -i "s|var = \".*\"|var = \"$OPTARG\"|" src/Syntax.hs ;;
        s) sed -i "s|ssosPath = \".*\"|ssosPath = \"$OPTARG\"|" src/Syntax.hs  
           
           # Also replace line in cabal file following 'extra-source-file:' with the new path
           # to allow for automatic rebuilding after changes in .ssos file
           sed -i "s|^extra-source-files: .*|extra-source-files: $OPTARG|" tool.cabal ;;
           
        *) echo "Usage: -p <prog> -x <var> -s <ssosPath>"; exit 1 ;;
    esac 
done &&

echo "Configuration updated. Run 'cabal build' or 'cabal run' to build or run the tool on your specification."
