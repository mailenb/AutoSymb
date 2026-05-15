
## Configuration
Before compiling the tool, we must run the script configure.sh. 

In the source code, there are some specification-dependent values that the generator must know at compile time. Specifically, the names of the top-most program and variable non-terminal, and the file path to the .ssos specification. Running the bash script before compilation ensures that we define these parameters correctly without requiring manual edits to the source code. To run the script, we execute the following command:
`
    $ ./configure.sh -p <p> -x <x> -s <symbolic SOS path>
`
The script uses `sed -i` to substitute the variable values with the values from the flag fields. 


To build the tool, we run the following command after running the script:
`
$ cabal build
`
This will automatically generate and embed both types of executors in the original source files. 

To run the interpreters on a program written in the specified language, we execute the following command:
`
    $ cabal run tool [<cabal flags>] -- 
                     [<mode>] [-ast] <program path>
`

We may freely add additional flags to Cabal when executing the run command. For example, we can use the flags `-ddump-splices` and `-ddump-to-file` to inspect the generated code from TH. 