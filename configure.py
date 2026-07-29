import subprocess

# Create path.rtk
abs_path = subprocess.getoutput("pwd")
f = open("path.rkt", "w")
f.write("#lang racket\n")
f.write("(provide (all-defined-out))\n")
f.write("(define srcpath \"" + abs_path + "\")\n")
print("path.rkt is created.")
