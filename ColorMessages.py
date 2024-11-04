from termcolor import colored

def success(msg):
    print("[",end="")
    print(colored("+","green"),end="")
    print("] ",end="")
    print(msg)

def warning(msg):
    print("[",end="")
    print(colored("*","yellow"),end="")
    print("] ",end="")
    print(msg)

def error(msg):
    print("[",end="")
    print(colored("-","red"),end="")
    print("] ",end="")
    print(msg)

def info(msg):
    print("[",end="")
    print(colored("i","white"),end="")
    print("] ",end="")
    print(msg)