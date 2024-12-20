from SiegelModularForms import *
import time

k = ZZ(sys.argv[1])
print("\nk = {}\n".format(k))
t = time.time()
test = SMF(2,k,False)._ConfirmDimZero()
print("\n")
print(time.time() - t)
print(test)
assert test

