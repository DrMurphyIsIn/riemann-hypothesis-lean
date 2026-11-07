import re
import os
C=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),'logs')+'/'
def us(t): return sum(float(x) for x in re.findall(r'([\d.]+) user', t))
k=us(open(C+'kernel.log').read())
n=open(C+'nanoda.log').read(); nu=us(n); ex=sum(float(x) for x in re.findall(r'^real ([\d.]+)', n, re.M))
c=open(C+'controls.log').read(); cr=sum(float(x) for x in re.findall(r'^real ([\d.]+)', c, re.M))
print(f"lean user {k:.0f}s; lean4export real {ex:.0f}s; nanoda user {nu:.0f}s; planted nanoda real {cr:.0f}s (incl. slot wait); total {(k+ex+nu+cr)/3600:.2f} h")
