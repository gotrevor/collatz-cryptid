H=[0, -2, 5, 7, 0, 9, 10, 6, 0, 14, 13, 17, 0, 17, 26, 22, 0, 30, 27, 25, 0, 31, 26, 38]
W=[0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, -1, 0, 0, -1, 0, 1, 0, 0, 1, -1]
x,y=10,2
seen={}
for n in range(20000):
    r=x%24
    seen[r]=seen.get(r,0)+1
    x,y = 32*(x//24)+H[r], y+W[r]
    if y<0: print("halt",n);break
print(sorted(seen.items()))
# phases: n mod 4 -> residues
