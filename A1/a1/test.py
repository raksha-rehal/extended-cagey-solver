from itertools import permutations

print("start")

perms = permutations(range(1,4), 3)

for perm in perms:
    print(perm)
    
for perm in perms:
    print(type(perms))