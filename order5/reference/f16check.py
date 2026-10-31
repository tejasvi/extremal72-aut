# F16 = F2[t]/(t^4+t^3+t^2+t+1); element = 4-bit int, bit k = coeff of t^k
def mul(a, b):
    r = 0
    for i in range(4):
        if (b >> i) & 1: r ^= a << i
    for d in range(7, 3, -1):
        if (r >> d) & 1: r ^= 0x1F << (d - 4)
    return r
def pw(a, e):
    r = 1
    for _ in range(e): r = mul(r, a)
    return r
mu5 = sorted(a for a in range(1, 16) if pw(a, 5) == 1)
print("mu5", mu5)
w = next(pw(a, 5) for a in range(1, 16) if pw(a, 5) != 1)
cls = {a: (1 if pw(a, 5) == 1 else (2 if pw(a, 5) == w else 3)) for a in range(1, 16)}
print("omega (norm of smallest non-mu5 element) =", w, "; class 2:", sorted(a for a in cls if cls[a] == 2), "; class 3:", sorted(a for a in cls if cls[a] == 3))
print("class of 1+t (3):", cls[3], " class of 1+t^2 (5):", cls[5])
# weights of psi(y) = y*(t+t^2+t^3+t^4) in F2[t]/(t^5-1)
def psi(p):
    r = 0
    for i in range(4):
        if (p >> i) & 1:
            for j in range(1, 5): r ^= 1 << ((i + j) % 5)
    return r
print("weights:", {a: bin(psi(a)).count('1') for a in range(16)})
