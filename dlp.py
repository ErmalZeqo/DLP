from prime import is_probable_prime
from math import sqrt
import random

# Ermal ZEQO 21315866
# Mohamed Nassim FERROUKH 21308499

#Exercice 1
#Q1
def bezout(a, b):
    """   Retourne (pgcd, u, v) tels que a*u + b*v = pgcd"""
    u_prev, u_curr = 1, 0
    v_prev, v_curr = 0, 1
    r_prev, r_curr = a, b

    while r_curr != 0:
        q = r_prev // r_curr

        u_next = u_prev - q * u_curr
        v_next = v_prev - q * v_curr
        r_next = r_prev - q * r_curr

        u_prev, u_curr = u_curr, u_next
        v_prev, v_curr = v_curr, v_next
        r_prev, r_curr = r_curr, r_next

    return r_prev, u_prev, v_prev

#Q2
def inv_mod(a, n):
    """Retourne a^(-1) mod N, none si on n'a pas inversible."""
    pgcd, u, v = bezout(a,n)
    if pgcd != 1: # il n’y a pas d’inverse
        return None
    return u % n


def invertibles(N):
    """
    Retourne la liste des éléments inversibles de Z/NZ.
    """
    L = []
    for a in range(N):
        if inv_mod(a, N) is not None:
            L.append(a)
    return L

#Q3
def phi(N):
   return len(invertibles(N))


# Exercice 2

# Q1
def exp(a, n, p):
    """
    Calcule a^n mod p par exponentiation modulaire itérative.
    """
    if p <= 0:
        print("Le module p doit être strictement positif.")
    if n < 0:
        print("Cette fonction ne gère pas les exposants négatifs.")

    a %= p
    res = 1

    while n > 0:
        if n & 1:
            res = (res * a) % p
        a = (a * a) % p
        n >>= 1

    return res


# Petit helper : racine carrée entière
def isqrt(n):
    if n < 0:
        print("n doit être positif.")
    if n < 2:
        return n

    left, right = 1, n
    ans = 1
    while left <= right:
        mid = (left + right) // 2
        if mid * mid <= n:
            ans = mid
            left = mid + 1
        else:
            right = mid - 1
    return ans


# Petit helper : test de primalité exact (simple)
def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False

    d = 3
    r = isqrt(n)
    while d <= r:
        if n % d == 0:
            return False
        d += 2
    return True


# Q2
def factor(n):
    """
    Retourne la factorisation première de n sous la forme :
    [(p1, v1), (p2, v2), ...]
    """
    if n <= 0:
        print("n doit être strictement positif.")

    factors = []

    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    if v > 0:
        factors.append((2, v))

    d = 3
    while d * d <= n:
        v = 0
        while n % d == 0:
            n //= d
            v += 1
        if v > 0:
            factors.append((d, v))
        d += 2

    if n > 1:
        factors.append((n, 1))

    return factors


# Q3
def order(a, p, factors_p_minus1):
    """
    Calcule l'ordre de a dans (Z/pZ)^*.
    On suppose p premier et a != 0 mod p.
    """
    a %= p
    if a == 0:
        raise ValueError("0 n'appartient pas à (Z/pZ)^*.")

    ord_a = p - 1

    for q, _ in factors_p_minus1:
        while ord_a % q == 0 and exp(a, ord_a // q, p) == 1:
            ord_a //= q

    return ord_a


# Q4
def find_generator(p, factors_p_minus1):
    """
    Trouve un générateur de (Z/pZ)^*.
    """
    if p == 2:
        return 1

    prime_divisors = [q for q, _ in factors_p_minus1]

    for g in range(2, p):
        ok = True
        for q in prime_divisors:
            if exp(g, (p - 1) // q, p) == 1:
                ok = False
                break
        if ok:
            return g

    return None


# Q5
def generate_safe_prime(k):
    """
    Retourne le premier safe prime p de k bits trouvé,
    avec p = 2q + 1 et q premier.

    Version déterministe, sans aléatoire.
    """
    if k < 3:
        raise ValueError("k doit être >= 3.")

    q_min = 1 << (k - 2)          # plus petit entier a k-1 bits
    q_max = (1 << (k - 1)) - 1    # plus grand entier a k-1 bits

    # on commence au premier impair >= q_min
    q = q_min
    if q % 2 == 0:
        q += 1

    while q <= q_max:
        if is_prime(q):
            p = 2 * q + 1
            if p.bit_length() == k and is_prime(p):
                return p
        q += 2

    return None


# Q6
def bsgs(n, g, p):
    """
    Baby-Step Giant-Step :
    cherche x tel que g^x ≡ n (mod p).

    Retourne x si trouvé, sinon None.
    """
    n %= p
    g %= p

    if g == 0:
        raise ValueError("g doit appartenir à (Z/pZ)^*.")
    if n == 0:
        return None
    if n == 1:
        return 0

    factors_p_minus1 = factor(p - 1)
    ord_g = order(g, p, factors_p_minus1)

    # Vérifie que n appartient au sous-groupe engendré par g
    if exp(n, ord_g, p) != 1:
        return None

    m = isqrt(ord_g)
    if m * m < ord_g:
        m += 1

    # Baby steps : g^j
    baby = {}
    cur = 1
    for j in range(m):
        if cur not in baby:
            baby[cur] = j
        cur = (cur * g) % p

    # g^{-m} mod p
    g_inv = exp(g, p - 2, p)          # inverse de g modulo p
    factor_giant = exp(g_inv, m, p)

    # Giant steps : n * (g^{-m})^i
    gamma = n
    for i in range(m + 1):
        if gamma in baby:
            x = i * m + baby[gamma]
            if x < ord_g:
                return x
        gamma = (gamma * factor_giant) % p

    return None