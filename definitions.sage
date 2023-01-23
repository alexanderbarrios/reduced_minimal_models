from sage.schemes.elliptic_curves.weierstrass_morphism import *
S.<a,b,p,l,u,v,c,d,r,s,t,x,y,k,j,e>=QQ[]

# p-adic valuation
def vp(n,p):
	if n==0:
		return 'infinity'
	else:
		return log(1/Qp(p)(n).abs(),p)

# Reduces a polynomial mod n
def PolyMod(f,n):
    R = IntegerModRing(n)
    S.<a,b,p,l,u,v,c,d,r,s,t,x,y,k,c4,c6>=R[]
    return S(f)

# Factors a polynomial over a finite field of order p.
def PolyModFactor(f,p):
	R=GF(p)
	S.<a,b,p,l,u,v,c,d,r,s,t,x,y>=R[];S
	return factor(S(f))

# Given a positive integer n, the code below returns positive integers c and d such that d is squarefree and a=c^2*d
def sqdecom(n):
	if n < 1:
		return 'N/A'
	P=n.prime_factors()
	Sd=[]
	c2=product(p^(ZZ(vp(n,p)) -ZZ(mod(vp(n,p),2))) for p in P)
	c=ZZ(c2^(1/2))
	d=ZZ(n/c^2)
	return c,d

# Given a positive integer n, the code below returns positive integers c,d,e such that d and e are relatively prime and squarefree with a=c^3*d^2*e
def cubedecom(n):
	if n < 1:
		return 'N/A'
	P=n.prime_factors()
	Sd=[]
	Se=[]
	for p in P:
		f=ZZ(vp(n,p))
		if mod(f,3) ==2:
			Sd.append(p)
		if mod(f,3) ==1:
			Se.append(p)
	c3=product(p^(ZZ(vp(n,p)) -ZZ(mod(vp(n,p),3))) for p in P)
	c=ZZ(c3^(1/3))
	d=product(p for p in Sd)
	e=product(p for p in Se)
	return c,d,e

# The code below returns true if an integer n is cubefree. False if it is not.
def is_cubefree(n):
	if n==0:
		return False
	if n==1 or n==-1:
		return True
	else:
		P=n.prime_factors()
		M=max([vp(n,p) for p in P])
		if M<3:
			return True
		if M>2:
			return False

# The set R[i] corresponds to R_i=(a1,a2,a3) as given in (1.1)
R = [ [], (0,0,0), (0,0,1), (0,-1,0), (0,-1,1), (0,1,0), (0,1,1), (1,0,0), (1,0,1), (1,-1,0), (1,-1,1), (1,1,0), (1,1,1) ]

# Let E be an elliptic curve with c4 and c6 the invariants associated to a global minimal model of E. The code below outputs the reduced minimal model from c4 and c4. This algorithm is attained from Proposition 3.3
def RMM(c4,c6):
	a1=ZZ(mod(c6,2))
	c=ZZ(mod(2^(a1-1)*c6,24))
	if c == 0:
		a2,a3,A,B = 0,0, c4,2*c6
	if c == 12:
		a2,a3,A,B = 0,1,c4,2*(c6+216)
	if c == 8:
		a2,a3,A,B = -1,0,c4-16,2*(-6*c4+c6+32)
	if c == 20:
		a2,a3,A,B = -1,1,c4-16,2*(-6*c4+c6+248)
	if c == 16:
		a2,a3,A,B = 1,0,c4-16,2*(6*c4+c6-32)
	if c == 4:
		a2,a3,A,B = 1,1,c4-16,2*(6*c4+c6+184)
	if c == 23:
		a2,a3,A,B = 0,0,c4-1,3*c4 + 2*c6 -1
	if c == 11:
		a2,a3,A,B = 0,1,c4+23,3*c4 + 2*c6 +431
	if c == 3:
		a2,a3,A,B = -1,0,c4-9,-9*c4 + 2*c6 +27
	if c == 15:
		a2,a3,A,B = -1,1,c4+15,-9*c4 + 2*c6 +459
	if c == 19:
		a2,a3,A,B = 1,0,c4-25,15*c4 + 2*c6 -125
	if c == 7:
		a2,a3,A,B = 1,1,c4-1,15*c4 + 2*c6 + 307
	return [a1,a2,a3,-A/48,-B/1728]

# Models for the family of elliptic curves E_T. We use the following naming convention:
#    E_{C_N}  is EN
#    E_{C_2 \times C_{N}}  is E2N

def E2(a,b,d):
	A=a
	B=b^2*d
	return EllipticCurve([0,2*A,0,A^2-B,0])
def E3(a,b):
    return EllipticCurve([a,0,a^2*b,0,0])
def E30(a): # This is E_{C_3^0}
    return EllipticCurve([0,0,a,0,0])
def E4(a,b):
    return EllipticCurve([a,-a*b,-a^2*b,0,0])
def E5(a,b):
    return EllipticCurve([a-b,-a*b,-a^2*b,0,0])
def E6(a,b):
    return EllipticCurve([a - b, -a*b - b^2, -a^2*b - a*b^2, 0, 0])
def E7(a,b):
    return EllipticCurve([a^2 + a*b - b^2, a^2*b^2 - a*b^3, a^4*b^2 - a^3*b^3, 0, 0])
def E8(a,b):
    return EllipticCurve([-a^2 + 4*a*b - 2*b^2, -a^2*b^2 + 3*a*b^3 - 2*b^4, -a^3*b^3 + 3*a^2*b^4 - 2*a*b^5, 0, 0])
def E9(a,b):
    return EllipticCurve([a^3 + a*b^2 - b^3, a^4*b^2 - 2*a^3*b^3 + 2*a^2*b^4 - a*b^5, a^7*b^2 - 2*a^6*b^3 + 2*a^5*b^4 - a^4*b^5, 0, 0])
def E10(a,b):
    return EllipticCurve([a^3 - 2*a^2*b - 2*a*b^2 + 2*b^3, -a^3*b^3 + 3*a^2*b^4 - 2*a*b^5, -a^6*b^3 + 6*a^5*b^4 - 12*a^4*b^5 + 9*a^3*b^6 - 2*a^2*b^7, 0, 0])
def E12(a,b):
    return EllipticCurve([-a^4 + 2*a^3*b + 2*a^2*b^2 - 8*a*b^3 + 6*b^4, a^7*b - 9*a^6*b^2 + 36*a^5*b^3 - 83*a^4*b^4 + 119*a^3*b^5 - 106*a^2*b^6 + 54*a*b^7 - 12*b^8, -a^11*b + 12*a^10*b^2 - 66*a^9*b^3 + 219*a^8*b^4 - 485*a^7*b^5 + 748*a^6*b^6 - 812*a^5*b^7 + 611*a^4*b^8 - 304*a^3*b^9 + 90*a^2*b^10 - 12*a*b^11, 0, 0])
def E22(a,b,d):
	A=a*d
	B=b*d
	return EllipticCurve([0,A+B,0,A*B,0])
def E24(a,b):
    return EllipticCurve([a, -a*b - 4*b^2, -a^2*b - 4*a*b^2, 0, 0])
def E26(a,b):
    return EllipticCurve([-19*a^2+2*a*b+b^2, -10*a^4+22*a^3*b-14*a^2*b^2+2*a*b^3, 90*a^6-198*a^5*b+116*a^4*b^2+4*a^3*b^3-14*a^2*b^4+2*a*b^5, 0, 0])
def E28(a,b):
    return EllipticCurve([-a^4 - 8*a^3*b - 24*a^2*b^2 + 64*b^4,-4*a^6*b^2 - 56*a^5*b^3 - 320*a^4*b^4 - 960*a^3*b^5 - 1536*a^2*b^6 - 1024*a*b^7,8*a^9*b^3 + 144*a^8*b^4 + 1024*a^7*b^5 + 3328*a^6*b^6 + 2048*a^5*b^7 - 21504*a^4*b^8 - 77824*a^3*b^9 - 114688*a^2*b^10 - 65536*a*b^11,0, 0])


# Definition for \alpha_T. We use the following naming convention:
#    \alpha_{C_N}  is alpN
#    \alpha_{C_2 \times C_{N}}  is alp2N

alp2(a,b,d)=(16) * (3*b^2*d + a^2)
alp30(a) = 0
alp3(a,b)=(a - 24*b)*a^3
alp4(a,b)=(a^2 + 16*a*b + 16*b^2)*a^2
alp5(a,b)=a^4 + 12*a^3*b + 14*a^2*b^2 - 12*a*b^3 + b^4
alp6(a,b)=(a + 3*b) * (a^3 + 9*a^2*b + 3*a*b^2 + 3*b^3)
alp7(a,b)=(a^2 - a*b + b^2) * (a^6 + 5*a^5*b - 10*a^4*b^2 - 15*a^3*b^3 + 30*a^2*b^4 - 11*a*b^5 + b^6)
alp8(a,b)=a^8 - 16*a^7*b + 96*a^6*b^2 - 288*a^5*b^3 + 480*a^4*b^4 - 448*a^3*b^5 + 224*a^2*b^6 - 64*a*b^7 + 16*b^8
alp9(a,b)=(a^3 - 3*a*b^2 + b^3) * (a^9 - 9*a^7*b^2 + 27*a^6*b^3 - 45*a^5*b^4 + 54*a^4*b^5 - 48*a^3*b^6 + 27*a^2*b^7 - 9*a*b^8 + b^9)
alp10(a,b)=a^12 - 8*a^11*b + 16*a^10*b^2 + 40*a^9*b^3 - 240*a^8*b^4 + 432*a^7*b^5 - 256*a^6*b^6 - 288*a^5*b^7 + 720*a^4*b^8 - 720*a^3*b^9 + 416*a^2*b^10 - 128*a*b^11 + 16*b^12
alp12(a,b)=(a^4 - 6*a^3*b + 12*a^2*b^2 - 12*a*b^3 + 6*b^4) * (a^12 - 18*a^11*b + 144*a^10*b^2 - 684*a^9*b^3 + 2154*a^8*b^4 - 4728*a^7*b^5 + 7368*a^6*b^6 - 8112*a^5*b^7 + 6132*a^4*b^8 - 3000*a^3*b^9 + 864*a^2*b^10 - 144*a*b^11 + 24*b^12)
alp22(a,b,d)=(16) * d^2 * (a^2 - a*b + b^2)
alp24(a,b)=a^4 + 16*a^3*b + 80*a^2*b^2 + 128*a*b^3 + 256*b^4
alp26(a,b)=(21*a^2 - 6*a*b + b^2) * (6861*a^6 - 2178*a^5*b - 825*a^4*b^2 + 180*a^3*b^3 + 75*a^2*b^4 - 18*a*b^5 + b^6)
alp28(a,b)=a^16 + 32*a^15*b + 448*a^14*b^2 + 3584*a^13*b^3 + 17664*a^12*b^4 + 51200*a^11*b^5 + 51200*a^10*b^6 - 237568*a^9*b^7 - 1183744*a^8*b^8 - 1900544*a^7*b^9 + 3276800*a^6*b^10 + 26214400*a^5*b^11 + 72351744*a^4*b^12 + 117440512*a^3*b^13 + 117440512*a^2*b^14 + 67108864*a*b^15 + 16777216*b^16

# Definition for \beta_T. We use the following naming convention:
#    \beta_{C_N}  is betN
#    \beta_{C_2 \times C_{N}}  is bet2N

bet2(a,b,d)=(-64) * a * (9*b^2*d - a^2)
bet30(a) = -216*a^2
bet3(a,b)=-(a^2 - 36*a*b + 216*b^2)*a^4
bet4(a,b)=-(a^2 + 16*a*b - 8*b^2)*(a + 8*b)*a^3
bet5(a,b)=(-1) * (a^2 + b^2) * (a^4 + 18*a^3*b + 74*a^2*b^2 - 18*a*b^3 + b^4)
bet6(a,b)=(-1) * (a^2 + 6*a*b - 3*b^2) * (a^4 + 12*a^3*b + 30*a^2*b^2 + 36*a*b^3 + 9*b^4)
bet7(a,b)=(-1) * (a^12 + 6*a^11*b - 15*a^10*b^2 - 46*a^9*b^3 + 174*a^8*b^4 - 222*a^7*b^5 + 273*a^6*b^6 - 486*a^5*b^7 + 570*a^4*b^8 - 354*a^3*b^9 + 117*a^2*b^10 - 18*a*b^11 + b^12)
bet8(a,b)=(-1) * (a^4 - 8*a^3*b + 16*a^2*b^2 - 16*a*b^3 + 8*b^4) * (a^8 - 16*a^7*b + 96*a^6*b^2 - 288*a^5*b^3 + 456*a^4*b^4 - 352*a^3*b^5 + 80*a^2*b^6 + 32*a*b^7 - 8*b^8)
bet9(a,b)=(-1) * (a^18 - 18*a^16*b^2 + 42*a^15*b^3 + 27*a^14*b^4 - 306*a^13*b^5 + 735*a^12*b^6 - 1080*a^11*b^7 + 1359*a^10*b^8 - 2032*a^9*b^9 + 3240*a^8*b^10 - 4230*a^7*b^11 + 4128*a^6*b^12 - 2970*a^5*b^13 + 1557*a^4*b^14 - 570*a^3*b^15 + 135*a^2*b^16 - 18*a*b^17 + b^18)
bet10(a,b)=(-1) * (a^2 - 2*a*b + 2*b^2) * (a^4 - 2*a^3*b + 2*b^4) * (a^4 - 2*a^3*b - 6*a^2*b^2 + 12*a*b^3 - 4*b^4) * (a^8 - 6*a^7*b + 4*a^6*b^2 + 48*a^5*b^3 - 146*a^4*b^4 + 176*a^3*b^5 - 104*a^2*b^6 + 32*a*b^7 - 4*b^8)
bet12(a,b)=(-1) * (a^8 - 12*a^7*b + 60*a^6*b^2 - 168*a^5*b^3 + 288*a^4*b^4 - 312*a^3*b^5 + 216*a^2*b^6 - 96*a*b^7 + 24*b^8) * (a^16 - 24*a^15*b + 264*a^14*b^2 - 1776*a^13*b^3 + 8208*a^12*b^4 - 27696*a^11*b^5 + 70632*a^10*b^6 - 138720*a^9*b^7 + 211296*a^8*b^8 - 248688*a^7*b^9 + 222552*a^6*b^10 - 146304*a^5*b^11 + 65880*a^4*b^12 - 17136*a^3*b^13 + 1008*a^2*b^14 + 576*a*b^15 - 72*b^16)
bet22(a,b,d)=(-32) * (a - 2*b) * (a + b) * (2*a - b) * d^3
bet24(a,b)=(-1) * (a^2 + 8*a*b - 16*b^2) * (a^2 + 8*a*b + 8*b^2) * (a^2 + 8*a*b + 32*b^2)
bet26(a,b)=(-1) * (183*a^4 - 36*a^3*b - 30*a^2*b^2 + 12*a*b^3 - b^4) * (393*a^4 - 156*a^3*b + 30*a^2*b^2 - 12*a*b^3 + b^4) * (759*a^4 - 228*a^3*b - 30*a^2*b^2 + 12*a*b^3 - b^4)
bet28(a,b)=(-1) * (a^8 + 16*a^7*b + 96*a^6*b^2 + 256*a^5*b^3 - 256*a^4*b^4 - 4096*a^3*b^5 - 12288*a^2*b^6 - 16384*a*b^7 - 8192*b^8) * (a^8 + 16*a^7*b + 96*a^6*b^2 + 256*a^5*b^3 + 128*a^4*b^4 - 1024*a^3*b^5 - 3072*a^2*b^6 - 4096*a*b^7 - 2048*b^8) * (a^8 + 16*a^7*b + 96*a^6*b^2 + 256*a^5*b^3 + 512*a^4*b^4 + 2048*a^3*b^5 + 6144*a^2*b^6 + 8192*a*b^7 + 4096*b^8)


# Definition for \gamma_T. We use the following naming convention:
#    \gamma_{C_N}  is gamN
#    \gamma_{C_2 \times C_{N}}  is gam2N

gam2(a,b,d)=(64) * d * b^2 * (b^2*d - a^2)^2
gam30(a) = -27*a^4
gam3(a,b)=(a - 27*b)*a^8*b^3
gam4(a,b)=(a + 16*b)*a^7*b^4
gam5(a,b)=(-1) * b^5 * a^5 * (a^2 + 11*a*b - b^2)
gam6(a,b)=(a + 9*b) * a^2 * (a + b)^3 * b^6
gam7(a,b)=(-1) * b^7 * a^7 * (a - b)^7 * (a^3 + 5*a^2*b - 8*a*b^2 + b^3)
gam8(a,b)=a^2 * (a - 2*b)^4 * b^8 * (a - b)^8 * (a^2 - 8*a*b + 8*b^2)
gam9(a,b)=(-1) * b^9 * a^9 * (a - b)^9 * (a^2 - a*b + b^2)^3 * (a^3 + 3*a^2*b - 6*a*b^2 + b^3)
gam10(a,b)=a^5 * (a - 2*b)^5 * b^10 * (a - b)^10 * (a^2 + 2*a*b - 4*b^2) * (a^2 - 3*a*b + b^2)^2
gam12(a,b)=a^2 * (a - 2*b)^6 * b^12 * (a - b)^12 * (a^2 - 6*a*b + 6*b^2) * (a^2 - 2*a*b + 2*b^2)^3 * (a^2 - 3*a*b + 3*b^2)^4
gam22(a,b,d)=(16) * b^2 * a^2 * (a - b)^2 * d^6
gam24(a,b)=a^2 * (a + 8*b)^2 * b^4 * (a + 4*b)^4
gam26(a,b)=(64) * (-9*a + b)^2 * (-3*a + b)^2 * (3*a + b)^2 * (-5*a + b)^6 * (-a + b)^6 * a^6
gam28(a,b)=(256) * b^8 * a^8 * (a + 2*b)^8 * (a + 4*b)^8 * (a^2 - 8*b^2)^2 * (a^2 + 8*a*b + 8*b^2)^2 * (a^2 + 4*a*b + 8*b^2)^4

# The definitions below output the minimal signature of ET. The code is based on Theorem 4.4 from the author's article, Minimal models of rational elliptic curves with non-trivial torsion

def sig2(a,b,d):
	if is_squarefree(gcd(a,b)) == False or d == 1 or b ==0 or is_squarefree(d) == False:
		return 'N/A'
	else:
		c4=ZZ(alp2(a,b,d))
		c6=ZZ(bet2(a,b,d))
		md=ZZ(gam2(a,b,d))
		if md ==0:
			return 'N/A'
		else:
			if vp(b^2*d-a^2,2)>7 and vp(a,2) == 1 and vp(b,2) == 1 and ZZ(mod(a,8)) ==2:
				u=4
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(b^2*d-a^2,2)>7 and vp(a,2) == 1 and vp(b,2) == 1 and ZZ(mod(a,8)) ==6:
				u=2
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(b^2*d-a^2,2) in [4,5,6,7] and vp(a,2) == 1 and vp(b,2) == 1:
				u=2
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(b,2) >2 and ZZ(mod(a,4)) ==3:
				u=2
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			else:
				u=1
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig30(a,b):
	if is_cubefree(a) == False:
		return 'N/A'
	else:
		c4=ZZ(alp30(a))
		c6=ZZ(bet30(a))
		md=ZZ(gam30(a))
		if md ==0:
			return 'N/A'
		else:
			u=1
			return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig3(a,b):
	if gcd(a,b) !=1 or a<1:
		return 'N/A'
	else:
		c4=ZZ(alp3(a,b))
		c6=ZZ(bet3(a,b))
		md=ZZ(gam3(a,b))
		if md ==0:
			return 'N/A'
		else:
			c,d,e = cubedecom(a)
			u=c^2*d
			return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig4(a,b):
	if gcd(a,b) !=1 or a<1:
		return 'N/A'
	else:
		c4=ZZ(alp4(a,b))
		c6=ZZ(bet4(a,b))
		md=ZZ(gam4(a,b))
		if md ==0:
			return 'N/A'
		else:
			c,d = sqdecom(a)
			if vp(a,2) < 8 or mod(b*d,4) != 3:
				u=c
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if is_even(vp(a,2)) and vp(a,2)>7 and ZZ(mod(b*d,4)) == 3:
				u=2*c
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig5(a,b):
	if gcd(a,b) !=1:
		return 'N/A'
	else:
		c4=ZZ(alp5(a,b))
		c6=ZZ(bet5(a,b))
		md=ZZ(gam5(a,b))
		if md ==0:
			return 'N/A'
		else:
			u=1
			return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig6(a,b):
	if gcd(a,b) !=1:
		return 'N/A'
	else:
		c4=ZZ(alp6(a,b))
		c6=ZZ(bet6(a,b))
		md=ZZ(gam6(a,b))
		if md ==0:
			return 'N/A'
		else:
			if vp(a+b,2)<3:
				u=1
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(a+b,2)>2 or vp(a+b,2) == 'infinity':
				u=2
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig7(a,b):
	if gcd(a,b) !=1:
		return 'N/A'
	else:
		c4=ZZ(alp7(a,b))
		c6=ZZ(bet7(a,b))
		md=ZZ(gam7(a,b))
		if md ==0:
			return 'N/A'
		else:
			u=1
			return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig8(a,b):
	if gcd(a,b) !=1:
		return 'N/A'
	else:
		c4=ZZ(alp8(a,b))
		c6=ZZ(bet8(a,b))
		md=ZZ(gam8(a,b))
		if md ==0:
			return 'N/A'
		else:
			if vp(a,2) != 1:
				u=1
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(a,2) == 1:
				u=2
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig9(a,b):
	if gcd(a,b) !=1:
		return 'N/A'
	else:
		c4=ZZ(alp9(a,b))
		c6=ZZ(bet9(a,b))
		md=ZZ(gam9(a,b))
		if md ==0:
			return 'N/A'
		else:
			u=1
			return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig10(a,b):
	if gcd(a,b) !=1:
		return 'N/A'
	else:
		c4=ZZ(alp10(a,b))
		c6=ZZ(bet10(a,b))
		md=ZZ(gam10(a,b))
		if md ==0:
			return 'N/A'
		else:
			if vp(a,2) == 0:
				u=1
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(a,2) != 0:
				u=2
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig12(a,b):
	if gcd(a,b) !=1:
		return 'N/A'
	else:
		c4=ZZ(alp12(a,b))
		c6=ZZ(bet12(a,b))
		md=ZZ(gam12(a,b))
		if md ==0:
			return 'N/A'
		else:
			if vp(a,2) == 0:
				u=1
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(a,2) != 0:
				u=2
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig22(a,b,d):
	if gcd(a,b) !=1 or is_odd(a) or is_squarefree(d) == False:
		return 'N/A'
	else:
		c4=ZZ(alp22(a,b,d))
		c6=ZZ(bet22(a,b,d))
		md=ZZ(gam22(a,b,d))
		if md ==0:
			return 'N/A'
		else:
			if vp(a,2) < 4 or mod(b*d,4) != 1:
				u=1
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(a,2) >3 and mod(b*d,4) == 1:
				u=2
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig24(a,b):
	if gcd(a,b) !=1:
		return 'N/A'
	else:
		c4=ZZ(alp24(a,b))
		c6=ZZ(bet24(a,b))
		md=ZZ(gam24(a,b))
		if md ==0:
			return 'N/A'
		else:
			if vp(a,2) < 2:
				u=1
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(a,2) >1 and vp(a+4*b,2) < 4:
				u=2
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(a,2) == 2 and vp(a+4*b,2) > 3:
				u=4
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig26(a,b):
	if gcd(a,b) !=1:
		return 'N/A'
	else:
		c4=ZZ(alp26(a,b))
		c6=ZZ(bet26(a,b))
		md=ZZ(gam26(a,b))
		if md ==0:
			return 'N/A'
		else:
			if is_odd(a+b):
				u=1
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if ZZ(mod(a+b,4)) == 0:
				u=4
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if ZZ(mod(a+b,4)) == 2:
				u=16
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

def sig28(a,b):
	if gcd(a,b) !=1:
		return 'N/A'
	else:
		c4=ZZ(alp28(a,b))
		c6=ZZ(bet28(a,b))
		md=ZZ(gam28(a,b))
		if md ==0:
			return 'N/A'
		else:
			if vp(a,2) == 0:
				u=1
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(a,2) == 1:
				u=16
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)
			if vp(a,2) > 1:
				u=64
				return (u^(-4)*c4,u^(-6)*c6,u^(-12)*md)

# Let gam denote the discriminant of E2. The definition below contructs the set {(a,b,d)| a in (-n..n), b in (1..n), d in (1..n) such that gcd(a,b) and d is squarefree, b!=0, and gam(a,b,d) != 0}.
# In particular, the code provides a set of parameters for which E2 is non-singular and the parameters satisfy the conclusion of Proposition 2.2.
def set2(gam,n):
	T=[]
	for a in (-n..n):
		for b in (1..n):
			for d in (1..n):
				if is_squarefree(gcd(a,b)) and d != 1 and b != 0 and is_squarefree(d) and gam(a,b,d) != 0:
					T.append((a,b,d))
	return sorted(Set(T))

# Let gam denote the discriminant of E22. The definition below contructs the set {(a,b,d)| a in (-2n..2n), b in (-n..n), d in (1..n) such that gcd(a,b)=1, d is squarefree, a is even, and gam(a,b,d) != 0}.
# In particular, the code provides a set of parameters for which E22 is non-singular and the parameters satisfy the conclusion of Proposition 2.2.
def set22(gam,n):
	T=[]
	for a in (-2*n..2*n):
		for b in (-n..n):
			for d in (1..n):
				if gcd(a,b) == 1 and is_squarefree(d) and gam(a,b,d) != 0 and is_even(a):
					T.append((a,b,d))
	return sorted(Set(T))

# Let gam denote the discriminant of E4. The definition below contructs the set {(a,b)| a in (1..n), b in (-n..n) such that gcd(a,b)=1 and gam(a,b) != 0} union {(2^8*a,b)| a in (1..n), b in (-n..n) such that gcd(2^8*a,b)=1 and gam(2^8*a,b) != 0}.
# In particular, the code provides a set of parameters for which E4 is non-singular and the parameters satisfy the conclusion of Proposition 2.2. We note that the union is necessary to obtain representatives that satisfy the assumptions for attaining u=2c where a=c^3*d^2*e with gcd(d,e)=1 and d,e squarefree.
def set4(gam,n):
	T=[]
	for a in (1..n):
		for b in (-n..n):
			aa=2^8*a
			if gcd(a,b)==1 and gam(a,b) != 0:
				T.append((a,b))
			if gcd(aa,b)==1 and gam(aa,b) != 0:
				T.append((aa,b))
	return sorted(Set(T))

#Let gam denote the discriminant of ET for T != C2,C22,,C3^0,C4. The definition below contructs the set {(a,b)| a in (1..n), b in (-n..n) such that gcd(a,b)=1 and gam(a,b) != 0}.
# In particular, the code provides a set of parameters for which ET is non-singular and the parameters satisfy the conclusion of Proposition 2.2.
def set1(gam,n):
	T=[]
	for a in (1..n):
		for b in (-n..n):
			if gcd(a,b)==1 and gam(a,b) != 0:
				T.append((a,b))
	return sorted(Set(T))
