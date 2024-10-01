
//Computing a Groebner basis from Stroh's syzygies
weights := [15,10,6,4,2,12,10,8,7,5,9,7,3,5,6,6,4,4,5,3,2,4,3,3,2,1];
RingCov<R,D,C,B,A,lambda,mu,nu,n,m,rho,pi,l,u,w,v,Delta,s,t,p,i,r,q,T,H,f>
:= PolynomialRing(Rationals(), weights);

S := [RingCov ! 0: i in [1..20]];
S[1] := 1/3*f^3*p + 1/2*f^2*H*i - 1/18*f^4*A - H^3 - 2*T^2;
S[2] := 1/6*f^3*l - 1/3*f^2*i^2 - f*H*p + H^2*i + 2*T*q;
S[3] := f*r - H*q + i*T;
S[4] := f^2*s - 1/2*f*i*q + 3*H*r + 3*T*p;
S[5] := f^2*Delta - 2*f*i*p + H*i^2 + 2*q^2;
S[6] := f^2*B - 2*f*i*l + 6*H*Delta + i^3 - 6*p^2;
S[7] := f*t + 2*H*s+ T*l;
S[8] := f*u + 2*i*s + q*l;
S[9] := f*m - 2*l*p - i*Delta + B*H - 1/3*A*i^2;
S[10] := f*w + 2*p*s - l*r;
S[11] := f*v + 1/2*i*t + 1/6*A*q*i + q*Delta;
S[12] := f*C - 2*l*Delta - 1/2*i*m + B*p;
S[13] := f*pi + 2*i*v + 2*i*w + q*m;
S[14] := f*n + H*C - 2*Delta^2 - 3/4*i*l^2 - 1/2*i*A*Delta;
S[15] := f*nu + 2*l*v + 2*l*w - 2*m*s;
S[16] := f*rho - 1/3*A*i*v + 4/3*B*i*s + 5/6*i*u*l + n*q;
S[17] := f*mu + 2*n*s + 1/3*A*l*v - 4/3*B*l*s - 5/6*u*l^2;
S[18] := Delta*m - C*p - 1/2*i*n + 1/2*B*i*l - 1/6*f*B^2;
S[19] := f*lambda - 1/3*A*m*v + 4/3*B*m*s + 5/6*u*m*l - 2*n*v - 2*n*w;
S[20] := f*R - 1/3*i*(A*lambda + B*mu - C*nu) - 1/3*Delta*(6*lambda+A*mu+B*nu) - 1/2*l^2*mu - m*l*nu;
&and[IsHomogeneous(S[i]): i in [1..20]];

//This takes too long.
//SetNthreads(4);
//SetVerbose("Groebner", true);
//GB := GroebnerBasis(S);
//GB, _, denom := GroebnerBasis(S : ReturnDenominators := true, GlobalModular := true);

//Get relations from GetBasisAndRelationsCov at different weights

// Stroh's variables are (up to scaling, with old and new ordering):
// 0     3    2    1    7     6    5    4    11    10   9     8    14   13
// 0     1    5    21   2     3    6    13   4     8    9     22   7    12
// f     H    i    A    T     q    p    l    r     s    Delta B    t    u
// Co16  Co28 Co24 Co20 Co312 Co38 Co36 Co32 Co410 Co46 Co44  Co40 Co58 Co54
// 12   16    17    15   19   18   20   21   23    22    24     25
// 16   10    11    23   14   17   18   15   19    24    20     25
// m    v     w     C    pi   n    nu   rho  mu    D     lambda R
// Co52 Co661 Co662 Co60 Co74 Co72 Co82 Co94 Co102 Co100 Co122  Co150
Co16 := f;
Co28 := H;
Co24 := i;
Co20 := A;
Co312 := T;
Co38 := q;
Co36 := p;
Co32 := l;
Co410 := r;
Co46 := s;
Co44 := Delta;
Co40 := B;
Co58 := t;
Co54 := u;
Co52 := m;
Co661 := v;
Co662 := w;
Co60 := C;
Co74 := pi;
Co72 := n;
Co82 := nu;
Co94 := rho;
Co102 := mu;
Co100 := D;
Co122 := lambda;
Co150 := R;

bigstr := Split(Read("Groebner.dat"), "\n");
GB := [eval poly: poly in bigstr];
&and[IsHomogeneous(x): x in GB];

if false then
    for i in [1..#GB] do
        for j in [(i+1)..#GB] do
            red := NormalForm(SPolynomial(GB[i], GB[j]), GB);
            printf "%o, %o, %o\n", i, j, red eq 0;
            assert red eq 0;
        end for;
    end for;
end if;
//IsGroebner(GB);
//GB := ReduceGroebnerBasis(GB);


SetVerbose("Groebner", true);
newGB, _, denom := GroebnerBasis(GB : ReturnDenominators := true, GlobalModular := false);
Sort([x/LeadingCoefficient(x): x in GB]) eq Sort([x/LeadingCoefficient(x): x in newGB]);
