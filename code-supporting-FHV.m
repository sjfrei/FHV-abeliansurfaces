

//////////////////////////////////////////////////////////////////////
// Set-up
//////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////
// E is an element in G_{ell} as in Equation 2.3.12, and //
// M is M_{q,ell}, as in Equation 2.3.14.  We compute    //
// the conjugation in (2.3.15).  We use p instead of     //
// l to avoid confusing l with 1.                        //
///////////////////////////////////////////////////////////

F<b1,b2,d,w1,w2,x1,x2,y1,y2,z1,z2,p>:=FunctionField(Rationals(),12);
E:=Matrix([[1+x1*p, b1+y1*p,0,0],[w1*p, d+z1*p, 0,0],[0,0,1+x2*p, b2+y2*p],[0,0,w2*p, d+z2*p]]);
E;
M:=Matrix([[1,0,1/p,0],[0,1,0,0],[0,0,1/p,0],[0,0,0,1]]);
M;
R:=M^-1*E*M;
R;
Rmodp := Matrix([[1,b1,x1-x2,-b2],[0,d,w1,0],[0,0,1,0],[0,0,w2,d]]);
Rmodp;
S:=d*Transpose(Rmodp^-1);
S;

//////////////////////////////////////////////////////////////////////
// Proof supporting Theorem 1.2.1 (proof given in section 2.5)
//////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// We check for p=2 that the subgroups from Proposition  //
// 2.4.2 are not conjugate.  We do this by iterating     //
// iterating over GL_4(F_2), looking for a single matrix //
// that conjugates all matrices.  The code returns the   //
// empty set.                                            //
///////////////////////////////////////////////////////////

p:=2;
Ps := GeneralLinearGroup(4,GF(p));

for b1, b2, c1, c2, d, x1, x2 in GF(p) do
  M := Matrix([[1,b1,x1-x2,-b2],[0,d,c1,0],[0,0,1,0],[0,0,c2,d]]);
  if Determinant(M) eq 0 then continue; end if;
  N:=d*Transpose(M^-1);
  Ps0 := [];
  for P in Ps do
    if P*N*P^-1 eq M then
      Append(~Ps0, P);
    end if;
  end for;
  Ps := Ps0;
end for;
Ps;


//////////////////////////////////////////////////////////////////////
// Proof of Proposition 3.1.1
//////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// We check that the permutation representations for A[p]//
// and Adual[p] are not isomorphic by computing their    //
// permutation character.                                //
///////////////////////////////////////////////////////////


// Switch between p=3,5,7 to check all cases. 

p := 3;
k := GF(p);
V := [v : v in VectorSpace(k,4)];
G := [];
for b1, b2, c1, c2, d, x1, x2 in k do
  M := Matrix([[1,b1,x1-x2,-b2],[0,d,c1,0],[0,0,1,0],[0,0,c2,d]]);
  if Determinant(M) ne 0 then
    Append(~G,M);
  end if;
end for;
Gv := [M[1,1]*M[2,2]*Transpose(M^-1) : M in G];
rtpermrep := function(g);
  // takes a matrix g in GL_4(k) and returns the permutation action on k^4
  perm := [];
  for i := 1 to #V do
    Append(~perm, Index(V, V[i]*g));
  end for;
  sigma := Sym(#V)!perm;
  return sigma;
end function;
e := rtpermrep(G[1]);
Sn := Parent(e);
Ggp := sub<GL(4,k) | G>;
piG := hom<Ggp -> Sn | [rtpermrep(Ggp.i) : i in [1..#Generators(Ggp)]]>;
PermutationCharacter(Image(piG));
Gvgp := sub<GL(4,k) | Gv>;
piGv := hom<Gvgp -> Sn | [rtpermrep(Gvgp.i) : i in [1..#Generators(Gvgp)]]>;
PermutationCharacter(Image(piGv));
PermutationCharacter(Image(piG)) eq PermutationCharacter(Image(piGv));


///////////////////////////////////////////////////////////
// We check that the induced linear representations  for //
// the permutation representations for A[p] and Adual[p] //
// are not isomorphic by computing the multiplicity of   //
// the trivial representation in the induced linear      //
// representations for A[p] and Adual[p]. We find that   //
// they have different multiplicities.                   //
///////////////////////////////////////////////////////////

// Switch between p=3,5,7 to check all cases. 
// We note that running the code for p=7 on a Dartmouth server 
// took more than 48 hours (but less than 60).

p := 3;
k := GF(p);
V := [v : v in VectorSpace(k,4)];

permrep := function(g);
  // takes a matrix g in GL_4(k) and returns the permutation action on k^4
  perm := [];
  for i := 1 to #V do
    Append(~perm, Index(V, V[i]*Transpose(g)));
  end for;
  sigma := Sym(#V)!perm;
  return PermutationMatrix(Rationals(),sigma), sigma;
end function;

G := [];
for b1, b2, c1, c2, d, x1, x2 in k do
  M := Matrix([[1,b1,x1-x2,-b2],[0,d,c1,0],[0,0,1,0],[0,0,c2,d]]);
  if Determinant(M) ne 0 then
    Append(~G,M);
  end if;
end for;

W := VectorSpace(Rationals(),#V);
for g in G do
  W := Kernel(permrep(g)-1) meet W;
end for;

Gv := [M[1,1]*M[2,2]*Transpose(M^-1) : M in G];

Wv := VectorSpace(Rationals(),#V);
for g in Gv do
  Wv := Kernel(permrep(g)-1) meet Wv;
end for;

Dimension(W);
Dimension(Wv);


//////////////////////////////////////////////////////////////////////
// Justification of Remark 3.1.2
//////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// We check that the permutation representations for A[p]//
// and Adual[p] are isomorphic for p=2,3 when we take    //
// our elliptic curves from the more general setup in    //
// section 2.6.  The permutation representations are     //
// conjugate subgroups in S_{p^4}.                       //
///////////////////////////////////////////////////////////

// Switch between p=2 and p=3 to check both cases.

p := 2;
// p:= 3;
k := GF(p);
V := [v : v in VectorSpace(k,4)];
G := [];
for a, b1, b2, c1, c2, d, x1, x2 in k do
  M := Matrix([[a,b1,x1-x2,-b2],[0,d,c1,0],[0,0,a,0],[0,0,c2,d]]);
  if Determinant(M) ne 0 then
    Append(~G,M);
  end if;
end for;
Gv := [M[1,1]*M[2,2]*Transpose(M^-1) : M in G];
rtpermrep := function(g);
  // takes a matrix g in GL_4(k) and returns the permutation action on k^4
  perm := [];
  for i := 1 to #V do
    Append(~perm, Index(V, V[i]*g));
  end for;
  sigma := Sym(#V)!perm;
  return sigma;
end function;
e := rtpermrep(G[1]);
Sn := Parent(e);
Ggp := sub<GL(4,k) | G>;
piG := hom<Ggp -> Sn | [rtpermrep(Ggp.i) : i in [1..#Generators(Ggp)]]>;
Gvgp := sub<GL(4,k) | Gv>;
piGv := hom<Gvgp -> Sn | [rtpermrep(Gvgp.i) : i in [1..#Generators(Gvgp)]]>;

IsConjugate(Sn, Image(piG), Image(piGv));
