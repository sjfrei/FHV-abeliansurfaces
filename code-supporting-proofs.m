

//////////////////////////////////////////////////////////////////////
// Set-up
//////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////
// E is as in Equation 3.2.8, and B is M_{q,p}, as in    //
// Equation 3.2.10. M is as in Equation 3.2.11. Mmodp is // 
// as in Proposition 3.2.12, and N is as in Proposition  //
// 3.3.2. We use p instead of l to avoid confusing l     //
// with 1.                                               //
///////////////////////////////////////////////////////////

F<a,b1,b2,c1,c2,d,x1,x2,y1,y2,z1,z2,p>:=FunctionField(Rationals(),13);
E:=Matrix([[a+x1*p, b1+y1*p,0,0],[c1*p, d+z1*p, 0,0],[0,0,a+x2*p, b2+y2*p],[0,0,c2*p, d+z2*p]]);
E;
B:=Matrix([[1,0,1/p,0],[0,1,0,0],[0,0,1/p,0],[0,0,0,1]]);
B;
M:=B^-1*E*B;
M;
Mmodp := Matrix([[a,b1,x1-x2,-b2],[0,d,c1,0],[0,0,a,0],[0,0,c2,d]]);
Mmodp;
N:=a*d*Transpose(Mmodp^-1);
N;

//////////////////////////////////////////////////////////////////////
// Proof supporting Theorem 4.1.1
//////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// We check for p=2 that the subgroups from Propositions //
// 3.2.12 and 3.3.2 are not conjugate. We do this by     //
// iterating over GL_4(F_2), looking for a matrix which  //
// conjugates all matrices in as in Proposition 3.2.12   //
// to those in 3.3.2. The code returns the empty set.    //
///////////////////////////////////////////////////////////

p:=2;
Ps := GeneralLinearGroup(4,GF(p));

for a, b1, b2, c1, c2, d, x1, x2 in GF(p) do
  M := Matrix([[a,b1,x1-x2,-b2],[0,d,c1,0],[0,0,a,0],[0,0,c2,d]]);
  if Determinant(M) eq 0 then continue; end if;
  N:=a*d*Transpose(M^-1);
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
// Proof of Proposition 4.2.1
//////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// We check that the permutation representations for A[p]//
// and Adual[p] are isomorphic for p=2,3 when we take    //
// curves as in Proposition 3.2.5. G is the subgroup as  //
// in Proposition 3.2.12, and Gv is the subgroup as in   //
// Proposition 3.3.2. The permutation representations    //
// are conjugate subgroups in S_{p^4}.                   //
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


//////////////////////////////////////////////////////////////////////
// Proof of Proposition 4.2.2
//////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// We check that the permutation representations for A[3]//
// and Adual[3] are not isomorphic by computing their    //
// permutation character. G is the subgroup as in        //
// Proposition 3.2.12, and Gv is the subgroup as in      //
// Proposition 3.3.2.                                    //
///////////////////////////////////////////////////////////

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
// the permutation representations for A[3] and Adual[3] //
// are not isomorphic by computing the multiplicity of   //
// the trivial representation in the induced linear      //
// representations for A[3] and Adual[3]. We find that   //
// they have different multiplicities. G is the subgroup //
// as in Proposition 3.2.12, Gv is the subgroup as in    //
// Proposition 3.3.2, and W and Wv are trivial           //
// subrepresentations corresponding to each.             //
///////////////////////////////////////////////////////////

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
