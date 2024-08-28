ell := 2;
GL4ell := GL(4,GF(ell));
// J := Matrix(GF(ell),[[0,0,1,0],[0,0,0,0],[-1,0,0,0],[0,0,0,0]]);
J := Matrix(GF(ell),[[0,1,0,0],[-1,0,0,0],[0,0,0,0],[0,0,0,0]]);
V := KMatrixSpace(GF(ell),2,2);
gs := [V | g : g in Generators(GSp(2,ell))] cat [V!Id(GSp(2,ell))];
hs := [V | h : h in Generators(GL(2,ell))] cat [V!Id(GL(2,ell))];
z := V![[0,0],[0,0]];
ms := [V | m : m in Basis(V)] cat [z];
Ggen := [GL4ell | BlockMatrix([[g,z],[m,h]]) : g in gs, h in hs, m in ms];
G := sub<GL4ell | Ggen>;
assert #G eq #GSp(2,ell)*#GL(2,ell)*#V;
 
sim := function(g);
  gjg := Transpose(g)*J*g;
  c := gjg[1,2];
  assert gjg eq c*J;
  return GL4ell!DiagonalMatrix([c : i in [1..Rank(g)]]);
end function;

_ := [sim(g) : g in G];

Gsubs := Subgroups(G);
Gout_notequiv_sub := [* *];  // those where the subgroup is not even isomorphic
Gout_notequiv := [* *];  // those without an equivalence to the twisted contragredient
Gout_notequiv_all := [* *];
for i := 1 to #Gsubs do
  Hrec := Gsubs[i];
  print i;
  H := Hrec`subgroup;
  Hdual := sub<GL4ell | [Transpose(h^(-1))*sim(h) : h in H]>;
  if not IsIsomorphic(H,Hdual) then
    print "!!!! not even an isomorphic group", Hrec;
    Append(~Gout_notequiv_sub, Hrec);
    Append(~Gout_notequiv_all, Hrec);
    continue;
  end if;
  if not IsConjugate(GL4ell,H,Hdual) then
    print "!!!!", Hrec;
    Append(~Gout_notequiv, Hrec);
    Append(~Gout_notequiv_all, Hrec);
  end if;
/* JV: this seems totally wrong to me, and I wrote it! 
  N := Normalizer(GL4ell,Hdual);
  for h in H do
    hdual := Transpose(h^(-1))*sim(h);
    N := [n : n in N | h^(nu*n) eq hdual];
    if N eq [] then
      print "!!!!", Hrec;
      Append(~Gout_notequiv, Hrec);
      Append(~Gout_notequiv_all, Hrec);
      break;
    end if;
  end for;
*/
  // assert &and[&and[h^(nu*n) eq Transpose(h^(-1))*sim(h) : h in H] : n in N];
end for;
