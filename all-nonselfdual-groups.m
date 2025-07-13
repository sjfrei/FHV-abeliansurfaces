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
Gout_notequiv_isom := [* *];  // those where the subgroup is not even isomorphic
Gout_notequiv_conj := [* *];  // those without an equivalence of subgroups to the twisted contragredient
Gout_notequiv_realz := [* *];  // the group is conjugate to the dual but the reps are not equivalent
Gout_notequiv_all := [* *];
for i := 1 to #Gsubs do
  print i;
  Hrec := Gsubs[i];
  H := Hrec`subgroup;
  Hdual := sub<GL4ell | [Transpose(h^(-1))*sim(h) : h in H]>;
  if not IsIsomorphic(H,Hdual) then
    print "!! not even an isomorphic group", Hrec;
    Append(~Gout_notequiv_isom, Hrec);
    Append(~Gout_notequiv_all, Hrec);
    continue;
  end if;
  bl, nu := IsConjugate(GL4ell,H,Hdual);
  if not bl then
    print "!!! not conjugate in GL_4(FF_ell)", Hrec;
    Append(~Gout_notequiv_conj, Hrec);
    Append(~Gout_notequiv_all, Hrec);
    continue;
  end if;

  // OK, now H^nu = Hdual, so we'd have to get the dual from something in the normalizer.
  N := Normalizer(GL4ell,Hdual);
  for h in H do
    hdual := Transpose(h^(-1))*sim(h);
    N := [n : n in N | h^(nu*n) eq hdual];
    if N eq [] then
      print "!!!! not conjugate for realz", Hrec;
      Append(~Gout_notequiv_realz, Hrec);
      Append(~Gout_notequiv_all, Hrec);
      break;
    end if;
  end for;
  // assert &and[&and[h^(nu*n) eq Transpose(h^(-1))*sim(h) : h in H] : n in N];
end for;
