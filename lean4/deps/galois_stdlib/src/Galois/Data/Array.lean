namespace Array

section
universe u
variables {α : Type u} [HasLess α] [DecidableRel (HasLess.Less : α → α → Prop)]

partial def ltAux (xs ys : Array α) : Nat → Bool
| n =>
  if hxs : n < xs.size then
    if hys : n < ys.size then
      let xn := xs.get ⟨n, hxs⟩;
      let yn := ys.get ⟨n, hys⟩;
      if  xn < yn then true
      else if yn < xn then false
      else ltAux (n+1)
    else false
  else if xs.size < ys.size then
    true
  else
    false

partial def lt (xs ys : Array α) : Bool := ltAux xs ys 0

end

end Array
