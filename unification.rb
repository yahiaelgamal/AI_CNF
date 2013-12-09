def hash_find obj, key
  if obj.respond_to?(:key?) && obj.key?(key)
    obj[key]
  elsif obj.respond_to?(:each)
    r = nil
    obj.find{ |*a| r=nested_hash_value(a.last,key) }
    r
  end
end

class Unifier


  # u treated as hash "might be changed to array"
  # t/x is translated to {x: 't'}
  def unify e1, e2
    unify1 e1, e2, {}
  end

  def unify1 e1, e2, u
    if u == false
      return false
    end

    if e1 == e2
      return u
    end

    #TODO
    if var? e1
      return unify_var e1, e2, u
    end

    if var? e2
      return unify_var e2, e1, u
    end

    if atom?(e1) || atom?(e2)
      return false
    end

    if length(e1) != length(e2)
      return false
    end

    return unify1 rest(e1), rest(e2), unify1( first(e1), first(e2), u)
  end

  def unify_var x, e, u
    f = hash_find u, x
    if f && u[f.to_sym] != f.to_sym
      return unify1 u[:x], e, u
    end
    
    t = subst(u, e)     #TODO

    if hash_find t, x
      return false
    end

    hs = {}
    hs[x.to_sym] = t
    return u.merge hs
  end
end
