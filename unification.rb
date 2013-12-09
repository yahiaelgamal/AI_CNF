class Expression
  include Comparable

  attr_accessor :terms

  def initialize terms=[]
    @terms = terms
  end

  def <=>(another_exp)
    if @terms == another_exp.terms
      0
    else
      1
    end
  end

  def length
    @terms.length
  end

  def to_s
    @terms.join " "
  end
end

class Term < Expression

end

class Predicate < Expression
  include Comparable

  attr_accessor :name, :params

  def initialize name, params
    @name, @params = name, params
  end

  def <=>(another_pred)
    if @name == another_pred.name && @params == another_pred.params
      0
    else
      1
    end
  end

  def length
    @params.length
  end

  def to_s
    "#{@name.to_s}(#{@params.join ', '})"
  end
end

class Constant < Term
  include Comparable

  attr_accessor :name

  def initialize name
    @name = name
  end

  def <=>(another_const)
    if @name == another_const.name
      0
    else
      1
    end
  end

  def length
    1
  end

  def to_s
    @name.to_s
  end
end

class Variable < Term
  include Comparable

  attr_accessor :name
  
  def initialize name
    @name = name
  end

  def <=>(another_var)
    if @name == another_var.name
      0
    else
      1
    end
  end

  def length
    1
  end

  def to_s
    @name.to_s
  end
end

class Function < Term
  include Comparable

  attr_accessor :name, :params

  def initialize name, params
    @name, @params = name, params
  end

  def <=>(another_func)
    if @name == another_func.name && @params == another_func.params
      0
    else
      1
    end
  end

  def length
    @params.length
  end

  def to_s
    "#{@name.to_s}(#{@params.join ', '})"
  end
end

class Unifier


  # u treated as hash "might be changed to array"
  # t/x is translated to {x: 't'}
  def unify e1, e2
    t = unify1 e1, e2, []
    anchor(t)
  end

  def anchor t
    t
  end

  def unify1 e1, e2, u
    if u == false
      return false
    end

    if e1 == e2
      return u
    end

    #TODO
    if e1.is_a? Variable
      return unify_var e1, e2, u
    end

    if e2.is_a? Variable
      return unify_var e2, e1, u
    end

    if e1.is_a?(Predicate) || e2.is_a?(Predicate)
      return false
    end

    if e1.length != e2.length
      return false
    end

    t1, t2 = e1.terms.shift, e2.terms.shift

    return ( unify1( e1, e2, unify1( t1, t2, u)))
  end

  def unify_var x, e, u
    s = find_subst u, x
    if s && s != x
      return unify1 s, e, u
    end

    t = subst(u, e)     #TODO

    if t.terms.index(x)
      return false
    end

    return u << [x, t]
  end

  # finds a substitution for x in u
  def find_subst u, x
    u.each do |sub|
      if sub[0] == x
        return sub[1]
      end
    end
    nil
  end

  # applies substitutions of u on e
  def subst u, e
    u.each do |sub|
      indx = e.terms.index(sub[0])
      if indx
        e.terms[indx] = sub[1]
      end
    end
    e
  end
end

x = Variable.new 'x'
a = Variable.new 'a'
u = Variable.new 'u'
v = Variable.new 'v'
f1 = Function.new 'f', [a]
f2 = Function.new 'f', [u]
g1 = Function.new 'g', [x]
g2 = Function.new 'g', [f1]
p1 = Predicate.new 'P', [x, g1, g2]
p2 = Predicate.new 'P', [f2, v, v]
unifier = Unifier.new
puts unifier.unify p1, p2