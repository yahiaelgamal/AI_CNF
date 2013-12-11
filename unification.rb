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

  def shift
    @terms.shift
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

class Predicate < Term
  include Comparable

  attr_accessor :name, :terms

  def initialize name, terms
    @name, @terms = name, terms
  end

  def <=>(another_pred)
    if @name == another_pred.name && @terms == another_pred.terms
      0
    else
      1
    end
  end

  def length
    @terms.length
  end

  def to_s
    "#{@name.to_s}(#{@terms.join ', '})"
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

class Unifier


  def unify e1, e2
    t = unify1 e1, e2, []
    puts "RESULT"
    #puts t.join "|"
    anchor t
  end

  def listify e

  end

  def anchor t
    t
  end

  def unify1 e1, e2, u
    puts '-'*40
    p e1
    p e2
    p u

    if u == false
      return false
    end
    puts 1
    if e1 == e2
      return u
    end
    puts 2
    if e1.is_a?(Variable)
      return unify_var e1, e2, u
    end
    puts 3
    if e2.is_a?(Variable)
      return unify_var e2, e1, u
    end
    puts 4
    if e1.is_a?(Constant) || e2.is_a?(Constant)
      return false
    end
    puts 5
    if e1.length != e2.length
      return false
    end
    # puts 6
    # puts e1.is_a? Predicate
    # puts e1
    # puts e2.class.name
    if e1.is_a? Array
      #puts "ARRRAYY111"
      ee1 = e1[1, e1.length]
      t1 = e1.first
    elsif e1.is_a? Predicate
      #puts "preddd11"
      ee1 = e1.terms
      t1 = e1.name
    end
    if e2.is_a? Array
      #puts "ARRRAYY222"
      ee2 = e2[1, e2.length]
      t2 = e2.first
    elsif e2.is_a? Predicate
      #puts "Preddd22"
      ee2 = e2.terms
      t2 = e2.name
    end
    puts '-'*40

    return ( unify1( ee1, ee2, unify1( t1, t2, u)))
  end

  def unify_var x, e, u
    s = find_subst u, x
    if s && s != x
      return unify1 s, e, u
    end

    t = subst(u, e)     #TODO

    if t.terms && t.terms.index(x)
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
      if e.terms
        indx = e.terms.index(sub[0])
        if indx
          e.terms[indx] = sub[1]
        end
      end
    end
    e
  end
end


#example 1
puts "="*50
puts "Example 1"
x = Variable.new 'x'
a = Constant.new 'a'
u = Variable.new 'u'
v = Variable.new 'v'
f1 = Predicate.new 'f', [a]
f2 = Predicate.new 'f', [u]
g1 = Predicate.new 'g', [x]
g2 = Predicate.new 'g', [f1]
p1 = Predicate.new 'P', [x, g1, g2]
p2 = Predicate.new 'P', [f2, v, v]
unifier = Unifier.new
p p1
p p2
p unifier.unify p1, p2


#example 2
puts "="*50
puts "Example 2"
a = Constant.new 'a'
y = Variable.new 'y'
z = Variable.new 'z'
u = Variable.new 'u'
f = Predicate.new 'f', [y]
p1 = Predicate.new 'P', [a, y, f]
p2 = Predicate.new 'P', [z, z, u]
unifier = Unifier.new
p p1
p p2
p unifier.unify p1, p2

#example 3
puts "="*50
puts "Example 3"
x = Variable.new 'x'
z = Variable.new 'z'
u = Variable.new 'u'
g1 = Predicate.new 'g', [x]
g2 = Predicate.new 'g', [z]
g3 = Predicate.new 'g', [g2]
g4 = Predicate.new 'g', [u]
f1 = Predicate.new 'f', [x, g1, x]
f2 = Predicate.new 'f', [g4, g3, z]
unifier = Unifier.new
p p1
p p2
p unifier.unify f1, f2