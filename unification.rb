#class Operator
  ## sym belongs to [^ v => <=>]
  #def initialize(sym)
    #self.sym = sym
  #end

  #def to_s
    #return self.sym
  #end
#end

class Quantifier
  # kind is either an A or an E
  attr_accessor :kind
  def initialize(kind)
    self.kind = kind
  end

  def to_s
    case self.kind
    when 'A'
      return "\u2200"
    when 'E'
      return "\u2203"
    end
  end
end

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

class Sentence < Expression

  attr_accessor :type, :vars
  # type is either ["atomic", "equiv", "neg", "op", "quant"]
  # hash includes keys such as
  #     predicate (in case of atomic),
  #     term1, term2 (in case of equiv)
  #     sentence (in case of neg)
  #     sentence1, sentence2, op (in case of "op")
  #     quant, variable, sentence (in case of quan)
  #
  def initialize(type, vars={})
    @type = type
    @vars= vars
    unless vars.is_a?(Hash)
      throw "Vars must be a Hash, it is a #{vars.class.name}"
    end

    case(type)
    when "atomic"
      unless vars.include?(:predicate)
        throw "Vars must include :predicate, it has #{@vars.keys}"
      end
    when "equiv"
      unless vars.include?(:term1) && vars.include?(:term2)
        throw "Vars must include :term1, :term2, it has #{@vars.keys}"
      end
    when "neg"
      unless vars.include?(:sentence)
        throw "Vars must include :sentence, it has #{@vars.keys}"
      end
    when "op"
      unless vars.include?(:op) && vars.include?(:sentence1) && vars.include?(:sentence2)
        throw "Vars must include :sentence1, :sentence2, :op , it has #{@vars.keys}"
      end
    when "quant"
      unless vars.include?(:quant) && vars.include?(:variable) && vars.include?(:sentence)
        throw "Vars must include :quant, :variable, :sentence , it has #{@vars.keys}"
      end
      unless vars[:variable].is_a? Variable
        throw "vars[:variable] is of class variable, it is a #{vars[:variable].class.name}"
      end
    end
  end

  def to_s
    case(@type)
    when "atomic"
      return @vars[:predicate].to_s
    when "equiv"
      return "#{@vars[:term1].to_s} = #{@vars[:term2].to_s}"
    when "neg"
      return "\u00AC(#{@vars[:sentence].to_s})"
    when "op"
      return "(#{@vars[:sentence1].to_s}) #{@vars[:op].to_s} (#{@vars[:sentence2].to_s})"
    when "quant"
      return "#{@vars[:quant].to_s}#{@vars[:variable].to_s}[#{@vars[:sentence].to_s}]"
    end
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




module CNF_Converter
  def self.eliminate_equiv(sentence)
    vars = sentence.vars
    case sentence.type
    when 'atomic'
      return sentence
    when 'equiv'
      return sentence
    when 'neg'
      vars[:sentence] = eliminate_equiv(vars[:sentence])
      return sentence
    when 'op'
      if vars[:op] != '<=>'
        return sentence
      end

      old_phi = vars[:sentence1]
      old_shi = vars[:sentence2]

      phi = eliminate_equiv(old_phi)
      shi = eliminate_equiv(old_shi)

      sentence1 = Sentence.new('op', {op: '=>', sentence1: phi, sentence2: shi})
      sentence2 = Sentence.new('op', {op: '=>', sentence1: shi, sentence2: phi})

      new_hash = {
        op: '^',
        sentence1: sentence1,
        sentence2: sentence2
      }
      return Sentence.new("op", new_hash)
    when 'quant'
      vars[:sentence] = eliminate_equiv(vars[:sentence])
      return sentence
    else
      return sentence
    end
  end

  def self.test_print
    y = Variable.new('y')
    f_y = Predicate.new('f', [y])
    sentence = Sentence.new('neg', {sentence: Sentence.new('atomic', {predicate: f_y})})
    puts sentence

    g_y = Predicate.new('g', [y])
    sentence2 = Sentence.new('op', {op: '<=>', sentence1: Sentence.new('atomic', {predicate: f_y}), sentence2: Sentence.new('atomic', {predicate: g_y})})
    puts sentence2
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
    zzc
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


def test_unification
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
end
#test_unification()
