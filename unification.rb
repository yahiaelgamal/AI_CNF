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
      unless vars[:sentence1].is_a?(Sentence) && vars[:sentence2].is_a?(Sentence)
        throw "vars[:sentence1] and vars[:sentence2] are not both Sentence they are\
        #{vars[:sentence1].class.name} and #{vars[:sentence2].class.name}"
      end
    when "quant"
      unless vars.include?(:quant) && vars.include?(:variable) && vars.include?(:sentence)
        throw "Vars must include :quant, :variable, :sentence , it has #{@vars.keys}"
      end
      unless vars[:variable].is_a? Variable
        throw "vars[:variable] is not of class variable, it is a #{vars[:variable].class.name}"
      end

      unless vars[:quant].is_a? Quantifier
        throw "vars[:quant] is not of class Quantifier, it is a #{vars[:variable].class.name}"
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

  def to_sentence
    Sentence.new('atomic', {predicate: self})
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
    if another_var.is_a?(Variable) && @name == another_var.name
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
  def self.eliminate_equiv(old_sentence)
    # incredibliy inefficient. but who cares, this is ruby after all
    sentence = Marshal.load( Marshal.dump(old_sentence) )
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
        vars[:sentence1] = eliminate_equiv(vars[:sentence1])
        vars[:sentence2] = eliminate_equiv(vars[:sentence2])
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

  def self.eliminate_impl(old_sentence)
    sentence = Marshal.load( Marshal.dump(old_sentence) )
    vars = sentence.vars
    case sentence.type
    when 'atomic'
      return sentence
    when 'equiv'
      return sentence
    when 'neg'
      vars[:sentence] = eliminate_impl(vars[:sentence])
      return sentence
    when 'op'
      if vars[:op] != '=>'
        vars[:sentence1] = eliminate_impl(vars[:sentence1])
        vars[:sentence2] = eliminate_impl(vars[:sentence2])
        return sentence
      end

      old_phi = vars[:sentence1]
      old_shi = vars[:sentence2]

      phi = eliminate_impl(old_phi)
      not_phi = Sentence.new('neg', {sentence: phi})
      shi = eliminate_impl(old_shi)

      sentence1 = Sentence.new('op', {op: 'v', sentence1: not_phi, sentence2: shi})

      return sentence1
    when 'quant'
      vars[:sentence] = eliminate_impl(vars[:sentence])
      return sentence
    else
      return sentence
    end
  end

  def self.propagate_neg(old_sentence)
    sentence = Marshal.load( Marshal.dump(old_sentence) )
    vars = sentence.vars

    case sentence.type
    when 'atomic'
      sentence = S.new('neg', {sentence: sentence})
      return sentence
    when 'equiv'
      sentence = S.new('neg', {sentence: sentence})
      return sentence
    when 'neg'
      sentence = vars[:sentence]
      return sentence
    when 'op'
      case vars[:op]
      when '^'
        vars[:op] = 'v'
        vars[:sentence1] = S.new('neg', {sentence: vars[:sentence1]})
        vars[:sentence2] = S.new('neg', {sentence: vars[:sentence2]})
      when 'v'
        vars[:op] = '^'
        vars[:sentence1] = S.new('neg', {sentence: vars[:sentence1]})
        vars[:sentence2] = S.new('neg', {sentence: vars[:sentence2]})
      end
      return sentence
    when 'quant'
      case vars[:quant].kind
      when 'A'
        vars[:quant] = Quantifier.new('E')
        vars[:sentence] = S.new('neg', {sentence: vars[:sentence]})
      when 'E'
        vars[:quant] = Quantifier.new('A')
        vars[:sentence] = S.new('neg', {sentence: vars[:sentence]})
      end
      return sentence
    end
  end

  def self.push_neg_inwards(old_sentence)
    sentence = Marshal.load( Marshal.dump(old_sentence) )
    vars = sentence.vars
    case sentence.type
    when 'atomic'
      return sentence
    when 'equiv'
      return sentence
    when 'neg'
      if vars[:sentence].type != 'atomic' && vars[:sentence].type != 'equiv'
        sentence = propagate_neg(vars[:sentence])
        vars = sentence.vars
        sentence = push_neg_inwards(sentence)
      end
      return sentence
    when 'op'
      vars[:sentence1] = push_neg_inwards(vars[:sentence1])
      vars[:sentence2] = push_neg_inwards(vars[:sentence2])
      return sentence
    when 'quant'
      vars[:sentence] = push_neg_inwards(vars[:sentence])
      return sentence
    else
      return sentence
    end
  end

  def self.standardize_apart(old_sentence, used_variables)

    sentence = Marshal.load( Marshal.dump(old_sentence) )
    vars = sentence.vars
    case sentence.type
    when 'atomic'
      return sentence
    when 'equiv'
      return sentence
    when 'neg'
      vars[:sentence] = standardize_apart(vars[:sentence], used_variables)
      return sentence
    when 'op'
      vars[:sentence1] = standardize_apart(vars[:sentence1], used_variables)
      vars[:sentence2] = standardize_apart(vars[:sentence2], used_variables)
      return sentence
    when 'quant'
      if used_variables.include? vars[:variable]
        new_name = make_a_new_name(used_variables)
        old_term = Variable.new(vars[:variable].name)
        vars[:variable].name = new_name
        replace_term!(vars[:sentence], old_term, Variable.new(new_name))
      else
        used_variables << vars[:variable]
      end
      vars[:sentence] = standardize_apart(vars[:sentence], used_variables)
    else
    end
    return sentence
  end

  def self.skolemize(old_sentence, global_vars, used_skolem_names)
    sentence = Marshal.load( Marshal.dump(old_sentence) )
    vars = sentence.vars
    case sentence.type
    when 'atomic'
      return sentence
    when 'equiv'
      return sentence
    when 'neg'
      vars[:sentence] = skolemize(vars[:sentence], global_vars.dup, used_skolem_names)
      return sentence
    when 'op'
      vars[:sentence1] = skolemize(vars[:sentence1], global_vars.dup, used_skolem_names)
      vars[:sentence2] = skolemize(vars[:sentence2], global_vars.dup, used_skolem_names)
      return sentence
    when 'quant'
      if vars[:quant].kind == 'A'
        global_vars << vars[:variable]
        vars[:sentence] = skolemize(vars[:sentence], global_vars.dup, used_skolem_names)
      else
        skolem_func_name = make_a_skolem_func_name(used_skolem_names)
        new_predicate = Predicate.new(skolem_func_name, global_vars)
        replace_term!(vars[:sentence], vars[:variable], new_predicate)
        sentence = skolemize(vars[:sentence], global_vars.dup, used_skolem_names)
      end
      return sentence
    else
      return sentence
    end
  end

  def self.replace_term!(sentence, old_term, new_term)
    vars = sentence.vars
    case sentence.type
    when 'atomic'
       predicate = vars[:predicate]
       predicate.terms.map! do |term|
        if term == old_term
          new_term
        else
          term
        end
      end
    when 'equiv'
      replace_term!(vars[:term1], old_term, new_term)
      replace_term!(vars[:term2], old_term, new_term)
    when 'neg'
      replace_term!(vars[:sentence], old_term, new_term)
    when 'op'
      replace_term!(vars[:sentence1], old_term, new_term)
      replace_term!(vars[:sentence2], old_term, new_term)
    when 'quant'
      replace_term!(vars[:sentence], old_term, new_term)
    else
    end
  end

  def self.discard_for_all(old_sentence)
    sentence = Marshal.load( Marshal.dump(old_sentence) )
    vars = sentence.vars
    case sentence.type
    when 'atomic'
      return sentence
    when 'equiv'
      return sentence
    when 'neg'
      vars[:sentence] = discard_for_all(vars[:sentence])
      return sentence
    when 'op'
      vars[:sentence1] = discard_for_all(vars[:sentence1])
      vars[:sentence2] = discard_for_all(vars[:sentence2])
      return sentence
    when 'quant'
      if vars[:quant].kind == 'A'
        vars[:sentence] = discard_for_all(vars[:sentence])
      else
        throw 'you are in the wrong step, you must skolemize first'
      end
      return vars[:sentence]
    end
  end

  def self.translate_to_CNF(old_sentence)
    sentence = Marshal.load( Marshal.dump(old_sentence) )
    vars = sentence.vars
    case sentence.type
    when 'atomic'
      return sentence
    when 'equiv'
      return sentence
    when 'neg'
      return sentence
    when 'op'

      if vars[:op] == 'v' && vars[:sentence2].vars[:op] == '^' && vars[:sentence1].vars[:op] != '^'

        phi = vars[:sentence1]
        shi = vars[:sentence2].vars[:sentence1]
        eita = vars[:sentence2].vars[:sentence2]

        left = S.new('op', {op: 'v', sentence1: phi, sentence2: shi})
        right = S.new('op', {op: 'v', sentence1: phi, sentence2: eita})

        vars[:op] = '^'
        vars[:sentence1] = left
        vars[:sentence2] = right
      elsif vars[:op] == '^' && vars[:sentence2].vars[:op] == 'v' && vars[:sentence1].vars[:op] != 'v'
        phi = vars[:sentence1]
        shi = vars[:sentence2].vars[:sentence1]
        eita = vars[:sentence2].vars[:sentence2]

        left = S.new('op', {op: '^', sentence1: phi, sentence2: shi})
        right = S.new('op', {op: '^', sentence1: phi, sentence2: eita})

        # TODO double check if this is desired
        vars[:op] = 'v'
        vars[:sentence1] = left
        vars[:sentence2] = right
      elsif vars[:op] == 'v' && vars[:sentence1].vars[:op] == '^' && vars[:sentence2].vars[:op] != '^'

        phi = vars[:sentence2]
        shi = vars[:sentence1].vars[:sentence2]
        eita = vars[:sentence1].vars[:sentence1]

        left = S.new('op', {op: 'v', sentence2: phi, sentence1: shi})
        right = S.new('op', {op: 'v', sentence2: phi, sentence1: eita})

        vars[:op] = '^'
        vars[:sentence2] = left
        vars[:sentence1] = right
      elsif vars[:op] == '^' && vars[:sentence1].vars[:op] == 'v' && vars[:sentence2].vars[:op] != 'v'
        phi = vars[:sentence2]
        shi = vars[:sentence1].vars[:sentence2]
        eita = vars[:sentence1].vars[:sentence1]

        left = S.new('op', {op: '^', sentence2: phi, sentence1: shi})
        right = S.new('op', {op: '^', sentence2: phi, sentence1: eita})

        # TODO double check if this is desired
        vars[:op] = 'v'
        vars[:sentence2] = left
        vars[:sentence1] = right
      else
      end

      vars[:sentence1] = translate_to_CNF(vars[:sentence1])
      vars[:sentence2] = translate_to_CNF(vars[:sentence2])
      return sentence
    else
      throw "there shouldn't be this type #{sentence.type}"
    end
  end

  # this is step kk
  def self.build_clauses(old_sentence)
    sentence = Marshal.load( Marshal.dump(old_sentence) )
    vars = sentence.vars

    case sentence.type
    when 'atomic'
      return sentence
    when 'equiv'
      return sentence
    when 'neg'
      return sentence
    when 'op'
      conjs = get_sentences_rec(sentence, [], '^')
      conjs.map! do |disj|
        disj = get_sentences_rec(disj, [], 'v')
      end
      conjs.uniq!
      return conjs
    else
      throw "You must trnslate to CNF first"
    end
  end

  def self.get_sentences_rec(sentence, sentences, op)
    vars = sentence.vars
    case sentence.type
    when 'atomic'
      return [sentence]
    when 'neg'
      return [sentence]
    when 'op'
      if (vars[:op] == op)
        sub_sents1 = get_sentences_rec(vars[:sentence1], [], op)
        sub_sents2 = get_sentences_rec(vars[:sentence2], [], op)
        return sentences + sub_sents1 + sub_sents2
      else
        return sentences + [sentence]
      end
    end
  end

  def self.print_clauses(conjs)
  end

  def self.make_a_new_name(used_variables)
    names = used_variables.map{|var| var.name}
    name = %w[m n o p q r s t u v w x y z].find {|name| !names.include?(name)}
    return name
  end

  def self.make_a_skolem_func_name(used_names)
    name = %w[sk sk1 sk2 sk3 sk4 sk5 sk6 sk7 sk8 sk9 sk10].find {|name| !used_names.include?(name)}
    return name
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

    # if t.terms && t.terms.index(x)
    #   return false
    # end

    if occurs_deeply(x, t)
      return false
    end

    return u << [x, t]
  end

  #checks if a variable x occurs deeply in term t
  def occurs_deeply x, t
    if t.is_a? Variable
      t == x ? true : false
    elsif t.is_a? Constant
      return false
    elsif t.is_a? Predicate
      return occurs_deeply(x, t.terms)
    elsif t.is_a? Array
      return (occurs_deeply x, t.first) || (occurs_deeply x, t[1, t.length])
    end
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
