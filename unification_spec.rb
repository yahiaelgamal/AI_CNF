
require_relative './unification.rb'

def make_lec7_sen
    x = V.new('x')
    y = V.new('y')

    # sen4 Q(y) ∧ R(y, x)
    sen4 = S.new('op', {op: '^',
                 sentence1: S.new('atomic', {predicate: P.new('Q', [y])}),
                 sentence2: S.new('atomic', {predicate: P.new('R', [y,x])})
    })

    # sen3 ∃y[Q(y) ∧ R(y, x)]
    sen3 = S.new('quant', {quant: Q.new('E'),
                 variable: y,
                 sentence: sen4})

    # sen2 = (Q(x) ∧ ∃y[Q(y) ∧ R(y, x)])
    sen2 = S.new('op', {op: '^',
                 sentence1: S.new('atomic', {predicate: P.new('Q', [x]) }),
                 sentence2: sen3
    })

   # sen1 = P(x) <=> (Q(x) ∧ ∃y[Q(y) ∧ R(y, x)])
    sen1 = S.new('op', {
      op: '<=>',
      sentence1: S.new('atomic', {predicate: P.new('P', [x])}),
      sentence2: sen2

    })

    # ∀x[P(x) <=> (Q(x) ∧ ∃y[Q(y) ∧ R(y, x)])]
    # ∀x[(P(x)) <=> ((Q(x)) ^ (∃y[(Q(y)) ^ (R(y, x))]))]
    sentence = S.new('quant', {
      quant: Q.new('A'),
      variable: x,
      sentence: sen1
    })

    return sentence
end

def make_second_example
  x = V.new('x')
  p_x = P.new('P', [x]).to_sentence
  neg_p_x = S.new('neg', {sentence: p_x} )
  q_x = P.new('Q', [x]).to_sentence


  # Q(x) ⇒ ¬P(x)
  sen3 = S.new('op', {op: '=>', sentence1: q_x, sentence2: neg_p_x})

  # ∀x[Q(x) ⇒ ¬P(x)]
  sen2 = S.new('quant' , {quant: Q.new('A'), variable: x, sentence: sen3})

  # P(x) ∧ ∀x[Q(x) ⇒ ¬P(x)]
  sen1 = S.new('op', {op: '^', sentence1: p_x, sentence2: sen2})

  # ∃x[P(x) ∧ ∀x[Q(x) ⇒ ¬P(x)]]
  sentence = S.new('quant', {quant: Q.new('E'), variable: x, sentence: sen1})
  return sentence
end

describe "Project" do 
  before(:all) do
    S = Sentence
    Q = Quantifier
    P = Predicate
    V = Variable
    C = Constant
    U = Unifier
    @fa = "\u2200"
    @te = "\u2203"
    @neg = "\u00AC"
  end
  
  describe Unifier do

    describe 'nested variable assigment' do
      it 'should fail cuz deeply nested' do
        x = V.new 'x'
        z = V.new 'z'
        u = V.new 'u'
        unif = U.new
        g1 = P.new 'g', [x]
        g2 = P.new 'g', [z]
        g3 = P.new 'g', [g2]
        g4 = P.new 'g', [u]
        f1 = P.new 'f', [x, g1, x]
        f2 = P.new 'f', [g4, g3, z]
        unif.unify(f1, f2).should == false

        f = P.new 'f', [x]
        g = P.new 'g', [f]
        p1 = P.new 'P', [g]
        p2 = P.new 'P', [x]
        unif.unify(p1, p2).should == false
      end
    end

    describe 'successful unification' do
      it 'should succeed and assign nested variables' do
        a = C.new 'a'
        y = V.new 'y'
        z = V.new 'z'
        u = V.new 'u'
        f = P.new 'f', [y]
        p1 = P.new 'P', [a, y, f]
        p2 = P.new 'P', [z, z, u]
        unif = U.new
        unif.unify(p1, p2).to_s.should == '[[z, a], [y, a], [u, f(a)]]'
      end

      it 'should unify successfully' do
        a = C.new 'a'
        u = V.new 'u'
        x = V.new 'x'
        v = V.new 'v'
        unif = U.new
        f1 = P.new 'f', [a]
        f2 = P.new 'f', [u]
        g1 = P.new 'g', [x]
        g2 = P.new 'g', [f1]
        p1 = P.new 'P', [x, g1, g2]
        p2 = P.new 'P', [f2, v, v]
        unif.unify(p1, p2).to_s.should == '[[x, f(a)], [v, g(f(a))], [u, a]]'
      end
    end

    describe 'anchor' do
      it 'should work simple' do
        a = V.new 'a'
        u = V.new 'u'
        x = V.new 'x'
        p_x = P.new('P',[x] )
        unif = U.new

        list = [[a, u], [x, a]]
        new_list = unif.anchor(list)
        p new_list

        list = [[a, p_x], [u, a]]
        new_list = unif.anchor(list)
        p new_list

      end
    end
  end


  describe CNF_Converter do

    describe 'pretty print' do
      it "should pretty_print" do
        y = V.new('y')
        f_y = P.new('f', [y])
        sentence = S.new('neg', {sentence: S.new('atomic', {predicate: f_y})})
        sentence.to_s.should == "\u00AC(f(y))"

        g_y = P.new('g', [y])
        sentence2 = S.new('op', {op: '<=>', sentence1: S.new('atomic', {predicate: f_y}), sentence2: Sentence.new('atomic', {predicate: g_y})})
        sentence2.to_s.should == "(f(y)) <=> (g(y))"
      end

      it 'should pretty print quantifier' do
        y = V.new('y')
        f_y = P.new('f', [y])
        inside = S.new('neg', {sentence: S.new('atomic', {predicate: f_y})})

        sen = S.new('quant', {
          quant: Q.new('A'),
          variable: V.new('y'),
          sentence: inside
        })
        sen.to_s.should == "#{@fa}y[#{@neg}(f(y))]"
      end
    end

    describe '<=> Elimination' do
      it 'should eliminiate <=>' do
        y = V.new('y')
        f_y = P.new('f', [y])
        g_y = P.new('g', [y])

        phi = S.new('atomic', {predicate: f_y})
        shi = S.new('atomic', {predicate: g_y})

        sen = S.new('op', {op: '<=>', sentence1: phi, sentence2: shi})
        new_sen = CNF_Converter.eliminate_equiv(sen)
        new_sen.type.should == 'op'
        vars = new_sen.vars
        vars[:op].should == '^'

        vars[:sentence1].to_s.should == '(f(y)) => (g(y))'
        vars[:sentence2].to_s.should == '(g(y)) => (f(y))'
      end

      it 'should eliminate with a quant' do
        x = V.new('x')
        y = V.new('y')

        # f(x) <=> g(x)
        sen2 = S.new('op', {
          op: '<=>',
          sentence1: S.new('atomic', {predicate: P.new('f', [x])}),
          sentence2: S.new('atomic', {predicate: P.new('g', [x])})})

        # for_all x f(x) <=> g(x) => for_all x [(f(x) => g(x)) ^ (g(x) => f(x))]
        sen = S.new('quant', {
          quant: Q.new('A'),
          variable: x,
          sentence: sen2
        })
        sen.to_s.should == "#{@fa}x[(f(x)) <=> (g(x))]"
        new_sen = CNF_Converter.eliminate_equiv(sen)
        new_sen.to_s.should == "#{@fa}x[((f(x)) => (g(x))) ^ ((g(x)) => (f(x)))]"

      end

      it 'should eliminate like lecture 7 slide 9' do
        sentence = make_lec7_sen
        sentence.to_s.should == "#{@fa}x[(P(x)) <=> ((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))]))]"

        new_sen = CNF_Converter.eliminate_equiv(sentence)
        new_sen.to_s.should == "#{@fa}x[((P(x)) => ((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))]))) ^ (((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))])) => (P(x)))]"
      end

      it 'should not change the original sentence' do
        sentence = make_lec7_sen
        old_string = sentence.to_s.dup
        new_sen = CNF_Converter.eliminate_equiv(sentence)
        new_string = sentence.to_s
        (old_string == new_string).should be_true
      end
    end

    describe '=> Elimination' do
      it 'should do it simply' do
        x = V.new('x')
        y = V.new('y')

        # p(x) => q(x)
        p_x = S.new('atomic', {predicate: P.new('p', [x])})
        q_x = S.new('atomic', {predicate: P.new('q', [x])})
        sen1 = S.new('op', {op: '=>', sentence1: p_x, sentence2: q_x})
        new_sen = CNF_Converter.eliminate_impl(sen1)
        new_sen.to_s.should == "(#{@neg}(p(x))) v (q(x))"
      end

      it 'should do it not very simply' do
        x = V.new('x')
        y = V.new('y')
        p_x = P.new('P', [x])
        q_x = P.new('Q', [x])
        q_y = P.new('Q', [y])
        r_y_x = P.new('R', [y,x])

        # Q(y) ∧ R(y, x)
        sen3 = S.new('op', {
          op: '^',
          sentence1: S.new('atomic', {predicate: q_y}),
          sentence2: S.new('atomic', {predicate: r_y_x})})

        #∃y[Q(y) ∧ R(y, x)]
        sen2 = S.new('quant', {
          quant: Q.new('E'),
          variable: y,
          sentence: sen3
        })

        # (Q(x) ∧ ∃y[Q(y) ∧ R(y, x)])
        sen1 = S.new('op', {
          op: '^',
          sentence1: S.new('atomic', {predicate: q_x}),
          sentence2: sen2
        })

        # (P(x) ⇒ (Q(x) ∧ ∃y[Q(y) ∧ R(y, x)]))
        sentence = S.new('op', {
          op: '=>',
          sentence1: S.new('atomic', {predicate: p_x}),
          sentence2: sen1
        })

        new_sen = CNF_Converter.eliminate_impl(sentence)
        new_sen.to_s.should == "(#{@neg}(P(x))) v ((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))]))"
      end

      it 'should do it lke lecture 7 slide 10' do
        # ∀x[(P(x) ⇒ (Q(x) ∧ ∃y[Q(y) ∧ R(y, x)])) ∧ ((Q(x) ∧ ∃y[Q(y) ∧ R(y, x)]) ⇒ P(x))]
        sentence = make_lec7_sen
        sentence1 = CNF_Converter.eliminate_equiv(sentence)
        sentence2 = CNF_Converter.eliminate_impl(sentence1)
        sentence2.to_s.should_not == sentence1.to_s

        sentence2.to_s.should == "#{@fa}x[((#{@neg}(P(x))) v ((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))]))) ^ ((#{@neg}((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))]))) v (P(x)))]"
      end
    end

    describe 'push neg inwards' do
      it 'should_propgate neg with' do
        x = V.new('x')
        y = V.new('y')
        f_y = P.new('f', [y])
        f_x = P.new('f', [x])
        phi = S.new('atomic', {predicate: f_x})
        shi = S.new('atomic', {predicate: f_y})

        new_phi = CNF_Converter.propagate_neg(phi)
        new_phi.to_s.should == "#{@neg}(f(x))"

        # (f(x)) ^ (f(y))
        conj = S.new('op', {op: '^', sentence1: phi, sentence2: shi})
        neg_conj = CNF_Converter.propagate_neg(conj)
        # (f(x)) ^ (f(y))
        neg_conj.to_s.should == "(#{@neg}(f(x))) v (#{@neg}(f(y)))"
      end

      it 'should eliminate simple' do
        x = V.new('x')
        y = V.new('y')
        f_y = P.new('f', [y])
        f_x = P.new('f', [x])
        phi = S.new('atomic', {predicate: f_x})
        shi = S.new('atomic', {predicate: f_y})
        neg_shi = S.new('neg', {sentence: shi})
        neg_phi = S.new('neg', {sentence: phi})

        # ¬(¬(f(x)))
        sentence = S.new('neg', {sentence: S.new('neg', {sentence: phi})})
        new_sen = CNF_Converter.push_neg_inwards(sentence)
        new_sen.to_s.should == 'f(x)'

        # ¬((f(x)) v (f(y)))
        sentence = S.new('neg', {sentence: S.new('op', {op: 'v',
                                                 sentence1: phi,
                                                 sentence2: shi })})
        new_sen = CNF_Converter.push_neg_inwards(sentence)
        new_sen.to_s.should == "(#{@neg}(f(x))) ^ (#{@neg}(f(y)))"

        # ¬((f(x)) v (¬(f(y))))
        sentence = S.new('neg', {sentence: S.new('op', {op: 'v',
                                                 sentence1: phi,
                                                 sentence2: neg_shi })})
        new_sen = CNF_Converter.push_neg_inwards(sentence)
        new_sen.to_s.should == "(#{@neg}(f(x))) ^ (f(y))"

        # ¬((¬(f(x))) v (¬(f(y))))
        sentence = S.new('neg', {sentence: S.new('op', {op: 'v',
                                                 sentence1: neg_phi,
                                                 sentence2: neg_shi })})
        new_sen = CNF_Converter.push_neg_inwards(sentence)
        new_sen.to_s.should == "(f(x)) ^ (f(y))"

        # ¬(∀x[f(x)])
        all_phi = S.new('quant', {quant: Q.new('A'), variable: x, sentence: phi})
        sentence = S.new('neg', {sentence: all_phi})
        new_sen = CNF_Converter.push_neg_inwards(sentence)
        new_sen.to_s.should == "#{@te}x[#{@neg}(f(x))]"

      end

      it 'should do a medium one' do
        x = V.new('x')
        y = V.new('y')

        q_x = P.new('Q', [x]).to_sentence
        q_y = P.new('Q', [y]).to_sentence
        r_y_x = P.new('R', [y, x]).to_sentence
        p_x = P.new('P', [x]).to_sentence


        # ∃y[Q(y) ∧ R(y, x)]
        sen3 = S.new('quant', {
          quant: Q.new('E'),
          variable: y,
          sentence: S.new('op', {op: '^', sentence1: q_y, sentence2: r_y_x})
        })

        # Q(x) ∧ ∃y[Q(y)   ∧ R(y, x)]
        sen2 = S.new('op', {op: '^', sentence1: q_x, sentence2: sen3 })

        # ¬(Q(x) ∧ ∃y[Q(y) ∧ R(y, x)])
        sen1 = S.new('neg', {sentence: sen2})

        # (¬(Q(x) ∧ ∃y[Q(y) ∧ R(y, x)])     ∨    P(x))
        sentence = S.new('op', {
          op: 'v',
          sentence1: sen1,
          sentence2: p_x
        })

        new_sen = CNF_Converter.push_neg_inwards(sentence)
        new_sen.to_s.should == "((#{@neg}(Q(x))) v (#{@fa}y[(#{@neg}(Q(y))) v (#{@neg}(R(y, x)))])) v (P(x))"

      end

      it 'should do like lecture 7 slide 11' do

        sentence = make_lec7_sen
        sentence1 = CNF_Converter.eliminate_equiv(sentence)
        sentence2 = CNF_Converter.eliminate_impl(sentence1)
        sentence3 = CNF_Converter.push_neg_inwards(sentence2)
        sentence3.to_s.should == "#{@fa}x[((#{@neg}(P(x))) v ((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))]))) ^ (((#{@neg}(Q(x))) v (#{@fa}y[(#{@neg}(Q(y))) v (#{@neg}(R(y, x)))])) v (P(x)))]"
      end
    end

    describe 'standarize apart' do
      it 'should change variables' do
        x = V.new('x')
        y = V.new('y')
        f_y = P.new('f', [y]).to_sentence
        g_y = P.new('g', [y]).to_sentence


        # FAy g(y)
        right = S.new('quant', {quant: Q.new('A'), variable: y, sentence: g_y})

        # TEy [f(y)]
        sen2 = S.new('quant', {quant: Q.new('E'), variable: y, sentence: f_y})

        # FAx [TEy [f(y)]]
        left = S.new('quant', {quant: Q.new('A'), variable: x, sentence: sen2})

        # FAx [TEy [f(y)]] ^ FAy g(y)
        sen = S.new('op', {op: '^', sentence1: left, sentence2: right})
        new_sen = CNF_Converter.standardize_apart(sen, [])
        new_sen.to_s.should == "(#{@fa}x[#{@te}y[f(y)]]) ^ (#{@fa}z[g(z)])"
      end

      it 'should do it like lecture 7' do
        sentence = make_lec7_sen
        sentence1 = CNF_Converter.eliminate_equiv(sentence)
        sentence2 = CNF_Converter.eliminate_impl(sentence1)
        sentence3 = CNF_Converter.push_neg_inwards(sentence2)
        sentence4 = CNF_Converter.standardize_apart(sentence3, [])
        sentence4.to_s.should == "#{@fa}x[((#{@neg}(P(x))) v ((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))]))) ^ (((#{@neg}(Q(x))) v (#{@fa}z[(#{@neg}(Q(z))) v (#{@neg}(R(z, x)))])) v (P(x)))]"
      end
    end

    describe 'skolemize' do
      it 'should do it simple' do

        y = V.new('y')
        f_y = P.new('f', [y]).to_sentence

        sen2 = S.new('quant', {quant: Q.new('E'), variable: y, sentence: f_y })

        # FA x2 [TEy f(y)]
        sen1 = S.new('quant', {quant: Q.new('A'), variable: V.new('x2'), sentence: sen2})
        # FA x1[FA x2 [TEy] ]
        sentence = S.new('quant', {quant: Q.new('A'), variable: V.new('x1'), sentence: sen1})

        new_sen = CNF_Converter.skolemize(sentence, [], [])
        new_sen.to_s.should == "#{@fa}x1[#{@fa}x2[f(sk(x1, x2))]]"
      end

      it 'should do it like in the lecture' do
        sentence = make_lec7_sen
        sentence1 = CNF_Converter.eliminate_equiv(sentence)
        sentence2 = CNF_Converter.eliminate_impl(sentence1)
        sentence3 = CNF_Converter.push_neg_inwards(sentence2)
        sentence4 = CNF_Converter.standardize_apart(sentence3, [])
        sentence5 = CNF_Converter.skolemize(sentence4, [], [])
        sentence5.to_s.should == "#{@fa}x[((#{@neg}(P(x))) v ((Q(x)) ^ ((Q(sk(x))) ^ (R(sk(x), x))))) ^ (((#{@neg}(Q(x))) v (#{@fa}z[(#{@neg}(Q(z))) v (#{@neg}(R(z, x)))])) v (P(x)))]"
      end
    end

    describe 'describe discard for all' do
      it 'should do it simple' do
        y = V.new('y')
        f_y = P.new('f', [y]).to_sentence

        sen2 = S.new('quant', {quant: Q.new('E'), variable: y, sentence: f_y })

        # FA x2 [TEy f(y)]
        sen1 = S.new('quant', {quant: Q.new('A'), variable: V.new('x2'), sentence: sen2})
        # FA x1[FA x2 [TEy] ]
        sentence = S.new('quant', {quant: Q.new('A'), variable: V.new('x1'), sentence: sen1})

        new_sen = CNF_Converter.skolemize(sentence, [], [])

        to_be_tested = CNF_Converter.discard_for_all(new_sen)
        to_be_tested.to_s.should == "f(sk(x1, x2))"
      end

      it 'should do like lecture 7' do
        sentence = make_lec7_sen
        sentence1 = CNF_Converter.eliminate_equiv(sentence)
        sentence2 = CNF_Converter.eliminate_impl(sentence1)
        sentence3 = CNF_Converter.push_neg_inwards(sentence2)
        sentence4 = CNF_Converter.standardize_apart(sentence3, [])
        sentence5 = CNF_Converter.skolemize(sentence4, [], [])
        sentence6 = CNF_Converter.discard_for_all(sentence5)
        sentence6.to_s.should == "((#{@neg}(P(x))) v ((Q(x)) ^ ((Q(sk(x))) ^ (R(sk(x), x))))) ^ (((#{@neg}(Q(x))) v ((#{@neg}(Q(z))) v (#{@neg}(R(z, x))))) v (P(x)))"
      end
    end

    describe 'translate to CNF' do
      it 'should do it simple' do
        x = V.new('x')
        y = V.new('y')
        f_x = P.new('f', [x]).to_sentence
        f_y = P.new('f', [y]).to_sentence
        g_y = P.new('g', [y]).to_sentence
        sen = S.new('op', {op: '^', sentence1: f_y, sentence2: g_y})
        sentence = S.new('op', {
          op: 'v',
          sentence1: f_x,
          sentence2: sen } )
        new_sen = CNF_Converter.translate_to_CNF(sentence)
        new_sen.to_s.should == "((f(x)) v (f(y))) ^ ((f(x)) v (g(y)))"
      end

      it 'should do it inverse' do
        x = V.new('x')
        y = V.new('y')
        f_x = P.new('f', [x]).to_sentence
        f_y = P.new('f', [y]).to_sentence
        g_y = P.new('g', [y]).to_sentence
        sen = S.new('op', {op: '^', sentence1: f_y, sentence2: g_y})

        # (f(y) ^ g(y)) v (f(x))
        sentence = S.new('op', {
          op: 'v',
          sentence1: sen,
          sentence2: f_x } )

        new_sen = CNF_Converter.translate_to_CNF(sentence)
        new_sen.to_s.should == "((f(y)) v (f(x))) ^ ((g(y)) v (f(x)))"

      end

      it 'should do lecture 7' do
        sentence = make_lec7_sen
        sentence1 = CNF_Converter.eliminate_equiv(sentence)
        sentence2 = CNF_Converter.eliminate_impl(sentence1)
        sentence3 = CNF_Converter.push_neg_inwards(sentence2)
        sentence4 = CNF_Converter.standardize_apart(sentence3, [])
        sentence5 = CNF_Converter.skolemize(sentence4, [], [])
        sentence6 = CNF_Converter.discard_for_all(sentence5)
        sentence7 = CNF_Converter.translate_to_CNF(sentence6)
        sentence7.to_s.should == "(((#{@neg}(P(x))) v (Q(x))) ^ (((#{@neg}(P(x))) v (Q(sk(x)))) ^ ((#{@neg}(P(x))) v (R(sk(x), x))))) ^ (((#{@neg}(Q(x))) v ((#{@neg}(Q(z))) v (#{@neg}(R(z, x))))) v (P(x)))"
      end
    end

    describe 'build clauses ' do
      it 'should do it simple' do
        x = V.new('x')
        y = V.new('y')
        f_x = P.new('f', [x]).to_sentence
        f_y = P.new('f', [y]).to_sentence
        g_y = P.new('g', [y]).to_sentence
        sen = S.new('op', {op: '^', sentence1: f_y, sentence2: g_y})
        sentence = S.new('op', {
          op: 'v',
          sentence1: f_x,
          sentence2: sen } )
        # ((f(x)) v (f(y))) ^ ((f(x)) v (g(y)))
        sentence = CNF_Converter.translate_to_CNF(sentence)
        conjs = CNF_Converter.get_sentences_rec(sentence, [], '^')
        conjs.inspect.should == "[(f(x)) v (f(y)), (f(x)) v (g(y))]"
      end

      it 'should do it medium' do
        x = V.new('x')
        y = V.new('y')
        f_x = P.new('f', [x]).to_sentence
        g_x = P.new('g', [x]).to_sentence
        f_y = P.new('f', [y]).to_sentence
        g_y = P.new('g', [y]).to_sentence
        neg_g_y = S.new('neg', {sentence: g_y})


        # (g(x) v g(y))
        sen2 = S.new('op', {op: 'v', sentence1: g_x, sentence2: neg_g_y})

        # (f(y) v (g(x) v g(y)))
        sen = S.new('op', {op: 'v', sentence1: f_y, sentence2: sen2})

        # f(x) ^ (f(y) v (g(x) v g(y)))
        sentence = S.new('op', {op: '^', sentence1: f_x, sentence2: sen})
        #p sentence
        CNF_Converter.build_clauses(sentence).inspect.should == "[[f(x)], [f(y), g(x), #{@neg}(g(y))]]"
      end

      it 'should do the lecture' do
        sentence = make_lec7_sen
        sentence1 = CNF_Converter.eliminate_equiv(sentence)
        sentence2 = CNF_Converter.eliminate_impl(sentence1)
        sentence3 = CNF_Converter.push_neg_inwards(sentence2)
        sentence4 = CNF_Converter.standardize_apart(sentence3, [])
        sentence5 = CNF_Converter.skolemize(sentence4, [], [])
        sentence6 = CNF_Converter.discard_for_all(sentence5)
        sentence7 = CNF_Converter.translate_to_CNF(sentence6)
        clauses = CNF_Converter.build_clauses(sentence7)
        clauses.inspect.should == "[[#{@neg}(P(x)), Q(x)], [#{@neg}(P(x)), Q(sk(x))], [#{@neg}(P(x)), R(sk(x), x)], [#{@neg}(Q(x)), #{@neg}(Q(z)), #{@neg}(R(z, x)), P(x)]]"
      end
    end

    describe 'standarize clauses' do
      it 'should do it simple' do
        x = V.new('x')
        f_x = P.new('f', [x]).to_sentence
        g_x = P.new('g', [x]).to_sentence
        h_x = P.new('h', [x]).to_sentence
        neg_h_x = S.new('neg', {sentence: h_x})

        clauses = [[f_x], [g_x, f_x], [f_x, h_x], [h_x, g_x]]
        CNF_Converter.standardize_clauses!(clauses)
        clauses.inspect.should == "[[f(x)], [g(z), f(z)], [f(y), h(y)], [h(w), g(w)]]"

        clauses = [[f_x], [g_x, f_x], [f_x, h_x], [neg_h_x, g_x]]
        CNF_Converter.standardize_clauses!(clauses)
        clauses.inspect.should == "[[f(x)], [g(z), f(z)], [f(y), h(y)], [#{@neg}(h(w)), g(w)]]"
      end

      it 'should do lecture 7' do
        sentence = make_lec7_sen
        sentence1 = CNF_Converter.eliminate_equiv(sentence)
        sentence2 = CNF_Converter.eliminate_impl(sentence1)
        sentence3 = CNF_Converter.push_neg_inwards(sentence2)
        sentence4 = CNF_Converter.standardize_apart(sentence3, [])
        sentence5 = CNF_Converter.skolemize(sentence4, [], [])
        sentence6 = CNF_Converter.discard_for_all(sentence5)
        sentence7 = CNF_Converter.translate_to_CNF(sentence6)
        clauses = CNF_Converter.build_clauses(sentence7)
        CNF_Converter.standardize_clauses!(clauses)
        clauses.inspect.should == "[[#{@neg}(P(x)), Q(x)], [#{@neg}(P(z)), Q(sk(z))], [#{@neg}(P(y)), R(sk(y), y)], [#{@neg}(Q(w)), #{@neg}(Q(v)), #{@neg}(R(v, w)), P(w)]]"
      end
    end

    it 'should do the second exampel' do
      sentence = make_second_example
      sentence1 = CNF_Converter.eliminate_equiv(sentence)
      sentence2 = CNF_Converter.eliminate_impl(sentence1)
      sentence3 = CNF_Converter.push_neg_inwards(sentence2)
      sentence4 = CNF_Converter.standardize_apart(sentence3, [])
      sentence5 = CNF_Converter.skolemize(sentence4, [], [])
      sentence6 = CNF_Converter.discard_for_all(sentence5)
      sentence7 = CNF_Converter.translate_to_CNF(sentence6)
      clauses = CNF_Converter.build_clauses(sentence7)
      CNF_Converter.standardize_clauses!(clauses)
      clauses.inspect.should == "[[P(sk())], [#{@neg}(Q(z)), #{@neg}(P(z))]]"
    end

    it 'top level method' do
      CNF_Converter.clause_form(make_second_example)
      CNF_Converter.clause_form(make_lec7_sen)
    end
  end
end
