
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

describe CNF_Converter do
  before(:all) do
    S = Sentence
    P = Predicate
    V = Variable
    Q = Quantifier
    @fa = "\u2200"
    @te = "\u2203"
    @neg = "\u00AC"
  end

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

      puts sen3
      #∃y[Q(y) ∧ R(y, x)]
      sen2 = S.new('quant', {
        quant: Q.new('E'),
        variable: y,
        sentence: sen3
      })
      puts sen2

      # (Q(x) ∧ ∃y[Q(y) ∧ R(y, x)])
      sen1 = S.new('op', {
        op: '^',
        sentence1: S.new('atomic', {predicate: q_x}),
        sentence2: sen2
      })
      puts sen1

      # (P(x) ⇒ (Q(x) ∧ ∃y[Q(y) ∧ R(y, x)]))
      sentence = S.new('op', {
        op: '=>', 
        sentence1: S.new('atomic', {predicate: p_x}),
        sentence2: sen1
      })

      puts sentence
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
end
