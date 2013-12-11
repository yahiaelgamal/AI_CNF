
require_relative './unification.rb'

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

  describe 'Hash Elimination' do
    it 'should eliminiate hash' do
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
                   sentence1: P.new('Q', [x]),
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

      sentence.to_s.should == "#{@fa}x[(P(x)) <=> ((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))]))]"

      new_sen = CNF_Converter.eliminate_equiv(sentence)
      new_sen.to_s.should == "#{@fa}x[((P(x)) => ((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))]))) ^ (((Q(x)) ^ (#{@te}y[(Q(y)) ^ (R(y, x))])) => (P(x)))]"
    end
  end
end
