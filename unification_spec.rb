
require_relative './unification.rb'

describe CNF_Converter do
  it "should pretty_print" do
    y = Variable.new('y')
    f_y = Predicate.new('f', [y])
    sentence = Sentence.new('neg', {sentence: Sentence.new('atomic', {predicate: f_y})})
    sentence.to_s.should == "\u00AC(f(y))"

    g_y = Predicate.new('g', [y])
    sentence2 = Sentence.new('op', {op: '<=>', sentence1: Sentence.new('atomic', {predicate: f_y}), sentence2: Sentence.new('atomic', {predicate: g_y})})
    sentence2.to_s.should == "f(y) <=> g(y)"
  end
end
