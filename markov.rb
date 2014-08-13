#!/usr/bin/env ruby
require 'triez'
require 'fiber'

class MarkovModel < Fiber
   def initialize(order)
      @order = order
      @model = Hash.new {|h, k| h[k] = Array.new }

      super() do
         loop do
            if (syllable = @model[@state.hash].sample)
               Fiber.yield syllable
               @state << syllable
            end
            @state.shift # randomize?
         end
      end
   end

   def train(ary)
      # train
      ary.each_cons(@order + 1) do |*key, n|
         while !key.empty?
            @model[key.hash] << n
            key.shift
         end
      end
      # when the state is empty, pick anything
      @model[Array.new.hash] = ary
      # start with any single element
      @state = [ary.sample]

      while @state.size < @order
         if (syllable = @model[@state.hash].sample)
            @state << syllable
         else
            @state.shift
         end
      end
   end
end

class SourceText
   TOKEN = %r{
      (
         [:\d\.]+ |
         [\p{Alpha}\'\-]+ |
         [\.,\p{P}] \s? |
         \s
      )
   }x

   def initialize(filename)
      @text = File.read(filename).gsub(/\s+/, " ").chomp << " "
   end

   def words
      @words ||= @text.scan(TOKEN).flatten
   end

   def syllables(*dicts)
      words.flat_map do |word|
         if word.index(/\w/)
            dicts.each {|dict|
               result = dict.hyphenate(word)
               break result if result
            } or [word]
         else
            [word]
         end
      end
   end
end

class DictHyph
   SEP = "\xA5".b

   def initialize(filename)
      @trie = Triez.new(value_type: :object)

      File.open(filename, 'rb') do |mhyph|
         mhyph.each do |line|
            line.chomp!
            @trie[line.delete(SEP).downcase] = line.split(SEP)
         end
      end
   end

   def hyphenate(word)
      @trie[word.downcase]
   end
end

class MyspellHyph
   def initialize(filename)
      @trie = Triez.new(value_type: :object)

      File.open(filename, "r") do |f|
         f.set_encoding(f.gets.chomp)
         f.each do |line|
            line.chomp!
            hyphens = line.scan(/([0-9])?([^0-9\.]|$)/).map do |n, _|
               (n || 0).to_i
            end
            @trie[line.delete('0-9')] = hyphens
         end
      end
   end

   def hyphenate(word)
      levels = Array.new(word.size, 0)

      w = "#{ word }."
      word.size.times do |n|
         (1 .. w.size - n).each do |len|
            if (points = @trie[w[n, len]])
               levels[n, points.size] = levels[n, points.size].zip(points).map(&:max)
            end
         end
      end

      levels.map(&:odd?).zip(word.chars).flatten(1).select {|o| o }.
               # 'a', true, 'b', 'c'
            chunk {|o| o != true }.select(&:first).
               # [true, 'a'], [true, 'b', 'c']
            map {|o| o.last.join } 
               # 'a', 'bc'
   end
end

src = SourceText.new('data/ASOIAF.txt')
word_list = DictHyph.new('data/mhyph.txt')
myspell_dict = MyspellHyph.new('/usr/share/myspell/dicts/hyph_en_US.dic')

order = 6

model = MarkovModel.new(order)
model.train(src.syllables(word_list, myspell_dict))

chain = 2_000.times.map do
   model.resume
end

File.open("data/chain-#{ order }.txt", ?w) {|f|
   f.write chain.join.gsub(/(?<=\.)\s+(.)/) {|m| "\s#{ m[1].upcase }" }
}
