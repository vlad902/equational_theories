=begin
cat equational_theories/Generated/Order5/Eq2Proof*.lean | grep theorem | ruby -ne 'puts $1 if $_ =~ /Equation(\d+)_implies_Equation2 /' > data/order5_equivalent_to_eq2.csv

grep "Table" equational_theories/Generated/All4x4Tables/data/*.txt | cut -d ' ' -f 2- > /tmp/magmas
grep "Table" equational_theories/Generated/FinSearch/data/*.txt | cut -d ' ' -f 2- >> /tmp/magmas
grep "Table" data/interesting_finite_magmas/order5_magmas.txt | cut -d ' ' -f 2- >> /tmp/magmas
cat data/smallest_magma_examples.txt | cut -d ' ' -f 2- >> /tmp/magmas
cat /tmp/magmas | sort -u | sed -e 's/ //'g > /tmp/t
cat /tmp/t | awk '{ print length, $0 }' | sort -n | cut -d' ' -f2- > /tmp/magmas
cat /tmp/magmas | ruby scripts/iterate_explore_magmas.rb
=end

require 'json'

OUT = "data/order5_satisfying_finite_magma.csv"
seen = Set.new

unknown = 4695.upto(62576).to_a
unknown -= File.read("data/order5_equivalent_to_eq2.csv").split("\n").map(&:to_i)

def transpose(table)
  result = Array.new(table.length) { [] }

  table.length.times { |i|
    table[i].each_with_index { |e, j|
      result[j].push(e)
    }
  }

  result
end

visited = {}
while gets
  puts "Unknowns: #{unknown.length}"

  table = JSON.parse($_)
  next if visited[table]
  visited[table] = true

  out = `python scripts/explore_magma.py --ids #{unknown.join(",")} --json #{JSON.generate(table)}`
  begin
    d = JSON.parse(out)
    seen += d["satisfies"]
    unknown -= d["satisfies"]
  rescue => e
    puts "Failed #{e.inspect}"
    #puts out
  end

  transp = transpose(table)
  next if visited[transp]
  visited[transp] = true

  out = `python scripts/explore_magma.py --ids #{unknown.join(",")} --json #{JSON.generate(transp)}`
  begin
    d = JSON.parse(out)
    seen += d["satisfies"]
    unknown -= d["satisfies"]
  rescue => e
    puts "Failed #{e.inspect}"
  end
end

puts
puts "Found #{seen.length} equations with satisfying finite magmas, writing to #{OUT}"
File.open(OUT, "w") { |f|
  f.puts seen.to_a.sort.map(&:to_s).join("\n")
}
