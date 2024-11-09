all_eqns = File.read("data/eq_size5.txt").split("\n")

# Skip over the fact that 1-999 is different lengths than the rest of the slices
START_EQ = 4000
all_eqns[START_EQ - 1, all_eqns.length].each_slice(1000).each_with_index { |eqns, slice_idx|
  start_eqn = START_EQ + (slice_idx*1000) 
  end_eqn = START_EQ + (slice_idx*1000) + eqns.length - 1

  puts "import equational_theories.Equations.Eqns#{start_eqn}_#{end_eqn}"
  File.open(File.join("equational_theories/Equations", "Eqns#{start_eqn}_#{end_eqn}.lean"), "w") { |f|
    f.puts <<-END
import equational_theories.Magma
import equational_theories.Equations.Command

/-! Equations list, numbers #{start_eqn}-#{end_eqn} -/

END
    eqns.each_with_index { |eq, eq_idx|
      f.puts "equation #{start_eqn + eq_idx} := #{eq}"
    }
  }
}
