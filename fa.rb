#!/usr/bin/ruby -w

# ########################################
# CMSC 330 - Project 2
# Name: Simon Zhu
# ########################################

#-----------------------------------------------------------
# FUNCTION DECLARATIONS
#-----------------------------------------------------------

class FiniteAutomaton
    @@nextID = 0	# shared across all states
    attr_reader:state, :start, :final, :alphabet, :transition

    #---------------------------------------------------------------
    # Constructor for the FA
    def initialize
        @start = nil 		# start state 
        @state = { } 		# all states
        @final = { } 		# final states
        @transition = { }	# transitions
        @alphabet = [ ] 	# symbols on transitions
    end

    #---------------------------------------------------------------
    # Return number of states
    def num_states
        @state.size
    end

    #---------------------------------------------------------------
    # Creates a new state 
    def new_state
        newID = @@nextID
        @@nextID += 1
        @state[newID] = true
        @transition[newID] = {}
        newID 
    end

    #---------------------------------------------------------------
    # Creates a new state
    def add_state(v)
        unless has_state?(v)
            @state[v] = true
            @transition[v] = {}
        end
    end

    #---------------------------------------------------------------
    # Returns true if the state exists
    def has_state?(v)
        @state[v]
    end

    #---------------------------------------------------------------
    # Set (or reset) the start state
    def set_start(v)
        add_state(v)
        @start = v
    end

    #---------------------------------------------------------------
    # Set (or reset) a final state
    # parameter final set to true, so never false?
    def set_final(v, final)
        add_state(v)
        if final
            @final[v] = true
        else
            @final.delete(v)
        end
    end

    #---------------------------------------------------------------
    # Returns true if the state is final
    def is_final?(v)
        @final[v]
    end

    #---------------------------------------------------------------
    # Creates a new transition from v1 to v2 with symbol x
    # Any previous transition from v1 with symbol x is removed
    def add_transition(v1, v2, x)
        add_state(v1)
        add_state(v2)
        if @transition[v1][x] == nil
          @transition[v1][x] = Array.new
        end
        @transition[v1][x].push(v2)
    end

    #---------------------------------------------------------------
    def get_start
      @start
    end
    
    #---------------------------------------------------------------
    # get array of final states
    def get_final
      @final.keys
    end
    
    #---------------------------------------------------------------
    # get array of states
    def get_state
      @state.keys
    end
  
    #---------------------------------------------------------------
    # get array of alphabet
    def get_alpha
      @alphabet
    end

    #---------------------------------------------------------------
    # Get the destination state from v1 with symbol x
    # Returns nil if non-existent
    def get_transition(v1,x)
        if has_state?(v1)
            @transition[v1][x]
        else
            nil
        end
    end

    #---------------------------------------------------------------
    # get the hash table of transitions
    def get_trans_hash
      @transition
    end

    #---------------------------------------------------------------
    # Returns true if the dfa accepts the given string
    def accept?(s, current)
        if s == ""
            is_final?(current)
        else
            dest = get_transition(current,s[0,1])
            if dest == nil || dest.size > 1
                false
            else
                accept?(s[1..-1], dest[0])
            end
        end
    end
    #---------------------------------------------------------------
    # Returns all states reachable from states ss
    #   using only epsilon transitions
    def eClosure(ss)
      visited = []
        discovered = [ss]
        while discovered != []
          n = discovered.pop
          if !(visited.include?(n))
            visited.push(n)
            successor = get_transition(n, "")
            if successor != nil
              successor.each{|s|
                if !(visited.include?(s))
                  discovered.push(s)
                end
              }
            end
          end
        end
      visited
    end

    #---------------------------------------------------------------
    # get all of the states that are reachable from letter
    def move(arr, letter)
      result = []
      arr.each{|a|
        list = get_transition(a, letter)
        if list != nil
          result = result | list
        end
      }
      result
    end
  
    #---------------------------------------------------------------
    # split for minimization algorithm for DFA
    def split(p, pstate)
      m = []
      r = p[0]
      pn = []
      p.each{|p0| pn.push(p0)}
      pn.delete(p[0])
      tag = 0
      
      pn.each{|p0|
          @alphabet.each{|a|
            t1 = get_transition(r, a)
            t2 = get_transition(p0, a)
            tag = 0
            if t1 != nil && t2 != nil  
              pstate.each{|s|
                if !(t1 == t2)
                  if !(m.include?(p0))
                    if s.include?(t1[0]) && s.include?(t2[0])
                      tag = 1
                    end
                  end
                else
                  tag = 1
                end
              }
              if tag == 0
                m.push(p0)
              end
          elsif t2 == nil && t1 == nil
            next
          elsif t1 != nil || t2 != nil
              m.push(p0)
          end
        }
      }
      m.each{|o| p.delete(o)}
      p = p.sort
      result = [p, m]
      result
    end

    #---------------------------------------------------------------
    # Prints FA 
    def prettyPrint
        print "% Start "
	puts @start

        # Final states in sorted order
	print "% Final {"
	@final.keys.sort.each { |x| print " #{x}" }
	puts " }" 

        # States in sorted order
	print "% States {"
	@state.keys.sort.each { |x| print " #{x}" }
	puts " }" 

        # Alphabet in alphabetical order
        print "% Alphabet {"
	@alphabet.sort.each { |x| print " #{x}" }
	puts " }" 

        # Transitions in lexicographic order
        puts "% Transitions {"
	@transition.keys.sort.each { |v1| 
            @transition[v1].keys.sort.each { |x| 
                v2 = get_transition(v1,x)
                i = 0
                while i < v2.size
                  puts "%  (#{v1} #{x} #{v2[i]})" 
                  i = i + 1
                end
            }
        }
	puts "% }" 
    end
        
    #---------------------------------------------------------------
    # accepts just symbol ("" = epsilon)
    def symbol! sym
        initialize
        s0 = new_state
        s1 = new_state
        set_start(s0)
        set_final(s1, true)
        add_transition(s0, s1, sym)
        if sym != "" && @alphabet.include?("#{sym}") == false
          @alphabet.push("#{sym}")
        end
    end

    #---------------------------------------------------------------
    # accept strings accepted by self, followed by strings accepted by newFA
    # syntax issue
    def concat! newFA
      # reset the final states and copy over start
      keys = @final.keys
      i = 0
      while i < keys.size
        add_transition(keys[i], newFA.get_start, "")
        set_final(keys[i], false)
        i = i + 1
      end
      
      # copy over the final states
      keys = newFA.get_final
      i = 0
      while i < keys.size
        set_final(keys[i], true)
        i = i + 1
      end
      
      # copy over the states
      keys = newFA.get_state
      i = 0
      while i < keys.size
        add_state(keys[i])
        i = i + 1
      end
      
      # copy over the transitions
      newFA.get_trans_hash.keys.sort.each { |v1| 
            newFA.get_trans_hash[v1].keys.sort.each { |x| 
                v2 = newFA.get_transition(v1,x)
                i = 0
                while i < v2.size
                  add_transition(v1, v2[i], x)
                  i = i + 1
                end
            }
      }
      
      # copy over the alphabets
      newFA.get_alpha.each{|a|
        if @alphabet.include?(a) == false
          @alphabet.push(a)
        end
      }
    end

    #---------------------------------------------------------------
    # accept strings accepted by either self or newFA
    def union! newFA
      s0 = new_state
      s1 = new_state
      add_transition(s0, @start, "")
      add_transition(s0, newFA.get_start, "")
      
      # reset the final states of the current object
      keys = @final.keys
      i = 0
      while i < keys.size
        add_transition(keys[i], s1, "")
        set_final(keys[i], false)
        i = i + 1
      end
      
      # set the final states of the other object
      keys = newFA.get_final
      i = 0
      while i < keys.size
        add_transition(keys[i], s1, "")
        i = i + 1
      end
      
      # copy over the states
      keys = newFA.get_state
      i = 0
      while i < keys.size
        add_state(keys[i])
        i = i + 1
      end
      
      # copy over the transitions
      newFA.get_trans_hash.keys.sort.each { |v1| 
            newFA.get_trans_hash[v1].keys.sort.each { |x| 
                v2 = newFA.get_transition(v1,x)
                i = 0
                while i < v2.size
                  add_transition(v1, v2[i], x)
                  i = i + 1
                end
            }
        }
        
      set_start(s0)
      set_final(s1, true)
      
      # copy over the alphabets
      newFA.get_alpha.each{|a|
        if @alphabet.include?(a) == false
          @alphabet.push(a)
        end
      }
    end

    #---------------------------------------------------------------
    # accept any sequence of 0 or more strings accepted by self
    def closure! 
      s0 = new_state
      s1 = new_state
      add_transition(s0, @start, "")
      
      # reset the final states of the current object
      keys = @final.keys
      i = 0
      while i < keys.size
        add_transition(keys[i], s1, "")
        set_final(keys[i], false)
        i = i + 1
      end
      
      add_transition(s0, s1, "")
      add_transition(s1, s0, "")
      
      set_start(s0)
      set_final(s1, true)
    end

    #---------------------------------------------------------------
    # returns DFA that accepts only strings accepted by self 
    def toDFA
      # create a new one, or modify the current one in place,
      # and return it
      fa = FiniteAutomaton.new
      rstate, group, result = {}, [], []
      empty = eClosure(@start)
      result.push(empty)
      n = fa.new_state
      fa.set_start(n)
      rstate[empty] = n
      
      while result != []
        curr = result.pop
        @alphabet.each{|alpha|
          empty = []
          group = move(curr, alpha)
          
          if group != nil && group != []
            group.each{|elem| group = group | eClosure(elem)}
            
            # check if the state is already in R
            if rstate[group] == nil && group.size != 0
              result.push(group)
              n = fa.new_state
              rstate[group] = n
            end
              fa.add_transition(rstate[curr], rstate[group], alpha)
              if fa.get_alpha.include?(alpha) == false
                fa.get_alpha.push(alpha)
              end
            end
        }
      end
      
      keys = @final.keys
      rkeys = rstate.keys
      final = []
      rkeys.each{|r| 
        keys.each{|k| if r.include?(k) then fa.set_final(rstate[r], true) end}
      }
      fa
    end

    #---------------------------------------------------------------
    # returns a DFA that accepts only strings accepted by self, 
    # but as minimal DFA.
    def minimize
      # create a new one, or modify the current one in place,
      # and return it
      fa = FiniteAutomaton.new
      keys = @state.keys.sort
      p0, p1 = [], []
      keys.each{|k| 
        if is_final?(k)
          p0 = p0.push(k)
        elsif
          p1 = p1.push(k)
        end
      }
      newfa = {}
      rstate = []
      if p0 != nil then rstate.push(p0) end
      if p1 != nil then rstate.push(p1) end
      pstate = []
      
      while pstate != rstate
        pstate = []
        rstate.each{|r| pstate.push(r)}
        rstate = []
        pstate.each{|p| 
          p = p.sort
          result = split(p, pstate)
          p0 = result[0]
          p1 = result[1]
          result.each{|r| 
            if r != []
              r = r.sort
              rstate = rstate.push(r)
            end
          }
        }
      end
      
      start = []
      final = []
      rstate.each{|r| newfa[r] = fa.new_state}
      list = newfa.keys
      list.each{|l|
        l.each{|k|
          if k == @start
            start.push(l)
          end
          if is_final?(k)
            final.push(l)
          end
        }
      }
      
      if start != []
        start.each{|s| if newfa[s] then fa.set_start(newfa[s]) end}
      end
      if final != []
        final.each{|f| fa.set_final(newfa[f], true)}
      end
      
      rstate.each{|r0|
        r0.each{|r1|
          @alphabet.each{|a|
            if get_transition(r1, a) != nil
              rstate.each{|r|
                if r.include?(get_transition(r1, a)[0])
                  if !(fa.get_transition(newfa[r0], a))
                    fa.add_transition(newfa[r0], newfa[r], a)
                    if fa.get_alpha.include?(a) == false
                      fa.get_alpha.push(a)
                    end
                  end
                end
              }
            end
          }
        }
      }
      fa
    end

    #---------------------------------------------------------------
    # return all strings accepted by FA with length <= strLen
    def genStr strLen
	sortedAlphabet = @alphabet.sort
        resultStrs = [ ] 
        testStrings = [ ]
        testStrings[0] = [] 
        testStrings[0].push ""
        1.upto(strLen.to_i) { |x|
            testStrings[x] = []
            testStrings[x-1].each { |s|
                sortedAlphabet.each { |c|
                    testStrings[x].push s+c
                }
            }
        }
        testStrings.flatten.each { |s|
       
            resultStrs.push s if accept? s, @start
        }
        result = ""
        resultStrs.each { |x| result.concat '"'+x+'" ' }
        result
    end

    #---------------------------------------------------------------
    # Create a graphvis file for our FA
            
    def dotfile()
    end

end

#---------------------------------------------------------------
# read standard input and interpret as a stack machine

def interpreter file
   dfaStack = [ ] 
   loop do
       line = file.gets
       if line == nil then break end
       words = line.scan(/\S+/)
       words.each{ |word|
           case word
               when /DONE/
                   return
               when /DOT/
                   f = dfaStack.last
                   f.dotfile
               when /SIZE/
                   f = dfaStack.last
                   puts f.num_states
               when /PRINT/
                   f = dfaStack.last
                   f.prettyPrint
               when /DFA/
                   f = dfaStack.pop
                   f2 = f.toDFA
                   dfaStack.push f2
               when /MINIMIZE/
                   f = dfaStack.pop
                   f2 = f.minimize
                   dfaStack.push f2
               when /GENSTR([0-9]+)/
                   f = dfaStack.last
                   puts f.genStr($1)
               when /"([a-z]*)"/
                   f = dfaStack.last
                   str = $1
                   if f.accept?(str, f.get_start)
                       puts "Accept #{str}"
                   else
                       puts "Reject #{str}"
                   end
               when /([a-zE])/
                   puts "Illegal syntax for: #{word}" if word.length != 1
                   f = FiniteAutomaton.new
                   sym = $1
                   sym="" if $1=="E"
                   f.symbol!(sym)
                   dfaStack.push f
               when /\*/
                   puts "Illegal syntax for: #{word}" if word.length != 1
                   f = dfaStack.pop
                   f.closure!
                   dfaStack.push f
               when /\|/
                   puts "Illegal syntax for: #{word}" if word.length != 1
                   f1 = dfaStack.pop
                   f2 = dfaStack.pop
                   f2.union!(f1)
                   dfaStack.push f2
               when /\./
                   puts "Illegal syntax for: #{word}" if word.length != 1
                   f1 = dfaStack.pop
                   f2 = dfaStack.pop
                   f2.concat!(f1)
                   dfaStack.push f2
               else
                   puts "Ignoring #{word}"
           end
        }
   end
end

#---------------------------------------------------------------
# main( )

if false			# just debugging messages
    f = FiniteAutomaton.new
    f.set_start(1)
    f.set_final(2)
    f.set_final(3)
    f.add_transition(1,2,"a")   # need to keep this for NFA
    f.add_transition(1,3,"a")  
    f.prettyPrint
end

if ARGV.length > 0 then
  file = open(ARGV[0])
else
  file = STDIN
end

interpreter file  # type "DONE" to exit

