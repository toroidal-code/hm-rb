#!/usr/bin/ruby
require 'set'

# Identifier
class Ident
  attr_reader :name
  def initialize(name); @name = name; end
  def to_s; @name; end
end

# Function application
class Apply
  attr_reader :fn, :arg
  def initialize(fn, arg)
    @fn = fn
    @arg = arg
  end

  def to_s
    "(#{@fn} #{@arg})"
  end
end

# Lambda abstraction
class Lambda
  attr_reader :v, :body
  def initialize(v, body)
    @v = v
    @body = body
  end

  def to_s
    "(fn #{@v} => #{@body})"
  end
end

# Let binding
class Let
  attr_reader :v, :defn, :body
  def initialize(v, defn, body)
    @v = v
    @defn = defn
    @body = body
  end

  def to_s
    "(let #{@v} = #{@defn} in #{@body})"
  end
end

# Letrec binding
class Letrec
  attr_reader :v, :defn, :body
  def initialize(v, defn, body)
    @v = v
    @defn = defn
    @body = body
  end

  def to_s
    "(letrec #{@v} = #{@defn} in #{@body})"
  end
end

class TypeError < StandardError
end
class ParseError < StandardError
end

# A type variable standing for an arbitrary type.
#
# All type variables have a unique id, but the names are only
# assigned when called the first time (lazy eval)
class TypeVariable
  @@next_variable_id = 0
  @@next_variable_name = 'a'

  attr_reader :name
  attr_accessor :instance
  # Create a new instance of TypeVariable
  # @return [TypeVariable] a new instance
  def initialize
    @id = @@next_variable_id
    @@next_variable_id += 1
    @name = nil
    @instance = nil
  end

  # Print the name, or if one doesn't exist, create it
  # @return [String] type variable's name
  def name
    if @name.nil?
      @name = @@next_variable_name
      @@next_variable_name = @@next_variable_name.next
    end
    @name
  end

  def to_s
    if not @instance.nil?
      @instance.to_s
    else
      name
    end
  end

  def inspect
    "TypeVariable(id = #{@id.to_s})"
  end
end

# An n-ary type constructor which builds a
# new type from an old one
class TypeOperator
  attr_reader :name, :types
  def initialize(name, types)
    @name = name
    @types = types
  end
  
  def to_s
    if @types.size == 0
      @name
    elsif @types.size == 2
      "(#{@types[0]} #{@name} #{@types[1]})"
    else
      "#{@name} #{@types.join(' ')}"
    end
  end
  def inspect
    to_s()
  end
end

# A binary type constructor which builds function
# types
class Function < TypeOperator
  def initialize(from_type, to_type)
    super('->', [from_type, to_type])
  end
  def inspect
    to_s
  end
end

# Basic types are constructed with a nullary type constructor
MyInteger = TypeOperator.new("int", [])  # Basic integer
MyBool    = TypeOperator.new("bool", []) # Basic bool



# Computes the type of the expression given by node.
# 
# The type of the node is computed in the context of the context of the
# supplied type environment env. Data types can be introduced into the
# language simply by having a predefined set of identifiers in the initial
# environment. environment; this way there is no need to change the syntax or, more
# importantly, the type-checking program when extending the language.
#
# @param  node [Node] The root of the abstract syntax tree.
# @param  env [Hash] The type environment is a mapping of expression 
#                    identifier names to type assignments.
# @param  non_generic=nil [Set] A set of non-generic variables, or None
# 
# @raise [TypeError] The type of the expression could not be inferred, for example
#                    if it is not possible to unify two types such as Integer and Bool
# @raise [ParseError] The abstract syntax tree rooted at node could not be parsed
# 
# @return [type] The computed type of the expression.
def analyse(node, env, non_generic=nil)
  if non_generic.nil?
    non_generic = Set.new
  end

  case node
  when Ident
    getType(node.name, env, non_generic)
  when Apply
    fun_type    = analyse(node.fn, env, non_generic)
    arg_type    = analyse(node.arg, env, non_generic)
    result_type = TypeVariable.new
    unify Function.new(arg_type, result_type), fun_type
    result_type
  when Lambda
    arg_type        = TypeVariable.new
    new_env         = env.dup
    new_env[node.v] = arg_type
    new_non_generic = non_generic.dup
    new_non_generic.add arg_type
    result_type     = analyse(node.body, new_env, new_non_generic)
    Function.new(arg_type, result_type)
  when Let
    defn_type       = analyse(node.defn, env, non_generic)
    new_env         = env.dup
    new_env[node.v] = defn_type
    analyse(node.body, new_env, non_generic)
  when Letrec
    new_type        = TypeVariable.new
    new_env         = env.dup
    new_env[node.v] = new_type
    new_non_generic = non_generic.dup
    new_non_generic.add new_type
    defn_type       = analyse(node.defn, new_env, new_non_generic)
    unify(new_type, defn_type)
    analyse(node.body, new_env, non_generic)
  end
  #raise "Unhandled syntax node #{t.class}"
end


#
# Get the type of identifier name from the type environment env.
# 
# @param  name [String] The identifier name
# @param  env [String] The type environment mapping from identifier names to types
# @param  non_generic [Set] A set of non-generic TypeVariables
# @raise [ParseError] Raised if name is an undefined symbol in the type environment.
# @return [type] [description]
def getType(name, env, non_generic)
  # puts "Name: #{name}"
  # if name == 'f'
  #   puts env
  #   puts isIntegerLiteral 'f'
  #   puts env.has_key? 'f'
  # end
  if env.include? name
    fresh(env[name], non_generic)
  elsif isIntegerLiteral name
    MyInteger
  else
    raise ParseError, "Undefined symbol #{name}"
  end
end


# 
# Makes a copy of a type expression.
#
# The type t is copied. The the generic variables are duplicated and the
# non_generic variables are shared.
#
# @param  t [type] A type to be copied.
# @param  non_generic [Set<TypeVariable>] A set of non-generic TypeVariables
# 
# @return [type] [description]
def fresh(t, non_generic)
  mappings = Hash.new

  freshrec = Proc.new { |tp|
    p = prune(tp)
    if p.is_a? TypeVariable
      if isGeneric(p, non_generic)
        if not mappings.include? p
          mappings[p] = TypeVariable.new
        end
        mappings[p]
      else
        p
      end
    elsif p.is_a? TypeOperator
      TypeOperator.new(p.name, p.types.map { |x| freshrec.call(x) })
    end
  }

  freshrec.call(t)
end


# 
# Unify the two types t1 and t2
# 
# Makes the types t1 and t2 the same
# 
# @param  t1 [type] The first type to be made equivalent
# @param  t2 [type] The second type to be equivalent
# 
# @raise [TypeError] Raised if the types cannot be unified
# 
# @return nil
def unify(t1, t2)
  a = prune t1
  b = prune t2
  if a.is_a? TypeVariable
    if a != b
      raise(TypeError, "recursive unification") if occursInType(a, b)
      a.instance = b
    end
  elsif a.is_a?(TypeOperator) and b.is_a?(TypeVariable)
    unify(b, a)
  elsif a.is_a?(TypeOperator) and b.is_a?(TypeOperator)
    if (a.name != b.name or a.types.size != b.types.size)
      raise TypeError, "Type mismatch #{a.to_s} != #{b.to_s}"
    end
    a.types.zip(b.types).each do |p, q|
      unify(p, q)
    end
  else
    raise "Not unified"
  end
end


# 
# Returns the currently defining instance of t.
# 
# As a side effect, collapses the list of type instances. The function Prune
# is used whenever a type expression has to be inspected: it will always
# return a type expression which is either an uninstantiated type variable or
# a type operator; i.e. it will skip instantiated variables, and will
# actually prune them from expressions to remove long chains of instantiated
# variables.
# 
# @param  t [type] The type to be pruned
# 
# @return [TypeVariable, TypeOperator] An uninstantiated TypeVariable or a TypeOperator
def prune(t)
  if t.is_a?(TypeVariable) and not t.instance.nil?
    t.instance = prune(t.instance)
    return t.instance
  else
    return t
  end
end



# 
# Checks whether a given variable occurs in a list of non-generic variables
#
# Note that a variables in such a list may be instantiated to a type term,
# in which case the variables contained in the type term are considered
# non-generic.
#
# Note: Must be called with v pre-pruned
# @param  v [TypeVariable] The TypeVariable to be tested for genericity
# @param  non_generic [Set<TypeVariable>] A set of non-generic TypeVariables
# 
# @return [Bool] true if v is a generic variable, otherwise false
def isGeneric(v, non_generic)
  not occursIn(v, non_generic)
end


# 
# Checks whether a type variable occurs in a type expression
# 
# Note: Must be called with v pre-pruned
# @param  v [TypeVariable] The TypeVariable to be tested for
# @param  type2 [type] The type in which to search
# 
# @return [Bool] true if v occurs in type2, else false
def occursInType(v, type2)
  pruned_type2 = prune(type2)

  if pruned_type2 == v
    return true
  elsif pruned_type2.is_a? TypeOperator
    return occursIn(v, pruned_type2.types)
  else
    return false
  end
end


# 
# Checks whether a types variable occurs in any other types
# 
# @param  v [TypeVariable] The TypeVariable to be tested for
# @param  types [type] The sequence of types in which to search
# 
# @return [Bool] true if t occurs in any of types, otherwise false
def occursIn(t, types)
  types.any? { |t2| occursInType(t, t2) }
end


# 
# Checks whether the name is an integer literal string
# @param  name [String] The identifier to check
# 
# @return [Bool] true if name is an integer literal, otherwise false
def isIntegerLiteral(name)
  result = true
  begin
    !!Integer(name)
  rescue ArgumentError, TypeError
    result = false
  end  
  result
end



# 
# Try to evaluate a type, printing the result or reporting errors
# @param  env [Hash] The type environment in which to evaluate the expression
# @param  node [type] The root node of the AST of the expression
# 
# @return [NilClass] nil
def tryExp(env, node)
  print "#{node.to_s} :  "  
  begin
    t = analyse(node, env)
    puts t.to_s
  rescue ParseError, TypeError => e
    puts e
  end
end

def main
  var1 = TypeVariable.new
  var2 = TypeVariable.new
  pair_type = TypeOperator.new('*', [var1, var2])
  var3 = TypeVariable.new

  my_env = { 'pair'  => Function.new(var1, Function.new(var2, pair_type)), 
             'true'  => MyBool,
             'cond'  => Function.new(MyBool, Function.new(var3, Function.new(var3, var3))),
             'zero'  => Function.new(MyInteger, MyBool),
             'pred'  => Function.new(MyInteger, MyInteger),
             'times' => Function.new(MyInteger, Function.new(MyInteger, MyInteger))
           }
  pair = Apply.new(Apply.new(Ident.new('pair'), Apply.new(Ident.new('f'), Ident.new('4'))), Apply.new(Ident.new('f'), Ident.new('true')))

  examples = [
    #factorial
    Letrec.new('factorial', # letrec factorial =
      Lambda.new('n',       # fn n =>
        Apply.new(
          Apply.new(        # cond (zero n) 1
            Apply.new(Ident.new('cond'), # cond (zero n)
              Apply.new(Ident.new('zero'), Ident.new('n'))),
            Ident.new('1')),
          Apply.new(     # times n
            Apply.new(Ident.new('times'), Ident.new('n')),
            Apply.new(Ident.new('factorial'),
              Apply.new(Ident.new('pred'), Ident.new('n')))
            )
          )
        ),    # in
      Apply.new(Ident.new('factorial'), Ident.new('5'))
      ),

      # Should fail:
      # fn x => (pair(x(3) (x(true)))
      Lambda.new("x",
        Apply.new(
          Apply.new(Ident.new("pair"),
            Apply.new(Ident.new("x"), Ident.new("3"))),
          Apply.new(Ident.new("x"), Ident.new("true")))),

      # pair(f(3), f(true))
      Apply.new(
        Apply.new(Ident.new("pair"), Apply.new(Ident.new("f"), Ident.new("4"))),
        Apply.new(Ident.new("f"), Ident.new("true"))),


      # let f = (fn x => x) in ((pair (f 4)) (f true))
      Let.new("f", Lambda.new("x", Ident.new("x")), pair),

      # fn f => f f (fail)
      Lambda.new("f", Apply.new(Ident.new("f"), Ident.new("f"))),

      # let g = fn f => 5 in g g
      Let.new("g",
        Lambda.new("f", Ident.new("5")),
        Apply.new(Ident.new("g"), Ident.new("g"))),

      # example that demonstrates generic and non-generic variables:
      # fn g => let f = fn x => g in pair (f 3, f true)
      Lambda.new("g",
        Let.new("f",
          Lambda.new("x", Ident.new("g")),
          Apply.new(
            Apply.new(Ident.new("pair"),
              Apply.new(Ident.new("f"), Ident.new("3"))
              ),
            Apply.new(Ident.new("f"), Ident.new("true"))))),

            # Function composition
            # fn f (fn g (fn arg (f g arg)))
            Lambda.new("f", Lambda.new("g", Lambda.new("arg", Apply.new(Ident.new("g"), Apply.new(Ident.new("f"), Ident.new("arg"))))))
      ]

  examples.each do |example|
    tryExp(my_env, example)
  end
end

main()