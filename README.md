# hm-rb

An implementation of the Hindley-Milner type inference/reconstruction algorithm in Ruby.

## About
This implementation is based on the [python version](http://smallshire.org.uk/sufficientlysmall/2010/04/11/a-hindley-milner-type-inference-implementation-in-python/), making this the fifth in the line of the implementations.

This was done in order to better understand how HM-inference, and Algorithm W work for my language [Brick](https://github.com/brick-lang). There will probably follow either a C or C++ version, that is closer to the Visitor pattern, in order to make AST traversals easy, but without Boost.
##Usage
```bash
ruby hm.rb
```

## Generate Documentation
```bash
yard doc hm.rb
```
