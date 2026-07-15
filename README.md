lua-ck
======

This is an interpreter for the (left-to-right) CBV lambda calculus written in
Lua?

_Why?_ When I have the time this will go into a ComputerCraft project. If you're
reading this, maybe I've already told you why I want this in Minecraft.

Otherwise, it was a fun little thing to spin up.

TODO
----

1. ~~Pretty printer:~~
   * ~~Right now I use Lua table pointers to label every syntactic object. This~~
      ~~means that a lot of things can be checked by pointer equality. However, it~~
      ~~also means my dirty implementation is horrendous to read.~~
2. Clean up code:
   * Think about the logic of when well-definedness of syntactic objects should be checked.
      Streamline Lua metatables for inheritance when appropriate.
3. Add basic operations.
   * Make this an interpreted language.
   * ComputerCraft primitives.
4. `call/cc`
   * All my homies love classical realizability.
