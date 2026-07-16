-- Lua's only datastructure is the hash table. This module will allow us to
-- refer to basic 'inductive types' as labeled tables.

-- Eventually, we will build a CK-machine.

local Prototype = require "Prototype"

local KINDS = {
    TYPE = "type",
    TERM = "term",
    CONT = "continuation",
    ENVR = "environment",
    LITR = "literal"
}

-- The general structure of a repr is a kind of hacky S-expression. There are
-- three fields: 'kind', 'head', and 'tail'. The 'head' is a repr that
-- represents the prototype of the term. The 'tail' is a list of reprs that
-- represent the arguments to the term.
--
-- Normally one also includes an 'identifier' field in a term. For Lua, this is
-- not necessary! This is because Lua tables are pass by reference.
local Repr = Prototype:Refine(function (This, kind, head, ...)
    local tail = {...}
    local obj = {kind = kind, head = head, tail = tail}

    local i = tostring(This.pretty_ctr)
    This.pretty_index[obj] = function() return tostring(i) end
    This.pretty_ctr = This.pretty_ctr + 1

    return obj
end)

Repr.pretty_ctr = 0
Repr.pretty_index = {}

-- If either a key or value is GC'ed, the whole pair gets GC'ed.
-- Basically, the pretty printer shouldn't block anything from getting GC'ed.
setmetatable(Repr.pretty_index, { __mode = "k" })

Repr:metamethods {
    __tostring = function (self)
        local s = Repr.pretty_index[self]
        if s then
            return tostring( s() or "" )
        else
            local tail_str = ""
            for k, v in pairs(self.tail) do
                tail_str = tail_str .. tostring(v) .. ", "
            end
            return string.format("Repr(%s, %s, {%s})", self.kind, tostring(self.head), tail_str)
        end
    end
}

function Repr.register (self, l)
    if type(l) == "string" then
        Repr.pretty_index[self] = function() return l end
    elseif type(l) == "function" then
        Repr.pretty_index[self] = l
    end
end

-- Lua tables are pass by reference. But we will want a single instance of nil
-- in order to check for bot.
--
-- This is a bit hacky since it introduces a cyclic reference. Oh well.
Repr.bot = Repr:new(KINDS.LITR, nil)
Repr.bot.head = Repr.bot
Repr.bot:register("Repr(nil)")

-- Now we can just check if a repr is nil by checking if it points to the same
-- table in memory!
function Repr.is_bot (self, r)
    return r == self.bot
end

function Repr.verify_t (self)
    return Prototype.parent(self) == Repr and self.kind and self.head and self.tail
end

function Repr.fresh ()
    -- Pass a fresh table to get a new ref.
    return Repr:new(KINDS.LITR)
end

-- Tables are pass by reference. If we want to duplicate a repr, we will need to
-- copy its elements.
function Repr.dupl(self)
    return Repr:new(self.kind, self.head, table.unpack(self.tail))
end

-- Now let's use the Repr prototype to define the syntax of a lambda calculus.
local Term = Repr:Refine(function(This, CAT, x1, x2) 
    return This.Constructors[CAT](This, x1, x2)
end)

-- Since the head of a repr is a repr, the combinators of our lambda calculus
-- are reprs. These for our CATegories.
Term.VAR = Repr:new(KINDS.LITR, Repr.fresh())
Term.LAM = Repr:new(KINDS.LITR, Repr.fresh())
Term.APP = Repr:new(KINDS.LITR, Repr.fresh())

Term.VAR:register("VAR")
Term.LAM:register("LAM")
Term.APP:register("APP")

-- How a term is built depends on the CAT.
Term.Constructors = {}

Term.Constructors[Term.VAR] = function(This, name)
    local repr = Repr:new(KINDS.TERM, Term.VAR, name)
    local s = Repr.pretty_index[repr]
    -- Vars are represented as "xi" by default.
    repr:register(function()
        return "x" .. tostring(s())
    end)
    return repr
end

Term.Constructors[Term.APP] = function(This, f, x)
    local repr = Repr:new(KINDS.TERM, Term.APP, f, x)
    -- M N is represented as "M" "N", by default
    repr:register(function()
        return string.format("(%s) (%s)", tostring(f), tostring(x))
    end)
    return repr
end

Term.Constructors[Term.LAM] = function(This, x, body)
    local repr = Repr:new(KINDS.TERM, Term.LAM, x, body)
    repr:register(function()
        return string.format("lam %s . (%s)", tostring(x), tostring(body))
    end)
    return repr
end

function Term.var (name)
    return Term:new(Term.VAR, name)
end

function Term.app (f, x)
    return Term:new(Term.APP, f, x)
end

function Term.lam (x, body)
    return Term:new(Term.LAM, x, body)
end

function Term.fresh_var ()
    return Term:new(Term.VAR, Repr.fresh())
end

function Term.is_var(t)
    return Prototype.parent(t) == Term
        and t.head == Term.VAR
        and #t.tail == 1
end

function Term.var_name(t)
    assert(Term.is_var(t), "Invalid variable: " .. tostring(t))
    return t.tail[1]
end

function Term.app_func(t)
    assert(t.kind == KINDS.TERM and t.head == Term.APP, "Invalid application: " .. tostring(t))
    return t.tail[1]
end

function Term.app_arg(t)
    assert(t.kind == KINDS.TERM and t.head == Term.APP, "Invalid application: " .. tostring(t))
    return t.tail[2]
end

function Term.lam_bound_var(t)
    assert(t.kind == KINDS.TERM and t.head == Term.LAM, "Invalid lambda: " .. tostring(t))
    return t.tail[1]
end

function Term.lam_body(t)
    assert(t.kind == KINDS.TERM and t.head == Term.LAM, "Invalid lambda: " .. tostring(t))
    return t.tail[2]
end

-- If this were just the lambda calculus, we would need to implement
-- capture-avoiding substitution now. Instead, applications will push arguments
-- to an environment.
--
-- An environment is a hashtable from variables to closures. Lua makes this
-- easy.
local Closure = Prototype:Refine(function (This, t, e)
    return {term = t, env = e}
end)

Closure:metamethods {
    __tostring = function(self)
        local s = tostring(self.term)
        return string.format("{%s, ..}", s)
    end
}

-- We put the environment's contents into a new field called `bindings`. Head
-- and tail are empty.  To make things easy, we use __newindex to amend the
-- environment in place.
local Envr = Repr:Refine(function (This, bindings)
    local repr = Repr:new(KINDS.ENVR, Repr.bot)
    
    repr.bindings = bindings
    local s = Repr.pretty_index[repr]

    repr:register(function()
        local cts = ""
        for k,v in pairs(repr.bindings) do
            cts = cts .. tostring(k) .. " -> " .. tostring(v) .. ", "
        end
        return "Envr(" .. tostring(s())  .. "){ " .. cts .. "}"
    end)

    setmetatable(repr, {
        __eager = true, -- Tell Prototype to use this __index first.
        __index = repr.bindings,
        __newindex = function(self, k, v)
            assert(Term.is_var(k), "Invalid variable: " .. tostring(k))
            self.bindings[k] = v
        end
    })

    return repr
end)

Envr.empty = Envr:new {}

function Envr.dupl (self)
    local new_bindings = {}
    for k, v in pairs(self.bindings) do
        new_bindings[k] = v
    end
    return Envr:new(new_bindings)
end

-- If E is an environment, and x is a repr of a variable, then E[x] is the term
-- that E assigns to x. If E does not assign a term to x, then E[x] is nil.

-- All that remains is to define the continuation class. A continuation is a
-- list of frames. Each frame is a pair of a term and an environment. The term
-- is the term that is being evaluated, and the environment is the environment
-- in which the term is being evaluated.

-- To keep things, simple, we will only implement three continuation frames we
-- need for a CK-machine: push and enter, and a halt frame.
local Cont = Repr:Refine(function (This, CAT, x, env, k) 
    local repr = Repr:new(KINDS.CONT, CAT, x, env, k)
    
    local s = This.Prettify_Methods[CAT](x, env, k)
    repr:register(s)
    return repr
end)

Cont.HALT  = Repr:new(KINDS.CONT, Repr.fresh())
Cont.PUSH  = Repr:new(KINDS.CONT, Repr.fresh())
Cont.ENTER = Repr:new(KINDS.CONT, Repr.fresh())

Cont.HALT:register("HALT")
Cont.PUSH:register("PUSH")
Cont.ENTER:register("ENTER")

-- We have to construct the pretty printer at define time.
Cont.Prettify_Methods = {}

Cont.Prettify_Methods[Cont.HALT] = function(x, env, k)
    return function ()
        return "Halt"
    end
end

Cont.Prettify_Methods[Cont.PUSH] = function(x, env, k)
    return function () 
        return string.format("Push(%s, %s) :: %s", tostring(x), tostring(env), tostring(k))
    end
end

Cont.Prettify_Methods[Cont.ENTER] = function(x, env, k)
    return function()
        return string.format("[_ -> (%s, %s)] :: %s", tostring(x), tostring(env), tostring(k))
    end
end

Cont.halt = Cont:new(Cont.HALT, Repr.bot)

Cont.push = function(arg, env, k)
    -- TODO: Check that arg is a term and env is an environment.
    local c = Cont:new(Cont.PUSH, arg, env, k)
    c.arg = function() return c.tail[1] end
    c.env = function() return c.tail[2] end
    c.k   = function() return c.tail[3] end
    return c
end

Cont.enter = function(lam, env, k)
    -- TODO: Check that value is a term and env is an environment.
    local c = Cont:new(Cont.ENTER, lam, env, k)
    c.lam = function() return c.tail[1] end
    c.env  = function() return c.tail[2] end
    c.k    = function() return c.tail[3] end
    return c
end

function Cont.is_halt(c)
    return c == Cont.halt
end

-- Finally, we can define the CK-machine. The CK-machine is a state machine that
-- evaluates terms in a given environment. The state of the CK-machine is a
-- triple of a term, an environment, and a continuation. The CK-machine has two
-- rules: the push rule and the enter rule. The push rule applies a function
-- to an argument, and the enter rule propagates an argument to a function body
-- in the continuation.

-- When the CK-machine reaches a halt state, if the current term is a variable,
-- then the machine will look up the variable in the environment. Otherwise, the
-- machine has more computation to do, or lookup has failed because the original
-- program had a free variable. In that case, the machine will return the
-- current term verbatim.
local CK = Prototype:Refine(function (This, term, env, cont)
    return {term = term, env = env, cont = cont}
end)

CK:metamethods {
    __tostring = function(self)
        return string.format("< %s || %s || %s >", self.term, self.env, self.cont)
    end
}

CK.steps = {}
CK.steps[Term.VAR] = {}

-- We will need our environment to point to closures of a lambda
-- term, which means environments will have type:
-- `environment` : `repr` -> (`repr`, `environment`)
-- 
-- Schematically, these are the transition rules.
--
-- (M N, e, k) -> (M, e:dupl() , push(N, e) :: k)
-- (lam x. M, e', push(N,e) :: k) -> (N, e, enter(lam x.M, e') :: k)
-- (x, e, k) -> (v', e', k), where e[x] = (v',e')
--


-- (x, e, HALT) -> (v', e', HALT), if e[x] = (v',e'), else return "x".
CK.steps[Term.VAR][Cont.HALT] = function(self)
    local closure = self.env[self.term]    
    if closure then
        self.term   = closure.term
        self.env    = closure.env
        return
    else
        return tostring(self.term)
    end

    error("This line should be unreachable.")
end

-- (x, e', push(M,e) :: k) -> (e'[x], e', push(M,e) :: k) or x @PUSH M.
CK.steps[Term.VAR][Cont.PUSH] = function(self)
    local closure = self.env[self.term]
    if closure then
        self.term   = closure.term
        self.env    = closure.env
        return
    else
        local arg = self.cont.arg()
        return string.format("%s @PUSH %s", tostring(self.term), tostring(arg))
    end

    error("This line should be unreachable.")
end

-- (y, e', enter(lam x. M, e) :: k) -> (M, e[x -> (y,e')], k)
CK.steps[Term.VAR][Cont.ENTER] = function(self)
    local term = self.term
    local env  = self.env    
    local cont = self.cont

    local lam = cont.lam()
    
    local bound_var = Term.lam_bound_var(lam)
    local body = Term.lam_body(lam)

    local kenv  = cont.env()
    local k     = cont.k()

    -- Should we duplicate kenv?
    -- I don't think so, since we can think of (lam x. M, e) as a closure which
    -- was already existent.
    kenv[bound_var] = Closure:new(term, env)

    self.term   = body
    self.env    = kenv
    self.cont   = k
end

CK.steps[Term.LAM] = {}

-- Lambdas are values.
CK.steps[Term.LAM][Cont.HALT] = function(self)
    return tostring(self.term)
end

-- (lam x. t, e', push (M,e) :: k) -> (M, e, enter (lam x. t, e') :: k)
-- Probably should rename the "return" continuation to, e.g., "call".
-- All we are doing is left-to-right call-by-value.
CK.steps[Term.LAM][Cont.PUSH] = function(self)
    local cont = self.cont
    local arg = cont.arg()
    local senv = self.env -- e'
    local kenv = cont.env() -- e
    local k = cont.k()

    local lam = self.term
    
    self.term = arg
    self.env = kenv
    self.cont = Cont.enter(lam, senv, k)
end

-- The environment probably needs to track e'
-- (lam x. t, e', enter (lam x' . M, e) :: k) 
--      -> (M, e[x' -> (lam x . t, e')], k)
CK.steps[Term.LAM][Cont.ENTER] = function(self)
    local term = self.term -- lam x . t
    local cont = self.cont
    local lam = cont.lam() -- lam x'. M

    local bound_var = Term.lam_bound_var(lam)
    local body = Term.lam_body(lam)

    local env = self.env -- e'
    local kenv = cont.env() -- e
    local k = cont.k()

    kenv[bound_var] = Closure:new(term, env)

    self.term = body
    self.env = kenv
    self.cont = k
end

CK.steps[Term.APP] = {}

-- (M N, e, k) -> (M, e:dupl(), push (N, e) :: k)
-- All rules are the same, just with different continuation.
CK.steps[Term.APP][Cont.HALT] = function(self)
    local func = Term.app_func(self.term)
    local arg = Term.app_arg(self.term)
    
    local env = self.env
    local new_env = Envr.dupl(env)

    self.term = func
    self.env = new_env
    self.cont = Cont.push(arg, env, self.cont)
end

CK.steps[Term.APP][Cont.PUSH] = function(self)
    local func = Term.app_func(self.term)
    local arg = Term.app_arg(self.term)

    local env = self.env
    local new_env = Envr.dupl(env)
    
    self.term = func
    self.env = new_env
    self.cont = Cont.push(arg, env, self.cont)
end

CK.steps[Term.APP][Cont.ENTER] = function(self)
    local func = Term.app_func(self.term)
    local arg = Term.app_arg(self.term)

    local env = self.env
    local new_env = Envr.dupl(env)

    self.term = func
    self.env = new_env
    self.cont = Cont.push(arg, env, self.cont)
end


function CK.step (self)
    -- We first pattern match on the term. Since the head of every term is a
    -- repr describing the term's constructor, this is just a table lookup.
    local term = self.term
    local cont = self.cont

    local term_head = term.head
    local cont_head = cont.head

    return CK.steps[term_head][cont_head](self)
end

function CK.run (self)
    while true do
        local result = self:step()
        if result then
            return result
        end
    end
end

function CK.trace (self)
    print(self)
    indent = ""
    while true do
        local result = self:step()
        if result then
            print("===> " .. tostring(result))
            return
        end
        indent = indent .. "  "
        print(indent .. "-> " .. tostring(self))
    end
end

-- Now we write an example program.
x = Term.fresh_var()
x:register("x")

y = Term.fresh_var()
y:register("y")

z = Term.fresh_var()
z:register("z")


omega = Term.lam(x, Term.app(x, x))
Omega = Term.app(omega, omega)

program = Term.app(
    Term.app(
        Term.lam(x, Term.lam(y, x)),
        z),
    omega
)

ck = CK:new(program, Envr.empty, Cont.halt)
ck:trace()