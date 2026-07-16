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

local function fst(t)
    return t[1]
end

local function snd(t)
    return t[2]
end

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
-- An environment is a hashtable from variables to terms. Lua makes this easy.
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

Envr.empty = Envr:new({})

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
-- need for a CK-machine: push and return, and a halt frame.
local Cont = Repr:Refine(function (This, CAT, x, env, k) 
    local repr = Repr:new(KINDS.CONT, CAT, x, env, k)
    
    local s = This.Prettify_Methods[CAT](x, env, k)
    repr:register(s)
    return repr
end)

Cont.HALT = Repr:new(KINDS.CONT, Repr.fresh())
Cont.PUSH = Repr:new(KINDS.CONT, Repr.fresh())
Cont.RETURN = Repr:new(KINDS.CONT, Repr.fresh())

Cont.HALT:register("HALT")
Cont.PUSH:register("PUSH")
Cont.RETURN:register("RETURN")

-- We have to construct the pretty printer at define time.
Cont.Prettify_Methods = {}

Cont.Prettify_Methods[Cont.HALT] = function(x, env, k)
    return function ()
        return "HALT"
    end
end

Cont.Prettify_Methods[Cont.PUSH] = function(x, env, k)
    return function () 
        return string.format("PUSH(%s,%s) :: %s", tostring(x), tostring(env), tostring(k))
    end
end

Cont.Prettify_Methods[Cont.RETURN] = function(x, env, k)
    return function()
        string.format("[_ -> (%s,%s)] :: %s", tostring(x), tostring(env), tostring(k))
    end
end

Cont.Halt = Cont:new(Cont.HALT, Repr.bot)

Cont.Push = function(arg, env, k)
    -- TODO: Check that func is a term and env is an environment.
    return Cont:new(Cont.PUSH, arg, env, k)
end

Cont.Return = function(func, env, k)
    -- TODO: Check that value is a term and env is an environment.
    return Cont:new(Cont.RETURN, func, env, k)
end

function Cont.is_halt(c)
    return c == Cont.Halt
end

function Cont.push_arg(c)
    assert(c.kind == KINDS.CONT and c.head == Cont.PUSH, "Invalid push frame: " .. tostring(c))
    return c.tail[1]
end

function Cont.push_env(c)
    assert(c.kind == KINDS.CONT and c.head == Cont.PUSH, "Invalid push frame: " .. tostring(c))
    return c.tail[2]
end

function Cont.push_cont(c)
    assert(c.kind == KINDS.CONT and c.head == Cont.PUSH, "Invalid push frame: " .. tostring(c))
    return c.tail[3]
end

function Cont.return_func(c)
    assert(c.kind == KINDS.CONT and c.head == Cont.RETURN, "Invalid return frame: " .. tostring(c))
    return c.tail[1]
end

function Cont.return_env(c)
    assert(c.kind == KINDS.CONT and c.head == Cont.RETURN, "Invalid return frame: " .. tostring(c))
    return c.tail[2]
end

function Cont.return_cont(c)
    assert(c.kind == KINDS.CONT and c.head == Cont.RETURN, "Invalid return frame: " .. tostring(c))
    return c.tail[3]
end

-- Finally, we can define the CK-machine. The CK-machine is a state machine that
-- evaluates terms in a given environment. The state of the CK-machine is a
-- triple of a term, an environment, and a continuation. The CK-machine has two
-- rules: the apply rule and the return rule. The apply rule applies a function
-- to an argument, and the return rule returns a value to the continuation.

-- When the CK-machine reaches a halt state, if the current term is a variable,
-- then the machine will look up the variable in the environment. Otherwise, the
-- machine has more computation to do, or lookup has failed because the original
-- program had a free variable. In that case, the machine will return the
-- current term verbatim.
local CK = Prototype:Refine(function (This, term, env, cont)
    return {term = term, env = env, cont = cont}
end)

CK.steps = {}
CK.steps[Term.VAR] = {}

-- We will need our environment to point to closures of a lambda
-- term, which means environments will have type:
-- `environment` : `repr` -> (`repr`, `environment`)
-- 
-- Schematically, these are the transition rules.
--
-- (M N, e, k) -> (M, e:dupl() , push(N, e) :: k)
-- (lam x. M, e', push(N,e) :: k) -> (N, e, return(lam x.M, e') :: k)
-- (x, e, k) -> (v', e', k), where e[x] = (v',e')
--


-- (x, e, HALT) -> (v', e', HALT), if e[x] = (v',e'), else return "x".
CK.steps[Term.VAR][Cont.HALT] = function(self)
    local closure = self.env[self.term]    
    if closure then
        self.term   = fst(closure)
        self.env    = snd(closure)
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
        self.term   = fst(closure)
        self.env    = snd(closure)
        return
    else
        local arg = Cont.push_arg(self.cont)
        return string.format("%s @PUSH %s", tostring(self.term), tostring(arg))
    end

    error("This line should be unreachable.")
end

-- (y, e', return(lam x. M, e) :: k) -> (M, e[x -> (y,e')], k)
CK.steps[Term.VAR][Cont.RETURN] = function(self)
    local term = self.term
    local env  = self.env    
    local cont = self.cont

    local lam = Cont.return_func(cont)
    
    local bound_var = Term.lam_bound_var(lam)
    local body = Term.lam_body(lam)

    local kenv  = Cont.return_env(cont)
    local k     = Cont.return_cont(cont)

    -- Should we duplicate kenv?
    -- I don't think so, since we can think of (lam x. M, e) as a closure which
    -- was already existent.
    kenv[bound_var] = {term, env}

    self.term   = body
    self.env    = kenv
    self.cont   = k
end

CK.steps[Term.LAM] = {}

-- Lambdas are values.
CK.steps[Term.LAM][Cont.HALT] = function(self)
    return tostring(self.term)
end

-- (lam x. t, e', push (M,e) :: k) -> (M, e, return (lam x. t, e') :: k)
-- Probably should rename the "return" continuation to, e.g., "call".
-- All we are doing is left-to-right call-by-value.
CK.steps[Term.LAM][Cont.PUSH] = function(self)
    local arg = Cont.push_arg(self.cont)
    local senv = self.env -- e'
    local kenv = Cont.push_env(self.cont) -- e
    local k = Cont.push_cont(self.cont)

    local lam = self.term
    
    self.term = arg
    self.env = kenv
    self.cont = Cont.Return(lam, senv, k)
end

-- The environment probably needs to track e'
-- (lam x. t, e', return (lam x' . M, e) :: k) 
--      -> (M, e[x' -> (lam x . t, e')], k)
CK.steps[Term.LAM][Cont.RETURN] = function(self)
    local term = self.term -- lam x . t
    local lam = Cont.return_func(self.cont) -- lam x'. M

    local bound_var = Term.lam_bound_var(lam)
    local body = Term.lam_body(lam)

    local env = self.env -- e'
    local kenv = Cont.return_env(self.cont) -- e
    local k = Cont.return_cont(self.cont)

    kenv[bound_var] = {term, env}

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
    self.cont = Cont.Push(arg, env, self.cont)
end

CK.steps[Term.APP][Cont.PUSH] = function(self)
    local func = Term.app_func(self.term)
    local arg = Term.app_arg(self.term)

    local env = self.env
    local new_env = Envr.dupl(env)
    
    self.term = func
    self.env = new_env
    self.cont = Cont.Push(arg, env, self.cont)
end

CK.steps[Term.APP][Cont.RETURN] = function(self)
    local func = Term.app_func(self.term)
    local arg = Term.app_arg(self.term)

    local env = self.env
    local new_env = Envr.dupl(env)

    self.term = func
    self.env = new_env
    self.cont = Cont.Push(arg, env, self.cont)
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

-- Now we write an example program.
x = Term.fresh_var()
x:register(function() return "x" end)

y = Term.fresh_var()
y:register(function() return "y" end)

z = Term.fresh_var()
z:register(function() return "z" end)


omega = Term.lam(x, Term.app(x, x))
Omega = Term.app(omega, omega)

program = Term.app(
    Term.app(
        Term.lam(x, Term.lam(y, x)),
        z),
    omega
)

ck_state = CK:new(program, Envr.empty, Cont.Halt)

print(tostring(program))
print("===============")
res = ck_state:run()
print(string.format("FINAL VALUE: %s", res)) -- should print y
print("===============")
print(string.format("FINAL TERM: %s", tostring(ck_state.term)))
print(string.format("FINAL CONT: %s", tostring(ck_state.cont)))
print(string.format("FINAL ENVR: %s", tostring(ck_state.env)))
