-- Lua's metatables have an __index method which permits OOP-like programming by
-- specifying a prototypical table for methods.
--
-- However, there is no way to specify an __index for metamethods. This means
-- things like `tostring`, governed by the metamethod __tostring, are not
-- inherited through nested __index references.
--
-- NOTE: This implementation changes the behavior of metamethod lookup: if a
-- metamethod is not-defined, a Prototype *will* return the function:
--   `function() return nil end`
-- This means checking if a metamethod is `nil` will not yield the same behavior
-- as ordinary Lua!
--
-- This is a simple solution. Introduce `__parent`, which behaves like `__index`
-- but works for metamethods too.
--

-- Declare namespace for package management.
local Prototype = {}
local Hidden = {}

local function PrototypeSearch(pt, f)
    -- Search the parents of Prototype pt for metamethod `f`.
    -- Returns earliest instance of `f` or nil.
    local mt = getmetatable(pt)

    -- Rule out trivial case.
    if not mt then return nil end

    -- First possibility is the metatable for pt has already defined this
    -- metamethod. To break cyclic references, use rawget. (Otherwise we may be
    -- calling __index to search for __index!)
    local nearest_f = rawget(mt,f)
    if nearest_f then return nearest_f end

    -- Another possibility is the metamethod existed before Prototype.Conform
    -- was callled on pt.
    local hidden_mt = rawget(mt,Hidden)
    if hidden_mt then
        nearest_f = rawget(hidden_mt,f)
        if nearest_f then return nearest_f end
    end
   
    -- At this point we need to pass to a Parent to search for a method.
    local p = rawget(mt,"__parent")
    if not p then return nil end

    -- Tail call
    return PrototypeSearch(p,f)
end

local LUA_METAMETHODS_MODIFIABLE = {
    __add = true,
    __sub = true,
    __mul = true,
    __div = true,
    __unm = true,
    __mod = true,
    __pow = true,
    __idiv = true,
    __band = true,
    __bor = true,
    __bxor = true, 
    __bnot = true,
    __shl = true,
    __shr = true,
    __eq = true,
    __lt = true,
    __le = true,
    __concat = true,
    __len = true,
    __newindex = true,
    __index = false, -- This is handled separately!
    __call = true,
    __mode = true,
    __close = true,
    __gc = true,
    __tostring = true,
    __metatable = false, -- PrototypeSearch calls getmetatable
    __name = true,
    __pairs = true,
    __ipairs = true,
    __iterator = true,
    __usedindex = true,

    __eager  = false, -- We will add these
    __parent = false
}

-- Do we need these Hidden fields?
function Prototype.Conform(Parent, obj)
    -- Modifies in place the metatable `mt` of `obj` to point to Parent. Return
    -- modified `obj`.
    -- Hides the original metatable of obj in `mt[Hidden]`. This is useful
    -- for breaking cyclic references for PrototypeSearch.
    --
    -- If mt.__eager is not nil when this is called, the object will prioritize
    -- its own __index method before searching a parent.

    local mt = {}
    -- Now swap the metatables.
    mt[Hidden] = getmetatable(obj) or {}
    setmetatable(obj,mt)
    
    -- Point to Parent.
    mt["__parent"] = Parent
    
    -- TODO: Should __newindex also follow __eager?
    for metamethod, modifiable in pairs(LUA_METAMETHODS_MODIFIABLE) do
        -- For every metamethod exposed by Lua, search all __parents to find a
        -- hit and use that function. Otherwise return nil.
        -- 
        -- If the metatable mt already defines the metamethod, do not overwrite.
        --
        -- Lookup happens once when Conform is called. Any updates to parent
        -- metamethods will not be registered!
        if modifiable then
            mt[metamethod] = PrototypeSearch(obj, metamethod) or nil
        end
    end
    
    -- Now handle __index
    local i = mt[Hidden]["__index"] -- original __index
    -- In Lua, if __index points to a table, run lookup there. We need to
    -- replicate that behavior.
    if type(i) == "table" then
        local old_i = i
        i = function(_,k) return old_i[k] end
    end
    local e = mt[Hidden].__eager
   
    if not i then 
        mt.__index = Parent 
    elseif i and e then
        mt.__index = function(t,k)
            return i(t,k) or Parent[k] or nil
        end
    elseif i then
        mt.__index = function(t,k)
            return Parent[k] or i(t,k) or nil
        end
    end
    
   setmetatable(obj, mt)
   return obj 
end

-- Do we need these Hidden fields?
function Prototype.Refine(Parent, constructor)
    -- Create a Subclass of Parent. If `constructor` is provided, this must be a
    -- function. It will be registered in a hidden field used by Prototype.new.
    --
    -- Call Prototype.Refine before defining fields of the Subclass. If you need
    -- to refer to these fields in the body of `constructor`, make the first
    -- argument to `constructor` a table called `This`. `Subclass` will be the
    -- first argument when calling Prototype.new 
    
    local Subclass = {}
    local mt = {}
    mt[Hidden] = {}

    if constructor then
        assert(type(constructor) == "function")
        mt[Hidden]["__constructor"] = constructor
    end

    -- Like Conform, we need to tell a Subclass to look to its Parent for
    -- missing fields.
    mt["__index"]  = Parent
    mt["__parent"] = Parent
    setmetatable(Subclass, mt)
    return Subclass
end

function Prototype.new(Class, ...)
    -- Create a new instance of Class. If Class has a constructor, call this
    -- with ... as arguments. Adjust metatable of new instance so that Class is
    -- the __parent.
    local mt = getmetatable(Class) or nil
    local constructor = mt[Hidden]["__constructor"] or nil

    if constructor then
        local obj = constructor(Class,...)
        Class:Conform(obj)
        return obj
    else
        local obj = Class:Conform({})
        return obj
    end
end

function Prototype.metamethods(x, mts)
    -- For every metamethod provided by mts, override the metatable of x with
    -- that metamethod.
    local mt = getmetatable(x)
    if mt then
        for k,v in pairs(mts) do
            if LUA_METAMETHODS_MODIFIABLE[k] then
                mt[k] = v
            end
        end
    end
end

function Prototype.parent(x)
    local mt = getmetatable(x)
    if mt then
        return mt["__parent"]
    else
        return nil
    end
end

return Prototype