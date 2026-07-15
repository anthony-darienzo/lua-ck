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
-- NOTE: Currently, __parent is searched before __index is called. We could
-- modify this by introducing an __eager attribute to determine which approach
-- to lookup goes first.

-- Declare namespace for package management.
local Prototype = {}

local function PrototypeSearch(pt, f)
    -- Search the parents of Prototype pt for metamethod `f`.
    -- Returns earliest instance of `f` or nil.
    local mt = getmetatable(pt)
    if not mt then return nil end
    
    if mt and mt[f] then
        return mt[f]
    end
   
    local p = mt["__parent"]
    if not p then return nil end

    -- Tail call
    return PrototypeSearch(p,f)
end

local LUA_METAMETHODS_NO_INDEX = {
    "__add", "__sub", "__mul", "__div", "__unm", "__mod", "__pow", "__idiv",
    "__band", "__bor", "__bxor", "__bnot", "__shl", "__shr",
    "__eq", "__lt", "__le",
    "__concat", "__len",
    "__newindex",
    --"__index", -- This is handled separately!
    "__call",
    "__mode", "__close", "__gc",
    "__tostring", "__metatable", "__name", "__pairs", "__ipairs",
    "__iterator", "__usedindex"
}

function Prototype.Conform(Parent, obj)
    -- Modifies in place the metatable of `obj` to point to Parent. Return
    -- modified `obj`.

    local mt = {}
    local old_mt = getmetatable(obj) or {}

    -- Point to Parent.
    mt["__parent"] = Parent
    
    -- Duplicate in case obj shares this metatable with something else.
    for k,v in pairs(old_mt) do
        mt[k] = v
    end
    for _,v in pairs(LUA_METAMETHODS_NO_INDEX) do
        -- For every metamethod exposed by Lua, search all __parents to find a
        -- hit and call that function. Otherwise return nil.
        -- 
        -- If the metatable mt already defines the metamethod, do not overwrite.
        if not mt[v] then
            mt[v] = function(...)
                local f = PrototypeSearch(obj, v) or function() return nil end
                return f(...)
            end
        end
    end
    -- Now handle __index
    mt[Prototype] = {} -- Hide method from other packages.
    mt[Prototype]["__index"] = mt["__index"]
    mt["__index"] = function(t, k)
        local p = mt["__parent"]
        local i = mt[Prototype]["__index"]
        if not i then
            return p[k] -- tail call if we know we won't check i.
        else
            return p[k] or i(t,k) or nil
        end
    end
    -- if obj is the only ref to old_mt, old_mt will be GC'ed.
   setmetatable(obj, mt)
   return obj 
end

function Prototype.Refine(Parent, constructor)
    -- Create a Subclass of Parent. If constructor is provided, put this in a hidden
    -- field to be used by Prototype.new
    
    local Subclass = Parent:Conform({})
    local mt = getmetatable(Subclass)

    mt[Prototype]["__constructor"] = constructor

    return Subclass
end

function Prototype.new(Class, ...)
    -- Create a new instance of Class. If Class has a constructor, call this
    -- with ... as arguments. Adjust metatable of new instance so that Class is
    -- the __parent.
    local mt = getmetatable(Class) or nil
    local constructor = mt[Prototype]["__constructor"] or nil

    if constructor then
        local obj = constructor(...)
        Class:Conform(obj)
        return obj
    else
        local obj = Class:Conform({})
        return obj
    end
end

return Prototype